"""Genshin NSFW Discord bot — art, IRL cosplay and clips from public boorus."""

from __future__ import annotations

import asyncio
import collections
import io
import json
import logging
import os
import random
import time
from dataclasses import dataclass, field, replace
from typing import Any, Callable

import aiohttp
import discord
from discord import app_commands

try:
    from dotenv import load_dotenv

    load_dotenv()
except ImportError:
    pass

discord.utils.setup_logging(level=logging.INFO)
log = logging.getLogger("genshinbot")

TOKEN = os.getenv("DISCORD_TOKEN", "").strip()
GUILD_ID = os.getenv("GUILD_ID", "").strip()
GELBOORU_API_KEY = os.getenv("GELBOORU_API_KEY", "").strip()
GELBOORU_USER_ID = os.getenv("GELBOORU_USER_ID", "").strip()

UA = "GenshinBooruBot/3.0"
VIDEO_EXTS = {"mp4", "webm"}
IMAGE_EXTS = {"jpg", "jpeg", "png", "gif", "webp"}
MAX_FILES = 10
CONCURRENCY = 4
HEADROOM = 64 * 1024
DEFAULT_LIMIT = 8 * 1024 * 1024
PAGE_TRIES = 2
DANBOORU_PAGE_SIZE = 100
RESULT_CACHE_MAX = 25
FOOTER_SEP = "  \u27e9  "

RECENT = collections.deque(maxlen=800)
CACHE: dict[tuple, list] = {}
CACHE_MAX = 512
PAGE_BOUNDS: dict[tuple[str, str], int] = {}
COUNTS: dict[str, int] = {}
_LIMITERS: dict[str, "HostLimiter"] = {}
_RESULTS: collections.OrderedDict[int, "Outcome"] = collections.OrderedDict()


# --------------------------------------------------------------- utilities

class HostLimiter:
    """Serialises requests to one host and enforces a minimum gap between them."""

    __slots__ = ("_interval", "_lock", "_last")

    def __init__(self, interval: float) -> None:
        self._interval = interval
        self._lock = asyncio.Lock()
        self._last = 0.0

    async def wait(self) -> None:
        async with self._lock:
            delta = time.monotonic() - self._last
            if delta < self._interval:
                await asyncio.sleep(self._interval - delta)
            self._last = time.monotonic()


def _limiter(host: str, interval: float) -> HostLimiter:
    lim = _LIMITERS.get(host)
    if lim is None:
        lim = HostLimiter(interval)
        _LIMITERS[host] = lim
    return lim


def _cache_put(key, value) -> None:
    if len(CACHE) >= CACHE_MAX:
        CACHE.pop(next(iter(CACHE)))
    CACHE[key] = value


def _remember(message_id: int, outcome: "Outcome") -> None:
    _RESULTS[message_id] = outcome
    _RESULTS.move_to_end(message_id)
    while len(_RESULTS) > RESULT_CACHE_MAX:
        _RESULTS.popitem(last=False)


def _int(value) -> int:
    try:
        return int(value or 0)
    except (TypeError, ValueError):
        return 0


def _norm(text: str) -> str:
    return "".join(c for c in (text or "").lower() if c.isalnum())


def _ext_from_url(url: str, fallback: str = "") -> str:
    if not url:
        return fallback
    tail = url.split("?", 1)[0].split("#", 1)[0].rsplit("/", 1)[-1]
    if "." not in tail:
        return fallback
    ext = tail.rsplit(".", 1)[-1].lower()
    return ext if 1 <= len(ext) <= 5 and ext.isalnum() else fallback


def _as_list(value) -> list:
    if value is None:
        return []
    if isinstance(value, list):
        return value
    if isinstance(value, dict):
        return [value]
    return []


def _dedupe(parts) -> str:
    seen, out = set(), []
    for part in parts:
        part = part.strip()
        if part and part not in seen:
            seen.add(part)
            out.append(part)
    return " ".join(out)


def _mk_post(site, pid, full, sample, preview, thumb, ext, size, page) -> dict:
    ext = (ext or "").lower().strip()
    if ext not in IMAGE_EXTS and ext not in VIDEO_EXTS:
        ext = _ext_from_url(full) or _ext_from_url(sample) or "jpg"
    return {
        "site": site,
        "id": pid,
        "full": full,
        "sample": sample or full,
        "preview": preview or sample or full,
        "thumb": thumb or preview or sample or full,
        "ext": ext,
        "is_video": ext in VIDEO_EXTS,
        "size": _int(size),
        "page": page,
    }



def _pick_ext(post: dict, ctype: str) -> str:
    ctype = ctype.lower().split(";")[0].strip()

    if ctype.startswith("video/"):
        ext = post.get("ext", "")
        return ext if ext in VIDEO_EXTS else "mp4"

    for needle, ext in (
        ("image/gif", "gif"),
        ("image/webp", "webp"),
        ("image/png", "png"),
        ("image/jpeg", "jpg"),
    ):
        if needle in ctype:
            return ext

    ext = post.get("ext", "")
    return ext if ext in VIDEO_EXTS else "jpg"



# ------------------------------------------------------------ character list

# Bare names. Resolved at startup against Danbooru's character tag index, which
# supplies the `_(genshin_impact)` disambiguator where one exists.
CHARACTERS: list[tuple[str, str]] = [
    ("Aloy", "aloy"), ("Amber", "amber"), ("Arlecchino", "arlecchino"),
    ("Barbara", "barbara"), ("Beidou", "beidou"), ("Candace", "candace"),
    ("Charlotte", "charlotte"), ("Chasca", "chasca"), ("Chevreuse", "chevreuse"),
    ("Chiori", "chiori"), ("Citlali", "citlali"), ("Clorinde", "clorinde"),
    ("Collei", "collei"), ("Columbina", "columbina"), ("Dehya", "dehya"),
    ("Diona", "diona"), ("Emilie", "emilie"), ("Escoffier", "escoffier"),
    ("Eula", "eula"), ("Faruzan", "faruzan"), ("Fischl", "fischl"),
    ("Furina", "furina"), ("Ganyu", "ganyu"), ("Hu Tao", "hu_tao"),
    ("Iansan", "iansan"), ("Ineffa", "ineffa"), ("Jahoda", "jahoda"),
    ("Jean", "jean"), ("Kachina", "kachina"), ("Kamisato Ayaka", "kamisato_ayaka"),
    ("Keqing", "keqing"), ("Kirara", "kirara"), ("Klee", "klee"),
    ("Kujou Sara", "kujou_sara"), ("Kuki Shinobu", "kuki_shinobu"), ("La Signora", "la_signora"),
    ("Lan Yan", "lan_yan"), ("Lauma", "lauma"), ("Layla", "layla"),
    ("Linnea", "linnea"), ("Lisa", "lisa"), ("Lumine", "lumine"),
    ("Lynette", "lynette"), ("Mavuika", "mavuika"), ("Mona", "mona"),
    ("Mualani", "mualani"), ("Nahida", "nahida"), ("Navia", "navia"),
    ("Nefer", "nefer"), ("Nicole", "nicole"), ("Nilou", "nilou"),
    ("Ningguang", "ningguang"), ("Noelle", "noelle"), ("Odette", "odette"),
    ("Paimon", "paimon"), ("Qiqi", "qiqi"), ("Raiden Shogun", "raiden_shogun"),
    ("Rosaria", "rosaria"), ("Sandrone", "sandrone"), ("Sangonomiya Kokomi", "sangonomiya_kokomi"),
    ("Sayu", "sayu"), ("Shenhe", "shenhe"), ("Skirk", "skirk"),
    ("Sucrose", "sucrose"), ("Varesa", "varesa"), ("Vesna", "vesna"),
    ("Vodyanitsa", "vodyanitsa"), ("Xianyun", "xianyun"), ("Xiangling", "xiangling"),
    ("Xilonen", "xilonen"), ("Xinyan", "xinyan"), ("Yae Miko", "yae_miko"),
    ("Yanfei", "yanfei"), ("Yaoyao", "yaoyao"), ("Yelan", "yelan"),
    ("Yoimiya", "yoimiya"), ("Yumemizuki Mizuki", "yumemizuki_mizuki"), ("Yun Jin", "yun_jin"),
    ("Zibai", "zibai"),
]

RESOLVED_CHARS: list[tuple[str, str]] = list(CHARACTERS)
CHAR_BY_TAG: dict[str, str] = {tag: display for display, tag in CHARACTERS}

POPULAR_TAGS = [
    "solo", "1girl", "swimsuit", "bikini", "lingerie", "nude", "topless",
    "large_breasts", "small_breasts", "cleavage", "underboob", "sideboob",
    "thighhighs", "stockings", "pantyhose", "no_panties", "skirt_lift",
    "kimono", "yukata", "cheongsam", "maid", "nurse", "bunny_girl", "cat_ears",
    "fox_ears", "glasses", "ponytail", "twintails", "braid", "long_hair",
    "short_hair", "wet", "wet_clothes", "beach", "onsen", "pool", "cosplay",
    "ahegao", "paizuri", "spread_legs", "from_behind", "mating_press",
    "doggystyle", "missionary", "cowgirl_position", "creampie", "cum",
    "censored", "uncensored", "animated", "video", "webm", "faceless_male",
    "yuri", "harem", "bondage", "see-through", "photo_(medium)", "feet",
]

PRESETS: dict[str, dict[str, str]] = {
    "default": {},
    "solo": {"extra_tags": "solo"},
    "swimsuit": {"extra_tags": "swimsuit"},
    "bikini": {"extra_tags": "bikini"},
    "lingerie": {"extra_tags": "lingerie"},
    "nude": {"extra_tags": "nude"},
    "large_breasts": {"extra_tags": "large_breasts"},
    "small_breasts": {"extra_tags": "small_breasts"},
    "thighhighs": {"extra_tags": "thighhighs"},
    "stockings": {"extra_tags": "stockings"},
    "paizuri": {"extra_tags": "paizuri"},
    "ahegao": {"extra_tags": "ahegao"},
    "creampie": {"extra_tags": "creampie"},
    "yuri": {"extra_tags": "yuri"},
    "uncensored": {"extra_tags": "uncensored"},
    "maid": {"extra_tags": "maid"},
    "bunny": {"extra_tags": "bunny_girl"},
    "kimono": {"extra_tags": "kimono"},
    "wet": {"extra_tags": "wet"},
    "beach": {"extra_tags": "beach"},
    "glasses": {"extra_tags": "glasses"},
    "feet": {"extra_tags": "feet"},
    "videos": {"mode": "video"},
    "gifs": {"mode": "video", "extra_tags": "animated"},
    "cosplay": {"kind": "cosplay", "rating": "any"},
    "irl": {"kind": "cosplay", "rating": "any"},
}


# ---------------------------------------------------------------- sources

@dataclass(frozen=True)
class Source:
    name: str
    url: str
    host: str
    max_page: int
    params: Callable[[str, int], dict[str, Any]]
    parse: Callable[[Any], list[dict]]
    min_interval: float = 0.4
    cosplay: bool = False
    # Tags appended when cosplaying. Danbooru's `cosplay` includes drawn
    # crossplay, so it also requires `photo_(medium)` for real photographs.
    cosplay_tags: tuple[str, ...] = ("cosplay",)
    auth: bool = False


def _p_danbooru(data) -> list[dict]:
    out = []
    for p in _as_list(data):
        full = p.get("file_url")
        if not full:
            continue
        pid = p.get("id")
        out.append(_mk_post(
            "Danbooru", pid, full, p.get("large_file_url"), p.get("large_file_url"),
            p.get("preview_file_url"), p.get("file_ext"), p.get("file_size"),
            f"https://danbooru.donmai.us/posts/{pid}",
        ))
    return out


def _p_gelbooru(data) -> list[dict]:
    posts = _as_list(data.get("post") if isinstance(data, dict) else data)
    out = []
    for p in posts:
        full = p.get("file_url")
        if not full:
            continue
        pid = p.get("id")
        out.append(_mk_post(
            "Gelbooru", pid, full, p.get("sample_url"), p.get("sample_url"),
            p.get("preview_url"), p.get("file_ext"), p.get("file_size"),
            f"https://gelbooru.com/index.php?page=post&s=view&id={pid}",
        ))
    return out


def _p_rule34(data) -> list[dict]:
    posts = _as_list(data.get("post") if isinstance(data, dict) else data)
    out = []
    for p in posts:
        full = p.get("file_url") or p.get("image")
        if not full:
            continue
        pid = p.get("id")
        out.append(_mk_post(
            "Rule34", pid, full, p.get("sample_url"), p.get("sample_url"),
            p.get("preview_url"), p.get("file_ext"), p.get("file_size"),
            f"https://rule34.xxx/index.php?page=post&s=view&id={pid}",
        ))
    return out


def _p_konachan(data) -> list[dict]:
    out = []
    for p in _as_list(data):
        full = p.get("file_url")
        if not full:
            continue
        pid = p.get("id")
        out.append(_mk_post(
            "Konachan", pid, full, p.get("sample_url"), p.get("sample_url"),
            p.get("preview_url"), p.get("file_ext"), p.get("file_size"),
            f"https://konachan.com/post/show/{pid}",
        ))
    return out


SOURCES: list[Source] = [
    Source(
        name="Danbooru",
        url="https://danbooru.donmai.us/posts.json",
        host="danbooru.donmai.us",
        max_page=1000,
        min_interval=0.2,
        cosplay=True,
        cosplay_tags=("cosplay", "photo_(medium)"),
        params=lambda t, pg: {"tags": t, "limit": DANBOORU_PAGE_SIZE, "page": pg},
        parse=_p_danbooru,
    ),
    Source(
        name="Gelbooru",
        url="https://gelbooru.com/index.php",
        host="gelbooru.com",
        max_page=200,
        min_interval=0.5,
        cosplay=True,
        auth=True,
        params=lambda t, pg: {
            "page": "dapi", "s": "post", "q": "index", "json": 1,
            "tags": t, "limit": 100, "pid": pg - 1,
            "api_key": GELBOORU_API_KEY, "user_id": GELBOORU_USER_ID,
        },
        parse=_p_gelbooru,
    ),
    Source(
        name="Rule34",
        url="https://api.rule34.xxx/index.php",
        host="api.rule34.xxx",
        max_page=600,
        min_interval=0.5,
        cosplay=True,
        params=lambda t, pg: {
            "page": "dapi", "s": "post", "q": "index", "json": 1,
            "tags": t, "limit": 100, "pid": pg - 1,
        },
        parse=_p_rule34,
    ),
    Source(
        name="Konachan",
        url="https://konachan.com/post.json",
        host="konachan.com",
        max_page=600,
        min_interval=0.5,
        params=lambda t, pg: {"tags": t, "limit": 100, "page": pg},
        parse=_p_konachan,
    ),
]


# ------------------------------------------------------------- fetch layer

async def _fetch_page(session: aiohttp.ClientSession, src: Source, tags: str, page: int):
    """Parsed posts for one page, or None if the page should be retried."""
    key = (src.name, tags, page)
    cached = CACHE.get(key)
    if cached is not None:
        return cached

    limiter = _limiter(src.host, src.min_interval)

    for attempt in range(3):
        await limiter.wait()
        try:
            async with session.get(
                src.url,
                params=src.params(tags, page),
                timeout=aiohttp.ClientTimeout(total=20),
            ) as r:
                if r.status == 429:
                    log.debug("%s: rate limited on page %s", src.name, page)
                    await asyncio.sleep(1.2 + attempt * 1.5 + random.random())
                    continue
                if r.status in (404, 410):
                    _cache_put(key, [])
                    return []
                if r.status != 200:
                    log.debug("%s: HTTP %s (page %s)", src.name, r.status, page)
                    await asyncio.sleep(0.35)
                    continue
                text = await r.text()
        except (aiohttp.ClientError, asyncio.TimeoutError) as exc:
            log.debug("%s: %s (page %s)", src.name, type(exc).__name__, page)
            await asyncio.sleep(0.35)
            continue

        if not text.strip():
            posts: list[dict] = []
        else:
            try:
                posts = src.parse(json.loads(text))
            except (ValueError, TypeError):
                continue

        _cache_put(key, posts)
        return posts

    return None


async def _danbooru_count(session, tags: str) -> int | None:
    if tags in COUNTS:
        return COUNTS[tags]
    try:
        await _limiter("danbooru.donmai.us", 0.2).wait()
        async with session.get(
            "https://danbooru.donmai.us/counts/posts.json",
            params={"tags": tags},
            timeout=aiohttp.ClientTimeout(total=15),
        ) as r:
            if r.status != 200:
                return None
            data = await r.json()
    except Exception:
        return None
    total = _int(data.get("counts", {}).get("posts"))
    COUNTS[tags] = total
    return total


def _random_page(src: Source, tags: str) -> int:
    hi = PAGE_BOUNDS.get((src.name, tags), src.max_page)
    return random.randint(1, max(1, hi))

def _matches(post: dict, mode: str) -> bool:
    if mode == "any":
        return True
    return post["is_video"] if mode == "video" else not post["is_video"]


async def _try_source(session, src: Source, tags: str, mode: str) -> dict | None:
    for _ in range(PAGE_TRIES):
        page = _random_page(src, tags)
        posts = await _fetch_page(session, src, tags, page)
        if posts is None:
            continue
        if not posts:
            PAGE_BOUNDS[(src.name, tags)] = max(1, page - 1)
            continue
        if page > PAGE_BOUNDS.get((src.name, tags), 0):
            PAGE_BOUNDS[(src.name, tags)] = min(page, src.max_page)
        good = [p for p in posts if _matches(p, mode)]
        if good:
            return random.choice(good)
    return None


async def _gather(session, build: Callable[[Source], str], mode: str,
                  sources: list[Source], count: int) -> list[dict]:
    want = min(count + 2, MAX_FILES + 4)
    pool = sources[:]
    random.shuffle(pool)
    fails: collections.Counter[str] = collections.Counter()

    if any(s.name == "Danbooru" for s in pool):
        await _danbooru_count(session, build(next(s for s in pool if s.name == "Danbooru")))

    picked: list[dict] = []
    seen: set[tuple] = set()
    attempts, cap = 0, want * 6 + 10

    while len(picked) < want and attempts < cap and pool:
        attempts += 1
        src = random.choice(pool)
        post = await _try_source(session, src, build(src), mode)
        if post is None:
            fails[src.name] += 1
            if fails[src.name] >= 2 and len(pool) > 1:
                pool.remove(src)
            continue
        fails[src.name] = 0
        key = (post["site"], post["id"])
        if key in seen:
            continue
        seen.add(key)
        if key in RECENT and attempts < want * 4:
            continue
        picked.append(post)

    RECENT.extend(seen)
    return picked
async def _download(session, post: dict, limit: int, sem: asyncio.Semaphore):
    urls = [
        post["full"] if post["is_video"]
        else (post["preview"] or post["full"])
    ]

    if post["is_video"]:
        for alt in (post["sample"], post["preview"]):
            if alt and alt not in urls:
                urls.append(alt)

    reason = "unreachable"

    async with sem:
        for url in urls:
            try:
                async with session.get(
                    url,
                    timeout=aiohttp.ClientTimeout(total=90)
                ) as r:
                    if r.status != 200:
                        reason = f"HTTP {r.status}"
                        continue

                    ctype = r.headers.get("Content-Type", "").lower()
                    clen = r.content_length

                    if clen and clen > limit:
                        reason = f"{clen // 1024} KB"
                        continue

                    blob = await r.read()

            except (aiohttp.ClientError, asyncio.TimeoutError) as exc:
                reason = type(exc).__name__
                continue

            if not blob:
                reason = "empty"
                continue

            if len(blob) > limit:
                reason = f"{len(blob) // 1024} KB"
                continue

            if post["is_video"]:
                if len(blob) >= 12 and blob[4:8] == b"ftyp":
                    extension = "mp4"
                elif blob.startswith(b"\x1a\x45\xdf\xa3"):
                    extension = "webm"
                else:
                    log.warning(
                        "Invalid video: %s, type=%s, size=%d",
                        url, ctype, len(blob)
                    )
                    reason = "invalid video data"
                    continue
            else:
                extension = _pick_ext(post, ctype)

            name = f"{post['site'].lower()}_{post['id']}.{extension}"
            return post, blob, name, None

    return post, None, None, reason


# ------------------------------------------------------------- search model

@dataclass
class Spec:
    user_id: int
    count: int = 3
    mode: str = "any"
    rating: str = "explicit"
    character: str = ""
    extra_tags: str = ""
    spoiler: bool = False
    kind: str = "art"
    limit: int = DEFAULT_LIMIT
    sites: tuple[str, ...] = ()


@dataclass
class Outcome:
    query: str
    character: str | None
    results: list[tuple[dict, bytes | None, str | None, str | None]] = field(default_factory=list)
    elapsed: float = 0.0


MODE_CODE = {"any": "a", "image": "i", "video": "v"}
RATING_CODE = {"explicit": "e", "questionable": "q", "safe": "s", "any": "a"}
KIND_CODE = {"art": "a", "cosplay": "c"}


def _encode_spec(spec: Spec) -> str:
    return ".".join([
        str(spec.count),
        MODE_CODE.get(spec.mode, "a"),
        RATING_CODE.get(spec.rating, "e"),
        KIND_CODE.get(spec.kind, "a"),
        "1" if spec.spoiler else "0",
        str(spec.user_id),
        spec.character or "-",
        (spec.extra_tags or "-").replace(" ", "+"),
    ])


def _decode_spec(message: discord.Message) -> Spec | None:
    for embed in message.embeds:
        text = embed.footer.text if embed.footer else None
        if not text or FOOTER_SEP not in text:
            continue
        try:
            count, mode, rating, kind, spoil, uid, char, extra = \
                text.rsplit(FOOTER_SEP, 1)[1].split(".", 7)
            return Spec(
                user_id=int(uid),
                count=max(1, min(int(count), MAX_FILES)),
                mode={v: k for k, v in MODE_CODE.items()}.get(mode, "any"),
                rating={v: k for k, v in RATING_CODE.items()}.get(rating, "explicit"),
                kind={v: k for k, v in KIND_CODE.items()}.get(kind, "art"),
                spoiler=spoil == "1",
                character="" if char == "-" else char,
                extra_tags="" if extra == "-" else extra.replace("+", " "),
            )
        except (ValueError, IndexError):
            return None
    return None


def _query_for(spec: Spec, character_tag: str) -> Callable[[Source], str]:
    def build(src: Source) -> str:
        parts = ["genshin_impact"]
        if spec.kind == "cosplay":
            parts.extend(src.cosplay_tags)
        if character_tag:
            parts.append(character_tag)
        if spec.rating and spec.rating != "any":
            parts.append(f"rating:{spec.rating}")
        if spec.extra_tags:
            parts.extend(spec.extra_tags.replace(",", " ").split())
        return _dedupe(parts)
    return build


def _display_query(spec: Spec, character_tag: str) -> str:
    parts = ["genshin_impact"]
    if spec.kind == "cosplay":
        parts.append("cosplay")
    if character_tag:
        parts.append(character_tag)
    if spec.rating and spec.rating != "any":
        parts.append(f"rating:{spec.rating}")
    if spec.extra_tags:
        parts.extend(spec.extra_tags.replace(",", " ").split())
    return _dedupe(parts)


def _pick_sources(spec: Spec) -> list[Source]:
    out = []
    for src in SOURCES:
        if src.auth and not (GELBOORU_API_KEY and GELBOORU_USER_ID):
            continue
        if spec.kind == "cosplay" and not src.cosplay:
            continue
        if spec.sites and src.name not in spec.sites:
            continue
        out.append(src)
    return out


async def run_search(session, spec: Spec) -> Outcome:
    started = time.monotonic()
    sources = _pick_sources(spec)

    character_tag = spec.character or (random.choice(RESOLVED_CHARS)[1] if RESOLVED_CHARS else "")
    display = CHAR_BY_TAG.get(character_tag, character_tag)

    posts = await _gather(session, _query_for(spec, character_tag), spec.mode, sources, spec.count) \
        if sources else []

    if not posts and character_tag:
        log.info("no results for %r, retrying without the character tag",
                 _display_query(spec, character_tag))
        display = None
        posts = await _gather(session, _query_for(spec, ""), spec.mode, sources, spec.count) \
            if sources else []

    query = _display_query(spec, "" if display is None else character_tag)

    if not posts:
        return Outcome(query, display, [], time.monotonic() - started)

    sem = asyncio.Semaphore(CONCURRENCY)
    raw = await asyncio.gather(*(_download(session, p, spec.limit, sem) for p in posts))

    ok = [r for r in raw if r[1] is not None][: spec.count]
    ok_ids = {(r[0]["site"], r[0]["id"]) for r in ok}
    bad = [r for r in raw if r[1] is None and (r[0]["site"], r[0]["id"]) not in ok_ids][:6]

    return Outcome(query, display, ok + bad, time.monotonic() - started)

def _render(spec: Spec, outcome: Outcome) -> tuple[list[discord.Embed], list[discord.File]]:
    files: list[discord.File] = []
    images: list[str] = []
    lines: list[str] = []
    failed: list[dict] = []

    for post, blob, name, reason in outcome.results:
        link = f"[{post['site']} #{post['id']}]({post['page']})"

        if blob is not None and name:
            upload = discord.File(
                io.BytesIO(blob),
                filename=name,
                spoiler=spec.spoiler
            )
            files.append(upload)
            lines.append(f"`{len(files):02d}` {link}")

            ext = _ext_from_url(name)

            if ext in IMAGE_EXTS:
                images.append(upload.filename)

        else:
            lines.append(f"~~{link}~~ · *{reason}*")
            failed.append(post)

    title = (
        "Genshin cosplay (IRL)"
        if spec.kind == "cosplay"
        else "Genshin Impact"
    )

    if outcome.character:
        title += f" · {outcome.character}"

    summary = discord.Embed(
        title=title,
        description="\n".join(lines) or "No results.",
        color=0x7B68EE
    )

    summary.set_footer(
        text=(
            f"{outcome.query} · {len(files)} file(s) · "
            f"{outcome.elapsed:.1f}s"
            f"{FOOTER_SEP}{_encode_spec(spec)}"
        )
    )

    embeds = [summary]

    if not spec.spoiler:
        # Put the first image directly in the main embed.
        if images:
            summary.set_image(
                url=f"attachment://{images[0]}"
            )

        # Discord allows a maximum of 10 embeds per message.
        for name in images[1:10]:
            image_embed = discord.Embed(color=0x7B68EE)
            image_embed.set_image(
                url=f"attachment://{name}"
            )
            embeds.append(image_embed)

    # Video files remain normal attachments so Discord
    # can display a video player when the format is supported.

    if not files and not spec.spoiler:
        for post in failed[:4]:
            thumbnail = post.get("thumb")
            if thumbnail:
                embed = discord.Embed(color=0x7B68EE)
                embed.set_image(url=thumbnail)
                embeds.append(embed)

    return embeds, files

# -------------------------------------------------------------- result view

class ResultView(discord.ui.View):
    """Stateless and persistent — parameters are read back out of the footer."""

    def __init__(self) -> None:
        super().__init__(timeout=None)
        self.add_item(self._mk("Reroll", "🎲", discord.ButtonStyle.primary, "r", self._reroll))
        self.add_item(self._mk("More", "➕", discord.ButtonStyle.secondary, "m", self._more))
        self.add_item(self._mk("Spoiler", "🙈", discord.ButtonStyle.secondary, "s", self._spoiler))
        self.add_item(self._mk("New girl", "🔀", discord.ButtonStyle.secondary, "n", self._new_girl))

    @staticmethod
    def _mk(label, emoji, style, code, callback) -> discord.ui.Button:
        button = discord.ui.Button(label=label, emoji=emoji, style=style, custom_id=f"gs:{code}")
        button.callback = callback
        return button

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        spec = _decode_spec(interaction.message)
        if spec and interaction.user.id != spec.user_id:
            await interaction.response.send_message(
                "Not your search — run the command yourself.", ephemeral=True
            )
            return False
        return True

    async def _spec(self, interaction) -> Spec | None:
        spec = _decode_spec(interaction.message)
        if spec is None:
            await interaction.response.send_message(
                "Couldn't read this message's settings — run the command again.", ephemeral=True
            )
        return spec

    async def _swap(self, interaction, spec: Spec) -> None:
        outcome = await run_search(interaction.client.session, spec)
        _remember(interaction.message.id, outcome)
        embeds, files = _render(spec, outcome)
        await interaction.edit_original_response(
            embeds=embeds,
            attachments=files,
            view=VIEW,
        )

    async def _reroll(self, interaction: discord.Interaction) -> None:
        spec = await self._spec(interaction)
        if spec is None:
            return
        await interaction.response.defer()
        await self._swap(interaction, spec)

    async def _new_girl(self, interaction: discord.Interaction) -> None:
        spec = await self._spec(interaction)
        if spec is None:
            return
        await interaction.response.defer()
        await self._swap(interaction, replace(spec, character=""))
    
    async def _spoiler(self, interaction: discord.Interaction) -> None:
        spec = await self._spec(interaction)
        if spec is None:
            return
        await interaction.response.defer()
        spec = replace(spec, spoiler=not spec.spoiler)
        outcome = _RESULTS.get(interaction.message.id)
        if outcome is None:
            outcome = await run_search(interaction.client.session, spec)
            _remember(interaction.message.id, outcome)
        embeds, files = _render(spec, outcome)
        await interaction.edit_original_response(
            embeds=embeds,
            attachments=files,
        )
    async def _more(self, interaction: discord.Interaction) -> None:
        spec = await self._spec(interaction)
        if spec is None:
            return
        await interaction.response.defer()
        spec = replace(spec, count=min(spec.count, 5))
        outcome = await run_search(interaction.client.session, spec)
        if not outcome.results:
            await interaction.followup.send("Nothing new — try again in a second.", ephemeral=True)
            return
        embeds, files = _render(spec, outcome)
        await interaction.followup.send(embeds=embeds, files=files, view=self)


# --------------------------------------------------------------- bot setup

intents = discord.Intents.default()
bot = discord.Client(intents=intents)
tree = app_commands.CommandTree(bot)


async def on_app_command_error(interaction: discord.Interaction, error: app_commands.AppCommandError) -> None:
    original = error.original if isinstance(error, app_commands.CommandInvokeError) else error

    if isinstance(original, app_commands.CommandOnCooldown):
        message = f"Slow down — try again in {original.retry_after:.1f}s."
    else:
        log.error(
    "Command failed: %s",
    original,
    exc_info=(type(original), original, original.__traceback__)
)
        message = "Something went wrong fetching that. Try again or loosen the tags."

    try:
        if interaction.response.is_done():
            await interaction.followup.send(message, ephemeral=True)
        else:
            await interaction.response.send_message(message, ephemeral=True)
    except discord.HTTPException:
        pass


tree.on_error = on_app_command_error


async def refresh_character_tags(session: aiohttp.ClientSession) -> None:
    """Resolve bare character names against Danbooru's character tag index."""
    global RESOLVED_CHARS, CHAR_BY_TAG
    known: set[str] = set()

    for page in range(1, 11):
        try:
            await _limiter("danbooru.donmai.us", 0.2).wait()
            async with session.get(
                "https://danbooru.donmai.us/tags.json",
                params={"search[name_matches]": "*genshin*", "search[category]": 4,
                        "limit": 1000, "page": page},
                timeout=aiohttp.ClientTimeout(total=30),
            ) as r:
                if r.status != 200:
                    log.info("tag validation: HTTP %s on page %s", r.status, page)
                    break
                data = await r.json()
        except Exception as exc:
            log.info("tag validation stopped on page %s (%s)", page, exc)
            break

        if not isinstance(data, list) or not data:
            break
        known.update(t["name"] for t in data if isinstance(t, dict) and t.get("name"))
        if len(data) < 1000:
            break

    if not known:
        log.info("tag validation skipped, keeping defaults")
        return

    resolved = []
    for display, tag in CHARACTERS:
        for candidate in (tag, f"{tag}_(genshin_impact)"):
            if candidate in known:
                resolved.append((display, candidate))
                break
        else:
            log.debug("unresolved character tag: %s", tag)

    if len(resolved) >= 10:
        RESOLVED_CHARS = sorted(resolved, key=lambda c: c[0].lower())
        CHAR_BY_TAG = {tag: display for display, tag in RESOLVED_CHARS}
        log.info("character tags validated: %d/%d", len(resolved), len(CHARACTERS))
    else:
        log.info("tag validation matched only %d, keeping defaults", len(resolved))


async def _char_autocomplete(interaction: discord.Interaction, current: str):
    needle = _norm(current)
    out = []
    for display, tag in RESOLVED_CHARS:
        if not needle or needle in _norm(display) or needle in tag:
            out.append(app_commands.Choice(name=display, value=tag))
        if len(out) >= 25:
            break
    return out


async def _tag_autocomplete(interaction: discord.Interaction, current: str):
    trailing_space = current.endswith(" ")
    parts = current.split()
    prefix = "" if trailing_space else (parts[-1].lower() if parts else "")
    head = parts[:-1] if (parts and not trailing_space) else parts

    matches = [t for t in POPULAR_TAGS if t.startswith(prefix)] if prefix else POPULAR_TAGS
    out = []
    for tag in matches[:25]:
        value = " ".join(head + [tag])
        if len(value) <= 100:
            out.append(app_commands.Choice(name=value, value=value))
    return out


async def _preset_autocomplete(interaction: discord.Interaction, current: str):
    needle = _norm(current)
    return [
        app_commands.Choice(name=name, value=name)
        for name in PRESETS
        if not needle or needle in _norm(name)
    ][:25]


def _file_limit(interaction: discord.Interaction) -> int:
    base = getattr(interaction.guild, "filesize_limit", DEFAULT_LIMIT) if interaction.guild else DEFAULT_LIMIT
    return max(512 * 1024, base - HEADROOM)


def _apply_preset(preset: str | None, count: int, type_: str | None, rating: str | None,
                  character: str, tags: str, spoiler: bool, user_id: int,
                  limit: int, default_rating: str) -> Spec:
    data = PRESETS.get(preset or "default", {})
    extra = " ".join(x for x in (data.get("extra_tags", ""), tags) if x)
    return Spec(
        user_id=user_id,
        count=count,
        mode=type_ or data.get("mode", "any"),
        rating=rating or data.get("rating", default_rating),
        kind=data.get("kind", "art"),
        character=character,
        extra_tags=extra,
        spoiler=spoiler,
        limit=limit,
    )


# ---------------------------------------------------------------- commands

TYPE_CHOICES = [
    app_commands.Choice(name="any", value="any"),
    app_commands.Choice(name="image only", value="image"),
    app_commands.Choice(name="video only", value="video"),
]
RATING_CHOICES = [
    app_commands.Choice(name="explicit", value="explicit"),
    app_commands.Choice(name="questionable", value="questionable"),
    app_commands.Choice(name="safe", value="safe"),
    app_commands.Choice(name="any", value="any"),
]


@app_commands.describe(
    count="How many (1-10)",
    preset="Quick tag bundle — leave blank for vanilla",
    type="image / video / any",
    rating="Rating filter",
    character="Leave blank for a random girl",
    tags="Extra booru tags",
    spoiler="Hide behind a spoiler",
)

@app_commands.choices(type=TYPE_CHOICES, rating=RATING_CHOICES)
@app_commands.autocomplete(character=_char_autocomplete, tags=_tag_autocomplete, preset=_preset_autocomplete)
async def _genshin(
    interaction: discord.Interaction,
    count: app_commands.Range[int, 1, 10] = 3,
    preset: str | None = None,
    type: str | None = None,
    rating: str | None = None,
    character: str = "",
    tags: str = "",
    spoiler: bool = False,
) -> None:
    await interaction.response.defer(thinking=True)

    spec = _apply_preset(
        preset,
        count,
        type,
        rating,
        character,
        tags,
        spoiler,
        interaction.user.id,
        _file_limit(interaction),
        "explicit",
    )

    outcome = await run_search(interaction.client.session, spec)

    
    embeds, files = _render(spec, outcome)
    message = await interaction.edit_original_response(
        embeds=embeds,
        attachments=files,
        view=VIEW,
    )
    _remember(message.id, outcome)





# One view instance shared by every message: it carries no per-message state,
# so this also acts as the global fallback that survives restarts.
View = ResultView


tree.add_command(app_commands.Command(
    name="genshin", description="Random Genshin Impact art — NSFW by default.", callback=_genshin
))
tree.add_command(app_commands.Command(
    name="g", description="Alias for /genshin", callback=_genshin
))


@app_commands.describe(
    count="How many (1-10)",
    preset="Quick tag bundle",
    type="image / video / any",
    spoiler="Hide behind a spoiler",
)
@app_commands.choices(type=TYPE_CHOICES)
@app_commands.autocomplete(preset=_preset_autocomplete)
async def _genshinporn(
    interaction: discord.Interaction,
    count: app_commands.Range[int, 1, 10] = 3,
    preset: str | None = None,
    type: str | None = None,
    spoiler: bool = False,
) -> None:
    await interaction.response.defer(thinking=True)
    spec = _apply_preset(preset, count, type, "explicit", "", "", spoiler,
                         interaction.user.id, _file_limit(interaction), "explicit")
    outcome = await run_search(interaction.client.session, spec)
    if not outcome.results:
        await interaction.edit_original_response(
            content=f"No results for `{outcome.query}`. Try `/genshin rating:any`."
        )
        return
    embeds, files = _render(spec, outcome)
    message = await interaction.edit_original_response(
        embeds=embeds,
        attachments=files,
        view=VIEW,
    )
    _remember(message.id, outcome)

tree.add_command(app_commands.Command(
    name="genshinporn", description="Random Genshin girl, explicit. Surprise me.", callback=_genshinporn
))
tree.add_command(app_commands.Command(
    name="gp", description="Alias for /genshinporn", callback=_genshinporn
))


@app_commands.describe(
    count="How many (1-10)",
    type="image / video / any",
    rating="Most cosplay is safe or questionable",
    character="Leave blank for a random cosplayer",
    tags="Extra booru tags",
    spoiler="Hide behind a spoiler",
)
@app_commands.choices(type=TYPE_CHOICES, rating=RATING_CHOICES)
@app_commands.autocomplete(character=_char_autocomplete, tags=_tag_autocomplete)
async def _cosplay(
    interaction: discord.Interaction,
    count: app_commands.Range[int, 1, 10] = 3,
    type: str | None = None,
    rating: str | None = None,
    character: str = "",
    tags: str = "",
    spoiler: bool = False,
) -> None:
    await interaction.response.defer(thinking=True)
    spec = Spec(
        user_id=interaction.user.id,
        count=count,
        mode=type or "any",
        rating=rating or "any",
        kind="cosplay",
        character=character,
        extra_tags=tags,
        spoiler=spoiler,
        limit=_file_limit(interaction),
    )
    outcome = await run_search(interaction.client.session, spec)
    if not outcome.results:
        await interaction.edit_original_response(
            content=f"No results for `{outcome.query}`. Try dropping the character or the tags."
        )
        return
    embeds, files = _render(spec, outcome)
    m
    message = await interaction.edit_original_response(
        embeds=embeds,
        attachments=files,
        view=VIEW,
    )
    _remember(message.id, outcome)



tree.add_command(app_commands.Command(
    name="cosplay", description="Random IRL Genshin cosplay photos and clips.", callback=_cosplay
))
tree.add_command(app_commands.Command(
    name="gc", description="Alias for /cosplay", callback=_cosplay
))


@app_commands.describe(query="Filter by name or tag")
async def _chars(interaction: discord.Interaction, query: str = "") -> None:
    chars = RESOLVED_CHARS
    if query:
        needle = _norm(query)
        chars = [c for c in chars if needle in _norm(c[0]) or needle in c[1]]
    if not chars:
        await interaction.response.send_message("No character matches that.", ephemeral=True)
        return

    lines = [f"`{tag}` — {display}" for display, tag in chars]

    embeds: list[discord.Embed] = []
    chunk: list[str] = []
    size = 0
    for line in lines:
        if chunk and size + len(line) + 1 > 3800:
            embeds.append(discord.Embed(description="\n".join(chunk), color=0x7B68EE))
            chunk, size = [], 0
        chunk.append(line)
        size += len(line) + 1
    if chunk:
        embeds.append(discord.Embed(description="\n".join(chunk), color=0x7B68EE))

    pages = len(embeds)
    embeds[0].title = f"Genshin girls ({len(chars)})"
    for index, embed in enumerate(embeds, 1):
        embed.set_footer(
            text="/genshin character:…  ·  /genshinporn for a random one"
            if pages == 1
            else f"page {index}/{pages}  ·  /genshinporn for a random one"
        )

    await interaction.response.send_message(embeds=embeds[:10], ephemeral=True)


tree.add_command(app_commands.Command(
    name="chars", description="List the Genshin girls you can search for.", callback=_chars
))


async def _presets(interaction: discord.Interaction) -> None:
    lines = []
    for name, data in PRESETS.items():
        bits = []
        if "extra_tags" in data:
            bits.append(data["extra_tags"])
        if "mode" in data:
            bits.append(f"type={data['mode']}")
        if data.get("kind") == "cosplay":
            bits.append("IRL cosplay")
        lines.append(f"`{name}` — {', '.join(bits) if bits else 'vanilla'}")
    embed = discord.Embed(title="Presets", description="\n".join(lines), color=0x7B68EE)
    embed.set_footer(text="Usage: /genshin preset:swimsuit character:hu_tao")
    await interaction.response.send_message(embed=embed, ephemeral=True)


tree.add_command(app_commands.Command(
    name="presets", description="List the built-in /genshin presets.", callback=_presets
))


# ------------------------------------------------------------------- runtime

VIEW = ResultView()

@bot.event
async def on_ready() -> None:
    log.info("logged in as %s (%d guilds)", bot.user, len(bot.guilds))

    if getattr(bot, "_startup_complete", False):
        return

    if not hasattr(bot, "session") or bot.session.closed:
        bot.session = aiohttp.ClientSession(
            headers={"User-Agent": UA}
        )

    bot.add_view(VIEW)

    if GUILD_ID:
        guild = discord.Object(id=int(GUILD_ID))
        tree.copy_global_to(guild=guild)
        synced = await tree.sync(guild=guild)
        log.info("Synced %d commands to guild %s", len(synced), GUILD_ID)
    else:
        synced = await tree.sync()
        log.info("Synced %d global commands", len(synced))

    asyncio.create_task(refresh_character_tags(bot.session))
    bot._startup_complete = True



if __name__ == "__main__":
    if not TOKEN:
        raise SystemExit("Set DISCORD_TOKEN in your .env file")
    bot.run(TOKEN, log_handler=None)
