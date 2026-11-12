"""Genshin NSFW Discord bot — art, IRL cosplay and clips from public boorus."""

from __future__ import annotations

import asyncio
import collections
import io
import html
import re
import json
import logging
import os
import random
import time
import sqlite3
import uuid
from contextlib import closing
from datetime import datetime, timezone
from pathlib import Path
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
# Required for /cosplay — it is the only cosplay source.
REDDIT_CLIENT_ID = os.getenv("REDDIT_CLIENT_ID", "").strip()
REDDIT_CLIENT_SECRET = os.getenv("REDDIT_CLIENT_SECRET", "").strip()
REDDIT_USER_AGENT = os.getenv("REDDIT_USER_AGENT", "GenshinCosplayDiscordBot/1.0").strip()
COSPLAY_SUBREDDIT = os.getenv("COSPLAY_SUBREDDIT", "GenshinImpactNSFW").strip()

UA = "GenshinBooruBot/3.0"
VIDEO_EXTS = {"mp4", "webm"}
IMAGE_EXTS = {"jpg", "jpeg", "png", "gif", "webp"}
MAX_FILES = 10
CONCURRENCY = 4
HEADROOM = 64 * 1024
DEFAULT_LIMIT = 8 * 1024 * 1024
PAGE_TRIES = 2
# Short, bounded searches/downloads: prevent slow hosts from stalling commands.
TOTAL_FETCH_BUDGET = 9.0
PRIMARY_SEARCH_BUDGET = 3.3
FALLBACK_SEARCH_BUDGET = 1.7
COSPLAY_SEARCH_BUDGET = 5.0
PAGE_REQUEST_TIMEOUT = 2.5
MEDIA_REQUEST_TIMEOUT = 4.0
DANBOORU_PAGE_SIZE = 100
RESULT_CACHE_MAX = 10
FOOTER_SEP = "  \u27e9  "

RECENT = collections.deque(maxlen=800)
CACHE: dict[tuple, list] = {}
CACHE_MAX = 512
PAGE_BOUNDS: dict[tuple[str, str], int] = {}
COUNTS: dict[str, int] = {}
_LIMITERS: dict[str, "HostLimiter"] = {}
_RESULTS: collections.OrderedDict[int, "Outcome"] = collections.OrderedDict()
_BUSY_MESSAGES: set[int] = set()
_REDDIT_TOKEN: tuple[str, float] | None = None

# Save files next to bot.py by default. On FadeHost this directory MUST be
# persistent and writable; set FAVORITES_DIR to a persistent path if necessary.
FAVORITES_DIR = Path(os.getenv("FAVORITES_DIR") or Path(__file__).resolve().parent).resolve()
FAVORITES_DB = FAVORITES_DIR / "favorites.sqlite3"
FAVORITES_MEDIA = FAVORITES_DIR / "favorites_media"
MAX_USER_FAVORITES = 250

# Custom button emojis (server emojis visible to the bot).
BUTTON_EMOJI_IDS = {
    "reroll": 1562142048658657310,
    "more": 1562144444386508970,
    "spoiler": 1562145840385101936,
    "new_girl": 1562141334075346996,
    "favorite": 1562144325641568356,
}


def _button_emoji(key: str, fallback: str, name: str | None = None) -> str | discord.PartialEmoji:
    emoji_id = BUTTON_EMOJI_IDS.get(key)
    if not emoji_id:
        return fallback
    emoji_name = name or key
    return discord.PartialEmoji(name=emoji_name, id=emoji_id)


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
    ('Aloy', 'aloy'), ('Amber', 'amber'), ('Arlecchino', 'arlecchino'),
    ('Barbara', 'barbara'), ('Beidou', 'beidou'), ('Candace', 'candace'),
    ('Charlotte', 'charlotte'), ('Chasca', 'chasca'), ('Chevreuse', 'chevreuse'),
    ('Chiori', 'chiori'), ('Citlali', 'citlali'), ('Clorinde', 'clorinde'),
    ('Collei', 'collei'), ('Columbina', 'columbina'), ('Dehya', 'dehya'),
    ('Emilie', 'emilie'), ('Escoffier', 'escoffier'), ('Eula', 'eula'),
    ('Faruzan', 'faruzan'), ('Fischl', 'fischl'), ('Furina', 'furina'),
    ('Ganyu', 'ganyu'), ('Hu Tao', 'hu_tao'), ('Ineffa', 'ineffa'),
    ('Jahoda', 'jahoda'), ('Jean', 'jean'), ('Kamisato Ayaka', 'kamisato_ayaka'),
    ('Keqing', 'keqing'), ('Kirara', 'kirara'), ('Kujou Sara', 'kujou_sara'),
    ('Kuki Shinobu', 'kuki_shinobu'), ('La Signora', 'la_signora'), ('Lan Yan', 'lan_yan'),
    ('Lauma', 'lauma'), ('Layla', 'layla'), ('Linnea', 'linnea'),
    ('Lisa', 'lisa'), ('Lumine', 'lumine'), ('Lynette', 'lynette'),
    ('Mavuika', 'mavuika'), ('Mona', 'mona'), ('Mualani', 'mualani'),
    ('Navia', 'navia'), ('Nefer', 'nefer'), ('Nicole', 'nicole'),
    ('Nilou', 'nilou'), ('Ningguang', 'ningguang'), ('Noelle', 'noelle'),
    ('Odette', 'odette'), ('Raiden Shogun', 'raiden_shogun'), ('Rosaria', 'rosaria'),
    ('Sandrone', 'sandrone'), ('Sangonomiya Kokomi', 'sangonomiya_kokomi'), ('Shenhe', 'shenhe'),
    ('Skirk', 'skirk'), ('Sucrose', 'sucrose'), ('Varesa', 'varesa'),
    ('Vesna', 'vesna'), ('Vodyanitsa', 'vodyanitsa'), ('Xianyun', 'xianyun'),
    ('Xiangling', 'xiangling'), ('Xilonen', 'xilonen'), ('Xinyan', 'xinyan'),
    ('Yae Miko', 'yae_miko'), ('Yanfei', 'yanfei'), ('Yelan', 'yelan'),
    ('Yoimiya', 'yoimiya'), ('Yumemizuki Mizuki', 'yumemizuki_mizuki'), ('Yun Jin', 'yun_jin'),
    ('Zibai', 'zibai'),
]

RESOLVED_CHARS: list[tuple[str, str]] = list(CHARACTERS)
CHAR_BY_TAG: dict[str, str] = {tag: display for display, tag in CHARACTERS}

# Adult-rated searches must never deliberately include child-coded characters.
# Applies to both explicitly selected characters and posts tagged with them.
CHILD_CODED_TAGS = frozenset({
    "aino", "diona", "dori", "iansan", "kachina", "klee",
    "nahida", "prune", "qiqi", "sayu", "sigewinne", "yaoyao",
    "paimon",  # Additional child-coded nonplayable character.
})

# Legacy adult-designation tags from this version; they do NOT override
# CHILD_CODED_TAGS exclusions when filtering posts.
ADULT_TAGS = frozenset({
    "amber", "barbara", "collei", "fischl", "jahoda", "kamisato_ayaka",
    "kirara", "lan_yan", "layla", "linnea", "lynette", "mualani", "noelle",
    "odette", "sucrose", "varesa", "vesna", "vodyanitsa", "xiangling",
    "xinyan",
})


def _base_character_tag(tag: str) -> str:
    return tag.split("_(genshin_impact)", 1)[0].lower().strip()


def _child_coded_character(tag: str) -> bool:
    return _base_character_tag(tag) in CHILD_CODED_TAGS


def _adult_character(tag: str) -> bool:
    return _base_character_tag(tag) in ADULT_TAGS


# Female-focused explicit results may include a male partner, but not male-focused
# or multi-male scenes. Keep the existing character/safety lists intact and make
# the gender-presence rule more precise than the earlier female-only filter.
MALE_CHARACTER_TAGS = frozenset({
    "aether", "albedo", "alhaitham", "arataki_itto", "baizhu", "bennett",
    "chongyun", "cyno", "dainsleif", "diluc", "dottore", "il_dottore",
    "freminet", "gaming", "gorou", "il_capitano", "capitano", "kaedehara_kazuha",
    "kaeya", "kamisato_ayato", "kinich", "lyney", "mika", "mitya",
    "neuvillette", "ororon", "pantalone", "pierro", "razor", "scaramouche",
    "sethos", "shikanoin_heizou", "tartaglia", "childe", "thoma", "tighnari",
    "varka", "venti", "wanderer", "wriothesley", "xiao", "xingqiu",
    "zhongli", "lohen", "valeriy", "teppei", "enjou", "ruu",
})
# Tags that indicate male presence but can still be female-focused.
MALE_PARTNER_TAGS = frozenset({
    "1boy", "1man", "male", "male_character", "male_pov", "male_hands",
    "faceless_male", "man", "otoko",
})
# Tags that make the male side the focus or imply several male participants.
MALE_FOCUS_TAGS = frozenset({
    "2boys", "3boys", "4boys", "5boys", "6+boys", "multiple_boys",
    "2men", "multiple_males", "male_only", "male_focus",
    "male_protagonist", "boys", "men", "guys",
})
FEMALE_PRESENCE_TAGS = frozenset({
    "1girl", "2girls", "3girls", "4girls", "5girls", "6+girls",
    "multiple_girls", "girl", "girls", "female", "female_focus",
    "all_female",
})


def _post_gender_markers(post: dict) -> set[str]:
    tags = (*(post.get("tags") or []), *(post.get("character_tags") or []))
    return {_base_character_tag(str(tag)) for tag in tags}


def _male_focused_post(post: dict) -> bool:
    names = _post_gender_markers(post)
    # Keep named male Genshin characters blocked here; generic male-partner tags
    # are allowed, but named male pairings would need a separate adult review.
    if names & (MALE_FOCUS_TAGS | MALE_CHARACTER_TAGS):
        return True
    return any(re.fullmatch(r"[2-9][0-9]*(?:boys?|men)", name) for name in names)


def _male_present(post: dict) -> bool:
    names = _post_gender_markers(post)
    return bool(names & (MALE_PARTNER_TAGS | MALE_FOCUS_TAGS)) or any(
        re.fullmatch(r"[1-9][0-9]*(?:boys?|men)", name) for name in names
    )


def _female_present(post: dict) -> bool:
    names = _post_gender_markers(post)
    return bool(names & KNOWN_FEMALE_TAGS) or bool(names & FEMALE_PRESENCE_TAGS)


def _reddit_male_mentioned(title: str, flair: str) -> bool:
    # Reddit has titles/flairs rather than structured booru character tags.
    label = (title + " " + flair).casefold().replace("_", " ")
    if set(re.findall(r"[a-z0-9]+", label)) & {"male", "men", "boy", "boys", "guy", "guys", "man"}:
        return True
    for name in MALE_CHARACTER_TAGS:
        candidate = name.replace("_", " ")
        if re.search(r"(?<![a-z0-9])" + re.escape(candidate) + r"(?![a-z0-9])", label):
            return True
    return False


def _explicit_blocked(character_tag: str) -> bool:
    """Never allow an explicitly selected blocked child-coded character."""
    return bool(character_tag) and _child_coded_character(character_tag)


def _allowed_adult_post(post: dict) -> bool:
    # Any blocked character disqualifies a post, even in mixed-character images.
    # Danbooru exposes character tags separately; check both fields so one
    # missing or incomplete field cannot override the exclusion.
    tags = post.get("tags") or []
    if not tags:
        return False
    character_tags = post.get("character_tags") or []
    if any(_child_coded_character(tag) for tag in (*tags, *character_tags)):
        return False
    if _male_focused_post(post):
        return False
    # Allow a male partner, but only when there is also a female subject.
    if _male_present(post) and not _female_present(post):
        return False
    return True


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

# Cosplay is matched against Reddit post titles, not booru tags, so the generic
# booru vocabulary mostly misses. Keep this list to words that show up in titles.
COSPLAY_TAGS = [
    "cosplay", "bikini", "swimsuit", "beach", "pool", "lingerie", "nude",
    "lewd", "maid", "bunny", "kimono", "yukata", "wet", "bath", "onsen",
    "stockings", "thighhighs", "self", "video",
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
        item = _mk_post(
            "Danbooru", pid, full, p.get("large_file_url"), p.get("large_file_url"),
            p.get("preview_file_url"), p.get("file_ext"), p.get("file_size"),
            f"https://danbooru.donmai.us/posts/{pid}",
        )
        item["tags"] = (p.get("tag_string") or "").split()
        item["character_tags"] = (p.get("tag_string_character") or "").split()
        item["rating"] = str(p.get("rating") or "").lower()
        out.append(item)
    return out


def _p_gelbooru(data) -> list[dict]:
    posts = _as_list(data.get("post") if isinstance(data, dict) else data)
    out = []
    for p in posts:
        full = p.get("file_url")
        if not full:
            continue
        pid = p.get("id")
        item = _mk_post(
            "Gelbooru", pid, full, p.get("sample_url"), p.get("sample_url"),
            p.get("preview_url"), p.get("file_ext"), p.get("file_size"),
            f"https://gelbooru.com/index.php?page=post&s=view&id={pid}",
        )
        tags = p.get("tags") or ""
        item["tags"] = tags.split() if isinstance(tags, str) else tags if isinstance(tags, list) else []
        out.append(item)
    return out


def _p_rule34(data) -> list[dict]:
    posts = _as_list(data.get("post") if isinstance(data, dict) else data)
    out = []
    for p in posts:
        full = p.get("file_url") or p.get("image")
        if not full:
            continue
        pid = p.get("id")
        item = _mk_post(
            "Rule34", pid, full, p.get("sample_url"), p.get("sample_url"),
            p.get("preview_url"), p.get("file_ext"), p.get("file_size"),
            f"https://rule34.xxx/index.php?page=post&s=view&id={pid}",
        )
        tags = p.get("tags") or ""
        item["tags"] = tags.split() if isinstance(tags, str) else tags if isinstance(tags, list) else []
        out.append(item)
    return out


def _p_konachan(data) -> list[dict]:
    out = []
    for p in _as_list(data):
        full = p.get("file_url")
        if not full:
            continue
        pid = p.get("id")
        item = _mk_post(
            "Konachan", pid, full, p.get("sample_url"), p.get("sample_url"),
            p.get("preview_url"), p.get("file_ext"), p.get("file_size"),
            f"https://konachan.com/post/show/{pid}",
        )
        tags = p.get("tags") or ""
        item["tags"] = tags.split() if isinstance(tags, str) else tags if isinstance(tags, list) else []
        out.append(item)
    return out


SOURCES: list[Source] = [
    Source(
        name="Danbooru",
        url="https://danbooru.donmai.us/posts.json",
        host="danbooru.donmai.us",
        max_page=1000,
        min_interval=0.2,
        cosplay=True,
        cosplay_tags=("cosplay_photo",),
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


# --- Approved Reddit Data API: the only cosplay source ----------------------

async def _reddit_token(session: aiohttp.ClientSession) -> str | None:
    """Client-credentials token, cached until shortly before it expires."""
    global _REDDIT_TOKEN
    if _REDDIT_TOKEN and _REDDIT_TOKEN[1] > time.time() + 60:
        return _REDDIT_TOKEN[0]

    await _limiter("oauth.reddit.com", 1.0).wait()
    try:
        async with session.post(
            "https://www.reddit.com/api/v1/access_token",
            auth=aiohttp.BasicAuth(REDDIT_CLIENT_ID, REDDIT_CLIENT_SECRET),
            data={"grant_type": "client_credentials"},
            headers={"User-Agent": REDDIT_USER_AGENT},
            timeout=aiohttp.ClientTimeout(total=2.5),
        ) as response:
            if response.status != 200:
                log.warning("Reddit OAuth failed: HTTP %s", response.status)
                return None
            data = await response.json()
    except (aiohttp.ClientError, asyncio.TimeoutError, ValueError):
        log.warning("Reddit OAuth unreachable")
        return None

    token = data.get("access_token")
    if not token:
        return None
    _REDDIT_TOKEN = (token, time.time() + _int(data.get("expires_in")) - 60)
    return token


async def _reddit_cosplay_posts(session: aiohttp.ClientSession, spec: "Spec", count: int) -> list[dict]:
    """Use Reddit ONLY with approved OAuth credentials; do not scrape Reddit pages."""
    if not (REDDIT_CLIENT_ID and REDDIT_CLIENT_SECRET):
        return []

    token = await _reddit_token(session)
    if not token:
        return []

    headers = {"User-Agent": REDDIT_USER_AGENT, "Authorization": f"bearer {token}"}
    # One subreddit, two ways in: newest posts, plus a cosplay-targeted
    # search so a run of art posts cannot crowd the cosplay out.
    searches = [
        (COSPLAY_SUBREDDIT, "new", None),
        (COSPLAY_SUBREDDIT, "search", "cosplay"),
    ]
    choices: list[dict] = []
    seen_ids: set[str] = set()
    async def fetch_listing(subreddit: str, operation: str, query: str | None) -> dict:
        if operation == "new":
            url = f"https://oauth.reddit.com/r/{subreddit}/new"
            params = {"limit": 100, "raw_json": 1}
        else:
            url = f"https://oauth.reddit.com/r/{subreddit}/search"
            params = {"q": query, "restrict_sr": 1, "sort": "new", "limit": 100, "raw_json": 1}
        try:
            await _limiter("oauth.reddit.com", 1.0).wait()
            async with session.get(
                url, headers=headers, params=params,
                timeout=aiohttp.ClientTimeout(total=2.75),
            ) as response:
                if response.status != 200:
                    log.info("Reddit r/%s: HTTP %s", subreddit, response.status)
                    return {}
                return await response.json()
        except (aiohttp.ClientError, asyncio.TimeoutError, ValueError):
            log.info("Reddit r/%s unreachable", subreddit)
            return {}

    # Request both Reddit listing paths concurrently without changing filtering.
    listings = await asyncio.gather(
        *(fetch_listing(subreddit, operation, query)
          for subreddit, operation, query in searches)
    )
    for data in listings:
        children = data.get("data", {}).get("children", [])
        for entry in children:
            p = entry.get("data", {})
            if p.get("removed_by_category") or p.get("is_self"):
                continue
            title = html.unescape(str(p.get("title", "")))
            flair = html.unescape(str(p.get("link_flair_text") or ""))
            ntext = _norm(title + " " + flair)
            # Reddit cosplay entries lack booru character tags; exclude known
            # child-coded character names mentioned in their title or flair.
            if any(_norm(tag) in ntext for tag in CHILD_CODED_TAGS):
                continue
            if _reddit_male_mentioned(title, flair):
                continue
            # This sub posts art and clips too — cosplay only, nothing else.
            if "cosplay" not in ntext:
                continue
            if spec.character and not any(
                _norm(_base_character_tag(spec.character)) == _norm(_base_character_tag(tag))
                for name, tag in CHARACTERS
                if _norm(name) in ntext or _norm(_base_character_tag(tag)) in ntext
            ):
                continue
            if spec.rating == "safe" and p.get("over_18"):
                continue
            if spec.rating in ("explicit", "questionable") and not p.get("over_18"):
                continue
            if spec.extra_tags and not all(
                _norm(t) in ntext for t in spec.extra_tags.replace(",", " ").split()
            ):
                continue

            vinfo = ((p.get("secure_media") or p.get("media") or {})
                     .get("reddit_video") or {})
            video_url = html.unescape(vinfo.get("fallback_url") or "")
            if video_url:
                url = video_url
                ext = "mp4"
            else:
                url = html.unescape(str(p.get("url_overridden_by_dest") or p.get("url") or ""))
                ext = _ext_from_url(url)
                if ext not in IMAGE_EXTS:
                    continue
            is_video = ext in VIDEO_EXTS
            if spec.mode == "video" and not is_video:
                continue
            if spec.mode == "image" and is_video:
                continue
            pid = str(p.get("id") or "")
            if not pid or pid in seen_ids or not url.startswith("https://"):
                continue
            seen_ids.add(pid)
            post = _mk_post(
                "Reddit", pid, url, url, url, url, ext, 0,
                "https://www.reddit.com" + str(p.get("permalink") or ""),
            )
            choices.append(post)
    random.shuffle(choices)
    return choices[:count]


async def _gather_cosplay(session: aiohttp.ClientSession, spec: "Spec") -> list[dict]:
    """Reddit only — r/GenshinImpactNSFW cosplay posts, never drawn artwork."""
    if not (REDDIT_CLIENT_ID and REDDIT_CLIENT_SECRET):
        return []

    posts = await _reddit_cosplay_posts(session, spec, spec.count + 6)

    picked: list[dict] = []
    seen: set[tuple] = set()
    for post in posts:
        key = (post["site"], post["id"])
        if key in seen:
            continue
        seen.add(key)
        if key in RECENT and len(picked) < spec.count:
            continue
        picked.append(post)

    RECENT.extend(seen)
    return picked[:MAX_FILES + 4]


# ------------------------------------------------------------- fetch layer

async def _fetch_page(session: aiohttp.ClientSession, src: Source, tags: str, page: int):
    """Parsed posts for one page; a slow host must not hold up the entire search."""
    key = (src.name, tags, page)
    cached = CACHE.get(key)
    if cached is not None:
        return cached

    limiter = _limiter(src.host, src.min_interval)

    for attempt in range(2):
        await limiter.wait()
        try:
            async with session.get(
                src.url,
                params=src.params(tags, page),
                timeout=aiohttp.ClientTimeout(total=PAGE_REQUEST_TIMEOUT),
            ) as r:
                if r.status == 429:
                    log.debug("%s: rate limited on page %s", src.name, page)
                    # Do not block the other sites for a long backoff.
                    return None
                if r.status in (404, 410):
                    _cache_put(key, [])
                    return []
                if r.status != 200:
                    log.debug("%s: HTTP %s (page %s)", src.name, r.status, page)
                    continue
                body = await r.text()
        except (aiohttp.ClientError, asyncio.TimeoutError) as exc:
            log.debug("%s: %s (page %s)", src.name, type(exc).__name__, page)
            continue

        if not body.strip():
            return []
        try:
            posts = src.parse(json.loads(body))
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
            timeout=aiohttp.ClientTimeout(total=1.5),
        ) as r:
            if r.status != 200:
                return None
            data = await r.json()
    except Exception:
        return None
    total = _int(data.get("counts", {}).get("posts"))
    COUNTS[tags] = total
    return total


def _matches(post: dict, mode: str) -> bool:
    if mode == "any":
        return True
    return post["is_video"] if mode == "video" else not post["is_video"]


async def _try_source(session, src: Source, tags: str, mode: str,
                      rating: str = "safe", want: int = 3) -> list[dict]:
    """Use known page counts or a small adaptive window; avoid empty high pages."""
    key = (src.name, tags)

    if key not in PAGE_BOUNDS:
        if src.name == "Danbooru":
            total = await _danbooru_count(session, tags)
            if total:
                PAGE_BOUNDS[key] = max(
                    1, min(src.max_page, (total + DANBOORU_PAGE_SIZE - 1) // DANBOORU_PAGE_SIZE)
                )
        # Sites without a count endpoint start near page 1, not page 200-600.
        PAGE_BOUNDS.setdefault(key, min(src.max_page, 3))

    attempted_pages: set[int] = set()
    for attempt in range(PAGE_TRIES):
        upper = PAGE_BOUNDS[key]
        if attempt == 0 and (src.name, tags, 1) not in CACHE:
            page = 1
        else:
            choices = [p for p in range(1, upper + 1) if p not in attempted_pages]
            if not choices:
                break
            page = random.choice(choices)
        attempted_pages.add(page)

        posts = await _fetch_page(session, src, tags, page)
        if posts is None:  # Timeout/rate limit: don't mistake it for the last page.
            continue
        if not posts:
            # An empty page means later pages are unlikely to contain results.
            PAGE_BOUNDS[key] = min(PAGE_BOUNDS[key], max(1, page - 1))
            continue

        # A short API page is the end of the available results for this query.
        if len(posts) < DANBOORU_PAGE_SIZE:
            PAGE_BOUNDS[key] = min(PAGE_BOUNDS[key], page)
        elif (page == PAGE_BOUNDS[key] and PAGE_BOUNDS[key] < src.max_page
              and not (src.name == "Danbooru" and COUNTS.get(tags, 0) > 0)):
            # Expand only after a full page proves the current window too small.
            PAGE_BOUNDS[key] = min(src.max_page, PAGE_BOUNDS[key] * 2)

        good = [p for p in posts if _matches(p, mode)
                and _allowed_adult_post(p)]
        if good:
            random.shuffle(good)
            return good[:want]
    return []


async def _gather(session, build: Callable[[Source], str], mode: str,
                  sources: list[Source], count: int, rating: str = "safe",
                  budget: float = PRIMARY_SEARCH_BUDGET) -> list[dict]:
    """Search independent sources concurrently; return the first useful pool."""
    want = min(count + 2, MAX_FILES + 4)
    pool = sources[:]
    random.shuffle(pool)
    tasks = {
        asyncio.create_task(_try_source(session, src, build(src), mode, rating, want))
        for src in pool
    }
    pending = set(tasks)
    candidates: list[dict] = []
    deadline = time.monotonic() + max(0.0, budget)
    try:
        while pending:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                break
            done, pending = await asyncio.wait(
                pending, timeout=remaining, return_when=asyncio.FIRST_COMPLETED
            )
            if not done:
                break
            for task in done:
                try:
                    candidates.extend(task.result())
                except Exception as exc:
                    log.debug("One art source failed: %s", type(exc).__name__)
            seen_now = {(p["site"], p["id"]) for p in candidates
                        if (p["site"], p["id"]) not in RECENT}
            if len(seen_now) >= want:
                break
    finally:
        for task in pending:
            task.cancel()
        if pending:
            await asyncio.gather(*pending, return_exceptions=True)

    # Prefer unseen posts, then fill with repeats when the pool is small.
    unique: dict[tuple, dict] = {}
    for post in candidates:
        unique.setdefault((post["site"], post["id"]), post)
    fresh = [p for key, p in unique.items() if key not in RECENT]
    repeats = [p for key, p in unique.items() if key in RECENT]
    random.shuffle(fresh)
    random.shuffle(repeats)
    picked = (fresh + repeats)[:want]
    RECENT.extend((p["site"], p["id"]) for p in picked)
    return picked


async def _download(session, post: dict, limit: int, sem: asyncio.Semaphore):
    if post["is_video"]:
        urls = [post["full"]]
        for alt in (post["sample"], post["preview"]):
            if alt and alt not in urls:
                urls.append(alt)
    else:
        # Prefer the sample, but always keep the full image as a fallback so a
        # dead sample URL doesn't cost us a perfectly good result.
        urls = [u for u in (post["preview"], post["full"]) if u]
        if not urls:
            urls = [post["full"]]

    reason = "unreachable"

    async with sem:
        for url in urls:
            try:
                async with session.get(
                    url,
                    headers=(
                        {"Referer": "https://gelbooru.com/"}
                        if post["site"] == "Gelbooru"
                        else None
                    ),
                    timeout=aiohttp.ClientTimeout(total=MEDIA_REQUEST_TIMEOUT)
                ) as r:
                    if r.status != 200:
                        reason = f"HTTP {r.status}"
                        continue

                    ctype = r.headers.get("Content-Type", "").lower()
                    clen = r.content_length

                    if clen and clen > limit:
                        reason = f"{clen // 1024} KB"
                        continue

                    # Stop reading as soon as a response exceeds the upload limit,
                    # even if the server omits or misreports Content-Length.
                    chunks = bytearray()
                    async for chunk in r.content.iter_chunked(64 * 1024):
                        if len(chunks) + len(chunk) > limit:
                            reason = f">{limit // 1024} KB"
                            chunks = None
                            break
                        chunks.extend(chunk)
                    if chunks is None:
                        continue
                    blob = bytes(chunks)

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
            continue
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
        if spec.kind == "cosplay" and src.name != "Danbooru":
            continue
        if spec.kind == "cosplay" and not src.cosplay:
            continue
        if spec.sites and src.name not in spec.sites:
            continue
        out.append(src)
    return out


async def run_search(session, spec: Spec, *, previous_character: str | None = None) -> Outcome:
    started = time.monotonic()
    deadline = started + TOTAL_FETCH_BUDGET
    sources = _pick_sources(spec)

    character_tag = spec.character
    if _explicit_blocked(character_tag):
        return Outcome(_display_query(spec, character_tag), None, [], time.monotonic() - started)
    if not character_tag and spec.kind != "cosplay":
        choices = [pair for pair in RESOLVED_CHARS
                   if (not _explicit_blocked(pair[1]))
                   and pair[0] != previous_character]
        character_tag = random.choice(choices)[1] if choices else ""
    display = CHAR_BY_TAG.get(character_tag, character_tag) if character_tag else None

    if spec.kind == "cosplay":
        # Reddit search is also bounded, including its OAuth and listing requests.
        try:
            posts = await asyncio.wait_for(
                _gather_cosplay(session, spec),
                timeout=min(COSPLAY_SEARCH_BUDGET, max(0.01, deadline - time.monotonic())),
            )
        except asyncio.TimeoutError:
            posts = []
    else:
        posts = await _gather(session, _query_for(spec, character_tag), spec.mode,
                              sources, spec.count, spec.rating,
                              budget=min(PRIMARY_SEARCH_BUDGET, max(0.0, deadline - time.monotonic()))) \
            if sources else []

    if not posts and character_tag and spec.kind != "cosplay":
        fallback_choices = [pair for pair in RESOLVED_CHARS
                            if pair[1] != character_tag
                            and not _explicit_blocked(pair[1])
                            and pair[0] != previous_character]
        if fallback_choices:
            fallback_display, fallback_tag = random.choice(fallback_choices)
            log.info("no results for %r, retrying with character %r",
                     _display_query(spec, character_tag), fallback_tag)
            posts = await _gather(session, _query_for(spec, fallback_tag), spec.mode,
                                  sources, spec.count, spec.rating,
                                  budget=min(FALLBACK_SEARCH_BUDGET, max(0.0, deadline - time.monotonic()))) \
                if sources else []
            if posts:
                character_tag = fallback_tag
                display = fallback_display

    query = _display_query(spec, "" if display is None else character_tag)
    if not posts:
        return Outcome(query, display, [], time.monotonic() - started)

    sem = asyncio.Semaphore(CONCURRENCY)
    tasks = [asyncio.create_task(_download(session, p, spec.limit, sem)) for p in posts]
    pending = set(tasks)
    raw: list[tuple] = []
    try:
        # Stop waiting as soon as enough successful attachments are downloaded.
        while pending and sum(r[1] is not None for r in raw) < spec.count:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                break
            done, pending = await asyncio.wait(
                pending, timeout=remaining, return_when=asyncio.FIRST_COMPLETED
            )
            if not done:
                break
            for task in done:
                try:
                    raw.append(task.result())
                except Exception as exc:
                    log.debug("Media download failed: %s", type(exc).__name__)
    finally:
        for task in pending:
            task.cancel()
        if pending:
            await asyncio.gather(*pending, return_exceptions=True)

    ok = [r for r in raw if r[1] is not None][:spec.count]
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

    # Keep the encoded settings last: a long tag list must never push them past
    # Discord's 2048 character footer limit, or the buttons lose their state.
    tail = f" · {len(files)} file(s) · {outcome.elapsed:.1f}s{FOOTER_SEP}{_encode_spec(spec)}"
    room = 2048 - len(tail)
    query = outcome.query if len(outcome.query) <= room else outcome.query[:max(1, room - 1)] + "…"
    summary.set_footer(text=query + tail)

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

    if not files and not spec.spoiler and spec.kind != "cosplay":
        for post in failed[:4]:
            thumbnail = post.get("thumb")
            if thumbnail:
                embed = discord.Embed(color=0x7B68EE)
                embed.set_image(url=thumbnail)
                embeds.append(embed)

    return embeds, files


# -------------------------------------------------------------- result view

class ResultView(discord.ui.View):
    """Persistent Discord buttons; search settings are restored from each embed."""

    def __init__(self) -> None:
        super().__init__(timeout=None)
        self.add_item(self._mk("Reroll", _button_emoji("reroll", "🎲", "reroll"), discord.ButtonStyle.primary, "r", self._reroll))
        self.add_item(self._mk("More", _button_emoji("more", "➕", "more"), discord.ButtonStyle.secondary, "m", self._more))
        self.add_item(self._mk("Spoiler", _button_emoji("spoiler", "🙈", "spoiler"), discord.ButtonStyle.secondary, "s", self._spoiler))
        self.add_item(self._mk("New girl", _button_emoji("new_girl", "🔀", "newgirl"), discord.ButtonStyle.secondary, "n", self._new_girl))
        self.add_item(self._mk("Favorite", _button_emoji("favorite", "❤️", "favorite"), discord.ButtonStyle.success, "f", self._favorite))

    @staticmethod
    def _mk(label, emoji, style, code, callback) -> discord.ui.Button:
        # The buttons are handled centrally by GenshinBot.on_interaction.
        # Do not also attach a View callback: two listeners could acknowledge
        # the same interaction and make buttons intermittently fail.
        return discord.ui.Button(label=label, emoji=emoji, style=style, custom_id=f"gs:{code}")

    async def validate_interaction(self, interaction: discord.Interaction) -> bool:
        spec = _decode_spec(interaction.message)
        if spec is None:
            await interaction.response.send_message(
                "These buttons belong to an older or invalid result. Please run the command again.",
                ephemeral=True,
            )
            return False
        if interaction.user.id != spec.user_id:
            await interaction.response.send_message(
                "Not your search — run the command yourself.", ephemeral=True,
            )
            return False
        return True

    async def on_error(self, interaction, error, item) -> None:
        log.error(
            "Result button %s failed: %s", getattr(item, "custom_id", item), error,
            exc_info=(type(error), error, error.__traceback__),
        )
        try:
            if interaction.response.is_done():
                await interaction.followup.send(
                    "Something went wrong. Check your FadeHost console logs and try again.",
                    ephemeral=True,
                )
            else:
                await interaction.response.send_message(
                    "Something went wrong. Check your FadeHost console logs and try again.",
                    ephemeral=True,
                )
        except discord.HTTPException:
            pass

    async def _spec(self, interaction: discord.Interaction) -> Spec | None:
        spec = _decode_spec(interaction.message)
        if spec is None:
            await interaction.response.send_message(
                "Couldn't read the search settings. Run the slash command again.", ephemeral=True,
            )
            return None
        if interaction.message.id in _BUSY_MESSAGES:
            await interaction.response.send_message(
                "This result is already updating. Please wait a moment.", ephemeral=True,
            )
            return None
        if spec.rating != "safe" and not _channel_is_nsfw(interaction):
            await interaction.response.send_message(
                "Adult-rated results can only be refreshed in age-restricted channels.", ephemeral=True,
            )
            return None
        if _explicit_blocked(spec.character):
            await interaction.response.send_message(
                "Searches for that excluded character are unavailable.", ephemeral=True,
            )
            return None

        _BUSY_MESSAGES.add(interaction.message.id)
        try:
            # For a button, this acknowledges the click WITHOUT creating a new
            # loading message. We can then edit the message whose button was used.
            await interaction.response.defer(thinking=False)
        except Exception:
            _BUSY_MESSAGES.discard(interaction.message.id)
            raise
        return replace(spec, limit=_file_limit(interaction))

    async def _swap(self, interaction: discord.Interaction, spec: Spec,
                    *, previous_character: str | None = None) -> None:
        outcome = await run_search(
            interaction.client.session, spec, previous_character=previous_character,
        )
        if not any(blob is not None for _, blob, _, _ in outcome.results):
            await interaction.followup.send(
                "No new downloadable results were found. Try again or use fewer tags.",
                ephemeral=True,
            )
            return
        embeds, files = _render(spec, outcome)
        # Edit *the actual message clicked*, including messages from /more.
        await interaction.message.edit(embeds=embeds, attachments=files, view=VIEW)
        _remember(interaction.message.id, outcome)

    async def _reroll(self, interaction: discord.Interaction) -> None:
        spec = await self._spec(interaction)
        if spec is None:
            return
        try:
            await self._swap(interaction, spec)
        finally:
            _BUSY_MESSAGES.discard(interaction.message.id)

    async def _new_girl(self, interaction: discord.Interaction) -> None:
        spec = await self._spec(interaction)
        if spec is None:
            return
        try:
            current = _RESULTS.get(interaction.message.id)
            previous = current.character if current else _character_from_embed(interaction.message)
            await self._swap(
                interaction, replace(spec, character=""), previous_character=previous,
            )
        finally:
            _BUSY_MESSAGES.discard(interaction.message.id)

    async def _spoiler(self, interaction: discord.Interaction) -> None:
        spec = await self._spec(interaction)
        if spec is None:
            return
        try:
            outcome = _RESULTS.get(interaction.message.id)
            if outcome is None:
                # Memory is erased on FadeHost restarts. Recover the exact files
                # from Discord instead of silently rerolling different results.
                outcome = await _recover_from_message(interaction.message, spec)
                if outcome is None:
                    await interaction.followup.send(
                        "Couldn't reload those attachments. Please reroll this result first.",
                        ephemeral=True,
                    )
                    return
            spec = replace(spec, spoiler=not spec.spoiler)
            embeds, files = _render(spec, outcome)
            await interaction.message.edit(embeds=embeds, attachments=files, view=VIEW)
            _remember(interaction.message.id, outcome)
        finally:
            _BUSY_MESSAGES.discard(interaction.message.id)

    async def _favorite(self, interaction: discord.Interaction) -> None:
        """Present one item per option; saving happens on selection."""
        if interaction.message.id in _BUSY_MESSAGES:
            await interaction.response.send_message(
                "Please wait for the current result update to finish.", ephemeral=True,
            )
            return
        spec = _decode_spec(interaction.message)
        if spec and spec.rating != "safe" and not _channel_is_nsfw(interaction):
            await interaction.response.send_message(
                "Favorites from adult-rated results require an age-restricted channel.",
                ephemeral=True,
            )
            return
        attachments = list(interaction.message.attachments)
        if not attachments:
            await interaction.response.send_message(
                "This result has no downloadable files to save.", ephemeral=True,
            )
            return
        source_map = _source_by_number(interaction.message)
        options = []
        for i, attachment in enumerate(attachments[:MAX_FILES], 1):
            site, post_id, _ = source_map.get(i, ("Discord", str(attachment.id), ""))
            label = f"{i:02d} · {site} #{post_id}"[:100]
            options.append(discord.SelectOption(
                label=label,
                value=f"{i}:{attachment.id}",
                description=("Video" if _ext_from_url(attachment.filename) in VIDEO_EXTS else "Image")
                + f" · {attachment.size // 1024} KB",
            ))
        picker = discord.ui.View(timeout=None)
        picker.add_item(discord.ui.Select(
            placeholder="Choose ONE image or video to save",
            min_values=1,
            max_values=1,
            options=options,
            custom_id=f"fav:save:{interaction.message.id}:{interaction.user.id}",
        ))
        await interaction.response.send_message(
            "Select the exact image or video you'd like to favorite:",
            view=picker,
            ephemeral=True,
        )

    async def _more(self, interaction: discord.Interaction) -> None:
        spec = await self._spec(interaction)
        if spec is None:
            return
        try:
            # The new message keeps the same original options/result count.
            outcome = await run_search(interaction.client.session, spec)
            if not any(blob is not None for _, blob, _, _ in outcome.results):
                await interaction.followup.send(
                    "No new downloadable results were found. Try again in a moment.",
                    ephemeral=True,
                )
                return
            embeds, files = _render(spec, outcome)
            message = await interaction.followup.send(embeds=embeds, files=files, view=VIEW)
            _remember(message.id, outcome)
        finally:
            _BUSY_MESSAGES.discard(interaction.message.id)


def _character_from_embed(message: discord.Message) -> str | None:
    if not message.embeds:
        return None
    title = message.embeds[0].title or ""
    return title.split(" · ", 1)[1] if " · " in title else None


async def _recover_from_message(message: discord.Message, spec: Spec) -> Outcome | None:
    """Rebuild the cached result from Discord's media after the bot restarts."""
    if not message.attachments or not message.embeds:
        return None
    source_by_number = {}
    description = message.embeds[0].description or ""
    for line in description.splitlines():
        found = re.match(r"`(\d+)`\s+\[([^\]]+) #([^\]]+)\]\(([^)]+)\)", line)
        if found:
            number, site, pid, url = found.groups()
            source_by_number[int(number)] = (site, pid, url)

    results = []
    for idx, attachment in enumerate(message.attachments, 1):
        if attachment.size > spec.limit:
            return None
        try:
            blob = await attachment.read(use_cached=True)
        except (discord.HTTPException, asyncio.TimeoutError):
            return None
        if not blob:
            return None
        name = attachment.filename.removeprefix("SPOILER_")
        extension = _ext_from_url(name)
        site, pid, url = source_by_number.get(
            idx, ("Discord", str(attachment.id), attachment.url),
        )
        post = _mk_post(
            site, pid, attachment.url, attachment.url, attachment.url,
            attachment.url, extension, len(blob), url,
        )
        results.append((post, blob, name, None))

    if not results:
        return None
    return Outcome(
        _display_query(spec, spec.character),
        _character_from_embed(message), results, 0.0,
    )

# -------------------------------------------------------------- favorites

def _init_favorites() -> None:
    """SQLite metadata plus local media files persist across bot restarts."""
    FAVORITES_DIR.mkdir(parents=True, exist_ok=True)
    FAVORITES_MEDIA.mkdir(parents=True, exist_ok=True)
    with closing(sqlite3.connect(FAVORITES_DB, timeout=20)) as conn:
        conn.execute("""
            CREATE TABLE IF NOT EXISTS favorites (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id TEXT NOT NULL,
                source_key TEXT NOT NULL,
                site TEXT NOT NULL,
                post_id TEXT NOT NULL,
                source_url TEXT NOT NULL,
                character TEXT NOT NULL,
                rating TEXT NOT NULL,
                kind TEXT NOT NULL,
                filename TEXT NOT NULL,
                stored_filename TEXT NOT NULL,
                size_bytes INTEGER NOT NULL,
                created_at TEXT NOT NULL,
                UNIQUE(user_id, source_key)
            )
        """)
        conn.execute("CREATE INDEX IF NOT EXISTS ix_favorites_user ON favorites(user_id, id DESC)")
        conn.commit()


def _db() -> sqlite3.Connection:
    conn = sqlite3.connect(FAVORITES_DB, timeout=20)
    conn.row_factory = sqlite3.Row
    return conn


def _favorites_for(user_id: int) -> list[dict]:
    with closing(_db()) as conn:
        return [dict(row) for row in conn.execute(
            "SELECT * FROM favorites WHERE user_id=? ORDER BY id DESC", (str(user_id),),
        ).fetchall()]


def _favorite_source_key(site: str, post_id: str) -> str:
    return f"{site.lower()}:{post_id}"


def _store_favorite(user_id: int, post: dict, blob: bytes, filename: str,
                    *, character: str, rating: str, kind: str) -> tuple[str, int]:
    """Returns (created/already/limit, id). A disk copy, not a hotlink, is saved."""
    site, pid = str(post.get("site", "Discord")), str(post.get("id", ""))
    key = _favorite_source_key(site, pid)
    with closing(_db()) as conn:
        existing = conn.execute(
            "SELECT id FROM favorites WHERE user_id=? AND source_key=?",
            (str(user_id), key),
        ).fetchone()
        if existing:
            return "already", existing["id"]
        count = conn.execute(
            "SELECT COUNT(*) FROM favorites WHERE user_id=?", (str(user_id),),
        ).fetchone()[0]
        if count >= MAX_USER_FAVORITES:
            return "limit", 0

        extension = _ext_from_url(filename)
        if extension not in IMAGE_EXTS | VIDEO_EXTS:
            raise ValueError("Unsupported favorite media type")
        saved_name = f"{uuid.uuid4().hex}.{extension}"
        target = FAVORITES_MEDIA / saved_name
        temp_path = FAVORITES_MEDIA / (saved_name + ".part")
        try:
            temp_path.write_bytes(blob)
            temp_path.replace(target)
            conn.execute("""
                INSERT INTO favorites
                (user_id, source_key, site, post_id, source_url, character,
                 rating, kind, filename, stored_filename, size_bytes, created_at)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                str(user_id), key, site, pid, str(post.get("page", "")),
                character, rating, kind, Path(filename).name, saved_name,
                len(blob), datetime.now(timezone.utc).isoformat(timespec="seconds"),
            ))
            conn.commit()
            fav_id = conn.execute("SELECT last_insert_rowid()").fetchone()[0]
        except sqlite3.IntegrityError:
            target.unlink(missing_ok=True)
            existing = conn.execute(
                "SELECT id FROM favorites WHERE user_id=? AND source_key=?",
                (str(user_id), key),
            ).fetchone()
            if existing:
                return "already", existing["id"]
            raise
        except Exception:
            target.unlink(missing_ok=True)
            raise
        finally:
            temp_path.unlink(missing_ok=True)
    return "created", fav_id


def _remove_favorite(user_id: int, fav_id: int) -> bool:
    with closing(_db()) as conn:
        row = conn.execute(
            "SELECT stored_filename FROM favorites WHERE id=? AND user_id=?",
            (fav_id, str(user_id)),
        ).fetchone()
        if not row:
            return False
        conn.execute("DELETE FROM favorites WHERE id=? AND user_id=?", (fav_id, str(user_id)))
        conn.commit()
    (FAVORITES_MEDIA / row["stored_filename"]).unlink(missing_ok=True)
    return True


def _source_by_number(message: discord.Message) -> dict[int, tuple[str, str, str]]:
    result = {}
    if not message.embeds:
        return result
    for line in (message.embeds[0].description or "").splitlines():
        found = re.match(r"`(\d+)`\s+\[([^\]]+) #([^\]]+)\]\(([^)]+)\)", line)
        if found:
            number, site, pid, url = found.groups()
            result[int(number)] = (site, pid, url)
    return result


def _favorite_browser_view(user_id: int, fav_id: int, index: int, total: int) -> discord.ui.View:
    """Custom IDs are enough; GenshinBot routes clicks even after restarts."""
    view = discord.ui.View(timeout=None)
    for label, emoji, action, disabled, style in (
        ("Previous", "⬅️", "prev", index == 0, discord.ButtonStyle.secondary),
        ("Next", "➡️", "next", index >= total - 1, discord.ButtonStyle.secondary),
        ("Remove", "🗑️", "remove", False, discord.ButtonStyle.danger),
    ):
        view.add_item(discord.ui.Button(
            label=label, emoji=emoji, style=style, disabled=disabled,
            custom_id=f"fav:browse:{action}:{user_id}:{fav_id}",
        ))
    return view


async def _favorite_browser_payload(user_id: int, target_id: int | None = None
                                   ) -> tuple[discord.Embed, discord.File, discord.ui.View] | None:
    rows = await asyncio.to_thread(_favorites_for, user_id)
    if not rows:
        return None
    index = next((i for i, row in enumerate(rows) if row["id"] == target_id), 0)
    row = rows[index]
    media_path = FAVORITES_MEDIA / row["stored_filename"]
    try:
        blob = await asyncio.to_thread(media_path.read_bytes)
    except OSError:
        log.exception("Favorite file missing: %s", media_path)
        raise FileNotFoundError(f"Favorite #{row['id']} media is missing on FadeHost")
    file = discord.File(io.BytesIO(blob), filename=row["filename"])
    embed = discord.Embed(
        title=f"❤️ Favorites · {index + 1}/{len(rows)}",
        description=f"**Favorite ID:** `{row['id']}`\n"
                    f"**Character:** {discord.utils.escape_markdown(row['character'] or 'Unknown')}\n"
                    f"**Source:** {discord.utils.escape_markdown(row['site'])} #{discord.utils.escape_markdown(row['post_id'])}\n"
                    f"**Type:** {'Video' if _ext_from_url(row['filename']) in VIDEO_EXTS else 'Image'}\n"
                    f"**Saved:** {row['created_at'][:10]} (UTC)",
        color=0xE85A83,
    )
    if row["source_url"].startswith(("https://", "http://")):
        embed.add_field(name="Original post", value=f"[View source]({row['source_url']})", inline=False)
    if _ext_from_url(row["filename"]) in IMAGE_EXTS:
        embed.set_image(url=f"attachment://{file.filename}")
    return embed, file, _favorite_browser_view(user_id, row["id"], index, len(rows))


async def _handle_favorite_save(interaction: discord.Interaction, custom_id: str) -> None:
    """Validate the original message and save exactly one selected attachment."""
    try:
        _, _, message_id_text, owner_text = custom_id.split(":", 3)
        message_id, owner_id = int(message_id_text), int(owner_text)
    except ValueError:
        await interaction.response.send_message("Invalid favorite selection.", ephemeral=True)
        return
    if interaction.user.id != owner_id:
        await interaction.response.send_message("This isn't your favorite selector.", ephemeral=True)
        return
    values = (interaction.data or {}).get("values", [])
    try:
        index_text, attachment_id_text = values[0].split(":", 1)
        index, attachment_id = int(index_text), int(attachment_id_text)
    except (ValueError, IndexError, AttributeError):
        await interaction.response.send_message("Choose a valid media item.", ephemeral=True)
        return
    await interaction.response.defer(thinking=False)
    # Fetch the ORIGINAL public result rather than the ephemeral select message.
    original = await interaction.channel.fetch_message(message_id)
    spec = _decode_spec(original)
    if spec is None or spec.user_id != owner_id:
        await interaction.followup.send("The original result is no longer valid.", ephemeral=True)
        return
    if spec.rating != "safe" and not _channel_is_nsfw(interaction):
        await interaction.followup.send("Use an age-restricted channel to save this result.", ephemeral=True)
        return
    attachments = original.attachments
    if not (1 <= index <= len(attachments)) or attachments[index - 1].id != attachment_id:
        await interaction.followup.send(
            "That result changed. Click ❤️ Favorite again to choose from the current files.",
            ephemeral=True,
        )
        return
    attachment = attachments[index - 1]
    if attachment.size > _file_limit(interaction):
        await interaction.followup.send("That file is too large for this bot to save.", ephemeral=True)
        return
    name = attachment.filename.removeprefix("SPOILER_")
    if _ext_from_url(name) not in IMAGE_EXTS | VIDEO_EXTS:
        await interaction.followup.send("Unsupported file type.", ephemeral=True)
        return
    source_map = _source_by_number(original)
    site, pid, url = source_map.get(index, ("Discord", str(attachment.id), attachment.url))
    post = {"site": site, "id": pid, "page": url}
    blob = await attachment.read(use_cached=True)
    if not blob:
        await interaction.followup.send("Couldn't download that attachment.", ephemeral=True)
        return
    status, fav_id = await asyncio.to_thread(
        _store_favorite, owner_id, post, blob, name,
        character=_character_from_embed(original) or "", rating=spec.rating,
        kind=spec.kind,
    )
    if status == "created":
        reply = f"❤️ Saved item {index} as favorite **#{fav_id}**! Open `/favorites` to view it."
    elif status == "already":
        reply = f"Already saved as favorite **#{fav_id}**."
    else:
        reply = f"You've reached {MAX_USER_FAVORITES} favorites. Remove an old one first."
    await interaction.followup.send(reply, ephemeral=True)


async def _handle_favorite_browse(interaction: discord.Interaction, custom_id: str) -> None:
    try:
        _, _, action, owner_text, selected_text = custom_id.split(":", 4)
        owner_id, current_id = int(owner_text), int(selected_text)
    except ValueError:
        await interaction.response.send_message("Invalid favorites button.", ephemeral=True)
        return
    if interaction.user.id != owner_id:
        await interaction.response.send_message("These aren't your favorites.", ephemeral=True)
        return
    if not _channel_is_nsfw(interaction):
        await interaction.response.send_message(
            "Browse your saved media in an age-restricted channel.", ephemeral=True,
        )
        return
    if action not in ("prev", "next", "remove"):
        await interaction.response.send_message("Unknown favorites action.", ephemeral=True)
        return
    await interaction.response.defer(thinking=False)
    rows = await asyncio.to_thread(_favorites_for, owner_id)
    pos = next((i for i, row in enumerate(rows) if row["id"] == current_id), None)
    if action == "remove":
        if pos is not None:
            await asyncio.to_thread(_remove_favorite, owner_id, current_id)
        remaining = await asyncio.to_thread(_favorites_for, owner_id)
        next_id = remaining[min(pos or 0, len(remaining) - 1)]["id"] if remaining else None
    elif not rows:
        next_id = None
    else:
        if pos is None:
            pos = 0
        pos = max(0, min(len(rows) - 1, pos + (-1 if action == "prev" else 1)))
        next_id = rows[pos]["id"]
    if next_id is None:
        await interaction.edit_original_response(
            content="You don't have any favorites yet. Use ❤️ Favorite on a search result.",
            embeds=[], attachments=[], view=None,
        )
        return
    payload = await _favorite_browser_payload(owner_id, next_id)
    if payload is None:
        await interaction.edit_original_response(
            content="Your favorites list is empty.", embeds=[], attachments=[], view=None,
        )
    else:
        embed, file, view = payload
        await interaction.edit_original_response(content=None, embeds=[embed], attachments=[file], view=view)

# --------------------------------------------------------------- bot setup

intents = discord.Intents.default()


class GenshinBot(discord.Client):
    async def setup_hook(self) -> None:
        # Route component clicks directly. This also handles older result
        # messages after a bot restart, without depending on view registration.
        log.info("BUTTON_FIX_V2 active: direct component interaction routing")
        await asyncio.to_thread(_init_favorites)
        log.info("FAVORITES_V1 ready: database %s", FAVORITES_DB)
        self.session = aiohttp.ClientSession(headers={"User-Agent": UA})

    async def on_interaction(self, interaction: discord.Interaction) -> None:
        if interaction.type != discord.InteractionType.component:
            return
        payload = interaction.data
        if not isinstance(payload, dict):
            return
        custom_id = payload.get("custom_id", "")
        callbacks = {
            "gs:r": VIEW._reroll,
            "gs:m": VIEW._more,
            "gs:s": VIEW._spoiler,
            "gs:n": VIEW._new_girl,
            "gs:f": VIEW._favorite,
        }
        callback = callbacks.get(custom_id)
        if callback is None and not custom_id.startswith(("fav:save:", "fav:browse:")):
            return
        log.info(
            "BUTTON_FIX_V2 received %s from user %s on message %s",
            custom_id, interaction.user.id,
            getattr(interaction.message, "id", "unknown"),
        )
        try:
            if custom_id.startswith("fav:save:"):
                await _handle_favorite_save(interaction, custom_id)
            elif custom_id.startswith("fav:browse:"):
                await _handle_favorite_browse(interaction, custom_id)
            else:
                if not await VIEW.validate_interaction(interaction):
                    return
                await callback(interaction)
        except Exception:
            log.exception("BUTTON_FIX_V2 action %s crashed", custom_id)
            try:
                message = "Button error. Please check the FadeHost console logs."
                if interaction.response.is_done():
                    await interaction.followup.send(message, ephemeral=True)
                else:
                    await interaction.response.send_message(message, ephemeral=True)
            except discord.HTTPException:
                log.exception("BUTTON_FIX_V2 could not report the error in Discord")

    async def close(self) -> None:
        session = getattr(self, "session", None)
        if session is not None and not session.closed:
            await session.close()
        await super().close()


bot = GenshinBot(intents=intents)
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


# /genshin offers all validated characters across three separate 25-choice
# autocomplete fields. /cosplay keeps its existing searchable character field.
async def _char_group_autocomplete(current: str, group: int):
    chars = sorted(RESOLVED_CHARS, key=lambda pair: pair[0].lower())
    needle = _norm(current)
    # When typing in the original field, keep full-roster search available.
    # Empty input shows this field's designated group instead.
    options = chars if (needle and group == 0) else chars[group * 25:(group + 1) * 25]
    return [
        app_commands.Choice(name=display, value=tag)
        for display, tag in options
        if not needle or needle in _norm(display) or needle in _norm(tag)
    ][:25]


async def _genshin_char_1(interaction: discord.Interaction, current: str):
    return await _char_group_autocomplete(current, 0)


async def _genshin_char_2(interaction: discord.Interaction, current: str):
    return await _char_group_autocomplete(current, 1)


async def _genshin_char_3(interaction: discord.Interaction, current: str):
    return await _char_group_autocomplete(current, 2)


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


def _channel_is_nsfw(interaction: discord.Interaction) -> bool:
    channel = interaction.channel
    checker = getattr(channel, "is_nsfw", None)
    return bool(callable(checker) and checker())


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
    character="Character group 1 (first 25) — or type any name",
    character_2="Character group 2 (next 25); choose only one group",
    character_3="Character group 3 (remaining names); choose only one group",
    tags="Extra booru tags",
    spoiler="Hide behind a spoiler",
)

@app_commands.choices(type=TYPE_CHOICES, rating=RATING_CHOICES)
@app_commands.autocomplete(
    character=_genshin_char_1, character_2=_genshin_char_2, character_3=_genshin_char_3,
    tags=_tag_autocomplete, preset=_preset_autocomplete,
)
async def _genshin(
    interaction: discord.Interaction,
    count: app_commands.Range[int, 1, 10] = 3,
    preset: str | None = None,
    type: str | None = None,
    rating: str | None = None,
    character: str = "",
    character_2: str = "",
    character_3: str = "",
    tags: str = "",
    spoiler: bool = False,
) -> None:
    await interaction.response.defer(thinking=True)

    selected_characters = [c for c in (character, character_2, character_3) if c]
    if len(selected_characters) > 1:
        await interaction.edit_original_response(
            content="Choose a character from only one of the three character fields."
        )
        return

    spec = _apply_preset(
        preset,
        count,
        type,
        rating,
        selected_characters[0] if selected_characters else "",
        tags,
        spoiler,
        interaction.user.id,
        _file_limit(interaction),
        "explicit",
    )

    if spec.character and _child_coded_character(spec.character):
        await interaction.edit_original_response(
            content="Searches for that excluded character are unavailable."
        )
        return
    if spec.rating != "safe" and not _channel_is_nsfw(interaction):
        await interaction.edit_original_response(
            content="Use an age-restricted channel for adult-rated searches, or select rating:safe."
        )
        return

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
    if not _channel_is_nsfw(interaction):
        await interaction.edit_original_response(
            content="Run adult-rated commands in an age-restricted Discord channel."
        )
        return
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
    if spec.character and _child_coded_character(spec.character):
        await interaction.edit_original_response(
            content="Searches for that excluded character are unavailable."
        )
        return
    if spec.rating != "safe" and not _channel_is_nsfw(interaction):
        await interaction.edit_original_response(
            content="Run adult-rated cosplay searches in an age-restricted Discord channel, or select rating:safe."
        )
        return

    outcome = await run_search(interaction.client.session, spec)
    if not outcome.results:
        await interaction.edit_original_response(
            content=f"No verified Genshin cosplay found for `{outcome.query}`. Try image only, fewer tags, or rating:any."
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


# ------------------------------------------------------------- favorites commands

@app_commands.describe(page="Favorite number in your collection (newest first)")
async def _favorites(interaction: discord.Interaction,
                     page: app_commands.Range[int, 1, 250] = 1) -> None:
    """View saved images/videos; browsing and removal use persistent buttons."""
    if not _channel_is_nsfw(interaction):
        await interaction.response.send_message(
            "Browse favorites in an age-restricted channel.", ephemeral=True,
        )
        return
    await interaction.response.defer(thinking=True, ephemeral=True)
    rows = await asyncio.to_thread(_favorites_for, interaction.user.id)
    if not rows:
        await interaction.followup.send(
            "No favorites yet! Use the ❤️ Favorite button on any result, then choose an item.",
            ephemeral=True,
        )
        return
    selected = rows[min(page - 1, len(rows) - 1)]["id"]
    payload = await _favorite_browser_payload(interaction.user.id, selected)
    if payload:
        embed, file, view = payload
        await interaction.followup.send(embed=embed, file=file, view=view, ephemeral=True)


tree.add_command(app_commands.Command(
    name="favorites", description="Browse your personally saved images and videos.", callback=_favorites,
))


@app_commands.describe(id="Favorite ID shown by /favorites")
async def _unfavorite(interaction: discord.Interaction, id: int) -> None:
    if id <= 0:
        await interaction.response.send_message("Enter a valid favorite ID.", ephemeral=True)
        return
    removed = await asyncio.to_thread(_remove_favorite, interaction.user.id, id)
    await interaction.response.send_message(
        f"🗑️ Removed favorite #{id}." if removed else "Favorite not found in your collection.",
        ephemeral=True,
    )


tree.add_command(app_commands.Command(
    name="unfavorite", description="Remove one favorite by its ID.", callback=_unfavorite,
))

# ------------------------------------------------------------------- runtime

VIEW = ResultView()

@bot.event
async def on_ready() -> None:
    log.info("logged in as %s (%d guilds)", bot.user, len(bot.guilds))

    if getattr(bot, "_startup_complete", False):
        return

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
