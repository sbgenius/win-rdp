#!/usr/bin/env python3
"""Chunk Scanner: a single-file Minecraft chunk and biome explorer.

Just run it:

    python web.py
    python web.py --port 8080 --dir /some/folder

Your browser opens automatically. The first time (and whenever you pick
"Install version..." in the Version menu) a setup screen downloads everything
that version needs, once:

    * the official server jar            (used to generate chunks)
    * the official block textures         (used to draw blocks)
    * the Cubiomes biome engine           (compiled once; needs a C compiler)
    * amulet-core, the Python library that reads the generated world

Everything lives in the "mcseed" folder next to this file. Share the folder
without "mcseed" and the other person just runs web.py and installs the
versions they want.

Requirements: Python 3.9+, Java (for chunk scanning), a C compiler (gcc, clang
or cc; only for the biome map). By running this you accept the Minecraft EULA:
https://aka.ms/MinecraftEULA   Textures are Mojang's property: personal use only.

In the app:
  * "Biome map": a wide Chunkbase-style map computed without any server.
    Hover a chunk for its biomes, click it to analyze its blocks.
  * "Chunk scan": every block type in a chunk with counts, every coordinate
    (CSV download), a layer view for any Y, and a heightmap.
"""
import argparse
import base64
import csv
import ctypes
import hashlib
import importlib
import importlib.util
import io
import json
import os
import platform
import queue
import re
import shutil
import subprocess
import sys
import threading
import time
import urllib.request
import uuid
import webbrowser
import zipfile
from collections import Counter
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlparse

APP_DIR = Path(__file__).resolve().parent
DEFAULT_DIR = APP_DIR / "mcseed"

MANIFEST_URL = "https://piston-meta.mojang.com/mc/game/version_manifest_v2.json"
CUBIOMES_ZIP = "https://github.com/Cubitect/cubiomes/archive/refs/heads/master.zip"
CUBIOMES_ZIP_AT = "https://github.com/Cubitect/cubiomes/archive/{sha}.zip"
CUBIOMES_API = "https://api.github.com/repos/Cubitect/cubiomes/commits/master"
TEXTURE_PREFIX = "assets/minecraft/textures/block/"
MIN_VERSION = (1, 18)          # oldest release offered in the installer

DIMENSIONS = {
    "overworld": "minecraft:overworld",
    "nether": "minecraft:the_nether",
    "end": "minecraft:the_end",
}
# Vertical range per dimension (inclusive), used only by the slow fallback scan.
DEFAULT_Y = {
    "overworld": (-64, 319),
    "nether": (0, 255),
    "end": (0, 255),
}
DIMS = {"overworld": 0, "nether": -1, "end": 1}    # Cubiomes dimension ids
MAX_CELLS = 2_200_000

CACHE = {}            # scan id -> result dict (newest last)
CACHE_LIMIT = 5
SCAN_LOCK = threading.Lock()   # only one server/world access at a time
ARGS = None


class SetupError(RuntimeError):
    pass


class BiomeError(RuntimeError):
    pass


# --------------------------------------------------------------------------
# Config (mcseed/config.json, same format as the old setup.py)
# --------------------------------------------------------------------------
def read_cfg():
    p = Path(ARGS.dir) / "config.json"
    cfg = {}
    if p.exists():
        try:
            cfg = json.loads(p.read_text())
        except ValueError:
            cfg = {}
    cfg.setdefault("versions", [])
    cfg.setdefault("memory", "2G")
    return cfg


def write_cfg(cfg):
    d = Path(ARGS.dir)
    d.mkdir(parents=True, exist_ok=True)
    (d / "config.json").write_text(json.dumps(cfg, indent=2))


def installed_versions():
    """Versions that have a server jar on disk."""
    d = Path(ARGS.dir)
    return [v for v in read_cfg()["versions"] if (d / "jars" / f"{v}.jar").exists()]


def version_key(v):
    return tuple(int(p) for p in v.split("."))


_JAVA = {}


def installed_java_major():
    if "v" in _JAVA:
        return _JAVA["v"]
    try:
        out = subprocess.run(["java", "-version"], capture_output=True, text=True).stderr
        m = re.search(r'version "(\d+)(?:\.(\d+))?', out)
        major = int(m.group(1)) if m else None
        if major == 1 and m:
            major = int(m.group(2))
    except (FileNotFoundError, OSError):
        major = None
    _JAVA["v"] = major
    return major


def amulet_ok():
    return importlib.util.find_spec("amulet") is not None


# --------------------------------------------------------------------------
# Downloads
# --------------------------------------------------------------------------
def fetch_json(url):
    with urllib.request.urlopen(url, timeout=30) as r:
        return json.load(r)


def download(url, dest, sha1=None, sid=None, label="Downloading"):
    """Download with progress reporting to the setup screen and optional SHA-1 check."""
    dest = Path(dest)
    dest.parent.mkdir(parents=True, exist_ok=True)
    part = dest.with_name(dest.name + ".part")
    h = hashlib.sha1()
    got, last = 0, 0.0
    try:
        with urllib.request.urlopen(url, timeout=60) as r, open(part, "wb") as f:
            total = int(r.headers.get("Content-Length") or 0)
            while True:
                chunk = r.read(1 << 16)
                if not chunk:
                    break
                f.write(chunk)
                h.update(chunk)
                got += len(chunk)
                now = time.time()
                if sid and now - last > 0.15:
                    last = now
                    if total:
                        _step(sid, progress=got / total, detail=f"{label}: {got / 1e6:.1f} / {total / 1e6:.1f} MB")
                    else:
                        _step(sid, progress=None, detail=f"{label}: {got / 1e6:.1f} MB")
        if sha1 and h.hexdigest() != sha1:
            raise SetupError("Checksum mismatch on a downloaded file; please try again.")
        os.replace(part, dest)
    finally:
        if part.exists():
            part.unlink()


_MANIFEST = {"t": 0.0, "data": None}


def manifest():
    if _MANIFEST["data"] is None or time.time() - _MANIFEST["t"] > 600:
        _MANIFEST["data"] = fetch_json(MANIFEST_URL)
        _MANIFEST["t"] = time.time()
    return _MANIFEST["data"]


def list_versions():
    """Release versions (newest first) that this app offers to install."""
    out = []
    for v in manifest()["versions"]:
        m = re.fullmatch(r"(\d+)\.(\d+)(?:\.(\d+))?", v["id"])
        if v.get("type") == "release" and m and (int(m.group(1)), int(m.group(2))) >= MIN_VERSION:
            out.append(v["id"])
    return out


# --------------------------------------------------------------------------
# Chunk generation (starts the vanilla server headlessly)
# --------------------------------------------------------------------------
def has_if_loaded(version):
    """`execute if loaded` exists from Java 1.19.4 on (26.x and later included)."""
    m = re.fullmatch(r"(\d+)\.(\d+)(?:\.(\d+))?", version or "")
    if not m:
        return True
    return (int(m.group(1)), int(m.group(2)), int(m.group(3) or 0)) >= (1, 19, 4)


def generate_chunk(run_dir, jar, memory, dim_id, x, z, verbose, version=None):
    cmd = ["java", f"-Xmx{memory}", "-jar", str(jar.resolve()), "--nogui"]
    try:
        proc = subprocess.Popen(
            cmd, cwd=run_dir, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, text=True, bufsize=1,
        )
    except FileNotFoundError:
        raise ValueError("Java was not found. Install Java (https://adoptium.net) and restart web.py.")
    q = queue.Queue()

    def pump():
        for line in proc.stdout:
            q.put(line)

    threading.Thread(target=pump, daemon=True).start()

    def send(command):
        proc.stdin.write(command + "\n")
        proc.stdin.flush()

    def wait_for(pattern, timeout):
        end = time.time() + timeout
        while time.time() < end:
            try:
                line = q.get(timeout=1)
            except queue.Empty:
                if proc.poll() is not None:
                    raise RuntimeError("Server exited unexpectedly (is your Java version new enough?).")
                continue
            if verbose:
                print("  [server]", line.rstrip())
            if re.search(pattern, line):
                return line
        raise TimeoutError(f"Timed out waiting for: {pattern}")

    try:
        wait_for(r"Done \(", 300)
        send(f"execute in {dim_id} run forceload add {x} {z}")
        modern = has_if_loaded(version)
        for _ in range(90):
            if modern:
                send(f"execute in {dim_id} if loaded {x} 64 {z}")
                line = wait_for(r"Test (passed|failed)", 15)
                loaded = "passed" in line
            else:
                # Older servers have no `if loaded`. `setblock ... keep` never changes anything here
                # (it only replaces air with air) but refuses with "not loaded" until the chunk exists.
                send(f"execute in {dim_id} run setblock {x} 64 {z} minecraft:air keep")
                line = wait_for(r"Changed the block|Could not set the block|not loaded", 15)
                loaded = "not loaded" not in line
            if loaded:
                break
            time.sleep(1)
        else:
            raise TimeoutError("Chunk never finished loading.")
        send(f"execute in {dim_id} run forceload remove {x} {z}")
        send("save-all flush")
        wait_for(r"Saved the game", 60)
    finally:
        if proc.poll() is None:
            send("stop")
            try:
                proc.wait(timeout=60)
            except subprocess.TimeoutExpired:
                proc.kill()


def block_text(block):
    text = getattr(block, "full_blockstate", None) or block.namespaced_name
    return text.replace('"', "")


def short_name(name):
    return name[len("minecraft:"):] if name.startswith("minecraft:") else name


# --------------------------------------------------------------------------
# Biome engine (Cubiomes, compiled once)
# --------------------------------------------------------------------------
# Thin C wrapper so Python never has to know the layout of Cubiomes' structs.
SHIM = r"""
#include <stdlib.h>
#include <string.h>
#include "generator.h"
#include "util.h"

#ifdef _WIN32
#define EXPORT __declspec(dllexport)
#else
#define EXPORT
#endif

EXPORT int shim_mc(const char *s) { return str2mc(s); }

EXPORT int shim_gen(int mc, int dim, unsigned long long seed, int scale,
                    int x, int z, int w, int h, int y, int *out)
{
    Generator *g = (Generator *)malloc(sizeof(Generator));
    if (!g) return -2;
    setupGenerator(g, mc, 0);
    applySeed(g, dim, (uint64_t)seed);
    Range r = {scale, x, z, w, h, y, 1};
    int *cache = allocCache(g, r);
    if (!cache) { free(g); return -3; }
    int err = genBiomes(g, cache, r);
    if (!err) memcpy(out, cache, (size_t)w * (size_t)h * sizeof(int));
    free(cache);
    free(g);
    return err;
}

EXPORT int shim_gen_strided(int mc, int dim, unsigned long long seed, int step,
                            int x0, int z0, int w, int h, int yq, int *out)
{
    Generator *g = (Generator *)malloc(sizeof(Generator));
    if (!g) return -2;
    setupGenerator(g, mc, 0);
    applySeed(g, dim, (uint64_t)seed);
    for (int j = 0; j < h; j++) {
        for (int i = 0; i < w; i++) {
            int bx = x0 + i * step + step / 2;
            int bz = z0 + j * step + step / 2;
            out[(size_t)j * (size_t)w + (size_t)i] = getBiomeAt(g, 4, bx >> 2, yq, bz >> 2);
        }
    }
    free(g);
    return 0;
}

EXPORT const char *shim_name(int mc, int id) { return biome2str(mc, id); }

EXPORT void shim_colors(unsigned char *out) { initBiomeColors((unsigned char (*)[3])out); }
"""


SHIM_REV = 2    # bump when the C wrapper changes so existing builds get rebuilt

# Slime chunks: pure Java-Random maths, no Cubiomes API needed.
SHIM_SLIME = r"""
static unsigned long long jr_step(unsigned long long *s) { *s = (*s * 0x5DEECE66DULL + 0xBULL) & ((1ULL << 48) - 1); return *s; }
EXPORT int shim_slime(unsigned long long seed, int cx0, int cz0, int w, int h, unsigned char *out)
{
    for (int j = 0; j < h; j++) for (int i = 0; i < w; i++) {
        int x = cx0 + i, z = cz0 + j;
        int xx = (int)((unsigned)x * (unsigned)x * 4987142u), x1 = (int)((unsigned)x * 5947611u);
        int zz = (int)((unsigned)z * (unsigned)z), z1 = (int)((unsigned)z * 389711u);
        long long v = (long long)seed + xx + x1 + (long long)zz * 4392871LL + z1;
        v ^= 987234911LL;
        unsigned long long st = ((unsigned long long)v ^ 0x5DEECE66DULL) & ((1ULL << 48) - 1);
        int bits, val;
        do { bits = (int)(jr_step(&st) >> 17); val = bits % 10; } while ((int)((unsigned)bits - (unsigned)val + 9u) < 0);
        out[(size_t)j * (size_t)w + (size_t)i] = (val == 0);
    }
    return 0;
}
"""

# Structures (villages, temples, ...): uses Cubiomes' finders.
SHIM_STRUCTS = r"""
#include "finders.h"
static int fdiv_(int a, int b) { int q = a / b; if ((a % b != 0) && ((a < 0) != (b < 0))) q--; return q; }
EXPORT const char *shim_struct_name(int t) { return struct2str(t); }
EXPORT int shim_struct_cfg(int mc, int t) { StructureConfig sc; return getStructureConfig(t, mc, &sc) ? (int)sc.regionSize : 0; }
EXPORT int shim_structs(int mc, int dim, unsigned long long seed, int t,
                        int x0, int z0, int x1, int z1, int *out, int maxn)
{
    StructureConfig sc;
    if (!getStructureConfig(t, mc, &sc)) return -1;
    Generator *g = (Generator *)malloc(sizeof(Generator));
    if (!g) return -2;
    setupGenerator(g, mc, 0);
    applySeed(g, dim, (uint64_t)seed);
    int rb = sc.regionSize * 16, n = 0;
    for (int rz = fdiv_(z0, rb); rz <= fdiv_(z1, rb); rz++)
        for (int rx = fdiv_(x0, rb); rx <= fdiv_(x1, rb); rx++) {
            Pos p;
            if (!getStructurePos(t, mc, (uint64_t)seed, rx, rz, &p)) continue;
            if (p.x < x0 || p.x > x1 || p.z < z0 || p.z > z1) continue;
            if (!isViableStructurePos(t, g, p.x, p.z, 0)) continue;
            if (n >= maxn) { free(g); return n; }
            out[2 * n] = p.x; out[2 * n + 1] = p.z; n++;
        }
    free(g);
    return n;
}
"""

SHIM_EXTRA = r"""
EXPORT int shim_strongholds(int mc, unsigned long long seed, int maxn, int *out)
{
    Generator *g = (Generator *)malloc(sizeof(Generator));
    if (!g) return -2;
    setupGenerator(g, mc, 0);
    applySeed(g, 0, (uint64_t)seed);
    StrongholdIter sh;
    initFirstStronghold(&sh, mc, (uint64_t)seed);
    int n = 0, rem;
    do { rem = nextStronghold(&sh, g); out[2 * n] = sh.pos.x; out[2 * n + 1] = sh.pos.z; n++; } while (rem > 0 && n < maxn);
    free(g);
    return n;
}
EXPORT int shim_spawn(int mc, unsigned long long seed, int *out)
{
    Generator *g = (Generator *)malloc(sizeof(Generator));
    if (!g) return -2;
    setupGenerator(g, mc, 0);
    applySeed(g, 0, (uint64_t)seed);
    Pos p = getSpawn(g);
    out[0] = p.x; out[1] = p.z;
    free(g);
    return 0;
}
"""
# Tried in order; if a newer Cubiomes changes an API, we fall back to a smaller wrapper
# so the biome map always keeps working.
SHIM_VARIANTS = [SHIM + SHIM_SLIME + SHIM_STRUCTS + SHIM_EXTRA, SHIM + SHIM_SLIME + SHIM_STRUCTS, SHIM + SHIM_SLIME, SHIM]


def lib_path(d):
    ext = {"Windows": ".dll", "Darwin": ".dylib"}.get(platform.system(), ".so")
    return Path(d) / "cubiomes" / ("libbiomes" + ext)


def biomes_available():
    return lib_path(ARGS.dir).exists()


def compiler_hint():
    s = platform.system()
    if s == "Windows":
        return "Install a C compiler (e.g. MSYS2/MinGW-w64 gcc, and add it to PATH), then use Version > Install version... > Install to retry."
    if s == "Darwin":
        return "Run  xcode-select --install  in a terminal, then use Version > Install version... > Install to retry."
    return "Install gcc (e.g. sudo apt install build-essential), then use Version > Install version... > Install to retry."


def build_cubiomes(d, sid="biomes"):
    """Download the Cubiomes source and compile it with the wrapper into <d>/cubiomes/."""
    global _LIB
    cc = next((shutil.which(c) for c in ("cc", "gcc", "clang") if shutil.which(c)), None)
    if not cc:
        raise BiomeError("No C compiler found (looked for cc, gcc, clang). " + compiler_hint())

    root = Path(d) / "cubiomes"
    src = root / "src"
    if src.exists():
        shutil.rmtree(src)
    src.mkdir(parents=True)

    zpath = root / "cubiomes.zip"
    sha = latest_cubiomes_sha()
    url = CUBIOMES_ZIP_AT.format(sha=sha) if sha else CUBIOMES_ZIP
    download(url, zpath, None, sid, "Cubiomes source")
    _step(sid, progress=None, detail="Unpacking Cubiomes...")
    with zipfile.ZipFile(zpath) as z:
        for info in z.infolist():
            parts = info.filename.split("/", 1)       # "cubiomes-master/<path>"
            if len(parts) == 2 and parts[1] and not info.is_dir():
                target = (src / parts[1]).resolve()
                if src.resolve() not in target.parents:   # ignore anything odd
                    continue
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(z.read(info))
    zpath.unlink()
    sources = [p for p in sorted(src.glob("*.c"))
               if "int main(" not in p.read_text(errors="ignore")]
    out = lib_path(d)
    tmp = out.with_name("building_" + out.name)
    _step(sid, progress=None, detail=f"Compiling with {Path(cc).name} (this can take a minute)...")
    r = None
    for variant in SHIM_VARIANTS:
        (src / "biomes_shim.c").write_text(variant)
        cmd = [cc, "-O3", "-fwrapv", "-I", str(src)]
        cmd += ["-dynamiclib"] if platform.system() == "Darwin" else ["-shared"]
        if platform.system() != "Windows":
            cmd += ["-fPIC"]
        cmd += ["-o", str(tmp)] + [str(s) for s in sources] + [str(src / "biomes_shim.c"), "-lm"]
        r = subprocess.run(cmd, capture_output=True, text=True)
        if r.returncode == 0:
            break
        joblog("biomes: a wrapper variant failed to compile, trying a smaller one")
    if r.returncode != 0:
        tail = "\n".join((r.stderr or r.stdout or "").strip().splitlines()[-6:])
        raise BiomeError("Compiling the biome engine failed:\n" + tail)
    _LIB = None
    try:
        os.replace(tmp, out)
    except OSError as e:
        raise BiomeError(f"Built the engine but couldn't replace {out.name} ({e}). Restart web.py and try again.")
    shutil.rmtree(src, ignore_errors=True)
    try:
        commit_file(d).write_text(f"{sha or ''}|{SHIM_REV}")
    except OSError:
        pass


def commit_file(d):
    return Path(d) / "cubiomes" / "commit.txt"


def latest_cubiomes_sha(timeout=5):
    """Newest commit id on Cubiomes' master branch, or None if offline / rate-limited."""
    try:
        req = urllib.request.Request(CUBIOMES_API, headers={
            "Accept": "application/vnd.github.sha", "User-Agent": "chunk-scanner"})
        with urllib.request.urlopen(req, timeout=timeout) as r:
            sha = r.read().decode().strip()
        return sha if re.fullmatch(r"[0-9a-f]{40}", sha) else None
    except Exception:
        return None


def update_cubiomes_if_newer(d):
    """At startup: if Cubiomes has new commits since we last built it, download and rebuild.
    Only runs if the engine is already installed; any failure keeps the old build."""
    if not lib_path(d).exists():
        return
    latest = latest_cubiomes_sha()
    if not latest:
        print("Biome engine: couldn't check for updates (offline?). Using the installed build.")
        return
    try:
        have = commit_file(d).read_text().strip()
    except OSError:
        have = ""
    if have == f"{latest}|{SHIM_REV}":
        print("Biome engine: up to date.")
        return
    print(f"Biome engine: newer Cubiomes found ({latest[:7]}); downloading and rebuilding...")
    try:
        build_cubiomes(d)
        print("Biome engine: updated.")
    except Exception as e:
        print(f"Biome engine: update failed, keeping the old build ({e})")


_LIB = None


def _load(d):
    global _LIB
    if _LIB is None:
        p = lib_path(d)
        if not p.exists():
            raise BiomeError("The biome engine isn't built yet. Open the Version menu > Install version... to set it up.")
        try:
            lib = ctypes.CDLL(str(p.resolve()))
        except OSError as e:
            raise BiomeError(f"Could not load {p}: {e}")
        if not hasattr(lib, "shim_gen_strided"):
            raise BiomeError("The compiled biome engine is out of date. Open the Version menu > Install version... to rebuild it.")
        c = ctypes
        lib.shim_mc.argtypes = [c.c_char_p]
        lib.shim_mc.restype = c.c_int
        lib.shim_gen.argtypes = [c.c_int, c.c_int, c.c_ulonglong, c.c_int, c.c_int, c.c_int,
                                 c.c_int, c.c_int, c.c_int, c.POINTER(c.c_int)]
        lib.shim_gen.restype = c.c_int
        lib.shim_gen_strided.argtypes = [c.c_int, c.c_int, c.c_ulonglong, c.c_int, c.c_int, c.c_int,
                                         c.c_int, c.c_int, c.c_int, c.POINTER(c.c_int)]
        lib.shim_gen_strided.restype = c.c_int
        lib.shim_name.argtypes = [c.c_int, c.c_int]
        lib.shim_name.restype = c.c_char_p
        lib.shim_colors.argtypes = [c.POINTER(c.c_ubyte)]
        lib.shim_colors.restype = None
        if hasattr(lib, "shim_slime"):
            lib.shim_slime.argtypes = [c.c_ulonglong, c.c_int, c.c_int, c.c_int, c.c_int, c.POINTER(c.c_ubyte)]
            lib.shim_slime.restype = c.c_int
        if hasattr(lib, "shim_structs"):
            lib.shim_struct_name.argtypes = [c.c_int]
            lib.shim_struct_name.restype = c.c_char_p
            lib.shim_struct_cfg.argtypes = [c.c_int, c.c_int]
            lib.shim_struct_cfg.restype = c.c_int
            lib.shim_structs.argtypes = [c.c_int, c.c_int, c.c_ulonglong, c.c_int, c.c_int, c.c_int,
                                         c.c_int, c.c_int, c.POINTER(c.c_int), c.c_int]
            lib.shim_structs.restype = c.c_int
        if hasattr(lib, "shim_strongholds"):
            lib.shim_strongholds.argtypes = [c.c_int, c.c_ulonglong, c.c_int, c.POINTER(c.c_int)]
            lib.shim_strongholds.restype = c.c_int
            lib.shim_spawn.argtypes = [c.c_int, c.c_ulonglong, c.POINTER(c.c_int)]
            lib.shim_spawn.restype = c.c_int
        colors = (c.c_ubyte * 768)()
        lib.shim_colors(colors)
        _LIB = (lib, bytes(colors))
    return _LIB


def seed_to_int(seed):
    """Same rule as Minecraft: a number is used as-is, any other text is hashed (Java String.hashCode)."""
    s = seed.strip()
    if re.fullmatch(r"-?\d+", s):
        return int(s) & 0xFFFFFFFFFFFFFFFF
    h = 0
    data = s.encode("utf-16-le")
    for i in range(0, len(data), 2):
        h = (31 * h + (data[i] | data[i + 1] << 8)) & 0xFFFFFFFF
    if h >= 0x80000000:
        h -= 0x100000000
    return h & 0xFFFFFFFFFFFFFFFF


def _resolve_mc(lib, version):
    m = re.fullmatch(r"(\d+)\.(\d+)(?:\.(\d+))?", version or "")
    if not m:
        raise BiomeError(f"Unrecognised version {version!r}.")
    major, minor, patch = m.group(1), m.group(2), m.group(3)
    tries = [version]
    if major == "1" and minor == "21" and patch and int(patch) >= 4:
        tries.append("1.21")          # 1.21.4+ is Cubiomes' newest ("1.21 WD") model, not 1.21.3
    if patch:
        tries += [f"{major}.{minor}.{p}" for p in range(int(patch) - 1, 0, -1)]
        tries.append(f"{major}.{minor}")
    # Newer than anything Cubiomes names (e.g. the 26.x releases): use its newest model.
    # "1.21" is Cubiomes' newest (the 1.21.4+ generation); worldgen is ~97% identical.
    tries += ["1.21", "1.20"]
    for t in tries:
        mc = lib.shim_mc(t.encode())
        if mc > 0:
            return mc, t
    raise BiomeError(f"This Cubiomes build doesn't know Minecraft {version} yet.")


# cubiomes struct name -> (label, colour, dimension, on by default)
STRUCT_DEFS = {
    "village": ("Village", "#e8c15a", 0, True), "desert_pyramid": ("Desert temple", "#e3a857", 0, True),
    "jungle_pyramid": ("Jungle temple", "#5fbf5f", 0, True), "swamp_hut": ("Witch hut", "#8a6fd1", 0, True),
    "igloo": ("Igloo", "#bfe7f5", 0, True), "ocean_ruin": ("Ocean ruin", "#4aa3c7", 0, False),
    "shipwreck": ("Shipwreck", "#7a5c3e", 0, False), "monument": ("Ocean monument", "#3fd0c9", 0, True),
    "mansion": ("Woodland mansion", "#b5483a", 0, True), "pillager_outpost": ("Pillager outpost", "#9a9a9a", 0, True),
    "ruined_portal": ("Ruined portal", "#c44fd1", 0, False), "buried_treasure": ("Buried treasure", "#f0e04a", 0, False),
    "mineshaft": ("Mineshaft", "#a0845c", 0, False), "ancient_city": ("Ancient city", "#2c7f8f", 0, True),
    "trail_ruins": ("Trail ruins", "#d98e6a", 0, False), "trial_chambers": ("Trial chambers", "#e07b39", 0, True),
    "amethyst_geode": ("Amethyst geode", "#b46be0", 0, False), "desert_well": ("Desert well", "#e8d26a", 0, False),
    "stronghold": ("Stronghold", "#ffffff", 0, True), "spawn": ("World spawn", "#ff4d4d", 0, True),
    "fortress": ("Nether fortress", "#c0392b", -1, True), "bastion_remnant": ("Bastion remnant", "#6b6b6b", -1, True),
    "ruined_portal_nether": ("Ruined portal", "#c44fd1", -1, False),
    "end_city": ("End city", "#d9a8f0", 1, True), "end_gateway": ("End gateway", "#7fe0d0", 1, False),
}
MAX_STRUCT_REGIONS = 100000
_SPECIAL_CACHE = {}


def generate_structures(d, seed, version, dimension, x0, z0, x1, z1, want=()):
    import ctypes as c
    if dimension not in DIMS:
        raise BiomeError("Unknown dimension.")
    if not str(seed).strip():
        raise BiomeError("Seed is required.")
    lib, _ = _load(d)
    if not hasattr(lib, "shim_structs"):
        raise BiomeError("This engine build has no structure support. Open Version > Install version... to rebuild it.")
    mc, used = _resolve_mc(lib, version)
    sd, dim = seed_to_int(str(seed)), DIMS[dimension]
    names = {}
    for t in range(0, 48):
        n = lib.shim_struct_name(t)
        if n:
            names[n.decode()] = t
    types, items = [], {}
    for name, (label, color, ddim, on) in STRUCT_DEFS.items():
        if ddim != dim:
            continue
        ent = {"id": name, "label": label, "color": color, "on": on, "skipped": False}
        if name in ("stronghold", "spawn"):
            if not hasattr(lib, "shim_strongholds"):
                continue
            if name not in want:
                types.append(ent)
                continue
            key = (mc, sd, name)
            if key not in _SPECIAL_CACHE:
                if name == "stronghold":
                    buf = (c.c_int * 256)()
                    n = lib.shim_strongholds(mc, sd, 128, buf)
                    _SPECIAL_CACHE[key] = [[buf[2 * i], buf[2 * i + 1]] for i in range(max(n, 0))]
                else:
                    buf = (c.c_int * 2)()
                    lib.shim_spawn(mc, sd, buf)
                    _SPECIAL_CACHE[key] = [[buf[0], buf[1]]]
            items[name] = [p for p in _SPECIAL_CACHE[key] if x0 <= p[0] <= x1 and z0 <= p[1] <= z1]
        else:
            t = names.get(name)
            rs = lib.shim_struct_cfg(mc, t) if t is not None else 0
            if not rs:
                continue                     # this structure doesn't exist in this version
            if name not in want:
                types.append(ent)            # listed, but not computed until the user turns it on
                continue
            rb = rs * 16
            if ((x1 - x0) // rb + 2) * ((z1 - z0) // rb + 2) > MAX_STRUCT_REGIONS:
                ent["skipped"] = True        # area too big: zoom in
            else:
                cap = 20000
                buf = (c.c_int * (2 * cap))()
                n = lib.shim_structs(mc, dim, sd, t, x0, z0, x1, z1, buf, cap)
                items[name] = [[buf[2 * i], buf[2 * i + 1]] for i in range(max(n, 0))]
        types.append(ent)
    return {"types": types, "items": items, "mc": used}


def generate_slime(d, seed, cx0, cz0, w, h):
    import ctypes as c
    if w < 1 or h < 1 or w * h > 250000:
        raise BiomeError("Zoom in to see slime chunks.")
    lib, _ = _load(d)
    if not hasattr(lib, "shim_slime"):
        raise BiomeError("This engine build has no slime-chunk support. Open Version > Install version... to rebuild it.")
    buf = (c.c_ubyte * (w * h))()
    lib.shim_slime(seed_to_int(str(seed)), cx0, cz0, w, h, buf)
    return {"cx0": cx0, "cz0": cz0, "w": w, "h": h, "grid": base64.b64encode(bytes(buf)).decode()}


def generate_biomes(d, seed, version, dimension, bx0, bz0, step, w, h, y):
    """Biomes for a w x h grid of cells. Each cell is step x step blocks (step is a multiple of 4);
    cell (i, j) covers blocks [bx0 + i*step, +step) x [bz0 + j*step, +step) and holds the biome at its centre."""
    import ctypes as c

    if dimension not in DIMS:
        raise BiomeError("Unknown dimension.")
    if not str(seed).strip():
        raise BiomeError("Seed is required.")
    if step < 4 or step % 4 or step > 8192 or bx0 % 4 or bz0 % 4:
        raise BiomeError("Bad map request (step and origin must be multiples of 4).")
    if w < 1 or h < 1 or w > 4096 or h > 4096 or w * h > MAX_CELLS:
        raise BiomeError("Requested map area is too large; zoom in a little.")

    lib, colors = _load(d)
    mc, used = _resolve_mc(lib, version)
    buf = (c.c_int * (w * h))()
    sd = seed_to_int(str(seed))
    if step == 4:   # fast batch path
        err = lib.shim_gen(mc, DIMS[dimension], sd, 4, bx0 >> 2, bz0 >> 2, w, h, y >> 2, buf)
    else:           # zoomed out: sample the biome at the centre of each big cell
        err = lib.shim_gen_strided(mc, DIMS[dimension], sd, step, bx0, bz0, w, h, y >> 2, buf)
    if err != 0:
        raise BiomeError(f"Cubiomes could not generate this area (code {err}); "
                         f"it may not support the {dimension} for {version}.")

    try:
        import numpy as np
        arr = np.frombuffer(buf, dtype=np.int32)
        ids = (arr & 0xFF).astype(np.uint8)
        data = ids.tobytes()
        present = np.unique(ids).tolist()
    except ImportError:
        data = bytes(v & 0xFF for v in buf)
        present = sorted(set(data))

    palette = []
    for i in present:
        name = lib.shim_name(mc, i)
        name = name.decode() if name else f"unknown_{i}"
        r, g, b = colors[i * 3], colors[i * 3 + 1], colors[i * 3 + 2]
        palette.append({"id": i, "name": name, "color": f"#{r:02x}{g:02x}{b:02x}"})

    return {
        "bx0": bx0, "bz0": bz0, "step": step, "w": w, "h": h,
        "grid": base64.b64encode(data).decode(),
        "palette": palette, "mc": used, "requested": version,
    }


# --------------------------------------------------------------------------
# Installer (runs in a background thread; the browser polls /api/job)
# --------------------------------------------------------------------------
JOB_LOCK = threading.Lock()
STEP_DEFS = [
    ("meta", "Look up version"),
    ("python", "Python library (amulet-core)"),
    ("java", "Java runtime"),
    ("server", "Server jar"),
    ("textures", "Block textures"),
    ("biomes", "Biome engine"),
]
JOB = {"state": "idle", "version": None, "steps": [], "log": [], "error": None}


def job_snapshot():
    with JOB_LOCK:
        snap = json.loads(json.dumps(JOB))
    snap["log"] = snap["log"][-12:]
    return snap


def _step(sid, **kw):
    with JOB_LOCK:
        for s in JOB["steps"]:
            if s["id"] == sid:
                s.update(kw)


def joblog(msg):
    with JOB_LOCK:
        JOB["log"].append(str(msg))
        del JOB["log"][:-200]


def start_install(version):
    if not re.fullmatch(r"\d+\.\d+(\.\d+)?", version or ""):
        raise ValueError("Pick a Minecraft version to install.")
    with JOB_LOCK:
        if JOB["state"] == "running":
            raise ValueError("An installation is already running.")
        JOB.update(
            state="running", version=version, error=None, log=[],
            steps=[{"id": i, "label": l, "status": "pending", "detail": "", "progress": None}
                   for i, l in STEP_DEFS],
        )
    threading.Thread(target=_install_thread, args=(version,), daemon=True).start()


def _run_step(sid, fn, fatal=False):
    _step(sid, status="active", detail="", progress=None)
    try:
        res = fn()
        status, detail = res if res else ("done", "")
        _step(sid, status=status, detail=detail, progress=None)
    except Exception as e:
        msg = str(e) if isinstance(e, (SetupError, BiomeError)) else f"{type(e).__name__}: {e}"
        joblog(f"{sid}: {msg}")
        if fatal:
            _step(sid, status="error", detail=msg, progress=None)
            raise SetupError(msg)
        _step(sid, status="warn", detail=msg, progress=None)


def _install_thread(version):
    d = Path(ARGS.dir)
    ctx = {}

    def meta():
        try:
            entry = next((v for v in manifest()["versions"] if v["id"] == version), None)
            if entry is None:
                raise SetupError(f"Version {version} not found in Mojang's manifest.")
            ctx["info"] = fetch_json(entry["url"])
        except OSError as e:
            raise SetupError(f"Couldn't reach Mojang's servers (check your internet connection): {e}")
        if not ctx["info"].get("downloads", {}).get("server"):
            raise SetupError(f"No server jar is published for {version}.")
        return "done", f"Minecraft {version}"

    def python_libs():
        if amulet_ok():
            return "skipped", "Already installed"
        _step("python", detail="Installing amulet-core with pip...")
        p = subprocess.Popen([sys.executable, "-m", "pip", "install", "amulet-core>=1.9,<2"],
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        tail = []
        for line in p.stdout:
            line = line.strip()
            if line:
                tail.append(line)
                joblog(line)
                _step("python", detail=line[:100])
        if p.wait() != 0:
            hint = ""
            if any("externally-managed" in t for t in tail):
                hint = (" Your Python is 'externally managed': run web.py from a virtual environment "
                        "(python -m venv .venv, activate it, then python web.py).")
            raise SetupError("pip could not install amulet-core (it may need Python 3.9 to 3.11)." + hint)
        importlib.invalidate_caches()
        if not amulet_ok():
            raise SetupError("amulet-core was installed but can't be found yet. Restart web.py.")
        return "done", "Installed"

    def java():
        need = ctx["info"].get("javaVersion", {}).get("majorVersion")
        have = installed_java_major()
        if have is None:
            raise SetupError(f"Java not found. Install Java {need or ''}+ from https://adoptium.net "
                             "(needed for chunk scanning; the biome map works without it).")
        if need and have < need:
            raise SetupError(f"Java {have} found, but Minecraft {version} needs Java {need}+. "
                             "Chunk scanning won't work until you upgrade.")
        return "done", f"Java {have} found"

    def server():
        srv = ctx["info"]["downloads"]["server"]
        jar = d / "jars" / f"{version}.jar"
        if jar.exists() and hashlib.sha1(jar.read_bytes()).hexdigest() == srv["sha1"]:
            detail = "Already downloaded"
            status = "skipped"
        else:
            download(srv["url"], jar, srv["sha1"], "server", "Server jar")
            status, detail = "done", "Downloaded"
        cfg = read_cfg()
        if version not in cfg["versions"]:
            cfg["versions"].append(version)
        cfg["versions"].sort(key=version_key)
        cfg["default_version"] = version
        write_cfg(cfg)
        return status, detail

    def textures():
        out_dir = d / "textures" / version
        if out_dir.is_dir() and any(out_dir.glob("*.png")):
            return "skipped", "Already extracted"
        client = ctx["info"].get("downloads", {}).get("client")
        if not client:
            raise SetupError(f"No client jar is published for {version}; blocks will be drawn as plain colours.")
        jar = d / "jars" / f"client_{version}.jar"
        try:
            download(client["url"], jar, client["sha1"], "textures", "Client jar")
            _step("textures", progress=None, detail="Extracting textures...")
            out_dir.mkdir(parents=True, exist_ok=True)
            count = 0
            with zipfile.ZipFile(jar) as z:
                for info in z.infolist():
                    n = info.filename
                    if n.startswith(TEXTURE_PREFIX) and n.endswith(".png") and "/" not in n[len(TEXTURE_PREFIX):]:
                        (out_dir / n[len(TEXTURE_PREFIX):]).write_bytes(z.read(info))
                        count += 1
        finally:
            if jar.exists():
                jar.unlink()
        return "done", f"{count} textures"

    def biomes():
        try:
            lib, _ = _load(d)
            _resolve_mc(lib, version)
            return "skipped", "Already built; supports this version"
        except BiomeError as e:
            joblog(f"biomes: building ({e})")
        build_cubiomes(d, "biomes")
        lib, _ = _load(d)
        _resolve_mc(lib, version)
        return "done", "Built"

    try:
        _run_step("meta", meta, fatal=True)
        _run_step("python", python_libs)
        _run_step("java", java)
        _run_step("server", server, fatal=True)
        _run_step("textures", textures)
        _run_step("biomes", biomes)
        with JOB_LOCK:
            JOB["state"] = "done"
    except SetupError as e:
        with JOB_LOCK:
            JOB.update(state="error", error=str(e))
    except Exception as e:     # never leave the job stuck in "running"
        with JOB_LOCK:
            JOB.update(state="error", error=f"{type(e).__name__}: {e}")


# --------------------------------------------------------------------------
# Scanning
# --------------------------------------------------------------------------
def collect_chunk_blocks(world_path, version, dim_id, cx, cz, fallback_y):
    """Return {block name: [(x, y, z), ...]} for every block in the chunk."""
    import amulet
    import numpy as np

    level = amulet.load_level(str(world_path))
    x0, z0 = cx * 16, cz * 16
    ver = tuple(int(p) for p in version.split("."))

    def name_at(x, y, z):
        try:
            block, _ = level.get_version_block(x, y, z, dim_id, ("java", ver))
        except Exception:
            block = level.get_block(x, y, z, dim_id)
        return re.split(r"[\[{]", block_text(block))[0]

    try:
        try:
            found = {}
            names = {}
            chunk = level.get_chunk(cx, cz, dim_id)
            for cy in sorted(chunk.blocks.sub_chunks):
                arr = chunk.blocks.get_sub_chunk(cy)
                for bid in np.unique(arr).tolist():
                    pos = np.argwhere(arr == bid)
                    if bid not in names:
                        i, j, k = (int(v) for v in pos[0])
                        names[bid] = name_at(x0 + i, cy * 16 + j, z0 + k)
                    out = found.setdefault(names[bid], [])
                    for i, j, k in pos.tolist():
                        out.append((x0 + i, cy * 16 + j, z0 + k))
            return found
        except (AttributeError, KeyError, TypeError) as e:
            print(f"Fast path unavailable ({e!r}); using slow per-block scan...", file=sys.stderr)

        found = {}
        lo, hi = fallback_y
        for y in range(lo, hi + 1):
            for x in range(x0, x0 + 16):
                for z in range(z0, z0 + 16):
                    found.setdefault(name_at(x, y, z), []).append((x, y, z))
        return found
    finally:
        level.close()


def run_scan(x, z, seed, version, dimension):
    d = Path(ARGS.dir)
    cfg = read_cfg()
    version = version or cfg.get("default_version")
    jar = d / "jars" / f"{version}.jar"
    if not version or not jar.exists():
        raise ValueError(f"Minecraft {version or ''} isn't installed yet. "
                         "Use the Version menu > Install version...")
    if not amulet_ok():
        raise ValueError("The Python library amulet-core is missing. "
                         "Use the Version menu > Install version... > Install to set it up.")
    if dimension not in DIMENSIONS:
        raise ValueError("Unknown dimension.")
    seed = str(seed).strip()
    if not seed:
        raise ValueError("Seed is required.")

    dim_id = DIMENSIONS[dimension]
    safe_seed = re.sub(r"[^A-Za-z0-9_-]", "_", seed)
    run_dir = d / "worlds" / f"{version}_{safe_seed}"
    run_dir.mkdir(parents=True, exist_ok=True)
    (run_dir / "eula.txt").write_text("eula=true\n")
    (run_dir / "server.properties").write_text(
        f"level-seed={seed}\n"
        "level-name=world\n"
        "online-mode=false\n"
        "server-port=25599\n"
        "spawn-protection=0\n"
        "view-distance=2\n"
        "simulation-distance=2\n"
    )
    world = run_dir / "world"

    cx, cz = x >> 4, z >> 4
    marker = run_dir / "generated.json"
    done = set(json.loads(marker.read_text())) if marker.exists() else set()
    key = f"{dim_id}:{cx}:{cz}"
    if key not in done:
        generate_chunk(run_dir, jar, cfg.get("memory", "2G"), dim_id, x, z, False, version)
        done.add(key)
        marker.write_text(json.dumps(sorted(done)))

    blocks = collect_chunk_blocks(world, version, dim_id, cx, cz, DEFAULT_Y[dimension])
    for coords in blocks.values():
        coords.sort(key=lambda c: (c[1], c[0], c[2]))   # by height, then x, then z

    scan_id = uuid.uuid4().hex[:12]
    result = {
        "id": scan_id,
        "cx": cx, "cz": cz,
        "x0": cx * 16, "z0": cz * 16,
        "version": version, "seed": seed, "dimension": dimension,
        "blocks": blocks,
    }
    CACHE[scan_id] = result
    while len(CACHE) > CACHE_LIMIT:
        CACHE.pop(next(iter(CACHE)))
    return result


def summary(result):
    counts = Counter({n: len(c) for n, c in result["blocks"].items()})
    ys = [c[1] for coords in result["blocks"].values() for c in (coords[0], coords[-1])]
    return {
        "id": result["id"],
        "cx": result["cx"], "cz": result["cz"],
        "x0": result["x0"], "z0": result["z0"],
        "version": result["version"], "seed": result["seed"],
        "dimension": result["dimension"],
        "ymin": min(ys), "ymax": max(ys),
        "total": sum(counts.values()),
        "blocks": [{"name": short_name(n), "count": c}
                   for n, c in sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))],
    }


def get_result(scan_id):
    result = CACHE.get(scan_id)
    if result is None:
        raise KeyError("Scan expired. Run the scan again.")
    return result


def find_block(scan_id, short):
    result = get_result(scan_id)
    for name, coords in result["blocks"].items():
        if short_name(name) == short:
            return result, name, coords
    raise KeyError(f"Block {short!r} not found in this scan.")


def ensure_by_y(result):
    """Index every block by height: by_y[y][z_row][x_col] = block name. Built once per scan."""
    if "by_y" in result:
        return
    by_y = {}
    x0, z0 = result["x0"], result["z0"]
    for name, coords in result["blocks"].items():
        short = short_name(name)
        for x, yy, z in coords:
            grid = by_y.get(yy)
            if grid is None:
                grid = by_y[yy] = [[None] * 16 for _ in range(16)]
            grid[z - z0][x - x0] = short
    result["by_y"] = by_y


def heightmap(scan_id):
    """Per-column surface heights: highest non-air block ("top") and highest non-liquid block ("ground")."""
    result = get_result(scan_id)
    ensure_by_y(result)
    by_y = result["by_y"]
    ys = sorted(by_y, reverse=True)
    air = {"air", "cave_air", "void_air"}
    liquid = {"water", "lava", "bubble_column"}
    out = {k: [[None] * 16 for _ in range(16)] for k in ("top_y", "top_b", "ground_y", "ground_b")}
    for z in range(16):
        for x in range(16):
            for y in ys:
                name = by_y[y][z][x] or "air"
                if name in air:
                    continue
                if out["top_y"][z][x] is None:
                    out["top_y"][z][x], out["top_b"][z][x] = y, name
                if name not in liquid:
                    out["ground_y"][z][x], out["ground_b"][z][x] = y, name
                    break
    return out


def layer_at(scan_id, y):
    """16x16 cross section at height y: palette + grid[z_row][x_col] of palette indexes."""
    result = get_result(scan_id)
    ensure_by_y(result)
    grid = result["by_y"].get(y)
    if grid is None:
        raise KeyError(f"No blocks at y={y} in this scan.")
    palette, index = [], {}
    out = []
    for row in grid:
        r = []
        for name in row:
            name = name or "air"
            if name not in index:
                index[name] = len(palette)
                palette.append(name)
            r.append(index[name])
        out.append(r)
    return {"y": y, "palette": palette, "grid": out}


def voxels(scan_id):
    """Dense voxel dump for the interactive view: uint16 palette index per block (0 = air), base64."""
    result = get_result(scan_id)
    air = {"air", "cave_air", "void_air"}
    ys = [c[1] for coords in result["blocks"].values() for c in (coords[0], coords[-1])]
    ymin, ymax = min(ys), max(ys)
    x0, z0 = result["x0"], result["z0"]
    buf = bytearray(2 * 256 * (ymax - ymin + 1))
    palette = ["air"]
    for name, coords in result["blocks"].items():
        sn = short_name(name)
        if sn in air or len(palette) > 65535:
            continue
        idx = len(palette)
        palette.append(sn)
        lo, hi = idx & 255, idx >> 8
        for x, y, z in coords:
            i = 2 * ((y - ymin) * 256 + (z - z0) * 16 + (x - x0))
            buf[i] = lo
            buf[i + 1] = hi
    return {"ymin": ymin, "ymax": ymax, "palette": palette, "data": base64.b64encode(bytes(buf)).decode()}


def texture_info(version):
    """Pick the texture folder for this version (or the newest one available)."""
    base = Path(ARGS.dir) / "textures"
    if not base.exists():
        return None, []
    dirs = [base / version] + sorted((p for p in base.iterdir() if p.is_dir() and p.name != version),
                                     key=lambda p: p.name, reverse=True)
    for p in dirs:
        if p.is_dir():
            files = [f.stem for f in p.glob("*.png")]
            if files:
                return p.name, files
    return None, []


# --------------------------------------------------------------------------
# HTTP
# --------------------------------------------------------------------------
class Handler(BaseHTTPRequestHandler):
    def log_message(self, fmt, *a):
        pass

    def send_bytes(self, code, body, ctype, extra=None):
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        for k, v in (extra or {}).items():
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(body)

    def send_json(self, obj, code=200):
        self.send_bytes(code, json.dumps(obj).encode(), "application/json")

    def do_GET(self):
        url = urlparse(self.path)
        q = {k: v[0] for k, v in parse_qs(url.query).items()}
        try:
            if url.path == "/":
                self.send_bytes(200, PAGE.encode(), "text/html; charset=utf-8")
            elif url.path == "/api/config":
                inst = installed_versions()
                default = read_cfg().get("default_version")
                self.send_json({
                    "versions": inst,
                    "default_version": default if default in inst else (inst[-1] if inst else None),
                    "dimensions": list(DIMENSIONS),
                    "setup_ok": bool(inst),
                    "biomes_ready": biomes_available(),
                    "java_ok": installed_java_major() is not None,
                    "amulet_ok": amulet_ok(),
                    "job": job_snapshot(),
                })
            elif url.path == "/api/versions":
                try:
                    self.send_json({"versions": list_versions(), "installed": installed_versions()})
                except OSError as e:
                    self.send_json({"error": f"Couldn't reach Mojang's servers. Check your internet connection ({e})."}, 502)
            elif url.path == "/api/job":
                self.send_json(job_snapshot())
            elif url.path == "/api/biomes":
                self.send_json(generate_biomes(
                    ARGS.dir, q.get("seed", ""), q.get("version", ""), q.get("dimension", "overworld"),
                    int(q.get("bx0", "0")), int(q.get("bz0", "0")), int(q.get("step", "4")),
                    int(q.get("w", "64")), int(q.get("h", "48")), int(q.get("y", "63"))))
            elif url.path == "/api/structures":
                self.send_json(generate_structures(
                    ARGS.dir, q.get("seed", ""), q.get("version", ""), q.get("dimension", "overworld"),
                    int(q.get("x0", "0")), int(q.get("z0", "0")), int(q.get("x1", "0")), int(q.get("z1", "0")),
                    {t for t in q.get("types", "").split(",") if t}))
            elif url.path == "/api/slime":
                self.send_json(generate_slime(
                    ARGS.dir, q.get("seed", ""), int(q.get("cx0", "0")), int(q.get("cz0", "0")),
                    int(q.get("w", "1")), int(q.get("h", "1"))))
            elif url.path == "/api/heightmap":
                self.send_json(heightmap(q.get("id", "")))
            elif url.path == "/api/coords":
                _, _, coords = find_block(q.get("id", ""), q.get("block", ""))
                self.send_json({"count": len(coords), "coords": coords})
            elif url.path == "/api/voxels":
                self.send_json(voxels(q.get("id", "")))
            elif url.path == "/api/layer":
                self.send_json(layer_at(q.get("id", ""), int(q.get("y", "54"))))
            elif url.path == "/api/textures":
                ver, files = texture_info(q.get("version", ""))
                self.send_json({"version": ver, "files": files})
            elif url.path.startswith("/tex/"):
                parts = url.path[5:].split("/")
                if (len(parts) != 2 or not re.fullmatch(r"[\w.\-]+", parts[0])
                        or not re.fullmatch(r"[\w\-]+\.png", parts[1])):
                    return self.send_bytes(404, b"Not found", "text/plain")
                p = Path(ARGS.dir) / "textures" / parts[0] / parts[1]
                if not p.is_file():
                    return self.send_bytes(404, b"Not found", "text/plain")
                self.send_bytes(200, p.read_bytes(), "image/png", {"Cache-Control": "max-age=3600"})
            elif url.path == "/api/csv":
                result, name, coords = find_block(q.get("id", ""), q.get("block", ""))
                buf = io.StringIO()
                w = csv.writer(buf)
                w.writerow(["x", "y", "z", "block"])
                for x, y, z in coords:
                    w.writerow([x, y, z, short_name(name)])
                fname = f"{short_name(name)}_{result['cx']}_{result['cz']}.csv"
                self.send_bytes(200, buf.getvalue().encode(), "text/csv",
                                {"Content-Disposition": f'attachment; filename="{fname}"'})
            else:
                self.send_bytes(404, b"Not found", "text/plain")
        except BiomeError as e:
            self.send_json({"error": str(e)}, 400)
        except KeyError as e:
            self.send_json({"error": str(e.args[0])}, 404)
        except ValueError:
            self.send_json({"error": "Bad request."}, 400)
        except Exception as e:
            self.send_json({"error": str(e)}, 500)

    def do_POST(self):
        path = urlparse(self.path).path
        if path == "/api/install":
            try:
                length = int(self.headers.get("Content-Length", 0))
                body = json.loads(self.rfile.read(length) or b"{}")
                start_install(str(body.get("version", "")).strip())
                return self.send_json(job_snapshot())
            except (ValueError, json.JSONDecodeError) as e:
                return self.send_json({"error": str(e) or "Bad request."}, 400)
        if path != "/api/scan":
            return self.send_bytes(404, b"Not found", "text/plain")
        try:
            length = int(self.headers.get("Content-Length", 0))
            body = json.loads(self.rfile.read(length) or b"{}")
            x, z = int(body["x"]), int(body["z"])
        except (ValueError, KeyError, json.JSONDecodeError):
            return self.send_json({"error": "X and Z must be whole numbers."}, 400)
        try:
            with SCAN_LOCK:
                result = run_scan(x, z, body.get("seed", ""), body.get("version"),
                                  body.get("dimension", "overworld"))
            self.send_json(summary(result))
        except ValueError as e:
            self.send_json({"error": str(e)}, 400)
        except Exception as e:
            self.send_json({"error": f"{type(e).__name__}: {e}"}, 500)


# --------------------------------------------------------------------------
# Page
# --------------------------------------------------------------------------
PAGE = r"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Chunk Scanner</title>
<style>
  :root {
    --bg: #1a1a1a;
    --panel: #232323;
    --panel-2: #2d2d2d;
    --line: #3c3c3c;
    --text: #d4d4d4;
    --muted: #8c8c8c;
    --accent: #3ecf6e;
    --accent-ink: #04210f;
    --warn: #e3b341;
    --bad: #ff8a7a;
    --mono: ui-monospace, "SF Mono", Menlo, Consolas, "Liberation Mono", monospace;
    --sans: "Segoe UI", system-ui, -apple-system, "Helvetica Neue", Arial, sans-serif;
  }
  * { box-sizing: border-box; }
  html, body { height: 100%; }
  body {
    margin: 0; background: var(--bg); color: var(--text);
    font: 15px/1.45 var(--sans);
    display: flex; flex-direction: column;
  }
  header {
    padding: 14px 20px; border-bottom: 1px solid var(--line);
    display: flex; flex-wrap: wrap; gap: 14px 18px; align-items: flex-end;
    background: var(--panel);
  }
  .push-right { margin-left: auto; }
  label { display: flex; flex-direction: column; gap: 4px; font-size: 13px; color: var(--muted); }
  input, select {
    background: var(--bg); color: var(--text); border: 1px solid var(--line);
    border-radius: 6px; padding: 8px 10px; font: inherit; min-width: 0;
  }
  input[type=number] { width: 110px; font-family: var(--mono); }
  input#seed { width: 160px; font-family: var(--mono); }
  input:focus-visible, select:focus-visible, button:focus-visible, .row:focus-visible, canvas:focus-visible {
    outline: 2px solid var(--accent); outline-offset: 1px;
  }
  button {
    font: inherit; cursor: pointer; border-radius: 6px; padding: 8px 14px;
    border: 1px solid var(--line); background: var(--panel-2); color: var(--text);
  }
  button:hover { border-color: var(--accent); }
  button.primary { background: var(--accent); color: var(--accent-ink); border-color: var(--accent); font-weight: 700; }
  button.primary:hover { filter: brightness(1.08); }
  button:disabled { opacity: .5; cursor: default; }

  #status { display: none; }
  #status.unused { padding: 8px 20px; font-size: 14px; color: var(--muted); border-bottom: 1px solid var(--line); min-height: 38px; }
  #status.err { color: var(--bad); }
  #status.busy::before {
    content: ""; display: inline-block; width: 10px; height: 10px; margin-right: 8px;
    border: 2px solid var(--accent); border-top-color: transparent; border-radius: 50%;
    animation: spin .8s linear infinite; vertical-align: -1px;
  }
  @keyframes spin { to { transform: rotate(360deg); } }
  @media (prefers-reduced-motion: reduce) { #status.busy::before { animation: none; } }

  main { flex: 1; min-height: 0; display: grid; grid-template-columns: minmax(280px, 380px) 1fr; }
  @media (max-width: 800px) { main { grid-template-columns: 1fr; } .detail { border-top: 1px solid var(--line); } }

  .list { display: flex; flex-direction: column; min-height: 0; border-right: 1px solid var(--line); }
  .list-tools { display: flex; gap: 8px; padding: 12px; border-bottom: 1px solid var(--line); }
  .list-tools input { flex: 1; }
  #rows, #blegend { overflow-y: auto; flex: 1; min-height: 200px; }
  .row {
    display: grid; grid-template-columns: 18px 1fr auto; gap: 10px; align-items: center;
    padding: 8px 14px; cursor: pointer; border-bottom: 1px solid rgba(255,255,255,.04);
    position: relative;
  }
  .row:hover { background: var(--panel); }
  .row.sel { background: var(--panel-2); box-shadow: inset 3px 0 var(--accent); }
  .sw {
    width: 18px; height: 18px; border-radius: 2px; border: 1px solid rgba(255,255,255,.25);
    background-size: 100% 100%; image-rendering: pixelated;
  }
  .name { overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
  .cnt { font-family: var(--mono); font-size: 13px; color: var(--muted); }
  .bar { position: absolute; left: 0; bottom: 0; height: 2px; background: var(--accent); opacity: .55; }
  .empty { padding: 28px 0; color: var(--muted); }
  .list .empty { padding: 28px 20px; }

  .detail { padding: 0 22px 18px; overflow-y: auto; min-height: 0; }
  .tabs { display: flex; gap: 6px; padding: 14px 0; position: sticky; top: 0; background: var(--bg); z-index: 1; }
  .tabs button.on { background: var(--accent); color: var(--accent-ink); border-color: var(--accent); font-weight: 600; }
  .detail h2 { margin: 0; font-size: 22px; font-family: var(--mono); font-weight: 600; word-break: break-all; display: flex; align-items: center; gap: 10px; }
  .detail h2 .sw { width: 28px; height: 28px; flex: none; }
  .meta { color: var(--muted); margin: 4px 0 14px; }
  .actions { display: flex; gap: 8px; flex-wrap: wrap; margin-bottom: 18px; }
  .cap { font-family: var(--mono); font-size: 12px; color: var(--muted); min-height: 18px; margin-top: 6px; }
  table { border-collapse: collapse; width: 100%; max-width: 520px; font-family: var(--mono); font-size: 13px; }
  th, td { text-align: right; padding: 4px 12px; border-bottom: 1px solid rgba(255,255,255,.05); }
  th { color: var(--muted); font-weight: 600; position: sticky; top: 52px; background: var(--bg); }
  tbody tr { cursor: pointer; }
  tbody tr:hover { background: var(--panel); }
  .more { margin-top: 12px; }

  .ctl { display: flex; align-items: center; gap: 8px; flex-wrap: wrap; margin-bottom: 8px; }
  .ctl .ylab { color: var(--muted); }
  .ctl input[type=number] { width: 90px; text-align: center; }
  .ctl button { min-width: 40px; font-weight: 700; }
  .ctl input[type=range] { flex: 1; min-width: 160px; max-width: 320px; padding: 0; accent-color: var(--accent); }
  #layer, #hmap {
    display: block; width: 100%; max-width: 512px; aspect-ratio: 1; image-rendering: pixelated;
    background: var(--panel); border: 1px solid var(--line); border-radius: 4px; cursor: crosshair;
  }
  .legend { margin-top: 14px; max-width: 512px; display: grid; grid-template-columns: repeat(auto-fill, minmax(190px, 1fr)); gap: 4px 12px; }
  .lg { display: flex; align-items: center; gap: 8px; padding: 3px 6px; border-radius: 4px; cursor: pointer; font-size: 13px; }
  .lg:hover { background: var(--panel); }
  .lg.sel { background: var(--panel-2); box-shadow: inset 2px 0 var(--accent); }
  .lg .sw { width: 16px; height: 16px; flex: none; }
  .lg .n { flex: 1; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
  .lg .c { font-family: var(--mono); color: var(--muted); }

  .coordgrid { display: grid; grid-template-columns: minmax(280px, 380px) minmax(240px, 1fr); gap: 22px; align-items: stretch; }
  .charts { display: flex; flex-direction: column; gap: 18px; min-width: 0; }
  .chart canvas { width: 100%; height: auto; }
  .coordbox { position: relative; min-height: 320px; min-width: 0; background: var(--panel); border: 1px solid var(--line); border-radius: 6px; }
  .coordscroll { position: absolute; inset: 0; overflow-y: auto; padding: 0 0 10px; }
  .coordscroll table { max-width: none; }
  .coordscroll th { top: 0; background: var(--panel); }
  .coordscroll .more { margin: 12px 12px 0; }
  .coordscroll .cap { padding: 0 12px; }
  @media (max-width: 900px) { .coordgrid { grid-template-columns: 1fr; } .coordbox { height: 420px; } }
  .chart h3 { margin: 0 0 6px; font-size: 13px; font-weight: 600; color: var(--muted); }
  .chart canvas { display: block; background: var(--panel); border: 1px solid var(--line); border-radius: 6px; }
  .scale { max-width: 512px; margin-top: 10px; }
  .scale .gr { height: 10px; border-radius: 3px; border: 1px solid var(--line); }
  .scale .lb { display: flex; justify-content: space-between; font-family: var(--mono); font-size: 12px; color: var(--muted); margin-top: 2px; }
  .hide { display: none !important; }
  .maintabs {
    display: flex; gap: 2px; padding: 0 20px; background: var(--panel);
    border-bottom: 1px solid var(--line);
  }
  .maintabs button {
    background: transparent; border: 0; border-bottom: 3px solid transparent; border-radius: 0;
    padding: 12px 20px 9px; margin-bottom: -1px; font-size: 16px; font-weight: 600; color: var(--muted);
  }
  .maintabs button:hover { color: var(--text); background: rgba(255,255,255,.04); }
  .maintabs button.on { color: var(--accent); border-bottom-color: var(--accent); }
  .maintabs button:focus-visible { outline-offset: -2px; }

  /* number inputs: themed stepper instead of the native grey arrows */
  input[type=number] { -moz-appearance: textfield; appearance: textfield; }
  input[type=number]::-webkit-inner-spin-button, input[type=number]::-webkit-outer-spin-button { -webkit-appearance: none; margin: 0; }
  .num { position: relative; display: inline-flex; }
  .num input { padding-right: 28px; }
  .num .stp { position: absolute; right: 1px; top: 1px; bottom: 1px; width: 22px; display: flex; flex-direction: column; border-left: 1px solid var(--line); }
  .num .stp button {
    flex: 1; min-width: 0; padding: 0; border: 0; border-radius: 0; background: var(--panel-2); color: var(--muted);
    display: flex; align-items: center; justify-content: center;
  }
  .num .stp button:first-child { border-top-right-radius: 5px; border-bottom: 1px solid var(--line); }
  .num .stp button:last-child { border-bottom-right-radius: 5px; }
  .num .stp button:hover { background: var(--accent); color: var(--accent-ink); }
  .num .stp svg { width: 10px; height: 10px; fill: none; stroke: currentColor; stroke-width: 2.2; stroke-linecap: round; stroke-linejoin: round; }

  #exploreview { grid-template-columns: 1fr; }
  .xwrap { position: relative; min-height: 0; overflow: hidden; background: #121212; }
  #xcv { position: absolute; inset: 0; width: 100%; height: 100%; display: block; outline: none; }
  .xmsg { position: absolute; inset: 0; z-index: 2; display: flex; align-items: center; justify-content: center; padding: 20px; background: rgba(18, 18, 18, .72); }
  .xcard { max-width: 460px; background: var(--panel); border: 1px solid var(--line); border-radius: 10px; padding: 20px 24px; text-align: center; }
  .xcard h3 { margin: 0 0 8px; font-size: 20px; }
  .xcard p { margin: 0 0 14px; color: var(--muted); }
  .xcard kbd { font-family: var(--mono); font-size: 12px; background: var(--bg); border: 1px solid var(--line); border-radius: 4px; padding: 1px 6px; color: var(--text); }
  .xcard .loading { padding: 8px 4px; justify-content: center; }
  .xbtns { display: flex; gap: 8px; justify-content: center; flex-wrap: wrap; }
  .xcross { position: absolute; left: 50%; top: 50%; width: 18px; height: 18px; margin: -9px 0 0 -9px; pointer-events: none; z-index: 1; }
  .xcross::before, .xcross::after { content: ""; position: absolute; background: rgba(255,255,255,.85); mix-blend-mode: difference; }
  .xcross::before { left: 8px; top: 0; width: 2px; height: 18px; }
  .xcross::after { top: 8px; left: 0; height: 2px; width: 18px; }
  .xhud { position: absolute; left: 12px; bottom: 12px; z-index: 1; padding: 6px 10px; border-radius: 6px; background: rgba(24, 24, 24, .8); border: 1px solid var(--line); font-family: var(--mono); font-size: 12px; color: var(--muted); pointer-events: none; }
  .spinner {
    width: 22px; height: 22px; flex: none; border: 3px solid var(--line); border-top-color: var(--accent);
    border-radius: 50%; animation: spin .8s linear infinite;
  }
  .loading { display: flex; align-items: center; gap: 12px; padding: 28px 20px; color: var(--muted); }
  .maploading {
    position: absolute; inset: 0; z-index: 3; display: flex; align-items: center; justify-content: center; gap: 12px;
    background: rgba(24, 24, 24, .85); color: var(--muted);
  }
  @media (prefers-reduced-motion: reduce) { .spinner { animation: none; } }
  #mapview { grid-template-columns: minmax(240px, 320px) 1fr minmax(200px, 250px); }
  @media (max-width: 800px) { #mapview { grid-template-columns: 1fr; } }
  .mappane { padding: 10px 14px 8px; min-height: 0; min-width: 0; overflow: hidden; display: flex; flex-direction: column; }
  .mappane .ctl { align-items: flex-end; margin-bottom: 10px; gap: 14px; flex: none; }
  .mappane .cap { flex: none; }
  .slist { border-right: 0; border-left: 1px solid var(--line); }
  #sbody { overflow-y: auto; flex: 1; min-height: 200px; }
  .ico { width: 22px; height: 22px; flex: none; }
  .row.off .name { color: var(--muted); }
  .snote { padding: 10px 16px; font-family: var(--mono); font-size: 12px; color: var(--muted); }
  .layers { display: flex; flex-wrap: wrap; gap: 6px; margin: -2px 0 8px; flex: none; min-height: 0; }
  .layers:empty { display: none; }
  .layers label {
    display: inline-flex; align-items: center; gap: 6px; padding: 2px 9px; font-size: 12px; cursor: pointer;
    font-family: var(--mono); border: 1px solid var(--line); border-radius: 12px; color: var(--muted); user-select: none;
  }
  .layers label.on { color: #fff; border-color: rgba(255,255,255,.35); }
  .layers input { display: none; }
  .layers i { width: 9px; height: 9px; border-radius: 50%; border: 1px solid rgba(0,0,0,.7); display: inline-block; }
  .layers .note { font-family: var(--mono); font-size: 12px; color: var(--muted); align-self: center; }
  .mapwrap {
    position: relative; flex: 1; min-height: 240px; width: 100%; overflow: hidden;
    border: 1px solid var(--line); border-radius: 4px; background: var(--panel);
  }
  .mapwrap canvas { position: absolute; left: 0; top: 0; width: 100%; height: 100%; image-rendering: pixelated; }
  #bover { cursor: grab; }
  .tip {
    position: absolute; display: none; pointer-events: none; z-index: 2; min-width: 190px;
    background: rgba(24, 24, 24, .96); border: 1px solid var(--line); border-radius: 6px;
    padding: 8px 10px; font-size: 13px; line-height: 1.5;
  }
  .tip b { font-family: var(--mono); }
  .tip .xz { font-family: var(--mono); font-size: 12px; color: var(--muted); }
  .tip .bl { display: flex; align-items: center; gap: 6px; }
  .tip .bl .sw { width: 11px; height: 11px; flex: none; }
  .tip .bl .pc { margin-left: auto; padding-left: 12px; font-family: var(--mono); color: var(--muted); }
  .tip .go { margin-top: 4px; color: var(--accent); }
  .toast {
    position: fixed; bottom: 18px; right: 18px; background: var(--accent); color: var(--accent-ink);
    padding: 8px 14px; border-radius: 6px; font-weight: 600; opacity: 0; pointer-events: none;
    transition: opacity .15s;
  }
  .toast.show { opacity: 1; }
  .toast.err { background: var(--bad); color: #2b0600; max-width: min(520px, calc(100vw - 36px)); }

  .muted { color: var(--muted); }
  .setup {
    position: fixed; inset: 0; z-index: 10; display: flex; align-items: center; justify-content: center;
    padding: 18px; background: rgba(10, 10, 10, .92);
  }
  .setup-card {
    width: min(560px, 100%); max-height: 100%; overflow-y: auto; background: var(--panel);
    border: 1px solid var(--line); border-radius: 10px; padding: 22px 24px;
  }
  .setup-card h2 { margin: 0 0 6px; font-size: 22px; }
  .setup-card p { margin: 0 0 14px; }
  .setup-pick { display: flex; flex-wrap: wrap; gap: 10px; align-items: flex-end; margin-bottom: 6px; }
  .setup-pick label { flex: 1; min-width: 160px; }
  .setup-pick select { width: 100%; }
  .steps { list-style: none; margin: 14px 0 12px; padding: 0; display: flex; flex-direction: column; gap: 8px; }
  .steps li { display: grid; grid-template-columns: 22px 1fr; gap: 10px; align-items: start; }
  .steps .ic { width: 20px; height: 20px; text-align: center; font-weight: 700; line-height: 20px; color: var(--muted); }
  .steps .active .ic {
    border: 2px solid var(--accent); border-top-color: transparent; border-radius: 50%;
    animation: spin .8s linear infinite; width: 16px; height: 16px; margin: 2px;
  }
  .steps .done .ic, .steps .skipped .ic { color: #8fd18f; }
  .steps .warn .ic { color: var(--warn); }
  .steps .error .ic { color: var(--bad); }
  .steps .pending { opacity: .55; }
  .steps .lb { display: block; }
  .steps .dt { display: block; font-size: 13px; color: var(--muted); white-space: pre-wrap; word-break: break-word; }
  .steps .warn .dt { color: var(--warn); }
  .steps .error .dt { color: var(--bad); }
  .pbar { height: 8px; background: var(--bg); border: 1px solid var(--line); border-radius: 4px; overflow: hidden; }
  .pbar > div { height: 100%; width: 0; background: var(--accent); transition: width .25s; }
  #setup-msg { margin: 12px 0 0; }
  #setup-msg.err { color: var(--bad); }
  .setup-actions { display: flex; gap: 10px; margin-top: 14px; }
  @media (prefers-reduced-motion: reduce) { .steps .active .ic { animation: none; } }
</style>
</head>
<body>
<header>
  <label>X <input id="x" type="number" value="0"></label>
  <label>Z <input id="z" type="number" value="0"></label>
  <label>Seed <input id="seed" type="text" placeholder="12345"></label>
  <label>Dimension <select id="dimension"></select></label>
  <button id="locate" title="Center the biome map on X and Z">Show on map</button>
  <label class="push-right">Version <select id="version"></select></label>
</header>
<nav class="maintabs" role="tablist">
  <button id="mode-map" class="on" role="tab" aria-selected="true">Biome map</button>
  <button id="mode-scan" role="tab" aria-selected="false">Chunk scan</button>
  <button id="mode-explore" role="tab" aria-selected="false">Interactive view</button>
</nav>
<div id="status">Enter a seed and a coordinate, then press Show on map. Click any chunk on the map to scan it.</div>
<main id="scanview" class="hide">
  <section class="list">
    <div class="list-tools">
      <input id="filter" type="search" placeholder="Filter blocks" aria-label="Filter blocks">
      <button id="sort" title="Change sort order">Most common</button>
    </div>
    <div id="rows"><div class="empty">No scan yet.</div></div>
  </section>
  <section class="detail">
    <div class="tabs">
      <button id="tab-coords" class="on" disabled>Block coordinates</button>
      <button id="tab-layer" disabled>Layer view</button>
      <button id="tab-height" disabled>Heightmap</button>
    </div>
    <div id="pane"><div class="empty">Click a chunk on the Biome map to scan it, or type X and Z and press Enter.</div></div>
  </section>
</main>
<main id="exploreview" class="hide">
  <div class="xwrap" id="xwrap">
    <canvas id="xcv"></canvas>
    <div class="xcross hide" id="xcross"></div>
    <div class="xhud hide" id="xhud"></div>
    <div class="xmsg" id="xmsg"></div>
  </div>
</main>
<main id="mapview">
  <section class="list">
    <div class="list-tools">
      <input id="bfilter" type="search" placeholder="Filter biomes" aria-label="Filter biomes">
    </div>
    <div id="blegend"><div class="empty">Press Show on map to draw the biomes around X and Z. Click a biome here to highlight it.</div></div>
  </section>
  <section class="mappane">
    <div class="ctl">
      <label>Biome height (Y) <input id="my" type="number" value="63"></label>
      <label>Zoom
        <select id="mzoom"></select>
      </label>
    </div>
    <div class="mapwrap" id="mapwrap">
      <canvas id="bmap" width="840" height="640"></canvas>
      <canvas id="bover" width="840" height="640"></canvas>
      <div class="maploading hide" id="maploading"><span class="spinner"></span><span>Computing biomes...</span></div>
      <div class="tip" id="tip"></div>
    </div>
    <div class="cap" id="mcap">&nbsp;</div>
  </section>
  <section class="list slist">
    <div class="list-tools"><input id="sfilter" type="search" placeholder="Filter structures" aria-label="Filter structures"></div>
    <div id="sbody"></div>
  </section>
</main>
<div class="setup hide" id="setup" role="dialog" aria-modal="true" aria-labelledby="setup-title">
  <div class="setup-card">
    <h2 id="setup-title">Setting up Chunk Scanner</h2>
    <p class="muted" id="setup-intro"></p>
    <div class="setup-pick" id="setup-pick">
      <label>Minecraft version <select id="setup-version"></select></label>
      <button id="setup-go" class="primary">Install</button>
      <button id="setup-cancel">Cancel</button>
    </div>
    <ol class="steps hide" id="setup-steps"></ol>
    <div class="pbar hide" id="setup-pbar"><div id="setup-bar"></div></div>
    <div id="setup-msg"></div>
    <div class="setup-actions">
      <button id="setup-done" class="primary hide">Continue</button>
      <button id="setup-retry" class="hide">Back</button>
    </div>
  </div>
</div>
<div class="toast" id="toast"></div>

<script>
const $ = id => document.getElementById(id);
let scanData = null, sortMode = "count", selected = null, coords = [], shown = 0;
let view = "coords", layerY = 54, curLayer = null;
const PAGE = 1000, CELL = 32;
const LAYERS = new Map();

/* ---------- textures ---------- */
const TEX = {ver: null, files: new Set()};
const IMG = new Map(), TILE = new Map(), FILE = new Map();
const AIR = new Set(["air", "cave_air", "void_air"]);
const ALIAS = {
  water: "water_still", bubble_column: "water_still", lava: "lava_still",
  snow_block: "snow", grass: "short_grass", short_grass: "short_grass",
  dirt_path: "dirt_path_top", farmland: "farmland", "moving_piston": "piston_top",
};
const GRASS = "#91bd59", FOLIAGE = "#77ab2f";
const TINT = {
  grass_block: GRASS, short_grass: GRASS, grass: GRASS, tall_grass: GRASS, fern: GRASS, large_fern: GRASS,
  sugar_cane: GRASS, oak_leaves: FOLIAGE, jungle_leaves: FOLIAGE, acacia_leaves: FOLIAGE,
  dark_oak_leaves: FOLIAGE, mangrove_leaves: FOLIAGE, vine: FOLIAGE, birch_leaves: "#80a755",
  spruce_leaves: "#619961", water: "#3f76e4", bubble_column: "#3f76e4", lily_pad: "#208030",
};

function candidates(name) {
  const bases = [];
  if (ALIAS[name]) bases.push(ALIAS[name]);
  bases.push(name);
  let n = name.replace(/^waxed_/, "").replace(/^infested_/, "");
  if (n !== name) bases.push(n);
  n = n.replace(/_wood$/, "_log");
  bases.push(n);
  const m = n.match(/^(.*)_(stairs|slab|fence_gate|fence|wall|button|pressure_plate)$/);
  if (m) bases.push(m[1], m[1] + "_planks", m[1] + "s", m[1] + "_block");
  const out = [];
  for (const b of bases)
    for (const suffix of ["_top", "", "_side", "_front", "_0", "_bottom", "_stage7", "_stage0"])
      out.push(b + suffix);
  return out;
}
function resolveFile(name) {
  if (FILE.has(name)) return FILE.get(name);
  let f = null;
  if (!AIR.has(name)) f = candidates(name).find(c => TEX.files.has(c)) || null;
  FILE.set(name, f);
  return f;
}
function hashColor(name) {
  let h = 0;
  for (const c of name) h = (h * 31 + c.charCodeAt(0)) >>> 0;
  return `hsl(${h % 360} 45% ${35 + (h >> 8) % 25}%)`;
}
function tile(name) {
  if (TILE.has(name)) return TILE.get(name);
  const cv = document.createElement("canvas");
  cv.width = cv.height = 16;
  const g = cv.getContext("2d");
  g.imageSmoothingEnabled = false;
  const file = resolveFile(name), img = file && IMG.get(file);
  if (AIR.has(name)) {
    for (let i = 0; i < 4; i++) for (let j = 0; j < 4; j++) {
      g.fillStyle = (i + j) % 2 ? "#262626" : "#2f2f2f";
      g.fillRect(i * 4, j * 4, 4, 4);
    }
  } else if (img) {
    // animated textures are tall strips: draw only the first square frame
    g.drawImage(img, 0, 0, img.width, img.width, 0, 0, 16, 16);
    const t = TINT[name];
    if (t) {
      g.globalCompositeOperation = "multiply";
      g.fillStyle = t; g.fillRect(0, 0, 16, 16);
      g.globalCompositeOperation = "destination-in";
      g.drawImage(img, 0, 0, img.width, img.width, 0, 0, 16, 16);
    }
  } else {
    g.fillStyle = hashColor(name);
    g.fillRect(0, 0, 16, 16);
  }
  TILE.set(name, cv);
  return cv;
}
function swatch(name) {
  return `style="background-image:url(${tile(name).toDataURL()})"`;
}
async function loadTextures() {
  TILE.clear(); IMG.clear(); FILE.clear();
  let t = {version: null, files: []};
  try { t = await (await fetch("api/textures?version=" + encodeURIComponent(scanData.version))).json(); } catch (e) {}
  TEX.ver = t.version; TEX.files = new Set(t.files);
  const need = new Set();
  for (const b of scanData.blocks) { const f = resolveFile(b.name); if (f) need.add(f); }
  await Promise.all([...need].map(f => new Promise(res => {
    const im = new Image();
    im.onload = () => { IMG.set(f, im); res(); };
    im.onerror = res;
    im.src = `/tex/${TEX.ver}/${f}.png`;
  })));
  return t.files.length > 0;
}

/* ---------- helpers ---------- */
function status(msg, kind) { if (kind === "err") toast(msg, true); }
function toast(msg, err) {
  const t = $("toast");
  t.textContent = msg; t.classList.toggle("err", !!err); t.classList.add("show");
  clearTimeout(toast.t); toast.t = setTimeout(() => t.classList.remove("show"), err ? 6000 : 1400);
}

const S = {timer: null, mandatory: false, prevVersion: null};
const setShow = (id, on) => $(id).classList.toggle("hide", !on);

async function loadConfig(select) {
  const cfg = await (await fetch("api/config")).json();
  const want = select || $("version").value || cfg.default_version;
  $("version").innerHTML = cfg.versions.map(v =>
    `<option ${v === want ? "selected" : ""}>${v}</option>`).join("") +
    '<option value="__install__">+ Install version...</option>';
  S.prevVersion = $("version").value;
  $("dimension").innerHTML = cfg.dimensions.map(d => `<option>${d}</option>`).join("");
  return cfg;
}

$("version").addEventListener("change", () => {
  if ($("version").value === "__install__") { $("version").value = S.prevVersion; openSetup(false); }
  else S.prevVersion = $("version").value;
});

async function openSetup(mandatory) {
  S.mandatory = mandatory;
  $("setup").classList.remove("hide");
  const job = await (await fetch("api/job")).json();
  if (job.state === "running") { showProgress(job); poll(); return; }
  showPicker();
}

async function showPicker() {
  setShow("setup-pick", true); setShow("setup-steps", false); setShow("setup-pbar", false);
  setShow("setup-done", false); setShow("setup-retry", false); setShow("setup-cancel", !S.mandatory);
  $("setup-msg").textContent = ""; $("setup-msg").className = "";
  $("setup-intro").textContent = S.mandatory
    ? "Welcome! Pick the Minecraft version you want to explore. This downloads the server, block textures and builds the biome engine once; it takes a few minutes, and later versions are much faster."
    : "Pick a version to install. Installing an already-installed version repairs anything that is missing.";
  const sel = $("setup-version");
  sel.innerHTML = "<option>Loading versions...</option>"; sel.disabled = true; $("setup-go").disabled = true;
  try {
    const res = await fetch("api/versions");
    const d = await res.json();
    if (!res.ok) throw new Error(d.error || "Couldn't load the version list.");
    sel.innerHTML = d.versions.map(v =>
      `<option value="${v}">${v}${d.installed.includes(v) ? "  (installed)" : ""}</option>`).join("");
    const first = d.versions.find(v => !d.installed.includes(v));
    if (first) sel.value = first;
    sel.disabled = false; $("setup-go").disabled = false; sel.focus();
  } catch (e) {
    sel.innerHTML = "<option>Unavailable</option>";
    $("setup-msg").textContent = e.message; $("setup-msg").className = "err";
    setShow("setup-retry", true); $("setup-retry").textContent = "Try again";
  }
}
$("setup-retry").onclick = showPicker;
$("setup-cancel").onclick = () => $("setup").classList.add("hide");
$("setup-go").onclick = async () => {
  $("setup-go").disabled = true;
  try {
    const res = await fetch("api/install", {
      method: "POST", headers: {"Content-Type": "application/json"},
      body: JSON.stringify({version: $("setup-version").value}),
    });
    const d = await res.json();
    if (!res.ok) throw new Error(d.error || "Couldn't start the installation.");
    showProgress(d); poll();
  } catch (e) {
    $("setup-go").disabled = false;
    $("setup-msg").textContent = e.message; $("setup-msg").className = "err";
  }
};

const ICON = {pending: "\u25CB", done: "\u2713", skipped: "\u2713", warn: "!", error: "\u2715", active: ""};
function showProgress(job) {
  setShow("setup-pick", false); setShow("setup-steps", true); setShow("setup-pbar", true);
  setShow("setup-retry", false);
  if (job.state === "running") { $("setup-msg").textContent = ""; $("setup-msg").className = ""; }
  $("setup-title").textContent = `Setting up Minecraft ${job.version}`;
  $("setup-intro").textContent = job.state === "running"
    ? "Keep this tab open. Things already installed are skipped, so this only happens once per version."
    : "";
  const ol = $("setup-steps");
  ol.innerHTML = "";
  let finished = 0, activeFrac = 0;
  for (const s of job.steps) {
    const li = document.createElement("li");
    li.className = s.status;
    const ic = document.createElement("span"); ic.className = "ic"; ic.textContent = ICON[s.status] || "";
    const box = document.createElement("span");
    const lb = document.createElement("span"); lb.className = "lb"; lb.textContent = s.label;
    box.append(lb);
    if (s.detail) { const dt = document.createElement("span"); dt.className = "dt"; dt.textContent = s.detail; box.append(dt); }
    li.append(ic, box); ol.append(li);
    if (s.status === "active") activeFrac = s.progress || 0;
    else if (s.status !== "pending") finished++;
  }
  const pct = job.state === "done" ? 100 : Math.min(99, (finished + activeFrac) / job.steps.length * 100);
  $("setup-bar").style.width = pct + "%";
}

function poll() {
  clearInterval(S.timer);
  S.timer = setInterval(async () => {
    let job;
    try { job = await (await fetch("api/job")).json(); } catch (e) { return; }
    showProgress(job);
    if (job.state === "running") return;
    clearInterval(S.timer);
    finishSetup(job);
  }, 600);
}

async function finishSetup(job) {
  const msg = $("setup-msg");
  if (job.state === "error") {
    msg.textContent = job.error || "Installation failed."; msg.className = "err";
    setShow("setup-retry", true); $("setup-retry").textContent = "Back";
    return;
  }
  const cfg = await loadConfig(job.version);
  S.mandatory = false;
  const warns = job.steps.filter(s => s.status === "warn");
  if (!warns.length) {
    msg.textContent = `Minecraft ${job.version} is ready.`; msg.className = "";
    setTimeout(() => { $("setup").classList.add("hide"); announce(cfg); }, 900);
    return;
  }
  msg.textContent = "Installed, with notes: some optional parts need attention (see the steps above). You can fix them and run Install again from the Version menu.";
  msg.className = "";
  setShow("setup-done", true);
  $("setup-done").onclick = () => { $("setup").classList.add("hide"); announce(cfg); };
}

function announce(cfg) {
  const notes = [];
  if (!cfg.biomes_ready) notes.push("The biome map isn't available (the biome engine isn't built).");
  if (!cfg.java_ok) notes.push("Java wasn't found, so chunk scanning won't work yet.");
  if (!cfg.amulet_ok) notes.push("amulet-core is missing, so chunk scanning won't work yet.");
  if (notes.length) status(notes.join(" ") + " Use Version > Install version... to fix this.", "err");
  else status("Enter a seed and a coordinate, then show the biome map or scan the chunk the coordinate sits in.");
}

async function init() {
  const cfg = await loadConfig();
  const saved = JSON.parse(localStorage.getItem("scanner") || "{}");
  for (const k of ["x", "z", "seed"]) if (saved[k] !== undefined) $(k).value = saved[k];
  if (!cfg.setup_ok) { openSetup(true); return; }
  if (cfg.job && cfg.job.state === "running") openSetup(false);
  announce(cfg);
}

const SCAN_EMPTY = "Click a chunk on the Biome map to scan it, or type X and Z and press Enter.";
let scanTok = 0;
function scanReset(loading) {
  scanBusy = loading; X.ready = false; X.id = null; stopExplore(); exploreStatus();
  scanData = null; selected = null; curLayer = null; coords = []; hmData = null;
  $("tab-coords").disabled = $("tab-layer").disabled = $("tab-height").disabled = true;
  const l = '<div class="loading"><span class="spinner"></span><span>Scanning chunk...</span></div>';
  $("rows").innerHTML = loading ? l : '<div class="empty">No scan yet.</div>';
  $("pane").innerHTML = loading ? l : `<div class="empty">${SCAN_EMPTY}</div>`;
}

async function doScan(back) {
  const toExplore = back === "explore";
  const body = {
    x: $("x").value, z: $("z").value, seed: $("seed").value,
    version: $("version").value, dimension: $("dimension").value,
  };
  try { localStorage.setItem("scanner", JSON.stringify(body)); } catch (e) {}
  const tk = ++scanTok;
  scanReset(true);
  setMode(toExplore ? "explore" : "scan");
  status("Scanning. If this chunk is new, the server must start and generate it, which can take a minute or more.", "busy");
  try {
    const res = await fetch("api/scan", {
      method: "POST", headers: {"Content-Type": "application/json"}, body: JSON.stringify(body),
    });
    const data = await res.json();
    if (tk !== scanTok) return;
    if (!res.ok) throw new Error(data.error || "Scan failed.");
    scanData = data; scanBusy = false; selected = null; curLayer = null; LAYERS.clear();
    layerY = Math.max(data.ymin, Math.min(data.ymax, layerY));
    const haveTex = await loadTextures();
    if (tk !== scanTok) return;
    status(`Chunk (${data.cx}, ${data.cz}) in ${data.dimension}: x ${data.x0}..${data.x0 + 15}, ` +
           `z ${data.z0}..${data.z0 + 15}. ${data.total.toLocaleString()} blocks, ${data.blocks.length} types.` +
           (haveTex ? "" : `  No textures for this version yet: use Version > Install version... > Install to download them.`));
    $("tab-coords").disabled = $("tab-layer").disabled = $("tab-height").disabled = false;
    renderList();
    setView(view);
    if (mode === "explore") enterExplore();
  } catch (e) {
    if (tk !== scanTok) return;
    scanReset(false);
    $("pane").innerHTML = `<div class="empty" style="color:var(--bad)">${e.message}</div>`;
    status(e.message, "err");
  }
}

/* ---------- block list ---------- */
function renderList() {
  if (!scanData) return;
  const f = $("filter").value.trim().toLowerCase();
  let blocks = scanData.blocks.filter(b => b.name.includes(f));
  if (sortMode === "name") blocks = [...blocks].sort((a, b) => a.name.localeCompare(b.name));
  const max = Math.max(...scanData.blocks.map(b => b.count));
  $("sort").textContent = sortMode === "count" ? "Most common" : "A to Z";
  if (!blocks.length) { $("rows").innerHTML = '<div class="empty">No blocks match.</div>'; return; }
  $("rows").innerHTML = blocks.map(b => `
    <div class="row ${b.name === selected ? "sel" : ""}" tabindex="0" data-name="${b.name}">
      <span class="sw" ${swatch(b.name)}></span>
      <span class="name">${b.name}</span>
      <span class="cnt">${b.count.toLocaleString()}</span>
      <span class="bar" style="width:${Math.max(1, b.count / max * 100)}%"></span>
    </div>`).join("");
}

/* ---------- tabs ---------- */
function setView(v) {
  view = v;
  $("tab-coords").classList.toggle("on", v === "coords");
  $("tab-layer").classList.toggle("on", v === "layer");
  $("tab-height").classList.toggle("on", v === "height");
  if (!scanData) return;
  if (v === "layer") buildLayerPane();
  else if (v === "height") buildHeightPane();
  else if (selected) loadCoords(selected);
  else $("pane").innerHTML = '<div class="empty">Click a block in the list to see all of its coordinates.</div>';
}
function pickFromList(name) {
  selected = name;
  renderList();
  setView("coords");
}

/* ---------- coordinates view ---------- */
async function loadCoords(name) {
  $("pane").innerHTML = '<div class="empty">Loading coordinates...</div>';
  try {
    const res = await fetch(`api/coords?id=${scanData.id}&block=${encodeURIComponent(name)}`);
    const data = await res.json();
    if (!res.ok) throw new Error(data.error);
    if (view !== "coords" || selected !== name) return;
    coords = data.coords; shown = 0;
    renderCoords(name);
  } catch (e) {
    $("pane").innerHTML = `<div class="empty" style="color:var(--bad)">${e.message}</div>`;
  }
}

function renderCoords(name) {
  const total = scanData.total, n = coords.length;
  $("pane").innerHTML = `
    <h2><span class="sw" ${swatch(name)}></span>${name}</h2>
    <div class="meta">${n.toLocaleString()} blocks (${(n / total * 100).toFixed(2)}% of the chunk)</div>
    <div class="actions">
      <button id="csv">Download CSV</button>
      <button id="copy">Copy all coordinates</button>
    </div>
    <div class="coordgrid">
    <div class="charts">
      <div class="chart"><h3>Top-down view (blocks per column)</h3>
        <canvas id="colmap" width="320" height="320"></canvas><div class="cap" id="colcap">&nbsp;</div></div>
      <div class="chart"><h3>Height (blocks per Y level)</h3>
        <canvas id="hist" width="420" height="200"></canvas><div class="cap" id="histcap">&nbsp;</div></div>
    </div>
    <div class="coordbox"><div class="coordscroll">
      <table><thead><tr><th>X</th><th>Y</th><th>Z</th></tr></thead><tbody id="tbody"></tbody></table>
      <button class="more" id="more">Show more</button>
      <div class="cap">Click a row to copy "x y z".</div>
    </div></div>
    </div>`;
  drawColumnMap(); drawYHist(); showMore();
  $("csv").onclick = () => { location.href = `api/csv?id=${scanData.id}&block=${encodeURIComponent(name)}`; };
  $("copy").onclick = () => {
    navigator.clipboard.writeText(coords.map(c => c.join(" ")).join("\n"))
      .then(() => toast("Copied " + coords.length.toLocaleString() + " coordinates"),
            () => toast("Copy blocked by the browser"));
  };
  $("more").onclick = showMore;
}

function showMore() {
  const end = Math.min(coords.length, shown + PAGE);
  let html = "";
  for (let i = shown; i < end; i++) html += `<tr><td>${coords[i][0]}</td><td>${coords[i][1]}</td><td>${coords[i][2]}</td></tr>`;
  $("tbody").insertAdjacentHTML("beforeend", html);
  shown = end;
  const left = coords.length - shown;
  $("more").style.display = left > 0 ? "" : "none";
  $("more").textContent = `Show ${Math.min(PAGE, left).toLocaleString()} more (${left.toLocaleString()} remaining)`;
}

/* ---------- layer view ---------- */
function buildLayerPane() {
  $("pane").innerHTML = `
    <div class="ctl">
      <span class="ylab">Y</span>
      <button id="ydown" aria-label="Down one level">&minus;</button>
      <input id="yin" type="number" aria-label="Y level" min="${scanData.ymin}" max="${scanData.ymax}" value="${layerY}">
      <button id="yup" aria-label="Up one level">+</button>
      <input id="yr" type="range" aria-label="Y slider" min="${scanData.ymin}" max="${scanData.ymax}" value="${layerY}">
    </div>
    <div class="meta" id="layermeta"></div>
    <canvas id="layer" width="${CELL * 16}" height="${CELL * 16}" tabindex="0" aria-label="Cross section of the chunk"></canvas>
    <div class="cap" id="layercap">&nbsp;</div>
    <div class="legend" id="legend"></div>`;
  $("ydown").onclick = () => setY(layerY - 1);
  $("yup").onclick = () => setY(layerY + 1);
  $("yin").onchange = () => setY(parseInt($("yin").value, 10));
  $("yr").oninput = () => setY(parseInt($("yr").value, 10));
  const cv = $("layer");
  cv.onmousemove = e => {
    const c = cellAt(e);
    if (c && curLayer) $("layercap").textContent =
      `x ${scanData.x0 + c.i}, y ${curLayer.y}, z ${scanData.z0 + c.j}: ${c.name}`;
  };
  cv.onclick = e => { const c = cellAt(e); if (c) selectInLayer(c.name); };
  drawLayer();
}
function cellAt(e) {
  if (!curLayer) return null;
  const r = $("layer").getBoundingClientRect();
  const i = Math.floor((e.clientX - r.left) / r.width * 16), j = Math.floor((e.clientY - r.top) / r.height * 16);
  if (i < 0 || i > 15 || j < 0 || j > 15) return null;
  return {i, j, name: curLayer.palette[curLayer.grid[j][i]]};
}
function setY(v) {
  if (!Number.isFinite(v)) v = layerY;
  layerY = Math.max(scanData.ymin, Math.min(scanData.ymax, v));
  $("yin").value = layerY; $("yr").value = layerY;
  drawLayer();
}
function selectInLayer(name) {
  selected = name === selected ? null : name;
  renderList(); paintLayer();
}
async function drawLayer() {
  const sd = scanData;
  const y = layerY, key = scanData.id + ":" + y;
  let d = LAYERS.get(key);
  if (!d) {
    try {
      const res = await fetch(`api/layer?id=${scanData.id}&y=${y}`);
      d = await res.json();
      if (!res.ok) throw new Error(d.error);
    } catch (e) {
      if (view === "layer" && y === layerY) $("layermeta").textContent = e.message;
      return;
    }
    LAYERS.set(key, d);
  }
  if (sd !== scanData || view !== "layer" || y !== layerY) return;   // user moved on
  curLayer = d;
  paintLayer();
}
function paintLayer() {
  const d = curLayer, cv = $("layer");
  if (!d || !cv) return;
  const g = cv.getContext("2d");
  g.imageSmoothingEnabled = false;
  g.clearRect(0, 0, cv.width, cv.height);
  const counts = new Array(d.palette.length).fill(0);
  for (let j = 0; j < 16; j++) for (let i = 0; i < 16; i++) {
    const idx = d.grid[j][i];
    counts[idx]++;
    g.drawImage(tile(d.palette[idx]), i * CELL, j * CELL, CELL, CELL);
  }
  g.strokeStyle = "rgba(0,0,0,.28)"; g.lineWidth = 1;
  for (let k = 0; k <= 16; k++) {
    g.beginPath(); g.moveTo(k * CELL + .5, 0); g.lineTo(k * CELL + .5, cv.height); g.stroke();
    g.beginPath(); g.moveTo(0, k * CELL + .5); g.lineTo(cv.width, k * CELL + .5); g.stroke();
  }
  if (selected) {
    g.strokeStyle = "#3ecf6e"; g.lineWidth = 3;
    for (let j = 0; j < 16; j++) for (let i = 0; i < 16; i++)
      if (d.palette[d.grid[j][i]] === selected) g.strokeRect(i * CELL + 2, j * CELL + 2, CELL - 4, CELL - 4);
  }
  $("layermeta").textContent =
    `y = ${d.y}, x ${scanData.x0}..${scanData.x0 + 15} (left to right), z ${scanData.z0}..${scanData.z0 + 15} (top to bottom). ` +
    `Click a block to highlight it. Arrow Up/Down changes Y.`;
  const order = counts.map((c, i) => [c, i]).sort((a, b) => b[0] - a[0]);
  $("legend").innerHTML = order.map(([c, i]) => {
    const n = d.palette[i];
    return `<div class="lg ${n === selected ? "sel" : ""}" data-name="${n}">
      <span class="sw" ${swatch(n)}></span><span class="n">${n}</span><span class="c">${c}</span></div>`;
  }).join("");
  document.querySelectorAll(".lg").forEach(el => el.onclick = () => selectInLayer(el.dataset.name));
}

/* ---------- events ---------- */
for (const id of ["x", "z", "seed"]) $(id).addEventListener("keydown", e => {
  if (e.key === "Enter") { if (mode === "map") showMap(); else doScan(mode === "explore" ? "explore" : undefined); }
});
$("filter").oninput = renderList;
$("sort").onclick = () => { sortMode = sortMode === "count" ? "name" : "count"; renderList(); };
$("tab-coords").onclick = () => setView("coords");
$("tab-layer").onclick = () => setView("layer");
$("tab-height").onclick = () => setView("height");
$("rows").addEventListener("click", e => { const r = e.target.closest(".row"); if (r) pickFromList(r.dataset.name); });
$("rows").addEventListener("keydown", e => {
  if (e.key === "Enter" || e.key === " ") { const r = e.target.closest(".row"); if (r) { e.preventDefault(); pickFromList(r.dataset.name); } }
});
$("pane").addEventListener("click", e => {
  const tr = e.target.closest("tbody tr");
  if (!tr) return;
  const t = [...tr.children].map(td => td.textContent).join(" ");
  navigator.clipboard.writeText(t).then(() => toast("Copied " + t), () => {});
});
document.addEventListener("keydown", e => {
  if (mode !== "scan" || view !== "layer" || !scanData || ["INPUT", "SELECT", "TEXTAREA"].includes(e.target.tagName)) return;
  if (e.key === "ArrowUp") { e.preventDefault(); setY(layerY + 1); }
  if (e.key === "ArrowDown") { e.preventDefault(); setY(layerY - 1); }
});
/* ---------- charts for the selected block ---------- */
function css(v) { return getComputedStyle(document.documentElement).getPropertyValue(v).trim(); }

function drawColumnMap() {
  const cv = $("colmap"), g = cv.getContext("2d"), cell = 20;
  const grid = Array.from({length: 16}, () => new Array(16).fill(0));
  for (const [x, , z] of coords) grid[x - scanData.x0][z - scanData.z0]++;
  let max = 1;
  for (const row of grid) for (const v of row) if (v > max) max = v;
  g.clearRect(0, 0, 320, 320);
  for (let i = 0; i < 16; i++) for (let j = 0; j < 16; j++) {
    const v = grid[i][j];
    g.fillStyle = v ? `rgba(62,207,110,${0.2 + 0.8 * v / max})` : "rgba(255,255,255,.03)";
    g.fillRect(i * cell + 1, j * cell + 1, cell - 2, cell - 2);
  }
  $("colcap").textContent = "Left to right is X, top to bottom is Z. Hover a cell.";
  cv.onmousemove = e => {
    const r = cv.getBoundingClientRect();
    const i = Math.floor((e.clientX - r.left) / r.width * 16), j = Math.floor((e.clientY - r.top) / r.height * 16);
    if (i >= 0 && i < 16 && j >= 0 && j < 16)
      $("colcap").textContent = `x ${scanData.x0 + i}, z ${scanData.z0 + j}: ${grid[i][j]} blocks`;
  };
}

function drawYHist() {
  const cv = $("hist"), g = cv.getContext("2d");
  const W = cv.width, H = cv.height, padL = 8, padB = 20, padT = 8;
  let lo = Infinity, hi = -Infinity;
  for (const c of coords) { if (c[1] < lo) lo = c[1]; if (c[1] > hi) hi = c[1]; }
  const span = hi - lo + 1, bins = new Array(span).fill(0);
  for (const c of coords) bins[c[1] - lo]++;
  let max = 1;
  for (const v of bins) if (v > max) max = v;
  const bw = (W - padL * 2) / span;
  g.clearRect(0, 0, W, H);
  g.fillStyle = css("--accent");
  bins.forEach((v, i) => {
    const h = (H - padB - padT) * v / max;
    g.fillRect(padL + i * bw, H - padB - h, Math.max(1, bw - (bw > 3 ? 1 : 0)), h);
  });
  g.fillStyle = css("--muted"); g.font = "11px " + css("--mono");
  g.textAlign = "left"; g.fillText("y " + lo, padL, H - 5);
  g.textAlign = "right"; g.fillText("y " + hi, W - padL, H - 5);
  $("histcap").textContent = "Hover to read a level.";
  cv.onmousemove = e => {
    const r = cv.getBoundingClientRect();
    const i = Math.floor(((e.clientX - r.left) / r.width * W - padL) / bw);
    if (i >= 0 && i < span) $("histcap").textContent = `y ${lo + i}: ${bins[i]} blocks`;
  };
}

/* ---------- heightmap (surface height of every column) ---------- */
const HM = new Map();
let hmData = null;
const STOPS = [[0, [27, 58, 107]], [.25, [46, 139, 87]], [.5, [201, 180, 88]], [.75, [139, 90, 43]], [1, [242, 242, 242]]];
function ramp(t) {
  for (let k = 1; k < STOPS.length; k++) {
    if (t <= STOPS[k][0]) {
      const [t0, a] = STOPS[k - 1], [t1, c] = STOPS[k], f = (t - t0) / (t1 - t0);
      return `rgb(${a.map((v, i) => Math.round(v + (c[i] - v) * f)).join(",")})`;
    }
  }
  return "rgb(242,242,242)";
}

async function buildHeightPane() {
  const sd = scanData;
  $("pane").innerHTML = '<div class="empty">Loading heightmap...</div>';
  let d = HM.get(scanData.id);
  if (!d) {
    try {
      const res = await fetch(`api/heightmap?id=${scanData.id}`);
      d = await res.json();
      if (!res.ok) throw new Error(d.error);
      HM.set(scanData.id, d);
    } catch (e) {
      if (view === "height") $("pane").innerHTML = `<div class="empty" style="color:var(--bad)">${e.message}</div>`;
      return;
    }
  }
  if (sd !== scanData || view !== "height") return;
  hmData = d;
  $("pane").innerHTML = `
    <div class="ctl">
      <label>Surface
        <select id="hm-kind">
          <option value="ground">Ground (ignores water and lava)</option>
          <option value="top">Top block (includes water and lava)</option>
        </select></label>
      <label>Colour by
        <select id="hm-color">
          <option value="height">Height</option>
          <option value="block">Surface block texture</option>
        </select></label>
    </div>
    <div class="meta" id="hm-meta"></div>
    <canvas id="hmap" width="${CELL * 16}" height="${CELL * 16}" aria-label="Surface heightmap of the chunk"></canvas>
    <div class="cap" id="hm-cap">&nbsp;</div>
    <div class="scale"><div class="gr" id="hm-gr"></div><div class="lb"><span id="hm-lo"></span><span id="hm-hi"></span></div></div>`;
  $("hm-kind").onchange = $("hm-color").onchange = paintHeight;
  $("hmap").onmousemove = e => {
    const r = $("hmap").getBoundingClientRect();
    const i = Math.floor((e.clientX - r.left) / r.width * 16), j = Math.floor((e.clientY - r.top) / r.height * 16);
    if (i < 0 || i > 15 || j < 0 || j > 15) return;
    const t = hmData.top_y[j][i], g = hmData.ground_y[j][i];
    $("hm-cap").textContent = `x ${scanData.x0 + i}, z ${scanData.z0 + j}: top ${hmData.top_b[j][i]} at y ${t}` +
      (g !== t ? `, ground ${hmData.ground_b[j][i]} at y ${g}` : "");
  };
  paintHeight();
}

function paintHeight() {
  const d = hmData, kind = $("hm-kind").value, how = $("hm-color").value;
  const ys = d[kind + "_y"], bl = d[kind + "_b"];
  let lo = Infinity, hi = -Infinity;
  for (const row of ys) for (const v of row) if (v !== null) { if (v < lo) lo = v; if (v > hi) hi = v; }
  const cv = $("hmap"), g = cv.getContext("2d");
  g.imageSmoothingEnabled = false;
  g.font = "bold 11px " + css("--mono"); g.textAlign = "center"; g.textBaseline = "middle";
  for (let j = 0; j < 16; j++) for (let i = 0; i < 16; i++) {
    const v = ys[j][i], x = i * CELL, y = j * CELL;
    if (v === null) { g.fillStyle = css("--panel"); g.fillRect(x, y, CELL, CELL); continue; }
    const t = hi === lo ? 0.5 : (v - lo) / (hi - lo);
    if (how === "block") {
      g.drawImage(tile(bl[j][i]), x, y, CELL, CELL);
      g.fillStyle = `rgba(0,0,0,${0.6 * (1 - t)})`; g.fillRect(x, y, CELL, CELL);
    } else {
      g.fillStyle = ramp(t); g.fillRect(x, y, CELL, CELL);
    }
    g.lineWidth = 3; g.strokeStyle = "rgba(0,0,0,.7)"; g.strokeText(v, x + CELL / 2, y + CELL / 2);
    g.fillStyle = "#fff"; g.fillText(v, x + CELL / 2, y + CELL / 2);
  }
  g.strokeStyle = "rgba(0,0,0,.28)"; g.lineWidth = 1;
  for (let k = 0; k <= 16; k++) {
    g.beginPath(); g.moveTo(k * CELL + .5, 0); g.lineTo(k * CELL + .5, cv.height); g.stroke();
    g.beginPath(); g.moveTo(0, k * CELL + .5); g.lineTo(cv.width, k * CELL + .5); g.stroke();
  }
  $("hm-meta").textContent = `Lowest y ${lo}, highest y ${hi}, spread ${hi - lo} blocks. ` +
    `x ${scanData.x0}..${scanData.x0 + 15} left to right, z ${scanData.z0}..${scanData.z0 + 15} top to bottom.`;
  $("hm-gr").style.background = how === "height"
    ? `linear-gradient(to right, ${STOPS.map(([t]) => ramp(t) + " " + t * 100 + "%").join(",")})`
    : "linear-gradient(to right, #000, #888)";
  $("hm-lo").textContent = "y " + lo + " (low)"; $("hm-hi").textContent = "y " + hi + " (high)";
}

/* ---------- interactive 3D view: spectator-style fly camera (block edits stay in the browser) ---------- */
const X = {ready: false, id: null, raf: 0, last: 0, locked: false, keys: new Set(), speed: 8, broken: 0,
           cam: null, target: null, gl: null, ms: null, mw: null, tex: null};
let scanBusy = false;
const PLANT_RE = /^(short_grass|grass|tall_grass|fern|large_fern|dead_bush|seagrass|tall_seagrass|kelp|kelp_plant|sugar_cane|vine|glow_lichen|sweet_berry_bush|lily_pad|torch|wall_torch|soul_torch|redstone_torch|rail|powered_rail|detector_rail|activator_rail|cobweb|.*_sapling|.*_tulip|poppy|dandelion|blue_orchid|allium|azure_bluet|cornflower|lily_of_the_valley|oxeye_daisy|wither_rose|torchflower|rose_bush|peony|lilac|sunflower|pitcher_plant|brown_mushroom|red_mushroom|crimson_roots|warped_roots|nether_sprouts|crimson_fungus|warped_fungus|.*_coral_fan|.*_coral_wall_fan|hanging_roots|spore_blossom|small_dripleaf|cave_vines|cave_vines_plant|weeping_vines|twisting_vines|bamboo|fire|soul_fire)$/;
const FACES = [
  {d: [0, 1, 0],  t: 0, sh: 1,   c: [[0,1,0],[1,1,0],[1,1,1],[0,1,1]]},
  {d: [0, -1, 0], t: 2, sh: .55, c: [[0,0,0],[1,0,0],[1,0,1],[0,0,1]]},
  {d: [1, 0, 0],  t: 1, sh: .8,  c: [[1,1,1],[1,1,0],[1,0,0],[1,0,1]]},
  {d: [-1, 0, 0], t: 1, sh: .8,  c: [[0,1,0],[0,1,1],[0,0,1],[0,0,0]]},
  {d: [0, 0, 1],  t: 1, sh: .68, c: [[0,1,1],[1,1,1],[1,0,1],[0,0,1]]},
  {d: [0, 0, -1], t: 1, sh: .68, c: [[1,1,0],[0,1,0],[0,0,0],[1,0,0]]},
];
const QUV = [[0, 0], [1, 0], [1, 1], [0, 1]];
const CROSS = [[[0,1,0],[1,1,1],[1,0,1],[0,0,0]], [[1,1,0],[0,1,1],[0,0,1],[1,0,0]]];
const BOTTOM_AS = {grass_block: "dirt", podzol: "dirt", mycelium: "dirt", dirt_path: "dirt", farmland: "dirt"};
const SKY = {overworld: [.47, .65, .85], nether: [.17, .05, .04], end: [.05, .03, .08]};
const FC = new Map();

function faceFile(name, face) {
  if (face === 0) return resolveFile(name);
  if (face === 2 && BOTTOM_AS[name] && TEX.files.has(BOTTOM_AS[name])) return BOTTOM_AS[name];
  const bases = ALIAS[name] ? [ALIAS[name], name] : [name];
  const sfx = face === 1 ? ["_side", "", "_front"] : ["_bottom", "_side", ""];
  for (const b of bases) for (const s of sfx) if (TEX.files.has(b + s)) return b + s;
  return resolveFile(name);
}
function faceCanvas(name, face) {
  const file = faceFile(name, face);
  if (face === 0 || !file || file === resolveFile(name)) return tile(name);
  const key = name + "|" + file;
  if (FC.has(key)) return FC.get(key);
  const img = IMG.get(file);
  if (!img) return tile(name);
  const cv = document.createElement("canvas");
  cv.width = cv.height = 16;
  const g = cv.getContext("2d");
  g.imageSmoothingEnabled = false;
  g.drawImage(img, 0, 0, img.width, img.width, 0, 0, 16, 16);
  const t = TINT[name];
  if (t && name !== "grass_block") {
    g.globalCompositeOperation = "multiply";
    g.fillStyle = t; g.fillRect(0, 0, 16, 16);
    g.globalCompositeOperation = "destination-in";
    g.drawImage(img, 0, 0, img.width, img.width, 0, 0, 16, 16);
  }
  FC.set(key, cv);
  return cv;
}

/* tiny matrix helpers (column-major) */
function mPersp(fov, a, n, f) {
  const t = 1 / Math.tan(fov / 2);
  return [t / a, 0, 0, 0, 0, t, 0, 0, 0, 0, (f + n) / (n - f), -1, 0, 0, 2 * f * n / (n - f), 0];
}
function mLook(e, c) {
  let fx = c[0] - e[0], fy = c[1] - e[1], fz = c[2] - e[2];
  let l = Math.hypot(fx, fy, fz); fx /= l; fy /= l; fz /= l;
  let sx = -fz, sy = 0, sz = fx; l = Math.hypot(sx, sz) || 1; sx /= l; sz /= l;
  const ux = sy * fz - sz * fy, uy = sz * fx - sx * fz, uz = sx * fy - sy * fx;
  return [sx, ux, -fx, 0, sy, uy, -fy, 0, sz, uz, -fz, 0,
          -(sx * e[0] + sy * e[1] + sz * e[2]), -(ux * e[0] + uy * e[1] + uz * e[2]), fx * e[0] + fy * e[1] + fz * e[2], 1];
}
function mMul(a, b) {
  const o = new Array(16);
  for (let c = 0; c < 4; c++) for (let r = 0; r < 4; r++) {
    let v = 0;
    for (let k = 0; k < 4; k++) v += a[k * 4 + r] * b[c * 4 + k];
    o[c * 4 + r] = v;
  }
  return o;
}

function glInit() {
  const cv = $("xcv");
  const gl = cv.getContext("webgl2", {antialias: true});
  if (!gl) return false;
  const prog = (vs, fs) => {
    const p = gl.createProgram();
    for (const [type, src] of [[gl.VERTEX_SHADER, vs], [gl.FRAGMENT_SHADER, fs]]) {
      const sh = gl.createShader(type);
      gl.shaderSource(sh, src); gl.compileShader(sh);
      if (!gl.getShaderParameter(sh, gl.COMPILE_STATUS)) throw new Error(gl.getShaderInfoLog(sh));
      gl.attachShader(p, sh);
    }
    gl.linkProgram(p);
    return p;
  };
  X.pm = prog([
    "#version 300 es",
    "layout(location=0) in vec3 aPos; layout(location=1) in vec2 aUv; layout(location=2) in float aShade;",
    "uniform mat4 uVP; out vec2 vUv; out float vShade;",
    "void main(){ vUv = aUv; vShade = aShade; gl_Position = uVP * vec4(aPos, 1.0); }"].join("\n"), [
    "#version 300 es",
    "precision mediump float; in vec2 vUv; in float vShade;",
    "uniform sampler2D uTex; uniform float uCut; uniform float uAlpha; out vec4 o;",
    "void main(){ vec4 c = texture(uTex, vUv); if (uCut > 0.5 && c.a < 0.5) discard; o = vec4(c.rgb * vShade, c.a * uAlpha); }"].join("\n"));
  X.pl = prog([
    "#version 300 es",
    "layout(location=0) in vec3 aPos; uniform mat4 uVP;",
    "void main(){ gl_Position = uVP * vec4(aPos, 1.0); }"].join("\n"), [
    "#version 300 es",
    "precision mediump float; uniform vec4 uC; out vec4 o;",
    "void main(){ o = uC; }"].join("\n"));
  X.um = {vp: gl.getUniformLocation(X.pm, "uVP"), tex: gl.getUniformLocation(X.pm, "uTex"),
          cut: gl.getUniformLocation(X.pm, "uCut"), alpha: gl.getUniformLocation(X.pm, "uAlpha")};
  X.ul = {vp: gl.getUniformLocation(X.pl, "uVP"), c: gl.getUniformLocation(X.pl, "uC")};
  X.lvao = gl.createVertexArray(); X.lbuf = gl.createBuffer();
  gl.bindVertexArray(X.lvao); gl.bindBuffer(gl.ARRAY_BUFFER, X.lbuf);
  gl.enableVertexAttribArray(0); gl.vertexAttribPointer(0, 3, gl.FLOAT, false, 0, 0);
  X.gl = gl;
  return true;
}

function buildAtlas() {
  const gl = X.gl, canv = [];
  const slot = c => { let i = canv.indexOf(c); if (i < 0) { i = canv.length; canv.push(c); } return i; };
  X.props = X.pal.map(n => {
    if (n === "air") return null;
    const water = n === "water" || n === "bubble_column", plant = PLANT_RE.test(n);
    const glass = n.includes("glass"), leaves = n.endsWith("leaves");
    return {water, plant, glass, opaque: !water && !plant && !glass && !leaves,
            tiles: [slot(faceCanvas(n, 0)), slot(faceCanvas(n, 1)), slot(faceCanvas(n, 2))]};
  });
  X.atlasH = Math.ceil(canv.length / 16) * 16;
  const at = document.createElement("canvas");
  at.width = 256; at.height = X.atlasH;
  const g = at.getContext("2d");
  canv.forEach((c, i) => g.drawImage(c, (i % 16) * 16, (i >> 4) * 16));
  if (X.tex) gl.deleteTexture(X.tex);
  X.tex = gl.createTexture();
  gl.bindTexture(gl.TEXTURE_2D, X.tex);
  gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, gl.RGBA, gl.UNSIGNED_BYTE, at);
  for (const [k, v] of [[gl.TEXTURE_MIN_FILTER, gl.NEAREST], [gl.TEXTURE_MAG_FILTER, gl.NEAREST],
                        [gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE], [gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE]])
    gl.texParameteri(gl.TEXTURE_2D, k, v);
}

function pushQuad(out, P, t, shade, N) {
  const col = t & 15, row = t >> 4, H = X.atlasH;
  const vtx = i => [P[i][0], P[i][1], P[i][2],
    (col + .02 + QUV[i][0] * .96) / 16, (row * 16 + .32 + QUV[i][1] * 15.36) / H, shade];
  let flip = false;
  if (N) {
    const ax = P[1][0] - P[0][0], ay = P[1][1] - P[0][1], az = P[1][2] - P[0][2];
    const bx = P[2][0] - P[0][0], by = P[2][1] - P[0][1], bz = P[2][2] - P[0][2];
    flip = (ay * bz - az * by) * N[0] + (az * bx - ax * bz) * N[1] + (ax * by - ay * bx) * N[2] < 0;
  }
  for (const i of (flip ? [0, 2, 1, 0, 3, 2] : [0, 1, 2, 0, 2, 3])) out.push(...vtx(i));
  if (!N) for (const i of [0, 2, 1, 0, 3, 2]) out.push(...vtx(i));   // both sides (plants, water)
}

function uploadMesh(key, arr) {
  const gl = X.gl;
  let m = X[key];
  if (!m) {
    m = X[key] = {vao: gl.createVertexArray(), buf: gl.createBuffer(), n: 0};
    gl.bindVertexArray(m.vao); gl.bindBuffer(gl.ARRAY_BUFFER, m.buf);
    gl.enableVertexAttribArray(0); gl.vertexAttribPointer(0, 3, gl.FLOAT, false, 24, 0);
    gl.enableVertexAttribArray(1); gl.vertexAttribPointer(1, 2, gl.FLOAT, false, 24, 12);
    gl.enableVertexAttribArray(2); gl.vertexAttribPointer(2, 1, gl.FLOAT, false, 24, 20);
  }
  gl.bindVertexArray(m.vao); gl.bindBuffer(gl.ARRAY_BUFFER, m.buf);
  gl.bufferData(gl.ARRAY_BUFFER, new Float32Array(arr), gl.STATIC_DRAW);
  m.n = arr.length / 6;
}

function rebuild() {
  const {vox, H, props} = X, S = [], W = [];
  const get = (x, y, z) => (x < 0 || z < 0 || y < 0 || x > 15 || z > 15 || y >= H) ? 0 : vox[y * 256 + z * 16 + x];
  for (let y = 0; y < H; y++) for (let z = 0; z < 16; z++) for (let x = 0; x < 16; x++) {
    const v = vox[y * 256 + z * 16 + x];
    if (!v) continue;
    const p = props[v];
    if (p.plant) {
      for (const q of CROSS) pushQuad(S, q.map(a => [x + a[0], y + a[1], z + a[2]]), p.tiles[0], .9, null);
      continue;
    }
    const out = p.water ? W : S;
    for (const f of FACES) {
      const nv = get(x + f.d[0], y + f.d[1], z + f.d[2]);
      if (nv) { const q = props[nv]; if (q.opaque || (nv === v && (p.water || p.glass))) continue; }
      pushQuad(out, f.c.map(a => [x + a[0], y + a[1], z + a[2]]), p.tiles[f.t], f.sh, p.water ? null : f.d);
    }
  }
  uploadMesh("ms", S); uploadMesh("mw", W);
}

function castRay(o, d, max) {
  const pos = [Math.floor(o[0]), Math.floor(o[1]), Math.floor(o[2])];
  const step = d.map(v => v > 0 ? 1 : -1), tD = d.map(v => v === 0 ? Infinity : Math.abs(1 / v));
  const tM = [0, 1, 2].map(i => d[i] === 0 ? Infinity : (d[i] > 0 ? pos[i] + 1 - o[i] : o[i] - pos[i]) * tD[i]);
  let t = 0;
  while (t <= max) {
    const [x, y, z] = pos;
    if (x >= 0 && z >= 0 && y >= 0 && x < 16 && z < 16 && y < X.H) {
      const v = X.vox[y * 256 + z * 16 + x];
      if (v && !X.props[v].water) return pos.slice();
    }
    const a = tM[0] < tM[1] ? (tM[0] < tM[2] ? 0 : 2) : (tM[1] < tM[2] ? 1 : 2);
    t = tM[a]; tM[a] += tD[a]; pos[a] += step[a];
  }
  return null;
}

function resetCamera() {
  let top = X.H / 2;
  for (let y = X.H - 1; y >= 0; y--) if (X.vox[y * 256 + 8 * 16 + 8]) { top = y + 1; break; }
  X.cam = {x: 8, y: top + 3, z: 8, yaw: Math.PI * .25, pitch: -.35};
}
function resetChunk() { X.vox.set(X.orig); X.broken = 0; rebuild(); }
function breakBlock() {
  const [x, y, z] = X.target;
  X.vox[y * 256 + z * 16 + x] = 0;
  X.broken++; X.target = null; rebuild();
}

function xFrame(now) {
  X.raf = requestAnimationFrame(xFrame);
  const dt = Math.min(.05, (now - X.last) / 1000 || 0); X.last = now;
  const gl = X.gl, cv = $("xcv"), c = X.cam;
  const dpr = window.devicePixelRatio || 1;
  const w = Math.max(1, Math.floor(cv.clientWidth * dpr)), h = Math.max(1, Math.floor(cv.clientHeight * dpr));
  if (cv.width !== w || cv.height !== h) { cv.width = w; cv.height = h; }
  if (X.locked) {
    const k = X.keys, sp = X.speed * dt, has = (...n) => n.some(i => k.has(i)) ? 1 : 0;
    const f = has("KeyW", "ArrowUp") - has("KeyS", "ArrowDown"), r = has("KeyD", "ArrowRight") - has("KeyA", "ArrowLeft");
    c.x += (Math.sin(c.yaw) * f + Math.cos(c.yaw) * r) * sp;
    c.z += (-Math.cos(c.yaw) * f + Math.sin(c.yaw) * r) * sp;
    c.y += (has("Space") - has("ShiftLeft", "ShiftRight")) * sp;
  }
  const cp = Math.cos(c.pitch), dir = [cp * Math.sin(c.yaw), Math.sin(c.pitch), -cp * Math.cos(c.yaw)];
  const eye = [c.x, c.y, c.z];
  X.target = castRay(eye, dir, 8);
  const vp = mMul(mPersp(70 * Math.PI / 180, w / h, .05, 600), mLook(eye, [eye[0] + dir[0], eye[1] + dir[1], eye[2] + dir[2]]));
  const sky = SKY[X.dim] || SKY.overworld;
  gl.viewport(0, 0, w, h);
  gl.clearColor(sky[0], sky[1], sky[2], 1);
  gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);
  gl.enable(gl.DEPTH_TEST); gl.enable(gl.CULL_FACE);
  gl.useProgram(X.pm);
  gl.uniformMatrix4fv(X.um.vp, false, vp);
  gl.activeTexture(gl.TEXTURE0); gl.bindTexture(gl.TEXTURE_2D, X.tex); gl.uniform1i(X.um.tex, 0);
  gl.uniform1f(X.um.cut, 1); gl.uniform1f(X.um.alpha, 1);
  gl.bindVertexArray(X.ms.vao); gl.drawArrays(gl.TRIANGLES, 0, X.ms.n);
  if (X.mw.n) {
    gl.enable(gl.BLEND); gl.blendFunc(gl.SRC_ALPHA, gl.ONE_MINUS_SRC_ALPHA); gl.depthMask(false);
    gl.uniform1f(X.um.cut, 0); gl.uniform1f(X.um.alpha, .6);
    gl.bindVertexArray(X.mw.vao); gl.drawArrays(gl.TRIANGLES, 0, X.mw.n);
    gl.depthMask(true); gl.disable(gl.BLEND);
  }
  const tg = X.target;
  if (tg) {
    const e = .003, lo = tg.map(v => v - e), hi = tg.map(v => v + 1 + e), v = [];
    const cn = i => [i & 1 ? hi[0] : lo[0], i & 2 ? hi[1] : lo[1], i & 4 ? hi[2] : lo[2]];
    for (const [a, b] of [[0,1],[2,3],[4,5],[6,7],[0,2],[1,3],[4,6],[5,7],[0,4],[1,5],[2,6],[3,7]]) v.push(...cn(a), ...cn(b));
    gl.disable(gl.CULL_FACE);
    gl.useProgram(X.pl);
    gl.uniformMatrix4fv(X.ul.vp, false, vp); gl.uniform4f(X.ul.c, .24, .81, .43, 1);
    gl.bindVertexArray(X.lvao); gl.bindBuffer(gl.ARRAY_BUFFER, X.lbuf);
    gl.bufferData(gl.ARRAY_BUFFER, new Float32Array(v), gl.DYNAMIC_DRAW);
    gl.drawArrays(gl.LINES, 0, 24);
  }
  const txt = `x ${(X.x0 + c.x).toFixed(1)}  y ${(X.ymin + c.y).toFixed(1)}  z ${(X.z0 + c.z).toFixed(1)}   speed ${X.speed.toFixed(0)}   broken ${X.broken}` +
    (tg ? `   |   ${X.pal[X.vox[tg[1] * 256 + tg[2] * 16 + tg[0]]]} (${X.x0 + tg[0]}, ${X.ymin + tg[1]}, ${X.z0 + tg[2]})` : "");
  const hud = $("xhud");
  if (hud.textContent !== txt) hud.textContent = txt;
}

const XSTART = `<div class="xcard"><h3>Interactive view</h3>
  <p>Click to look around. <kbd>W</kbd><kbd>A</kbd><kbd>S</kbd><kbd>D</kbd> fly, <kbd>Space</kbd> up, <kbd>Shift</kbd> down,
  scroll for speed, left-click breaks the block you aim at, <kbd>Esc</kbd> frees the mouse. You pass through walls.
  Broken blocks only change this view, never the world.</p>
  <div class="xbtns"><button class="primary" id="xgo">Start</button><button id="xreset">Restore blocks</button><button id="xhome">Reset camera</button></div></div>`;
const XLOAD = t => `<div class="xcard"><div class="loading"><span class="spinner"></span><span>${t}</span></div></div>`;
function exploreMsg(html) {
  $("xmsg").innerHTML = html; $("xmsg").classList.remove("hide");
  $("xcross").classList.add("hide"); $("xhud").classList.add("hide");
}
function exploreStatus() {
  if (mode !== "explore") return;
  if (scanBusy) exploreMsg(XLOAD("Scanning chunk..."));
  else if (!scanData) exploreMsg('<div class="xcard"><p>Nothing to explore yet. Click a chunk on the Biome map to scan it, then open this tab.</p></div>');
}
function xSync() {
  if (mode !== "explore" || !X.ready) return;
  if (X.locked) {
    $("xmsg").classList.add("hide"); $("xcross").classList.remove("hide"); $("xhud").classList.remove("hide");
  } else { exploreMsg(XSTART); $("xhud").classList.remove("hide"); }
}
function stopExplore() {
  cancelAnimationFrame(X.raf); X.raf = 0; X.keys.clear();
  if (document.pointerLockElement) document.exitPointerLock();
}
function lockPointer() { const p = $("xcv").requestPointerLock(); if (p && p.catch) p.catch(() => {}); }

async function enterExplore() {
  if (!scanData) { exploreStatus(); return; }
  if (X.ready && X.id === scanData.id) {
    xSync();
    if (!X.raf) { X.last = performance.now(); X.raf = requestAnimationFrame(xFrame); }
    return;
  }
  const sd = scanData;
  exploreMsg(XLOAD("Building 3D view..."));
  try {
    if (!X.gl && !glInit()) throw new Error("WebGL 2 isn't available in this browser.");
    const res = await fetch("api/voxels?id=" + encodeURIComponent(sd.id)), d = await res.json();
    if (!res.ok) throw new Error(d.error || "Could not load this chunk.");
    if (sd !== scanData) return;
    const bin = atob(d.data), bytes = new Uint8Array(bin.length);
    for (let i = 0; i < bin.length; i++) bytes[i] = bin.charCodeAt(i);
    X.vox = new Uint16Array(bytes.buffer); X.orig = X.vox.slice();
    X.pal = d.palette; X.ymin = d.ymin; X.H = d.ymax - d.ymin + 1;
    X.x0 = sd.x0; X.z0 = sd.z0; X.dim = sd.dimension;
    const need = new Set();
    for (const n of X.pal) if (n !== "air") for (const f of [1, 2]) {
      const file = faceFile(n, f);
      if (file && !IMG.has(file)) need.add(file);
    }
    await Promise.all([...need].map(f => new Promise(done => {
      const im = new Image();
      im.onload = () => { IMG.set(f, im); done(); };
      im.onerror = done;
      im.src = `/tex/${TEX.ver}/${f}.png`;
    })));
    if (sd !== scanData) return;
    FC.clear(); buildAtlas(); X.broken = 0; rebuild(); resetCamera();
    X.id = sd.id; X.ready = true;
    if (mode === "explore") enterExplore();
  } catch (e) {
    if (sd === scanData) exploreMsg(`<div class="xcard"><p style="color:var(--bad)">${e.message}</p></div>`);
  }
}

document.addEventListener("pointerlockchange", () => {
  X.locked = document.pointerLockElement === $("xcv");
  if (!X.locked) X.keys.clear();
  xSync();
});
document.addEventListener("mousemove", e => {
  if (!X.locked || !X.cam) return;
  X.cam.yaw += e.movementX * .0022;
  X.cam.pitch = Math.max(-1.55, Math.min(1.55, X.cam.pitch - e.movementY * .0022));
});
document.addEventListener("keydown", e => {
  if (mode !== "explore" || !X.locked) return;
  if (/^(Key[WASD]|Space|Shift(Left|Right)|Arrow(Up|Down|Left|Right))$/.test(e.code)) { e.preventDefault(); X.keys.add(e.code); }
});
document.addEventListener("keyup", e => X.keys.delete(e.code));
window.addEventListener("blur", () => X.keys.clear());
$("xcv").addEventListener("wheel", e => {
  if (!X.locked) return;
  e.preventDefault();
  X.speed = Math.max(1, Math.min(80, X.speed * (e.deltaY < 0 ? 1.25 : .8)));
}, {passive: false});
$("xcv").addEventListener("mousedown", e => {
  if (!X.ready) return;
  if (!X.locked) { lockPointer(); return; }
  if (e.button === 0 && X.target) breakBlock();
});
$("xmsg").addEventListener("click", e => {
  if (e.target.id === "xreset") { resetChunk(); return; }
  if (e.target.id === "xhome") { resetCamera(); return; }
  if (X.ready) lockPointer();
});

/* ---------- biome map (server-free, zoomable like Chunkbase) ---------- */
let mapW = 900, mapH = 600;
let mode = "map";
// zoom levels as screen pixels per block
const LEVELS = [2, 1.5, 1, 0.75, 0.5, 0.375, 0.25, 0.125, 1 / 16, 1 / 32, 1 / 64, 1 / 128, 1 / 256, 1 / 512, 1 / 1024];
const mv = {bx: 0, bz: 0, lvl: 5, data: null, img: null, hl: null, token: 0, hover: null, drag: null, zt: 0, wt: 0, rt: 0};
const bover = $("bover"), bmap = $("bmap");

function levelLabel(p) { return p >= 0.25 ? `${p * 16} px per chunk` : `${1 / p} blocks per pixel`; }
$("mzoom").innerHTML = LEVELS.map((p, i) => `<option value="${i}" ${i === mv.lvl ? "selected" : ""}>${levelLabel(p)}</option>`).join("");

// Each biome sample covers `step` blocks; zoomed out far, samples are spread so the number stays small.
function sampleStep(p) {
  const minCell = p >= 0.5 ? 2 : 3;
  return Math.max(4, 4 * Math.ceil(minCell / (p * 4)));
}

function setMode(m) {
  const prev = mode;
  mode = m;
  $("scanview").classList.toggle("hide", m !== "scan");
  $("mapview").classList.toggle("hide", m !== "map");
  $("exploreview").classList.toggle("hide", m !== "explore");
  $("mode-explore").classList.toggle("on", m === "explore");
  $("mode-explore").setAttribute("aria-selected", m === "explore");
  if (m === "explore") enterExplore(); else if (prev === "explore") stopExplore();
  $("mode-map").classList.toggle("on", m === "map");
  $("mode-scan").classList.toggle("on", m === "scan");
  $("mode-map").setAttribute("aria-selected", m === "map");
  $("mode-scan").setAttribute("aria-selected", m === "scan");
}

function showMap() {
  setMode("map");
  const x = parseInt($("x").value, 10), z = parseInt($("z").value, 10);
  mv.bx = Number.isFinite(x) ? x : 0;
  mv.bz = Number.isFinite(z) ? z : 0;
  mv.lvl = parseInt($("mzoom").value, 10);
  mv.hl = null; mv.hover = null;
  fetchRegion(true);
}

function mapLoading() {
  mv.data = null; mv.img = null;
  hideTip();
  const g = bmap.getContext("2d");
  g.fillStyle = "#161616"; g.fillRect(0, 0, mapW, mapH);
  bover.getContext("2d").clearRect(0, 0, mapW, mapH);
  const l = '<div class="loading"><span class="spinner"></span><span>Loading...</span></div>';
  $("blegend").innerHTML = l; $("sbody").innerHTML = l;
  $("mcap").innerHTML = "&nbsp;";
  $("maploading").classList.remove("hide");
}

async function fetchRegion(clear) {
  const p = LEVELS[mv.lvl], step = sampleStep(p);
  const vwB = mapW / p, vhB = mapH / p;
  const mx = vwB * 0.15, mz = vhB * 0.15;
  const bx0 = Math.floor((mv.bx - vwB / 2 - mx) / step) * step;
  const bz0 = Math.floor((mv.bz - vhB / 2 - mz) / step) * step;
  const w = Math.ceil((mv.bx + vwB / 2 + mx - bx0) / step) + 1;
  const h = Math.ceil((mv.bz + vhB / 2 + mz - bz0) / step) + 1;
  const q = new URLSearchParams({
    seed: $("seed").value, version: $("version").value, dimension: $("dimension").value,
    y: $("my").value || "63", bx0, bz0, step, w, h,
  });
  const token = ++mv.token;
  if (clear === true) mapLoading();
  status("Computing biomes (no Minecraft server involved)...", "busy");
  try {
    const res = await fetch("api/biomes?" + q);
    const d = await res.json();
    if (!res.ok) throw new Error(d.error || "Biome request failed.");
    if (token !== mv.token) return;
    const bin = atob(d.grid), bytes = new Uint8Array(bin.length);
    for (let i = 0; i < bin.length; i++) bytes[i] = bin.charCodeAt(i);
    const pal = new Map(), counts = new Map();
    for (const e of d.palette) {
      const n = parseInt(e.color.slice(1), 16);
      pal.set(e.id, {name: e.name, color: e.color, rgb: [(n >> 16) & 255, (n >> 8) & 255, n & 255]});
    }
    for (let i = 0; i < bytes.length; i++) counts.set(bytes[i], (counts.get(bytes[i]) || 0) + 1);
    mv.data = {bx0: d.bx0, bz0: d.bz0, step: d.step, w: d.w, h: d.h, bytes, pal, counts};
    $("maploading").classList.add("hide");
    buildImage(); paintMap(); renderBiomeLegend(); loadLayers(token);
    status(`Biome map: seed ${$("seed").value}, ${$("dimension").value}, Cubiomes version ${d.mc}` +
           (d.mc !== d.requested ? ` (closest to ${d.requested})` : "") +
           `. Hover a chunk for its biomes, click it to analyze its blocks, drag to pan, scroll to zoom.`);
  } catch (e) {
    if (token === mv.token) {
      $("maploading").classList.add("hide");
      if (!mv.data) {
        $("blegend").innerHTML = '<div class="empty">Press Show on map to draw the biomes around X and Z.</div>';
        renderLayers();
      }
      status(e.message, "err");
    }
  }
}

function buildImage() {
  const d = mv.data;
  const cv = document.createElement("canvas");
  cv.width = d.w; cv.height = d.h;
  const g = cv.getContext("2d"), im = g.createImageData(d.w, d.h);
  for (let i = 0; i < d.bytes.length; i++) {
    const id = d.bytes[i], rgb = d.pal.get(id).rgb;
    const f = (mv.hl === null || id === mv.hl) ? 1 : 0.28, o = i * 4;
    im.data[o] = rgb[0] * f; im.data[o + 1] = rgb[1] * f; im.data[o + 2] = rgb[2] * f; im.data[o + 3] = 255;
  }
  g.putImageData(im, 0, 0);
  mv.img = cv;
}

function topLeft() { const p = LEVELS[mv.lvl]; return {x: mv.bx - mapW / p / 2, z: mv.bz - mapH / p / 2}; }

function paintMap() {
  const d = mv.data;
  if (!d) return;
  const g = bmap.getContext("2d"), p = LEVELS[mv.lvl], t = topLeft();
  g.imageSmoothingEnabled = false;
  g.fillStyle = "#161616"; g.fillRect(0, 0, mapW, mapH);
  g.drawImage(mv.img, (d.bx0 - t.x) * p, (d.bz0 - t.z) * p, d.w * d.step * p, d.h * d.step * p);
  paintOver();
}

function label(g, text, x, y, align) {
  g.font = "12px " + css("--mono"); g.textAlign = align || "left"; g.textBaseline = "alphabetic";
  g.lineWidth = 3; g.strokeStyle = "rgba(0,0,0,.8)"; g.strokeText(text, x, y);
  g.fillStyle = "#fff"; g.fillText(text, x, y);
}

const NICE = [10, 20, 50, 100, 200, 500, 1000, 2000, 5000, 10000, 20000, 50000, 100000, 200000, 500000, 1000000];

function paintOver() {
  const g = bover.getContext("2d"), p = LEVELS[mv.lvl], t = topLeft();
  g.clearRect(0, 0, mapW, mapH);
  if (!mv.data) return;
  drawSlime(g, p, t);
  if (p >= 0.75) {   // chunk grid
    g.strokeStyle = "rgba(0,0,0,.22)"; g.lineWidth = 1; g.beginPath();
    for (let c = Math.ceil(t.x / 16); (c * 16 - t.x) * p <= mapW; c++) {
      const px = Math.round((c * 16 - t.x) * p) + .5; g.moveTo(px, 0); g.lineTo(px, mapH);
    }
    for (let c = Math.ceil(t.z / 16); (c * 16 - t.z) * p <= mapH; c++) {
      const pz = Math.round((c * 16 - t.z) * p) + .5; g.moveTo(0, pz); g.lineTo(mapW, pz);
    }
    g.stroke();
  }
  const ox = -t.x * p, oz = -t.z * p;   // world origin
  if (ox > -12 && ox < mapW + 12 && oz > -12 && oz < mapH + 12) {
    g.strokeStyle = "#3ecf6e"; g.lineWidth = 2; g.beginPath();
    g.moveTo(ox - 8, oz); g.lineTo(ox + 8, oz); g.moveTo(ox, oz - 8); g.lineTo(ox, oz + 8); g.stroke();
    label(g, "0, 0", ox + 10, oz - 8);
  }
  drawMarkers(g, p, t);
  if (mv.hover) {
    let x = (mv.hover.cx * 16 - t.x) * p, y = (mv.hover.cz * 16 - t.z) * p, s = 16 * p;
    if (s < 7) { x -= (7 - s) / 2; y -= (7 - s) / 2; s = 7; }
    g.strokeStyle = "#3ecf6e"; g.lineWidth = 2; g.strokeRect(x + 1, y + 1, s - 2, s - 2);
  }
  const nice = NICE.find(n => n * p >= 80) || NICE[NICE.length - 1], len = nice * p, bx = 16, by = mapH - 18;
  for (const [w, c] of [[5, "rgba(0,0,0,.8)"], [2, "#fff"]]) {
    g.strokeStyle = c; g.lineWidth = w; g.beginPath();
    g.moveTo(bx, by - 5); g.lineTo(bx, by); g.lineTo(bx + len, by); g.lineTo(bx + len, by - 5); g.stroke();
  }
  label(g, nice.toLocaleString() + " blocks", bx, by - 10);
}

function blockAt(e) {
  const r = bover.getBoundingClientRect(), p = LEVELS[mv.lvl], t = topLeft();
  const px = (e.clientX - r.left) * mapW / r.width, pz = (e.clientY - r.top) * mapH / r.height;
  const fx = t.x + px / p, fz = t.z + pz / p;
  const bx = Math.floor(fx), bz = Math.floor(fz);
  return {fx, fz, px, pz, bx, bz, cx: bx >> 4, cz: bz >> 4};
}

function biomeIdAt(bx, bz) {
  const d = mv.data, i = Math.floor((bx - d.bx0) / d.step), j = Math.floor((bz - d.bz0) / d.step);
  if (i < 0 || j < 0 || i >= d.w || j >= d.h) return null;
  return d.bytes[j * d.w + i];
}

function chunkBiomes(cx, cz) {
  const d = mv.data, counts = new Map();
  const i0 = Math.floor((cx * 16 - d.bx0) / d.step), i1 = Math.floor((cx * 16 + 15 - d.bx0) / d.step);
  const j0 = Math.floor((cz * 16 - d.bz0) / d.step), j1 = Math.floor((cz * 16 + 15 - d.bz0) / d.step);
  for (let j = j0; j <= j1; j++) for (let i = i0; i <= i1; i++) {
    if (i < 0 || j < 0 || i >= d.w || j >= d.h) continue;
    const id = d.bytes[j * d.w + i];
    counts.set(id, (counts.get(id) || 0) + 1);
  }
  const total = [...counts.values()].reduce((a, b) => a + b, 0);
  return {total, list: [...counts.entries()].sort((a, b) => b[1] - a[1])};
}

function showTip(e, c) {
  const tip = $("tip"), d = mv.data, cb = chunkBiomes(c.cx, c.cz);
  if (!cb.total) { tip.style.display = "none"; return; }
  tip.innerHTML = `<b>Chunk (${c.cx}, ${c.cz})</b><div class="xz">x ${c.cx * 16}..${c.cx * 16 + 15}, z ${c.cz * 16}..${c.cz * 16 + 15}</div>` +
    cb.list.map(([id, n]) => `<div class="bl"><span class="sw" style="background:${d.pal.get(id).color}"></span>` +
      `${d.pal.get(id).name}<span class="pc">${Math.round(n / cb.total * 100)}%</span></div>`).join("") +
    (d.step > 16 ? `<div class="xz">zoomed out: one sample per ${d.step} blocks</div>` : "") +
    `<div class="go">Click to analyze blocks</div>`;
  tip.style.display = "block";
  const wr = $("mapwrap").getBoundingClientRect();
  let left = e.clientX - wr.left + 16, top = e.clientY - wr.top + 16;
  if (left + tip.offsetWidth > wr.width) left = e.clientX - wr.left - tip.offsetWidth - 16;
  if (top + tip.offsetHeight > wr.height) top = e.clientY - wr.top - tip.offsetHeight - 16;
  tip.style.left = Math.max(0, left) + "px"; tip.style.top = Math.max(0, top) + "px";
}
function hideTip() { $("tip").style.display = "none"; }

function viewInside() {
  const d = mv.data, p = LEVELS[mv.lvl], t = topLeft(), vw = mapW / p, vh = mapH / p;
  const mx = vw * 0.03, mz = vh * 0.03;
  return d.step === sampleStep(p) && t.x >= d.bx0 + mx && t.x + vw <= d.bx0 + d.w * d.step - mx &&
         t.z >= d.bz0 + mz && t.z + vh <= d.bz0 + d.h * d.step - mz;
}

function analyzeChunk(cx, cz) {
  $("x").value = cx * 16 + 8; $("z").value = cz * 16 + 8;
  hideTip();
  doScan();
}

// ---- structure / slime-chunk layers: right-hand panel, everything off until clicked ----
const st = {types: [], items: {}, enabled: {}, slime: false, slimeData: null, note: "", tok: 0};
const MARKSZ = 24;   // on-screen icon size in px: constant, so icons stay readable at every zoom level
const poly = (g, p) => { g.beginPath(); g.moveTo(p[0], p[1]); for (let i = 2; i < p.length; i += 2) g.lineTo(p[i], p[i + 1]); g.closePath(); g.fill(); };
const ring = (g, r, w) => { g.lineWidth = w; g.beginPath(); g.arc(16, 16, r, 0, 6.2832); g.stroke(); };
const portal = g => { g.beginPath(); g.rect(9, 7, 14, 18); g.rect(12.5, 10.5, 7, 11); g.fill("evenodd"); };
const GLYPH = {   // simple pictograms on a 32x32 grid, drawn on a coloured disc
  village: g => { poly(g, [8, 17, 16, 8, 24, 17]); g.fillRect(10, 17, 12, 8); },
  desert_pyramid: g => poly(g, [7, 24, 16, 8, 25, 24]),
  jungle_pyramid: g => { g.fillRect(8, 21, 16, 4); g.fillRect(11, 16, 10, 4); g.fillRect(14, 11, 4, 4); },
  swamp_hut: g => { poly(g, [11, 18, 16, 6, 21, 18]); g.fillRect(8, 18, 16, 3); g.fillRect(12, 22, 8, 3); },
  igloo: g => { g.beginPath(); g.arc(16, 23, 9, Math.PI, 0); g.fill(); },
  ocean_ruin: g => { g.fillRect(8, 12, 4, 13); g.fillRect(14, 16, 4, 9); g.fillRect(20, 9, 4, 16); },
  shipwreck: g => { poly(g, [7, 19, 25, 19, 21, 25, 11, 25]); g.fillRect(15.5, 8, 1.6, 11); poly(g, [18, 9, 18, 18, 24, 18]); },
  monument: g => poly(g, [16, 6, 26, 16, 16, 26, 6, 16]),
  mansion: g => { poly(g, [5, 15, 11, 8, 21, 8, 27, 15]); g.fillRect(7, 15, 18, 10); },
  pillager_outpost: g => { g.fillRect(12, 12, 8, 13); g.fillRect(10, 8, 3, 4); g.fillRect(14.5, 8, 3, 4); g.fillRect(19, 8, 3, 4); },
  ruined_portal: portal, ruined_portal_nether: portal,
  amethyst_geode: g => poly(g, [16, 6, 24, 13, 20, 25, 12, 25, 8, 13]),
  desert_well: g => { g.fillRect(9, 9, 2.5, 8); g.fillRect(20.5, 9, 2.5, 8); g.fillRect(8, 7, 16, 3); g.fillRect(9, 17, 14, 8); },
  ancient_city: g => { ring(g, 8, 3); g.beginPath(); g.arc(16, 16, 2.5, 0, 6.2832); g.fill(); },
  trail_ruins: g => { g.fillRect(8, 9, 7, 5); g.fillRect(17, 9, 7, 5); g.fillRect(12, 15, 8, 5); g.fillRect(8, 21, 7, 4); g.fillRect(17, 21, 7, 4); },
  trial_chambers: g => { g.lineWidth = 3; g.strokeRect(9, 9, 14, 14); g.fillRect(14, 14, 4, 4); },
  stronghold: g => { g.lineWidth = 2.5; g.beginPath(); g.ellipse(16, 16, 10, 6, 0, 0, 6.2832); g.stroke(); g.beginPath(); g.arc(16, 16, 3.5, 0, 6.2832); g.fill(); },
  spawn: g => { const q = []; for (let i = 0; i < 10; i++) { const a = -Math.PI / 2 + i * Math.PI / 5, r = i % 2 ? 4.5 : 11; q.push(16 + r * Math.cos(a), 16.5 + r * Math.sin(a)); } poly(g, q); },
  fortress: g => { g.fillRect(8, 13, 16, 12); g.fillRect(8, 8, 4, 5); g.fillRect(14, 8, 4, 5); g.fillRect(20, 8, 4, 5); },
  bastion_remnant: g => poly(g, [8, 23, 24, 23, 20, 11, 12, 11]),
  end_city: g => { g.fillRect(13, 14, 6, 11); poly(g, [10, 14, 16, 6, 22, 14]); },
  end_gateway: g => { ring(g, 8, 3); ring(g, 3, 2); },
  __slime: (g, bg) => { g.fillRect(8, 9, 16, 15); g.fillStyle = bg; g.fillRect(11, 13, 3, 3); g.fillRect(18, 13, 3, 3); g.fillRect(13, 19, 6, 2); },
};
const SPR = {};
function sprite(id, color) {
  if (SPR[id]) return SPR[id];
  const cv = document.createElement("canvas"); cv.width = cv.height = 64;
  const g = cv.getContext("2d"); g.scale(2, 2);
  g.beginPath(); g.arc(16, 16, 14.5, 0, 6.2832); g.fillStyle = color; g.fill();
  g.lineWidth = 2; g.strokeStyle = "rgba(0,0,0,.85)"; g.stroke();
  const n = parseInt(color.slice(1), 16), lum = .299 * (n >> 16) + .587 * ((n >> 8) & 255) + .114 * (n & 255);
  g.fillStyle = g.strokeStyle = lum > 150 ? "#141414" : "#ffffff";
  (GLYPH[id] || (x => { x.beginPath(); x.arc(16, 16, 4, 0, 6.2832); x.fill(); }))(g, color);
  cv.url = cv.toDataURL();
  return (SPR[id] = cv);
}

function renderLayers() {
  const el = $("sbody");
  if (!mv.data) { el.innerHTML = '<div class="empty">Press Show on map, then click a structure to show it on the map.</div>'; return; }
  const f = $("sfilter").value.trim().toLowerCase(), list = st.types.slice();
  if ($("dimension").value === "overworld") list.push({id: "__slime", label: "Slime chunks", color: "#5fd35f"});
  el.innerHTML = list.filter(t => t.label.toLowerCase().includes(f)).map(t => {
    const on = t.id === "__slime" ? st.slime : !!st.enabled[t.id];
    const cnt = !on || t.id === "__slime" ? "" : t.skipped ? "zoom in" : (st.items[t.id] || []).length;
    return `<div class="row ${on ? "sel" : "off"}" tabindex="0" data-id="${t.id}">` +
           `<img class="ico" src="${sprite(t.id, t.color).url}" alt=""><span class="name">${t.label}</span><span class="cnt">${cnt}</span></div>`;
  }).join("") || '<div class="empty">No structures match.</div>';
  if (st.note) el.insertAdjacentHTML("beforeend", `<div class="snote">${st.note}</div>`);
}
function toggleLayer(id) {
  if (id === "__slime") { st.slime = !st.slime; if (st.slime) loadSlime(); else st.slimeData = null; }
  else { st.enabled[id] = !st.enabled[id]; if (st.enabled[id]) loadLayers(mv.token); }
  renderLayers(); paintOver();
}
$("sbody").addEventListener("click", e => { const r = e.target.closest(".row"); if (r) toggleLayer(r.dataset.id); });
$("sbody").addEventListener("keydown", e => {
  if (e.key === "Enter" || e.key === " ") { const r = e.target.closest(".row"); if (r) { e.preventDefault(); toggleLayer(r.dataset.id); } }
});
$("sfilter").addEventListener("input", renderLayers);

function regionBounds() { const d = mv.data; return {x0: d.bx0, z0: d.bz0, x1: d.bx0 + d.w * d.step, z1: d.bz0 + d.h * d.step}; }

async function loadLayers(token) {
  const b = regionBounds(), tk = ++st.tok;
  const want = Object.keys(st.enabled).filter(k => st.enabled[k]).join(",");
  const q = new URLSearchParams({seed: $("seed").value, version: $("version").value, dimension: $("dimension").value,
                                 x0: b.x0, z0: b.z0, x1: b.x1, z1: b.z1, types: want});
  try {
    const res = await fetch("api/structures?" + q), d = await res.json();
    if (!res.ok) throw new Error(d.error || "Structure request failed.");
    if (tk !== st.tok || token !== mv.token) return;
    st.types = d.types; st.items = d.items;
    st.note = d.types.some(t => t.skipped && st.enabled[t.id]) ? "Some structures need more zoom to load." : "";
  } catch (e) {
    if (tk !== st.tok) return;
    st.types = []; st.items = {}; st.note = "Structures unavailable: " + e.message;
  }
  if (st.slime) await loadSlime();
  renderLayers(); paintOver();
}

async function loadSlime() {
  if (!mv.data || $("dimension").value !== "overworld") return;
  if (LEVELS[mv.lvl] < 0.25) { st.slimeData = null; st.note = "Zoom in to see slime chunks."; renderLayers(); return; }
  const b = regionBounds(), cx0 = Math.floor(b.x0 / 16), cz0 = Math.floor(b.z0 / 16);
  const q = new URLSearchParams({seed: $("seed").value, cx0, cz0,
                                 w: Math.ceil(b.x1 / 16) - cx0 + 1, h: Math.ceil(b.z1 / 16) - cz0 + 1});
  try {
    const res = await fetch("api/slime?" + q), d = await res.json();
    if (!res.ok) throw new Error(d.error);
    const bin = atob(d.grid), bytes = new Uint8Array(bin.length);
    for (let i = 0; i < bin.length; i++) bytes[i] = bin.charCodeAt(i);
    st.slimeData = {cx0: d.cx0, cz0: d.cz0, w: d.w, h: d.h, bytes};
    if (st.note.startsWith("Zoom in to see slime")) st.note = "";
  } catch (e) { st.slimeData = null; st.note = e.message; }
  renderLayers(); paintOver();
}

function drawSlime(g, p, t) {
  const d = st.slimeData;
  if (!st.slime || !d || p < 0.25) return;
  g.fillStyle = "rgba(111,220,111,.45)";
  for (let j = 0; j < d.h; j++) for (let i = 0; i < d.w; i++) {
    if (!d.bytes[j * d.w + i]) continue;
    g.fillRect(((d.cx0 + i) * 16 - t.x) * p, ((d.cz0 + j) * 16 - t.z) * p, 16 * p, 16 * p);
  }
}

function drawMarkers(g, p, t) {
  const h = MARKSZ / 2;
  g.imageSmoothingEnabled = true; g.imageSmoothingQuality = "high";
  for (const ty of st.types) {
    if (!st.enabled[ty.id]) continue;
    const img = sprite(ty.id, ty.color), seen = new Set();
    for (const [x, z] of (st.items[ty.id] || [])) {
      const sx = (x - t.x) * p, sz = (z - t.z) * p;
      if (sx < -h || sz < -h || sx > mapW + h || sz > mapH + h) continue;
      const key = (Math.floor(sx / MARKSZ) + 64) * 1024 + Math.floor(sz / MARKSZ) + 64;
      if (seen.has(key)) continue;
      seen.add(key);
      g.drawImage(img, sx - h, sz - h, MARKSZ, MARKSZ);
    }
  }
}

function markerNear(c) {
  const tol = (MARKSZ / 2) / LEVELS[mv.lvl];
  let best = null, bd = tol * tol;
  for (const ty of st.types) {
    if (!st.enabled[ty.id]) continue;
    for (const [x, z] of (st.items[ty.id] || [])) {
      const dd = (x - c.bx) ** 2 + (z - c.bz) ** 2;
      if (dd <= bd) { bd = dd; best = {label: ty.label, x, z}; }
    }
  }
  return best;
}
renderLayers();

bover.addEventListener("mousemove", e => {
  if (!mv.data || mv.drag) return;
  const c = blockAt(e);
  if (!mv.hover || mv.hover.cx !== c.cx || mv.hover.cz !== c.cz) { mv.hover = {cx: c.cx, cz: c.cz}; paintOver(); }
  showTip(e, c);
  const id = biomeIdAt(c.bx, c.bz);
  const m = markerNear(c);
  $("mcap").textContent = m ? `${m.label} at x ${m.x}, z ${m.z}` :
                          id === null ? "" : `x ${c.bx}, z ${c.bz}: ${mv.data.pal.get(id).name}`;
});
bover.addEventListener("mouseleave", () => { mv.hover = null; hideTip(); paintOver(); });
bover.addEventListener("mousedown", e => {
  if (e.button !== 0 || !mv.data) return;
  mv.drag = {sx: e.clientX, sy: e.clientY, bx: mv.bx, bz: mv.bz, moved: false};
});
window.addEventListener("mousemove", e => {
  const dr = mv.drag;
  if (!dr) return;
  const k = mapW / bover.getBoundingClientRect().width, p = LEVELS[mv.lvl];
  const dx = (e.clientX - dr.sx) * k, dy = (e.clientY - dr.sy) * k;
  if (!dr.moved && Math.hypot(dx, dy) < 4) return;
  dr.moved = true; bover.style.cursor = "grabbing";
  mv.hover = null; hideTip();
  mv.bx = dr.bx - dx / p; mv.bz = dr.bz - dy / p;
  paintMap();
});
window.addEventListener("mouseup", e => {
  const dr = mv.drag;
  if (!dr) return;
  mv.drag = null; bover.style.cursor = "grab";
  if (dr.moved) { if (!viewInside()) fetchRegion(); }
  else { const c = blockAt(e); analyzeChunk(c.cx, c.cz); }
});
bover.addEventListener("wheel", e => {
  e.preventDefault();
  const now = Date.now();
  if (now - mv.wt < 70) return;
  const n = mv.lvl + (e.deltaY < 0 ? 1 : -1);
  if (n < 0 || n >= LEVELS.length) return;
  mv.wt = now;
  const c = blockAt(e), p = LEVELS[n];       // keep the block under the cursor fixed
  mv.lvl = n;
  mv.bx = c.fx - (c.px - mapW / 2) / p;
  mv.bz = c.fz - (c.pz - mapH / 2) / p;
  $("mzoom").value = n;
  mv.hover = null; hideTip();
  if (mv.data) { paintMap(); clearTimeout(mv.zt); mv.zt = setTimeout(fetchRegion, 200); }
}, {passive: false});

new ResizeObserver(() => {
  const w = $("mapwrap").clientWidth, h = $("mapwrap").clientHeight;
  if (w < 50 || h < 50 || (w === mapW && h === mapH)) return;
  mapW = w; mapH = h;
  bmap.width = bover.width = w; bmap.height = bover.height = h;
  paintMap();
  clearTimeout(mv.rt);
  mv.rt = setTimeout(() => { if (mv.data && !viewInside()) fetchRegion(); }, 250);
}).observe($("mapwrap"));

function renderBiomeLegend() {
  const d = mv.data;
  if (!d) return;
  const f = $("bfilter").value.trim().toLowerCase(), total = d.bytes.length;
  const rows = [...d.counts.entries()].map(([id, c]) => ({id, c, p: d.pal.get(id)}))
    .filter(r => r.p.name.includes(f)).sort((a, b) => b.c - a.c);
  const max = rows.length ? rows[0].c : 1;
  $("blegend").innerHTML = rows.map(r => `
    <div class="row ${mv.hl === r.id ? "sel" : ""}" tabindex="0" data-id="${r.id}">
      <span class="sw" style="background:${r.p.color}"></span>
      <span class="name">${r.p.name}</span>
      <span class="cnt">${(r.c / total * 100).toFixed(1)}%</span>
      <span class="bar" style="width:${Math.max(1, r.c / max * 100)}%"></span>
    </div>`).join("") || '<div class="empty">No biomes match.</div>';
}
function toggleHighlight(id) {
  mv.hl = mv.hl === id ? null : id;
  buildImage(); paintMap(); renderBiomeLegend();
}
$("blegend").addEventListener("click", e => { const r = e.target.closest(".row"); if (r) toggleHighlight(+r.dataset.id); });
$("blegend").addEventListener("keydown", e => {
  if (e.key === "Enter" || e.key === " ") { const r = e.target.closest(".row"); if (r) { e.preventDefault(); toggleHighlight(+r.dataset.id); } }
});
$("bfilter").oninput = renderBiomeLegend;
$("my").addEventListener("keydown", e => { if (e.key === "Enter") showMap(); });
$("mzoom").onchange = () => {
  const c = {bx: mv.bx, bz: mv.bz};
  mv.lvl = parseInt($("mzoom").value, 10);
  if (mv.data) { paintMap(); fetchRegion(); }
};
$("locate").onclick = showMap;
$("mode-map").onclick = () => setMode("map");
$("mode-scan").onclick = () => setMode("scan");
$("mode-explore").onclick = () => setMode("explore");

// switching dimension invalidates everything on screen: clear it and reload with the loading animation
$("dimension").addEventListener("change", () => {
  const hadScan = scanData !== null;
  if ((mode === "scan" || mode === "explore") && hadScan) doScan(mode);
  else { scanTok++; scanReset(false); }
  if (mv.data) showMap();
});

// themed up/down stepper for the top-bar number inputs
function addStepper(inp) {
  const w = document.createElement("span");
  w.className = "num";
  inp.parentNode.insertBefore(w, inp);
  w.appendChild(inp);
  const mk = (dir, d) => {
    const b = document.createElement("button");
    b.type = "button"; b.tabIndex = -1; b.setAttribute("aria-label", dir > 0 ? "Increase" : "Decrease");
    b.innerHTML = `<svg viewBox="0 0 10 10"><path d="${d}"/></svg>`;
    b.onclick = () => {
      if (inp.value === "") inp.value = 0;
      dir > 0 ? inp.stepUp() : inp.stepDown();
      inp.dispatchEvent(new Event("input", {bubbles: true}));
      inp.dispatchEvent(new Event("change", {bubbles: true}));
    };
    return b;
  };
  const st = document.createElement("span");
  st.className = "stp";
  st.append(mk(1, "M2 6.5 5 3.5 8 6.5"), mk(-1, "M2 3.5 5 6.5 8 3.5"));
  w.appendChild(st);
}
["x", "z", "my"].forEach(id => addStepper($(id)));

init();
</script>
</body>
</html>
"""




def main():
    global ARGS
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--port", type=int, default=8080)
    ap.add_argument("--dir", default=str(DEFAULT_DIR),
                    help="Where versions, textures and the biome engine are stored (default: mcseed next to web.py)")
    ap.add_argument("--no-browser", action="store_true", help="Don't open the browser automatically")
    ARGS = ap.parse_args()
    Path(ARGS.dir).mkdir(parents=True, exist_ok=True)

    update_cubiomes_if_newer(ARGS.dir)

    try:
        server = ThreadingHTTPServer(("127.0.0.1", ARGS.port), Handler)
    except OSError as e:
        sys.exit(f"Can't use port {ARGS.port} ({e}). Try:  python web.py --port 8081")
    url = f"http://localhost:{ARGS.port}"
    print(f"Chunk Scanner running at {url}  (Ctrl+C to stop)")
    if not ARGS.no_browser:
        threading.Timer(0.7, lambda: webbrowser.open(url)).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nStopped.")
    finally:
        server.server_close()


if __name__ == "__main__":
    main()
