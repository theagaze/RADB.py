#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Projetor Remote - controle de Android TV via ADB Wi-Fi.

Tema noturno em estilo liquid glass (aproximado com Tk), animacoes elasticas,
espelho ao vivo via scrcpy + ffmpeg e layout adaptavel a telas pequenas.
Arquivo unico. Somente biblioteca padrao + Tkinter (certifi e opcional).
Log de erros: cache/log.txt
"""

import base64
import collections
import hashlib
import json
import math
import os
import queue
import re
import shutil
import socket
import ssl
import struct
import subprocess
import threading
import time
import traceback
import urllib.request
import uuid
import zipfile
from pathlib import Path

import tkinter as tk
import tkinter.font as tkfont
from tkinter import filedialog, messagebox, simpledialog

# --------------------------------------------------------------------------- #
# Caminhos e configuracao
# --------------------------------------------------------------------------- #
BASE = Path(__file__).resolve().parent
CACHE = BASE / "cache"
CACHE.mkdir(parents=True, exist_ok=True)
PREFS_F = CACHE / "prefs.json"
FAVS_F = CACHE / "favs.json"
LOG_F = CACHE / "log.txt"
TVCTL_DEX = BASE / "tools" / "tvctl.dex"
REMOTE_TVCTL = "/data/local/tmp/tvctl.dex"
REMOTE_SCRCPY = "/data/local/tmp/scrcpy-server.jar"
PQ_FW = "/vendor/framework/droidlogic.software.core.jar"
SCRCPY_VER = "2.7"
SCRCPY_URL = (f"https://github.com/Genymobile/scrcpy/releases/download/v{SCRCPY_VER}/"
              f"scrcpy-server-v{SCRCPY_VER}")
SCRCPY_JAR = CACHE / f"scrcpy-server-v{SCRCPY_VER}.jar"
# SHA-256 do scrcpy-server v2.7 (confira com o SHA256SUMS.txt da release).
# Se mudar SCRCPY_VER, atualize este valor (ou ponha None para nao verificar).
SCRCPY_SHA256 = "a23c5659f36c260f105c022d27bcb3eafffa26070e7baa9eda66d01377a1adba"
FFMPEG_URLS = [
    "https://www.gyan.dev/ffmpeg/builds/ffmpeg-release-essentials.zip",
    "https://github.com/BtbN/FFmpeg-Builds/releases/latest/download/ffmpeg-master-latest-win64-gpl.zip",
]
MIRROR_W, MIRROR_H, MIRROR_FPS = 480, 270, 12
MIRROR_MAX_SIZE = 640
ALLOWED_ROOTS = ("/sdcard", "/storage/emulated/0", "/mnt/sdcard")
NOWIN = 0x08000000 if os.name == "nt" else 0

MEDIA_POLL_MS = 1500
TICK_MS = 250
FRAME_MS = 66
ENSURE_MIRROR_MS = 5000
SHOT_MS = 3000
VOL_POLL_MS = 5000
VOL_HOLD_S = 2.5

DEFAULT_PREFS = {"host": "192.168.100.12:5555", "dim": 0, "mirror": True, "kb": True, "base": None}
HOST_RE = re.compile(r"^[A-Za-z0-9._-]+(:\d{1,5})?$")


def log(msg):
    try:
        with open(LOG_F, "a", encoding="utf-8") as fh:
            fh.write(time.strftime("%d/%m %H:%M:%S ") + str(msg).rstrip() + "\n")
    except Exception:
        pass


def load_prefs():
    try:
        data = json.loads(PREFS_F.read_text(encoding="utf-8"))
        return {**DEFAULT_PREFS, **data}
    except Exception:
        return dict(DEFAULT_PREFS)


PREFS = load_prefs()
ADB_HOST = PREFS["host"]


def save_prefs():
    try:
        PREFS_F.write_text(json.dumps(PREFS, ensure_ascii=False, indent=1), encoding="utf-8")
    except Exception:
        log(traceback.format_exc())


KEY = {
    "UP": 19, "DOWN": 20, "LEFT": 21, "RIGHT": 22, "OK": 23, "HOME": 3, "BACK": 4,
    "VOL_UP": 24, "VOL_DOWN": 25, "POWER": 26, "MENU": 82, "MUTE": 164, "INFO": 165,
    "PLAY": 85, "STOP": 86, "NEXT": 87, "PREV": 88, "REW": 89, "FF": 90,
    "INPUT": 178, "SLEEP": 223, "WAKEUP": 224,
}

# --------------------------------------------------------------------------- #
# Tema noturno
# --------------------------------------------------------------------------- #
T = {
    "bg": "#05060A", "glass": "#131722", "glass_hi": "#1E2433", "edge": "#262C3D",
    "edge_hi": "#4A5470", "shadow": "#000000", "text": "#EEF1F8", "sub": "#8A93A8",
    "acc": "#7DA7FF", "acc2": "#A592FF", "ok": "#5FE3A6", "warn": "#FFB86B", "bad": "#FF6B7A",
}
FAM = "Segoe UI"
GLYPH = "Segoe UI Symbol"
SC = 1.0


def sz(n):
    return max(7, int(round(n * SC)))


def rgb(c):
    return int(c[1:3], 16), int(c[3:5], 16), int(c[5:7], 16)


def mix(a, b, t):
    t = max(0.0, min(1.0, t))
    ra, ga, ba = rgb(a)
    rb, gb, bb = rgb(b)
    return "#%02x%02x%02x" % (int(ra + (rb - ra) * t), int(ga + (gb - ga) * t), int(ba + (bb - ba) * t))


def rr(cv, x1, y1, x2, y2, r, **kw):
    r = max(0, min(r, (x2 - x1) / 2, (y2 - y1) / 2))
    pts = [x1 + r, y1, x2 - r, y1, x2, y1, x2, y1 + r, x2, y2 - r, x2, y2,
           x2 - r, y2, x1 + r, y2, x1, y2, x1, y2 - r, x1, y1 + r, x1, y1]
    return cv.create_polygon(pts, smooth=True, **kw)


def glass(cv, x1, y1, x2, y2, r, hov=0.0, acc=None, sel=False):
    fill = mix(T["glass"], T["glass_hi"], min(1.0, hov * 0.7 + (0.35 if sel else 0)))
    if acc:
        fill = mix(fill, acc, 0.16 + 0.12 * hov + (0.16 if sel else 0))
    rr(cv, x1, y1 + 3, x2, y2 + 3, r, fill=T["shadow"], outline="")
    rr(cv, x1, y1, x2, y2, r, fill=fill, outline=mix(T["edge"], T["edge_hi"], hov), width=1)
    rr(cv, x1 + 2, y1 + 2, x2 - 2, y1 + (y2 - y1) * 0.45, max(1, r - 2),
       fill=mix(fill, "#FFFFFF", 0.07), outline="")


# --------------------------------------------------------------------------- #
# Animacoes (um unico loop leve, resistente a widgets destruidos)
# --------------------------------------------------------------------------- #
def ease_cubic(t):
    return 1 - (1 - t) ** 3


def ease_back(t):
    c1 = 1.70158
    c3 = c1 + 1
    return 1 + c3 * (t - 1) ** 3 + c1 * (t - 1) ** 2


def ease_elastic(t):
    if t <= 0:
        return 0.0
    if t >= 1:
        return 1.0
    return 2 ** (-10 * t) * math.sin((t - 0.075) * 2 * math.pi / 0.3) + 1


_TW = []
_TW_ON = [False]
_ROOT = [None]


def tween(obj, attr, to, dur=0.4, ease=ease_cubic):
    _TW[:] = [t for t in _TW if not (t[0] is obj and t[1] == attr)]
    _TW.append([obj, attr, float(getattr(obj, attr)), float(to), time.monotonic(), dur, ease])
    if not _TW_ON[0] and _ROOT[0] is not None:
        _TW_ON[0] = True
        try:
            _ROOT[0].after(16, _frame)
        except Exception:
            _TW_ON[0] = False


def _frame():
    now = time.monotonic()
    keep, dirty = [], {}
    for t in list(_TW):
        obj, attr, a, b, t0, dur, ease = t
        k = (now - t0) / dur if dur > 0 else 1.0
        if k >= 1:
            val = b
        else:
            val = a + (b - a) * ease(max(0.0, k))
            keep.append(t)
        try:
            setattr(obj, attr, val)
            dirty[id(obj)] = obj
        except Exception:
            pass
    _TW[:] = keep
    for obj in dirty.values():
        try:
            obj.paint()
        except Exception:
            pass
    root = _ROOT[0]
    if _TW and root is not None:
        try:
            root.after(16, _frame)
            return
        except Exception:
            pass
    _TW_ON[0] = False


# --------------------------------------------------------------------------- #
# Utilitarios
# --------------------------------------------------------------------------- #
def trunc(text, n):
    text = text or ""
    return text if len(text) <= n else text[: n - 1] + "…"


def mmss(seconds):
    s = int(max(0, seconds or 0))
    return f"{s // 60:02d}:{s % 60:02d}"


def human(n):
    n = float(n or 0)
    for unit in ("B", "KB", "MB", "GB"):
        if n < 1024 or unit == "GB":
            return f"{n:.0f} B" if unit == "B" else f"{n:.1f} {unit}"
        n /= 1024


def shq(value):
    return "'" + str(value).replace("'", "'\\''") + "'"


def norm_remote(path):
    if not path:
        return None
    parts = []
    for part in ("/" + path.strip().lstrip("/")).split("/"):
        if part in ("", "."):
            continue
        if part == "..":
            if not parts:
                return None
            parts.pop()
            continue
        parts.append(part)
    clean = "/" + "/".join(parts)
    if not any(clean == r or clean.startswith(r + "/") for r in ALLOWED_ROOTS):
        return None
    return clean


def input_text_cmd(text):
    return "input text " + shq(text.replace(" ", "%s"))


def palette(key):
    cols = ["#7DA7FF", "#5FE3A6", "#FFB86B", "#FF6B7A", "#B98CFF", "#6FD6FF", "#FFD95A", "#8E97FF"]
    return cols[sum(map(ord, key)) % len(cols)]


def clamp(v, lo=0, hi=100):
    return max(lo, min(hi, v))


# --------------------------------------------------------------------------- #
# Rede (downloads)
# --------------------------------------------------------------------------- #
def _ssl_ctx(unverified=False):
    if unverified:
        return ssl._create_unverified_context()
    try:
        import certifi
        return ssl.create_default_context(cafile=certifi.where())
    except Exception:
        return ssl.create_default_context()


def open_url(url, timeout=60):
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 ProjetorRemote/1.0"})
    try:
        return urllib.request.urlopen(req, timeout=timeout, context=_ssl_ctx())
    except Exception as ex:
        reason = getattr(ex, "reason", ex)
        if isinstance(reason, ssl.SSLError) or "CERTIFICATE" in str(ex).upper():
            log("Certificado SSL nao verificado; tentando sem verificacao: " + str(ex))
            req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 ProjetorRemote/1.0"})
            return urllib.request.urlopen(req, timeout=timeout, context=_ssl_ctx(True))
        raise


def download(url, dest, progress=None, label="Baixando", min_size=10_000, sha256=None):
    dest = Path(dest)
    tmp = dest.with_name(dest.name + ".part")
    digest = hashlib.sha256()
    try:
        with open_url(url, timeout=90) as resp, open(tmp, "wb") as fh:
            total = int(resp.headers.get("Content-Length") or 0)
            got = 0
            while True:
                chunk = resp.read(256 * 1024)
                if not chunk:
                    break
                fh.write(chunk)
                digest.update(chunk)
                got += len(chunk)
                if progress:
                    progress(f"{label}… {got * 100 // total}%" if total else f"{label}… {human(got)}")
        if tmp.stat().st_size < min_size:
            raise RuntimeError(f"arquivo incompleto ({human(tmp.stat().st_size)})")
        if sha256 and digest.hexdigest() != sha256.lower():
            raise RuntimeError("SHA-256 do arquivo baixado nao confere (download corrompido ou adulterado)")
        tmp.replace(dest)
    except Exception:
        tmp.unlink(missing_ok=True)
        raise
    return dest


# --------------------------------------------------------------------------- #
# ADB
# --------------------------------------------------------------------------- #
def _run(args, timeout=45, binary=False):
    empty = b"" if binary else ""
    try:
        r = subprocess.run(args, capture_output=True, timeout=timeout, creationflags=NOWIN)
    except FileNotFoundError:
        return subprocess.CompletedProcess(args, 127, empty, "adb nao encontrado no PATH")
    except subprocess.TimeoutExpired:
        return subprocess.CompletedProcess(args, 124, empty, "tempo esgotado no ADB")
    if binary:
        return r
    return subprocess.CompletedProcess(args, r.returncode, r.stdout.decode("utf-8", "replace"),
                                       r.stderr.decode("utf-8", "replace"))


def adb(*args, timeout=45, binary=False):
    return _run(["adb", "-s", ADB_HOST, *args], timeout, binary)


def shell(cmd, timeout=60):
    return adb("shell", cmd, timeout=timeout)


def adb_devices_online():
    r = _run(["adb", "devices"], 12)
    for line in r.stdout.splitlines():
        parts = line.split()
        if len(parts) >= 2 and parts[0] == ADB_HOST and parts[1] == "device":
            return True
    return False


class KeyPipe:
    """Fallback de teclas: um `adb shell` aberto (sem espelho ativo)."""

    def __init__(self):
        self.q = queue.Queue()
        self.proc = None
        threading.Thread(target=self._loop, daemon=True).start()

    def send(self, cmd):
        self.q.put(cmd)

    def _open(self):
        try:
            self.proc = subprocess.Popen(["adb", "-s", ADB_HOST, "shell"], stdin=subprocess.PIPE,
                                         stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                                         creationflags=NOWIN)
        except Exception:
            self.proc = None

    def _loop(self):
        while True:
            cmd = self.q.get()
            for _ in range(2):
                if self.proc is None or self.proc.poll() is not None:
                    self._open()
                if self.proc is None:
                    break
                try:
                    self.proc.stdin.write((cmd + "\n").encode("utf-8"))
                    self.proc.stdin.flush()
                    break
                except Exception:
                    self.proc = None

    def close(self):
        p, self.proc = self.proc, None
        if p is not None:
            try:
                p.kill()
            except Exception:
                pass


class Coalescer:
    """Executa so o ultimo valor de cada chave (ex.: arrastar um slider)."""

    def __init__(self):
        self.lock = threading.Lock()
        self.pending = {}
        self.ev = threading.Event()
        threading.Thread(target=self._loop, daemon=True).start()

    def submit(self, key, fn, *args):
        with self.lock:
            self.pending[key] = (fn, args)
        self.ev.set()

    def _loop(self):
        while True:
            self.ev.wait()
            with self.lock:
                items = list(self.pending.values())
                self.pending.clear()
                self.ev.clear()
            for fn, args in items:
                try:
                    fn(*args)
                except Exception:
                    log(traceback.format_exc())


# --------------------------------------------------------------------------- #
# Ferramentas: ffmpeg e scrcpy-server
# --------------------------------------------------------------------------- #
def ffmpeg_bin():
    local = BASE / ("ffmpeg.exe" if os.name == "nt" else "ffmpeg")
    if local.exists():
        return str(local)
    return shutil.which("ffmpeg")


def install_ffmpeg(progress):
    """Baixa o build essencial do ffmpeg e extrai ffmpeg.exe na pasta do .py (Windows)."""
    if os.name != "nt":
        raise RuntimeError("instalacao automatica so no Windows (no Linux: sudo apt install ffmpeg)")
    zpath = CACHE / "ffmpeg.zip"
    last = None
    for url in FFMPEG_URLS:
        try:
            download(url, zpath, progress, "Baixando ffmpeg", min_size=5_000_000)
            last = None
            break
        except Exception as ex:
            last = ex
            log(f"ffmpeg: falha em {url}: {ex}\n{traceback.format_exc()}")
    if last is not None:
        raise RuntimeError(f"download do ffmpeg falhou ({last})")
    if not zipfile.is_zipfile(zpath):
        zpath.unlink(missing_ok=True)
        raise RuntimeError("o arquivo baixado nao e um zip valido")
    progress("Extraindo ffmpeg.exe…")
    with zipfile.ZipFile(zpath) as z:
        member = next((n for n in z.namelist() if n.lower().endswith("/bin/ffmpeg.exe")), None)
        if member is None:
            raise RuntimeError("ffmpeg.exe nao encontrado dentro do zip")
        with z.open(member) as src, open(BASE / "ffmpeg.exe", "wb") as dst:
            shutil.copyfileobj(src, dst)
    zpath.unlink(missing_ok=True)
    r = _run([str(BASE / "ffmpeg.exe"), "-version"], 20)
    if r.returncode != 0:
        raise RuntimeError("ffmpeg.exe extraido, mas nao executa")
    return r.stdout.splitlines()[0]


def _sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def ensure_scrcpy_jar(progress=None):
    if SCRCPY_JAR.exists() and SCRCPY_JAR.stat().st_size > 10_000:
        if not SCRCPY_SHA256 or _sha256_file(SCRCPY_JAR) == SCRCPY_SHA256.lower():
            return SCRCPY_JAR
        log("scrcpy-server em cache com SHA-256 diferente; baixando de novo")
        SCRCPY_JAR.unlink(missing_ok=True)
    download(SCRCPY_URL, SCRCPY_JAR, progress, "Baixando scrcpy-server", sha256=SCRCPY_SHA256)
    return SCRCPY_JAR


def install_live(progress):
    """Botao unico: garante ffmpeg e scrcpy-server. Retorna um resumo."""
    notes, errors = [], []
    try:
        ensure_scrcpy_jar(progress)
        notes.append("scrcpy-server ok")
    except Exception as ex:
        log(traceback.format_exc())
        errors.append(f"scrcpy: {ex}")
    if ffmpeg_bin():
        notes.append("ffmpeg ok")
    else:
        try:
            notes.append(install_ffmpeg(progress))
        except Exception as ex:
            log(traceback.format_exc())
            errors.append(f"ffmpeg: {ex}")
    if errors:
        raise RuntimeError(" | ".join(errors))
    return " · ".join(notes)


def push_scrcpy_jar(jar):
    size = jar.stat().st_size
    r = shell(f"stat -c %s {REMOTE_SCRCPY} 2>/dev/null", timeout=15)
    if r.stdout.strip() != str(size):
        p = adb("push", str(jar), REMOTE_SCRCPY, timeout=120)
        if p.returncode != 0:
            raise RuntimeError((p.stderr or "falha ao enviar scrcpy-server").strip())


def recv_exact(sock, n):
    buf = b""
    while len(buf) < n:
        chunk = sock.recv(n - len(buf))
        if not chunk:
            raise ConnectionError("conexao encerrada")
        buf += chunk
    return buf


def _drain_text(proc, dq):
    """Le a saida de um processo e guarda as ultimas linhas (para diagnostico)."""
    try:
        for raw in iter(proc.stdout.readline, b""):
            line = raw.decode("utf-8", "replace").strip()
            if line:
                dq.append(line)
    except Exception:
        pass


class Mirror:
    """Espelho ao vivo: servidor scrcpy no projetor, H.264 decodificado pelo ffmpeg.

    Ordem do protocolo scrcpy 2.x (tunnel_forward):
      1) conecta o socket de VIDEO e le 1 byte de sincronia
      2) conecta o socket de CONTROLE
      3) so entao o servidor envia 64 bytes (nome) + 12 bytes (codec/largura/altura) no video
    Teclas seguem pelo canal de controle (milissegundos)."""

    def __init__(self):
        self._lock = threading.Lock()
        self._fl = threading.Lock()
        self._state = "off"
        self._dead = False
        self._gen = 0
        self._stop_gen = 0
        self._frame = None
        self._seq = 0
        self._ctl_q = None
        self.port = None
        self.server = None
        self.ffmpeg = None
        self.sock_v = None
        self.sock_c = None
        self.error = ""
        self._vbytes = 0
        self.dev_w = 1280
        self.dev_h = 720
        self.srv_log = collections.deque(maxlen=12)
        self.ff_log = collections.deque(maxlen=12)

    @property
    def ready(self):
        return self._state == "on" and not self._dead

    def _tails(self):
        parts = []
        if self.srv_log:
            parts.append("servidor: " + " / ".join(list(self.srv_log)[-4:]))
        if self.ff_log:
            parts.append("ffmpeg: " + " / ".join(list(self.ff_log)[-4:]))
        return trunc(" | ".join(parts), 300)

    def start(self, progress=None):
        with self._lock:
            if self._state == "starting":
                return False
            if self._state == "on" and not self._dead:
                return True
            was_on = self._state == "on"
            self._state = "starting"
            token = self._stop_gen
        if was_on:
            self._teardown()
        try:
            self._launch(progress)
        except Exception as ex:
            self.error = str(ex)
            log("espelho: " + traceback.format_exc() + "\n" + self._tails())
            self._teardown()
            with self._lock:
                self._state = "off"
            return False
        with self._lock:
            if token != self._stop_gen:
                self._teardown()
                self._state = "off"
                return False
            # _dead NAO e zerado aqui: se o fluxo morreu logo apos o 1o frame, ready fica False
            # e o _ensure_mirror reinicia (antes ele ficava "pronto" com threads mortas).
            self._state = "on"
        self.error = ""
        return True

    def stop(self):
        with self._lock:
            self._stop_gen += 1
            self._state = "off"
        self._teardown()

    def latest(self):
        with self._fl:
            return self._frame, self._seq

    def send_keys(self, codes):
        q = self._ctl_q
        if not self.ready or q is None:
            return False
        parts = []
        for code in codes:
            parts.append(struct.pack(">BBIII", 0, 0, int(code), 0, 0))
            parts.append(struct.pack(">BBIII", 0, 1, int(code), 0, 0))
        q.put(b"".join(parts))
        return True

    def send_touch(self, action, x, y):
        """Envia mouse/cursor pelo scrcpy (0=down, 1=up, 2=move, 7=hover_move)."""
        q = self._ctl_q
        if not self.ready or q is None or not self.dev_w or not self.dev_h:
            return False
        x = max(0, min(self.dev_w - 1, int(x)))
        y = max(0, min(self.dev_h - 1, int(y)))
        a = int(action)
        pressure = 0xFFFF if a in (0, 2) else 0
        action_btn = 1 if a in (0, 1) else 0
        buttons = 1 if a in (0, 2) else 0
        msg = struct.pack(">BBqiiHHHII", 2, a, -1, x, y,
                          self.dev_w, self.dev_h, pressure, action_btn, buttons)
        q.put(msg)
        return True

    def send_text(self, txt):
        q = self._ctl_q
        if not self.ready or q is None:
            return False
        data = txt.encode("utf-8")[:300].decode("utf-8", "ignore").encode("utf-8")
        q.put(struct.pack(">BI", 1, len(data)) + data)
        return True

    def set_display_power(self, on):
        """Liga/desliga a saida de video do projetor sem parar os apps (igual ao
        `scrcpy --turn-screen-off`). Mensagem de controle tipo 10 + 1 byte."""
        q = self._ctl_q
        if not self.ready or q is None:
            return False
        q.put(struct.pack(">BB", 10, 1 if on else 0))
        return True

    def _mark_dead(self, gen):
        if gen == self._gen:
            self._dead = True

    def _teardown(self):
        self._dead = True
        q, self._ctl_q = self._ctl_q, None
        if q is not None:
            q.put(None)
        for s in (self.sock_v, self.sock_c):
            if s is not None:
                try:
                    s.close()
                except Exception:
                    pass
        for p in (self.ffmpeg, self.server):
            if p is not None:
                try:
                    p.kill()
                except Exception:
                    pass
        port, self.port = self.port, None
        if port:
            _run(["adb", "-s", ADB_HOST, "forward", "--remove", f"tcp:{port}"], 10)
        self.sock_v = self.sock_c = self.ffmpeg = self.server = None
        with self._fl:
            self._frame = None

    def _launch(self, progress=None):
        ff = ffmpeg_bin()
        if not ff:
            raise RuntimeError("ffmpeg nao encontrado (clique em Baixar transmissao ao vivo)")
        self._gen += 1
        gen = self._gen
        self._dead = False
        self.srv_log.clear()
        self.ff_log.clear()
        self._vbytes = 0
        push_scrcpy_jar(ensure_scrcpy_jar(progress))
        # remove servidor preso de tentativas anteriores
        shell("pkill -f 'com.genymobile.scrcpy.Serve[r]' 2>/dev/null; echo ok", timeout=10)

        scid = "%08x" % (uuid.uuid4().int & 0x7FFFFFFF)
        cmd = (f"CLASSPATH={REMOTE_SCRCPY} app_process / com.genymobile.scrcpy.Server {SCRCPY_VER} "
               f"scid={scid} log_level=info tunnel_forward=true control=true video=true audio=false "
               f"clipboard_autosync=false max_size={MIRROR_MAX_SIZE} max_fps={MIRROR_FPS} "
               f"video_bit_rate=2000000 video_codec=h264 "
               f"send_frame_meta=false send_codec_meta=true send_device_meta=true send_dummy_byte=true")
        self.server = subprocess.Popen(["adb", "-s", ADB_HOST, "shell", cmd], stdin=subprocess.DEVNULL,
                                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                       creationflags=NOWIN)
        threading.Thread(target=_drain_text, args=(self.server, self.srv_log), daemon=True).start()

        with socket.socket() as s:
            s.bind(("127.0.0.1", 0))
            self.port = s.getsockname()[1]
        r = _run(["adb", "-s", ADB_HOST, "forward", f"tcp:{self.port}", f"localabstract:scrcpy_{scid}"], 15)
        if r.returncode != 0:
            raise RuntimeError((r.stderr or "adb forward falhou").strip())

        # 1) video + byte de sincronia  2) controle  3) cabecalho (nome + codec)
        self.sock_v = self._connect_video()
        self.sock_c = self._connect_control()
        try:
            self.sock_v.settimeout(15)
            hdr = recv_exact(self.sock_v, 64 + 12)
            _codec, dw, dh = struct.unpack(">III", hdr[64:76])
            if dw > 0 and dh > 0:
                self.dev_w, self.dev_h = dw, dh
            self.sock_v.settimeout(None)
        except OSError as ex:
            time.sleep(0.3)
            raise RuntimeError(f"cabecalho do scrcpy nao chegou ({ex}). {self._tails()}")

        # IMPORTANTE: nao usar "-fflags +nobuffer" aqui. Com H.264 cru vindo de pipe ele faz o ffmpeg
        # descartar o keyframe lido no probe; o scrcpy so manda 1 keyframe no inicio => nenhuma imagem.
        # Tambem sem o filtro fps=: o H.264 cru nao tem timestamps e o max_fps do servidor ja limita.
        vf = (f"scale={MIRROR_W}:{MIRROR_H}:force_original_aspect_ratio=decrease:flags=fast_bilinear,"
              f"pad={MIRROR_W}:{MIRROR_H}:(ow-iw)/2:(oh-ih)/2:black")
        self.ffmpeg = subprocess.Popen(
            [ff, "-hide_banner", "-loglevel", "warning", "-fflags", "+discardcorrupt",
             "-flags", "low_delay", "-threads", "1", "-probesize", "4096", "-analyzeduration", "0",
             "-f", "h264", "-i", "pipe:0", "-an", "-sn", "-vf", vf,
             "-f", "rawvideo", "-pix_fmt", "rgb24", "pipe:1"],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, creationflags=NOWIN)
        # stderr do ffmpeg para diagnostico
        threading.Thread(target=self._drain_ff_err, daemon=True).start()
        self._ctl_q = queue.Queue()
        threading.Thread(target=self._pump_video, args=(gen,), daemon=True).start()
        threading.Thread(target=self._pump_frames, args=(gen,), daemon=True).start()
        threading.Thread(target=self._pump_control, args=(gen, self._ctl_q, self.sock_c), daemon=True).start()
        threading.Thread(target=self._drain_control, args=(gen,), daemon=True).start()

        # confirma que a imagem realmente chega
        t0 = time.time()
        while time.time() - t0 < 14:
            if self._dead:
                raise RuntimeError("o fluxo de video encerrou. " + self._tails())
            with self._fl:
                got = self._frame is not None
            if got:
                return
            time.sleep(0.1)
        raise RuntimeError(f"nenhuma imagem recebida em 14 s (video recebido do projetor: "
                           f"{self._vbytes} bytes). " + self._tails())

    def _drain_ff_err(self):
        ff = self.ffmpeg
        try:
            for raw in iter(ff.stderr.readline, b""):
                line = raw.decode("utf-8", "replace").strip()
                if line:
                    self.ff_log.append(line)
        except Exception:
            pass

    def _connect_video(self):
        deadline = time.time() + 25
        last = "sem resposta"
        while time.time() < deadline:
            if self.server.poll() is not None:
                time.sleep(0.3)
                raise RuntimeError("servidor scrcpy encerrou. " + self._tails())
            try:
                s = socket.create_connection(("127.0.0.1", self.port), timeout=3)
            except OSError as ex:
                last = str(ex)
                time.sleep(0.25)
                continue
            try:
                s.settimeout(3)
                recv_exact(s, 1)          # byte de sincronia (confirma que o servidor aceitou)
                s.settimeout(None)
                return s
            except OSError as ex:
                last = str(ex)
                s.close()
                time.sleep(0.3)
        raise RuntimeError(f"servidor scrcpy nao respondeu ({last}). " + self._tails())

    def _connect_control(self):
        for _ in range(30):
            try:
                s = socket.create_connection(("127.0.0.1", self.port), timeout=3)
                s.settimeout(None)
                return s
            except OSError:
                time.sleep(0.2)
        raise RuntimeError("canal de controle do scrcpy indisponivel")

    def _pump_video(self, gen):
        sock, ff = self.sock_v, self.ffmpeg
        try:
            while True:
                data = sock.recv(65536)
                if not data:
                    break
                self._vbytes += len(data)
                ff.stdin.write(data)
                ff.stdin.flush()
        except Exception:
            pass
        self._mark_dead(gen)

    def _pump_frames(self, gen):
        size = MIRROR_W * MIRROR_H * 3
        ff = self.ffmpeg
        try:
            while True:
                buf = ff.stdout.read(size)
                if len(buf) < size:
                    break
                with self._fl:
                    self._frame = buf
                    self._seq += 1
        except Exception:
            pass
        self._mark_dead(gen)

    def _pump_control(self, gen, q, sock):
        try:
            while True:
                msg = q.get()
                if msg is None:
                    break
                sock.sendall(msg)
        except Exception:
            pass
        self._mark_dead(gen)

    def _drain_control(self, gen):
        sock = self.sock_c
        try:
            while sock.recv(4096):
                pass
        except Exception:
            pass
        self._mark_dead(gen)


mirror = Mirror()

# --------------------------------------------------------------------------- #
# Imagem (PQ via tvctl) e volume
# --------------------------------------------------------------------------- #
_RESP_RE = re.compile(r"^(OK [bcs]|B=\d+ C=\d+ S=\d+( END)?|ERR.*)$")
IMG_CODE = {"brightness": "b", "contrast": "c", "saturation": "s"}


class PqController:
    def __init__(self):
        self._lock = threading.Lock()
        self._proc = None
        self._q = None
        self._deployed = False

    def _deploy(self):
        if self._deployed:
            return
        if not TVCTL_DEX.exists():
            raise RuntimeError("tools/tvctl.dex nao encontrado")
        size = TVCTL_DEX.stat().st_size
        r = shell(f"stat -c %s {REMOTE_TVCTL} 2>/dev/null", timeout=15)
        if r.stdout.strip() != str(size):
            p = adb("push", str(TVCTL_DEX), REMOTE_TVCTL, timeout=60)
            if p.returncode != 0:
                raise RuntimeError((p.stderr or "falha ao enviar tvctl.dex").strip())
        self._deployed = True

    @staticmethod
    def _pump(proc, q):
        try:
            for raw in iter(proc.stdout.readline, b""):
                q.put(raw.decode("utf-8", "replace").strip())
        except Exception:
            pass
        q.put(None)

    def _start(self):
        self._deploy()
        cmd = f"CLASSPATH={REMOTE_TVCTL}:{PQ_FW} app_process /system/bin com.tvctl.Server"
        proc = subprocess.Popen(["adb", "-s", ADB_HOST, "shell", cmd], stdin=subprocess.PIPE,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, creationflags=NOWIN)
        q = queue.Queue()
        threading.Thread(target=self._pump, args=(proc, q), daemon=True).start()
        deadline = time.time() + 15
        ready = False
        while time.time() < deadline:
            try:
                line = q.get(timeout=max(0.05, deadline - time.time()))
            except queue.Empty:
                break
            if line is None:
                break
            if line == "READY":
                ready = True
                break
        if not ready:
            try:
                proc.kill()
            except Exception:
                pass
            raise RuntimeError("tvctl nao iniciou")
        self._proc, self._q = proc, q

    def _stop(self):
        p, self._proc, self._q = self._proc, None, None
        if p is not None:
            try:
                p.kill()
            except Exception:
                pass

    def _request(self, cmd, timeout=6.0):
        with self._lock:
            for _ in range(2):
                try:
                    if self._proc is None or self._proc.poll() is not None:
                        self._stop()
                        self._start()
                    self._proc.stdin.write((cmd + "\n").encode())
                    self._proc.stdin.flush()
                    deadline = time.time() + timeout
                    while True:
                        left = deadline - time.time()
                        if left <= 0:
                            break
                        line = self._q.get(timeout=left)
                        if line is None:
                            break
                        if _RESP_RE.match(line):
                            return line
                except Exception:
                    pass
                self._stop()
            return None

    def state(self):
        line = self._request("g")
        m = re.search(r"B=(\d+) C=(\d+) S=(\d+)", line or "")
        if not m:
            return None
        return {"brightness": int(m.group(1)), "contrast": int(m.group(2)), "saturation": int(m.group(3))}

    def set(self, code, value):
        line = self._request(f"{code} {int(value)}")
        return bool(line and line.startswith("OK"))

    def close(self):
        with self._lock:
            self._stop()


pq = PqController()


def pq_set(kind, value):
    return pq.set(IMG_CODE[kind], clamp(int(value)))


def get_volume():
    r = shell("cmd media_session volume --stream 3 --get", timeout=20)
    m = re.search(r"volume is (\d+) in range \[(\d+)\.\.(\d+)\]", r.stdout or "")
    if not m:
        return None
    return {"level": int(m.group(1)), "max": int(m.group(3))}


def volume_set(level):
    return shell(f"cmd media_session volume --stream 3 --set {int(level)}", timeout=20).returncode == 0


_PB_LINE = re.compile(r"PlaybackState \{[^\n]*")
_PB_POS = re.compile(r"(?<!buffered )position=(-?\d+)")


def media_info():
    """Sessao ativa com posicao extrapolada: position + (agora - updated) * speed."""
    out = shell("dumpsys media_session; echo __UPTIME__; cat /proc/uptime", timeout=20).stdout or ""
    txt, _, up = out.partition("__UPTIME__")
    now_ms = None
    try:
        now_ms = float(up.split()[0]) * 1000.0
    except (IndexError, ValueError):
        pass
    states = []
    for m in _PB_LINE.finditer(txt):
        line = m.group(0)
        st = re.search(r"state=(\d+)", line)
        pos = _PB_POS.search(line)
        if not (st and pos):
            continue
        spd = re.search(r"speed=(-?[\d.]+)", line)
        upd = re.search(r"updated=(\d+)", line)
        states.append({"state": int(st.group(1)), "pos": int(pos.group(1)),
                       "speed": float(spd.group(1)) if spd else 1.0,
                       "upd": int(upd.group(1)) if upd else 0})
    chosen = next((s for s in states if s["state"] == 3), states[0] if states else None)
    info = {"playing": False, "pos": 0.0, "dur": 0.0, "title": "", "pkg": ""}
    if chosen:
        playing = chosen["state"] == 3
        pos = max(0, chosen["pos"]) / 1000.0
        if playing and now_ms and chosen["upd"]:
            elapsed = (now_ms - chosen["upd"]) / 1000.0
            if 0 <= elapsed < 600:
                pos += elapsed * (chosen["speed"] or 1.0)
        info["playing"] = playing
        info["pos"] = pos
    d = re.search(r"(?:android\.media\.metadata\.DURATION|duration)=(\d+)", txt)
    if d:
        info["dur"] = int(d.group(1)) / 1000.0
    t = re.search(r"description=([^\n,]+)", txt)
    if t:
        info["title"] = t.group(1).strip()
    p = re.search(r"package=([A-Za-z0-9_.]+)", txt)
    if p:
        info["pkg"] = p.group(1)
    return info


def screenshot_bytes():
    r = adb("exec-out", "screencap", "-p", timeout=25, binary=True)
    return r.stdout if r.returncode == 0 and r.stdout[:8] == b"\x89PNG\r\n\x1a\n" else None


def list_processes():
    r = shell("ps -A -o PID,NAME 2>/dev/null || ps", timeout=30)
    out = []
    for line in r.stdout.splitlines():
        parts = line.split()
        if len(parts) < 2 or not parts[0].isdigit():
            continue
        name = parts[-1]
        if name in ("NAME", "CMD") or name.startswith("["):
            continue
        out.append({"pid": int(parts[0]), "name": name})
    out.sort(key=lambda p: p["pid"])
    return out


def system_info():
    r = shell("getprop ro.product.model; getprop ro.build.version.release; df -h /sdcard | tail -n 1", timeout=20)
    return [ln.strip() for ln in r.stdout.splitlines() if ln.strip()]


def launchable_apps():
    apps, seen = [], set()
    for cat in ("LAUNCHER", "LEANBACK_LAUNCHER"):
        r = shell("cmd package query-activities --brief -a android.intent.action.MAIN "
                  f"-c android.intent.category.{cat}", timeout=30)
        for line in r.stdout.splitlines():
            line = line.strip()
            if "/" not in line or " " in line or line.startswith(("Activity", "priority", "cmd:")):
                continue
            pkg = line.split("/", 1)[0]
            if pkg in seen:
                continue
            seen.add(pkg)
            apps.append({"pkg": pkg, "activity": line})
    apps.sort(key=lambda a: a["pkg"])
    return apps


def list_dir(path):
    dir_arg = path if path.endswith("/") else path + "/"
    r = shell(f"ls -la {shq(dir_arg)} 2>&1", timeout=60)
    entries = []
    for line in r.stdout.splitlines():
        line = line.rstrip("\r")
        if not line or line.startswith(("total ", "ls:")):
            continue
        parts = line.split(None, 7)
        if len(parts) < 8:
            continue
        mode, size, name = parts[0], parts[4], parts[7]
        if name in (".", ".."):
            continue
        if " -> " in name:
            name = name.split(" -> ", 1)[0]
        try:
            size_i = int(size)
        except ValueError:
            size_i = 0
        entries.append({"name": name, "path": path.rstrip("/") + "/" + name,
                        "isDir": mode.startswith("d"), "size": size_i})
    entries.sort(key=lambda e: (not e["isDir"], e["name"].lower()))
    return entries, (r.stderr or "").strip()


def load_favs():
    try:
        data = json.loads(FAVS_F.read_text(encoding="utf-8")) if FAVS_F.exists() else []
        return set(data) if isinstance(data, list) else set()
    except Exception:
        return set()


def save_favs(favs):
    try:
        FAVS_F.write_text(json.dumps(sorted(favs)), encoding="utf-8")
    except Exception:
        log(traceback.format_exc())


# --------------------------------------------------------------------------- #
# Widgets de vidro
# --------------------------------------------------------------------------- #
class Glass(tk.Canvas):
    """Base: painel com animacao elastica de hover, pressao e clique confiavel."""

    def __init__(self, m, r=14, w=60, h=40, bg=None, click=None, acc=None, cursor="hand2"):
        super().__init__(m, width=w, height=h, highlightthickness=0, bd=0, bg=bg or T["bg"], cursor=cursor)
        self.r, self.click, self.acc = r, click, acc
        self.hov, self.prs = 0.0, 0.0
        self.sel = False
        self.enabled = True
        self._armed = False
        self.bind("<Enter>", lambda e: tween(self, "hov", 1.0, 0.3, ease_back))
        self.bind("<Leave>", self._leave)
        self.bind("<ButtonPress-1>", self._press)
        self.bind("<ButtonRelease-1>", self._release)
        self.bind("<Configure>", lambda e: self.paint())

    def _leave(self, _e):
        tween(self, "hov", 0.0, 0.3, ease_cubic)
        tween(self, "prs", 0.0, 0.6, ease_elastic)

    def _press(self, _e):
        self._armed = True
        tween(self, "prs", 1.0, 0.1, ease_cubic)

    def _release(self, e):
        tween(self, "prs", 0.0, 0.6, ease_elastic)
        inside = 0 <= e.x <= self.winfo_width() and 0 <= e.y <= self.winfo_height()
        fire = self._armed and inside and self.enabled and self.click is not None
        self._armed = False
        if fire:
            self.after_idle(self._fire)

    def _fire(self):
        try:
            self.click()
        except Exception as ex:
            log(traceback.format_exc())
            try:
                top = self.winfo_toplevel()
                if hasattr(top, "toast"):
                    top.toast(f"Erro: {trunc(str(ex), 70)}", "err")
            except Exception:
                pass

    def paint(self):
        self.delete("all")
        w, h = self.winfo_width(), self.winfo_height()
        if w < 4 or h < 4:
            return
        ins = self.prs * 2.5
        glass(self, ins, ins, w - ins, h - ins, self.r, self.hov, self.acc, self.sel)
        self.draw(w, h)

    def draw(self, w, h):
        pass


class Btn(Glass):
    def __init__(self, m, text="", glyph="", click=None, h=40, w=None, acc=None, bg=None,
                 size=11, big=False, fg=None):
        self.text, self.glyph, self.fsz, self.big = text, glyph, sz(size), big
        self.fg = fg or T["text"]
        ww = w or (sz(96) if big else max(sz(44), sz(26) + sz(8) * len(text) + (sz(24) if glyph else 0)))
        super().__init__(m, r=sz(16) if big else sz(h) // 2, w=ww, h=sz(h), bg=bg, click=click, acc=acc)

    def draw(self, w, h):
        cx, cy = w / 2, h / 2
        if self.big:
            self.create_text(cx, cy - h * 0.12, text=self.glyph, fill=self.fg, font=(GLYPH, int(self.fsz * 1.6)))
            self.create_text(cx, cy + h * 0.3, text=self.text, fill=T["sub"], font=(FAM, max(7, self.fsz - 2)))
        else:
            s = (self.glyph + "  " if self.glyph else "") + self.text
            font = (GLYPH, self.fsz + 1) if self.glyph and not self.text else (FAM, self.fsz, "bold")
            self.create_text(cx, cy, text=s, fill=self.fg, font=font)


class Toggle(tk.Canvas):
    def __init__(self, m, value=False, cb=None, bg=None):
        super().__init__(m, width=sz(52), height=sz(30), highlightthickness=0, bd=0,
                         bg=bg or T["glass"], cursor="hand2")
        self.v = bool(value)
        self.k = 1.0 if value else 0.0
        self.cb = cb
        self.bind("<Button-1>", self._tog)
        self.paint()

    def _tog(self, _e):
        self.v = not self.v
        tween(self, "k", 1.0 if self.v else 0.0, 0.55, ease_elastic)
        if self.cb:
            self.cb(self.v)

    def set(self, v):
        self.v = bool(v)
        self.k = 1.0 if self.v else 0.0
        self.paint()

    def paint(self):
        self.delete("all")
        W, H = sz(52), sz(30)
        rr(self, 0, 0, W, H, H / 2, fill=mix(T["edge"], T["ok"], clamp(self.k, 0, 1)), outline="")
        x = sz(4) + clamp(self.k, -0.1, 1.1) * (W - H)
        self.create_oval(x, sz(4), x + H - sz(8), H - sz(4), fill=T["text"], outline="")


class Slider(tk.Canvas):
    def __init__(self, m, on=None, on_end=None, bg=None, acc=None, h=30):
        super().__init__(m, height=sz(h), highlightthickness=0, bd=0, bg=bg or T["glass"], cursor="hand2")
        self.f = 0.0
        self.kr = float(sz(8))
        self.acc = acc or T["acc"]
        self.on, self.on_end = on, on_end
        self.drag = False
        self.enabled = True
        self.bind("<Configure>", lambda e: self.paint())
        self.bind("<ButtonPress-1>", self._down)
        self.bind("<B1-Motion>", self._move)
        self.bind("<ButtonRelease-1>", self._up)

    def set(self, f, anim=False):
        if self.drag:
            return
        f = clamp(f, 0.0, 1.0)
        if anim:
            tween(self, "f", f, 0.45, ease_back)
        else:
            self.f = f
            self.paint()

    def _at(self, x):
        pad = sz(12)
        return clamp((x - pad) / max(1, self.winfo_width() - 2 * pad), 0.0, 1.0)

    def _down(self, e):
        if not self.enabled:
            return
        self.drag = True
        tween(self, "kr", sz(11), 0.25, ease_back)
        self._set_drag(e.x)

    def _move(self, e):
        if self.drag and self.enabled:
            self._set_drag(e.x)

    def _set_drag(self, x):
        self.f = self._at(x)
        self.paint()
        if self.on:
            self.on(self.f)

    def _up(self, _e):
        if not self.drag:
            return
        self.drag = False
        tween(self, "kr", sz(8), 0.6, ease_elastic)
        if self.on_end:
            self.on_end(self.f)

    def paint(self):
        self.delete("all")
        w, h = self.winfo_width(), self.winfo_height()
        cy, pad = h / 2, sz(12)
        self.create_line(pad, cy, w - pad, cy, fill=T["edge"], width=sz(5), capstyle="round")
        x = pad + self.f * (w - 2 * pad)
        col = self.acc if self.enabled else T["sub"]
        self.create_line(pad, cy, x, cy, fill=col, width=sz(5), capstyle="round")
        self.create_oval(x - self.kr, cy - self.kr, x + self.kr, cy + self.kr, fill=T["text"], outline="")


class Card(tk.Frame):
    def __init__(self, m, title=None, **kw):
        super().__init__(m, bg=T["glass"], highlightbackground=T["edge"], highlightthickness=1, bd=0, **kw)
        if title:
            tk.Label(self, text=title.upper(), bg=T["glass"], fg=T["sub"],
                     font=(FAM, sz(8), "bold")).pack(anchor="w", padx=sz(14), pady=(sz(10), sz(4)))
        self.body = tk.Frame(self, bg=T["glass"])
        self.body.pack(fill="both", expand=True, padx=sz(12), pady=(0, sz(12)))


class Scroll(tk.Frame):
    """Pagina rolavel. Recebe o app e chama build() ao final."""

    def __init__(self, m, app):
        super().__init__(m, bg=T["bg"])
        self.app = app
        self.cv = tk.Canvas(self, bg=T["bg"], highlightthickness=0, bd=0)
        self.inner = tk.Frame(self.cv, bg=T["bg"])
        self.win = self.cv.create_window(0, 0, window=self.inner, anchor="nw")
        self.cv.pack(fill="both", expand=True)
        self.inner.bind("<Configure>", lambda e: self.cv.configure(scrollregion=self.cv.bbox("all")))
        self.cv.bind("<Configure>", lambda e: self.cv.itemconfigure(self.win, width=e.width))
        self.cv._wheel = lambda d: self.cv.yview_scroll(d * 2, "units")
        self.build()

    def build(self):
        pass


class RowList(tk.Canvas):
    ROW = 54

    def __init__(self, m, on_tap=None, empty=""):
        super().__init__(m, bg=T["glass"], highlightthickness=0, bd=0, cursor="hand2")
        self.items, self.off, self.on_tap, self.empty = [], 0, on_tap, empty
        self.hover, self._drag = -1, None
        self._wheel = lambda d: self._scroll(d * 40)
        self.bind("<Configure>", lambda e: self.redraw())
        self.bind("<ButtonPress-1>", self._press)
        self.bind("<B1-Motion>", self._motion)
        self.bind("<ButtonRelease-1>", self._release)
        self.bind("<Motion>", self._hover)
        self.bind("<Leave>", lambda e: self._set_hover(-1))

    def set_items(self, items):
        self.items, self.off = items, 0
        self.redraw()

    def _scroll(self, dy):
        self.off += dy
        self.redraw()

    def _press(self, e):
        self._drag = (e.y, self.off, False)

    def _motion(self, e):
        if not self._drag:
            return
        y0, off0, moved = self._drag
        moved = moved or abs(e.y - y0) > 6
        self._drag = (y0, off0, moved)
        if moved:
            self.off = off0 + (y0 - e.y)
            self.redraw()

    def _hover(self, e):
        idx = int((e.y + self.off) // (self.ROW * SC))
        self._set_hover(idx if 0 <= idx < len(self.items) else -1)

    def _set_hover(self, idx):
        if idx != self.hover:
            self.hover = idx
            self.redraw()

    def _release(self, e):
        if not self._drag:
            return
        _y0, _o, moved = self._drag
        self._drag = None
        if moved or self.on_tap is None:
            return
        idx = int((e.y + self.off) // (self.ROW * SC))
        if 0 <= idx < len(self.items):
            self.on_tap(self.items[idx], e.x > self.winfo_width() - sz(56))

    def redraw(self):
        self.delete("all")
        w, h = max(self.winfo_width(), 60), max(self.winfo_height(), 60)
        if not self.items:
            self.create_text(w / 2, h / 2, text=self.empty, fill=T["sub"], font=(FAM, sz(10)))
            return
        row = self.ROW * SC
        total = len(self.items) * row
        self.off = max(0, min(self.off, max(0, total - h)))
        first = int(self.off // row)
        last = min(len(self.items), int((self.off + h) // row) + 1)
        for i in range(first, last):
            it = self.items[i]
            y = i * row - self.off
            cy = y + row / 2
            bgc = mix(T["glass"], T["glass_hi"], 0.9) if i == self.hover else T["glass"]
            self.create_rectangle(0, y, w, y + row, fill=bgc, outline="")
            ax = sz(14)
            rr(self, ax, cy - sz(15), ax + sz(30), cy + sz(15), sz(9), fill=it.get("color", T["acc"]), outline="")
            self.create_text(ax + sz(15), cy, text=(it.get("letter") or "?"), fill="#FFFFFF",
                             font=(FAM, sz(10), "bold"))
            self.create_text(ax + sz(42), cy - sz(8), text=trunc(it.get("title", ""), 40), anchor="w",
                             fill=T["text"], font=(FAM, sz(10), "bold"))
            self.create_text(ax + sz(42), cy + sz(9), text=trunc(it.get("sub", ""), 54), anchor="w",
                             fill=T["sub"], font=(FAM, sz(8)))
            if it.get("badge"):
                self.create_text(w - sz(40), cy, text=it["badge"], fill=it.get("badge_color", T["ok"]),
                                 font=(FAM, sz(10), "bold"))
            self.create_text(w - sz(18), cy, text=it.get("chev", "›"), fill=T["sub"], font=(FAM, sz(12)))
            self.create_line(ax + sz(42), y + row - 1, w, y + row - 1, fill=T["edge"])


class Sheet(tk.Toplevel):
    def __init__(self, app, title, sub, actions):
        super().__init__(app)
        self.withdraw()
        self.configure(bg=T["bg"])
        self.title(title)
        self.transient(app)
        self.resizable(False, False)
        body = tk.Frame(self, bg=T["bg"], padx=sz(14), pady=sz(14))
        body.pack()
        tk.Label(body, text=title, bg=T["bg"], fg=T["text"], font=(FAM, sz(12), "bold"),
                 wraplength=sz(330)).pack(anchor="w", pady=(0, sz(2)))
        if sub:
            tk.Label(body, text=sub, bg=T["bg"], fg=T["sub"], font=(FAM, sz(9))).pack(anchor="w", pady=(0, sz(8)))
        for label, fn, acc in actions:
            Btn(body, label, click=lambda f=fn: self._go(f), w=sz(340), h=40, acc=acc, bg=T["bg"]).pack(pady=3)
        Btn(body, "Cancelar", click=self.destroy, w=sz(340), h=40, bg=T["bg"]).pack(pady=(8, 0))
        self.bind("<Escape>", lambda e: self.destroy())
        self.update_idletasks()
        x = app.winfo_rootx() + (app.winfo_width() - self.winfo_reqwidth()) // 2
        y = app.winfo_rooty() + max(20, (app.winfo_height() - self.winfo_reqheight()) // 2)
        self.geometry(f"+{x}+{y}")
        self.deiconify()
        try:
            self.grab_set()
        except tk.TclError:
            pass

    def _go(self, fn):
        self.destroy()
        fn()


class Toast(tk.Canvas):
    def __init__(self, app):
        super().__init__(app, highlightthickness=0, bd=0, bg=T["bg"], width=sz(200), height=sz(40))
        self.yo = float(-sz(70))
        self.kind, self.msg, self.job = "info", "", None
        self.place(relx=0.5, y=self.yo, anchor="n")

    def show(self, msg, kind="info"):
        self.msg, self.kind = msg, kind
        # Canvas.lift() e "levantar item"; para levantar o widget usamos o comando raise do Tk
        self.tk.call("raise", self._w)
        tween(self, "yo", sz(14), 0.6, ease_back)
        if self.job:
            try:
                self.after_cancel(self.job)
            except Exception:
                pass
        self.job = self.after(2600, lambda: tween(self, "yo", -sz(70), 0.35, ease_cubic))

    def paint(self):
        col = {"info": T["glass_hi"], "ok": T["ok"], "err": T["bad"]}.get(self.kind, T["glass_hi"])
        fg = T["text"] if self.kind == "info" else "#05060A"
        f = tkfont.Font(family=FAM, size=sz(10), weight="bold")
        w = f.measure(self.msg) + sz(36)
        self.config(width=w, height=sz(40))
        self.delete("all")
        rr(self, 0, 0, w, sz(40), sz(20), fill=col, outline="")
        self.create_text(w / 2, sz(20), text=self.msg, fill=fg, font=(FAM, sz(10), "bold"))
        self.place_configure(y=self.yo)


# --------------------------------------------------------------------------- #
# Paginas
# --------------------------------------------------------------------------- #
class HomePage(Scroll):
    def build(self):
        a = self.app
        inner = self.inner
        pad = dict(padx=sz(10), pady=sz(6))

        np = Card(inner, "Reproduzindo")
        np.pack(fill="x", **pad)
        self.np_title = tk.Label(np.body, text="Nada tocando", bg=T["glass"], fg=T["text"],
                                 font=(FAM, sz(13), "bold"), anchor="w")
        self.np_title.pack(fill="x")
        self.np_sub = tk.Label(np.body, text="—", bg=T["glass"], fg=T["sub"], font=(FAM, sz(9)), anchor="w")
        self.np_sub.pack(fill="x")
        self.seek = Slider(np.body, on_end=lambda f: a.seek_to(f))
        self.seek.pack(fill="x", pady=(sz(6), 0))
        self.seek.enabled = False
        self.np_time = tk.Label(np.body, text="00:00 / --:--", bg=T["glass"], fg=T["sub"], font=(FAM, sz(9)),
                                anchor="w")
        self.np_time.pack(fill="x")
        row = tk.Frame(np.body, bg=T["glass"])
        row.pack(fill="x", pady=(sz(6), 0))
        for i, (g, fn) in enumerate((("−30", lambda: a.seek(-30)), ("−10", lambda: a.seek(-10)),
                                     ("⏮", lambda: a.key(KEY["PREV"])), ("⏯", lambda: a.key(KEY["PLAY"])),
                                     ("⏭", lambda: a.key(KEY["NEXT"])), ("+10", lambda: a.seek(10)),
                                     ("+30", lambda: a.seek(30)))):
            row.columnconfigure(i, weight=1)
            Btn(row, glyph=g, click=fn, h=36, w=sz(56), bg=T["glass"], acc=T["acc"] if g == "⏯" else None,
                size=10).grid(row=0, column=i, padx=2, sticky="ew")

        grid = tk.Frame(inner, bg=T["bg"])
        grid.pack(fill="x", **pad)
        grid.columnconfigure(0, weight=1)
        grid.columnconfigure(1, weight=2)

        dp = Card(grid, "Navegação")
        dp.grid(row=0, column=0, sticky="nsew", padx=(0, sz(6)))
        pad3 = tk.Frame(dp.body, bg=T["glass"])
        pad3.pack()
        cells = {(0, 1): ("▲", "UP"), (1, 0): ("◀", "LEFT"), (1, 1): ("OK", "OK"), (1, 2): ("▶", "RIGHT"),
                 (2, 1): ("▼", "DOWN"), (2, 0): ("↩", "BACK"), (2, 2): ("⌂", "HOME")}
        for (r_, c_), (label, code) in cells.items():
            Btn(pad3, glyph=label, click=lambda k=code: a.key(KEY[k]), h=52, w=sz(58),
                acc=T["acc"] if code == "OK" else None, bg=T["glass"], size=12).grid(row=r_, column=c_, padx=3, pady=3)

        acts = Card(grid, "Ações")
        acts.grid(row=0, column=1, sticky="nsew", padx=(sz(6), 0))
        items = [("⏻", "Energia", lambda: a.key(KEY["POWER"]), T["bad"]),
                 ("⌂", "Início", lambda: a.key(KEY["HOME"]), None),
                 ("≡", "Menu", lambda: a.key(KEY["MENU"]), None),
                 ("⇆", "Fonte", lambda: a.key(KEY["INPUT"]), None),
                 ("ⓘ", "Info", lambda: a.key(KEY["INFO"]), None),
                 ("✕", "Mudo", lambda: a.key(KEY["MUTE"]), None),
                 ("⌨", "Digitar", a.ask_text, None),
                 ("☾", "Dormir", lambda: a.key(KEY["SLEEP"]), None)]
        for i in range(4):
            acts.body.columnconfigure(i, weight=1)
        for i, (g, label, fn, acc) in enumerate(items):
            Btn(acts.body, text=label, glyph=g, click=fn, big=True, h=sz(64), w=None, acc=acc,
                bg=T["glass"], size=12).grid(row=i // 4, column=i % 4, sticky="ew", padx=3, pady=3)

        vol = Card(inner, "Volume")
        vol.pack(fill="x", **pad)
        vr = tk.Frame(vol.body, bg=T["glass"])
        vr.pack(fill="x")
        Btn(vr, glyph="−", click=lambda: self.nudge_vol(-5), w=sz(40), h=36, bg=T["glass"]).pack(side="left")
        self.vol = Slider(vr, on=a.volume_drag, on_end=a.volume_release)
        self.vol.pack(side="left", fill="x", expand=True, padx=sz(8))
        Btn(vr, glyph="+", click=lambda: self.nudge_vol(5), w=sz(40), h=36, bg=T["glass"]).pack(side="left")
        self.vol_lbl = tk.Label(vr, text="--%", width=5, bg=T["glass"], fg=T["text"], font=(FAM, sz(10), "bold"))
        self.vol_lbl.pack(side="left", padx=(sz(8), 0))

    def nudge_vol(self, d):
        v = clamp(round(self.vol.f * 100) + d)
        self.vol.set(v / 100, anim=True)
        self.vol_lbl.configure(text=f"{v}%")
        self.app.set_volume_pct(v)
        self.app.note_volume_change()

    def set_volume_ui(self, pct):
        if not self.vol.drag:
            self.vol.set(pct / 100, anim=True)
            self.vol_lbl.configure(text=f"{pct}%")

    def _dim_drag(self, f):
        self.dim_lbl.configure(text=f"{round(f * 100)}%")

    def set_night_ui(self, dim):
        pass

    def show_time(self, est, dur, playing, title, pkg):
        self.np_title.configure(text=trunc(title or "Nada tocando", 60))
        state = "Tocando" if playing else "Pausado"
        self.np_sub.configure(text=f"{state} · {trunc(pkg, 40)}" if pkg else "Sem mídia ativa")
        self.np_time.configure(text=f"{mmss(est)} / {mmss(dur) if dur else '--:--'}")
        self.seek.enabled = dur > 0
        if dur > 0 and not self.seek.drag:
            self.seek.set(est / dur)


class LivePage(tk.Frame):
    def __init__(self, m, app):
        super().__init__(m, bg=T["bg"])
        self.app = app
        self._photo = None
        self._mimg = None
        self._show = None
        self._seq = -1
        self._busy = False
        self.card = Card(self)
        self.card.pack(fill="both", expand=True, padx=sz(10), pady=sz(8))
        self.scr = tk.Canvas(self.card.body, bg="#000000", highlightthickness=0, bd=0, height=sz(260))
        self.scr.pack(fill="both", expand=True, pady=(0, sz(6)))
        self.scr.bind("<Configure>", lambda e: self._draw())
        self._draw_box = (0.0, 0.0, 1.0, 1.0)
        self._hover_ts = 0.0
        self._drawn_fast = False
        self.scr.bind("<ButtonPress-1>", lambda e: self._touch(0, e))
        self.scr.bind("<B1-Motion>", lambda e: self._touch(2, e))
        self.scr.bind("<ButtonRelease-1>", lambda e: self._touch(1, e))
        self.scr.bind("<Motion>", self._hover)
        bar = tk.Frame(self.card.body, bg=T["glass"])
        bar.pack(fill="x")
        self.status = tk.Label(bar, text="Aguardando…", bg=T["glass"], fg=T["sub"], font=(FAM, sz(9)),
                               anchor="w", justify="left", wraplength=sz(520))
        self.status.pack(side="left", fill="x", expand=True)
        Btn(bar, "Atualizar", click=self.refresh, h=30, bg=T["glass"], size=9).pack(side="right", padx=2)
        Btn(bar, "Salvar PNG", click=self.save, h=30, bg=T["glass"], size=9).pack(side="right", padx=2)
        self.title = tk.Label(self.card.body, text="Nada tocando", bg=T["glass"], fg=T["text"],
                              font=(FAM, sz(12), "bold"), anchor="w")
        self.title.pack(fill="x", pady=(sz(6), 0))
        self.seek = Slider(self.card.body, on_end=lambda f: self.app.seek_to(f))
        self.seek.pack(fill="x")
        self.times = tk.Label(self.card.body, text="00:00 / --:--", bg=T["glass"], fg=T["sub"],
                              font=(FAM, sz(9)), anchor="w")
        self.times.pack(fill="x")
        ctl = tk.Frame(self.card.body, bg=T["glass"])
        ctl.pack(pady=sz(4))
        for g, fn in (("−30", lambda: self.app.seek(-30)), ("−10", lambda: self.app.seek(-10)),
                      ("⏮", lambda: self.app.key(KEY["PREV"])), ("⏯", lambda: self.app.key(KEY["PLAY"])),
                      ("⏭", lambda: self.app.key(KEY["NEXT"])), ("+10", lambda: self.app.seek(10)),
                      ("+30", lambda: self.app.seek(30))):
            Btn(ctl, glyph=g, click=fn, h=38, w=sz(60), bg=T["glass"], size=10).pack(side="left", padx=2)

    def on_show(self):
        self.refresh()
        self.app.poll_media(force=True)

    def show_time(self, est, dur, playing, title, pkg):
        self.title.configure(text=trunc(title or "Nada tocando", 70))
        self.times.configure(text=f"{mmss(est)} / {mmss(dur) if dur else '--:--'}")
        self.seek.enabled = dur > 0
        if dur > 0 and not self.seek.drag:
            self.seek.set(est / dur)

    def pull_frame(self):
        data, seq = self.app.mirror.latest()
        if data is None or seq == self._seq:
            return
        self._seq = seq
        if self._mimg is None:
            self._mimg = tk.PhotoImage(width=MIRROR_W, height=MIRROR_H)
        ppm = b"P6\n%d %d\n255\n" % (MIRROR_W, MIRROR_H) + data
        try:
            self._mimg.configure(data=ppm, format="ppm")
        except tk.TclError:
            return
        self._photo = self._mimg
        if not self._drawn_fast:
            self._draw()
        self.status.configure(text=f"Espelho ao vivo · {time.strftime('%H:%M:%S')}")

    def refresh(self):
        if self.app.mirror.ready:
            self.status.configure(text="Espelho ao vivo")
            return
        if not self.app.online:
            self.status.configure(text="Projetor desconectado")
            return
        if self._busy:
            return
        self._busy = True
        self.app.bg(screenshot_bytes, self._got)

    def _got(self, data, _err):
        self._busy = False
        if not data:
            self.status.configure(text="Sem captura (tela bloqueada ou sem permissão)")
            return
        try:
            self._photo = tk.PhotoImage(data=base64.b64encode(data).decode("ascii"))
        except tk.TclError:
            self.status.configure(text="Captura inválida")
            return
        self._draw()
        hint = ""
        if not ffmpeg_bin():
            hint = " · use 'Baixar transmissão ao vivo' em Ajustes"
        elif self.app.mirror.error:
            hint = " · espelho: " + trunc(self.app.mirror.error, 160)
        self.status.configure(text=f"Captura às {time.strftime('%H:%M:%S')}{hint}")

    def _draw(self):
        cv = self.scr
        cv.delete("all")
        self._drawn_fast = False
        if self._photo is None:
            cv.create_text(max(cv.winfo_width(), 1) / 2, max(cv.winfo_height(), 1) / 2,
                           text="Sem imagem ainda", fill=T["sub"], font=(FAM, sz(10)))
            return
        cw, ch = max(cv.winfo_width(), 1), max(cv.winfo_height(), 1)
        f = max(1, math.ceil(max(self._photo.width() / cw, self._photo.height() / ch)))
        self._show = self._photo.subsample(f) if f > 1 else self._photo
        sw, sh = self._show.width(), self._show.height()
        self._draw_box = ((cw - sw) / 2, (ch - sh) / 2, max(1, sw), max(1, sh))
        cv.create_image(cw / 2, ch / 2, image=self._show)
        self._drawn_fast = (self._show is self._mimg)

    def _map_xy(self, e):
        bx, by, bw, bh = self._draw_box
        pw, ph = self._photo.width(), self._photo.height()
        mx = (e.x - bx) * (pw / bw)
        my = (e.y - by) * (ph / bh)
        dw, dh = self.app.mirror.dev_w, self.app.mirror.dev_h
        sc_m = min(pw / dw, ph / dh)
        vw, vh = dw * sc_m, dh * sc_m
        vx0, vy0 = (pw - vw) / 2, (ph - vh) / 2
        return int((mx - vx0) * (dw / vw)), int((my - vy0) * (dh / vh)), mx, my, pw, ph

    def _hover(self, e):
        if self._photo is None or not self.app.mirror.ready:
            return
        now = time.monotonic()
        if now - self._hover_ts < 0.03:
            return
        self._hover_ts = now
        dx, dy, *_ = self._map_xy(e)
        self.app.mirror.send_touch(7, dx, dy)

    def _touch(self, action, e):
        if action == 0:
            self.scr.focus_set()
        if self._photo is None:
            return
        dx, dy, mx, my, pw, ph = self._map_xy(e)
        if self.app.mirror.ready:
            self.app.mirror.send_touch(action, dx, dy)
        elif action == 1 and self.app.online:
            self.app.kp.send(f"input tap {max(0, min(pw - 1, int(mx)))} {max(0, min(ph - 1, int(my)))}")

    def save(self):
        self.app.bg(screenshot_bytes, self._save_got)

    def _save_got(self, data, _err):
        if not data:
            self.app.toast("Não foi possível capturar a tela.", "err")
            return
        path = filedialog.asksaveasfilename(parent=self.app, defaultextension=".png",
                                            initialfile="projetor.png", filetypes=[("PNG", "*.png")])
        if path:
            Path(path).write_bytes(data)
            self.app.toast("Captura salva.", "ok")


class AppsPage(tk.Frame):
    def __init__(self, m, app):
        super().__init__(m, bg=T["bg"])
        self.app = app
        self.rows = []
        self.loaded = False
        bar = tk.Frame(self, bg=T["bg"])
        bar.pack(fill="x", padx=sz(12), pady=(sz(10), sz(4)))
        wrap = tk.Frame(bar, bg=T["glass_hi"])
        wrap.pack(side="left", fill="x", expand=True)
        self.q = tk.Entry(wrap, bg=T["glass_hi"], fg=T["text"], insertbackground=T["text"], relief="flat",
                          bd=0, font=(FAM, sz(11)))
        self.q.pack(fill="x", padx=sz(10), pady=sz(8))
        self.q.bind("<KeyRelease>", lambda e: self.apply())
        Btn(bar, "Atualizar", click=self.load, h=36, bg=T["bg"], size=9).pack(side="left", padx=(sz(8), 0))
        self.count = tk.Label(self, text="", bg=T["bg"], fg=T["sub"], font=(FAM, sz(9)), anchor="w")
        self.count.pack(fill="x", padx=sz(16))
        self.list = RowList(self, on_tap=self.tap, empty="Conecte o projetor para ver os apps")
        self.list.pack(fill="both", expand=True, padx=sz(12), pady=(sz(4), sz(10)))

    def on_show(self):
        if not self.loaded:
            self.load()
        else:
            self.refresh_running()

    def load(self):
        if not self.app.online:
            self.app.toast("Projetor desconectado.", "err")
            return
        self.app.bg(launchable_apps, self._loaded)

    def _loaded(self, apps, _err):
        if apps is None:
            self.app.toast("Falha ao listar apps.", "err")
            return
        self.loaded = True
        self.rows = [{"pkg": a["pkg"], "activity": a["activity"],
                      "title": a["pkg"].split(".")[-1].replace("_", " ").title(),
                      "letter": (a["pkg"].split(".")[-1][:1] or "?").upper(), "color": palette(a["pkg"]),
                      "running": False} for a in apps]
        self.apply()
        self.refresh_running()

    def refresh_running(self):
        self.app.bg(lambda: {p["name"].split(":")[0] for p in list_processes()}, self._running)

    def _running(self, names, _err):
        if names is None:
            return
        for r in self.rows:
            r["running"] = r["pkg"] in names
        self.apply()

    def apply(self):
        q = self.q.get().strip().lower()
        items = []
        for r in self.rows:
            if q and q not in (r["title"] + " " + r["pkg"]).lower():
                continue
            fav = r["pkg"] in self.app.favs
            it = dict(r)
            it["sub"] = r["pkg"]
            it["badge"] = "●" if r["running"] else ("★" if fav else "")
            it["badge_color"] = T["ok"] if r["running"] else T["warn"]
            it["fav"] = fav
            items.append(it)
        items.sort(key=lambda it: (not it["fav"], it["title"].lower()))
        self.list.set_items(items)
        self.count.configure(text=f"  {len(items)} de {len(self.rows)} apps")

    def tap(self, it, menu=False):
        a = self.app
        pkg, activity = it["pkg"], it["activity"]

        def toggle_fav():
            if pkg in a.favs:
                a.favs.discard(pkg)
            else:
                a.favs.add(pkg)
            save_favs(a.favs)
            self.apply()

        def uninstall():
            if messagebox.askyesno("Desinstalar", f"Desinstalar {pkg}?", parent=a):
                a.shell_toast(f"pm uninstall {shq(pkg)}", "App desinstalado.", "Falha.", 120, self.load)

        Sheet(a, it["title"], pkg, [
            ("Abrir", lambda: a.shell_toast(f"am start -n {shq(activity)}", "Abrindo…", "Falha ao abrir."), T["acc"]),
            ("Favoritar / remover", toggle_fav, None),
            ("Forçar parada", lambda: a.shell_toast(f"am force-stop {shq(pkg)}", "App parado.", "Falha.",
                                                    60, self.refresh_running), T["warn"]),
            ("Desinstalar", uninstall, T["bad"]),
        ])


class FilesPage(tk.Frame):
    def __init__(self, m, app):
        super().__init__(m, bg=T["bg"])
        self.app = app
        self.cur = "/sdcard"
        bar = tk.Frame(self, bg=T["bg"])
        bar.pack(fill="x", padx=sz(12), pady=(sz(10), sz(4)))
        wrap = tk.Frame(bar, bg=T["glass_hi"])
        wrap.pack(side="left", fill="x", expand=True)
        self.path_var = tk.StringVar(value=self.cur)
        e = tk.Entry(wrap, textvariable=self.path_var, bg=T["glass_hi"], fg=T["text"],
                     insertbackground=T["text"], relief="flat", bd=0, font=(FAM, sz(10)))
        e.pack(fill="x", padx=sz(10), pady=sz(8))
        e.bind("<Return>", lambda ev: self.go(self.path_var.get()))
        Btn(bar, "Ir", click=lambda: self.go(self.path_var.get()), h=36, bg=T["bg"], size=9).pack(side="left", padx=2)
        Btn(bar, glyph="⬆", click=self.up, h=36, w=sz(44), bg=T["bg"]).pack(side="left", padx=2)
        Btn(bar, glyph="↻", click=self.reload, h=36, w=sz(44), bg=T["bg"]).pack(side="left", padx=2)
        self.list = RowList(self, on_tap=self.tap, empty="Pasta vazia")
        self.list.pack(fill="both", expand=True, padx=sz(12), pady=(sz(4), sz(6)))
        tb = tk.Frame(self, bg=T["bg"])
        tb.pack(fill="x", padx=sz(12), pady=(0, sz(10)))
        Btn(tb, "Enviar arquivo", click=self.upload, h=38, acc=T["acc"], bg=T["bg"], size=9).pack(side="left", padx=2)
        Btn(tb, "Nova pasta", click=self.new_folder, h=38, bg=T["bg"], size=9).pack(side="left", padx=2)
        Btn(tb, "Instalar APK", click=self.install, h=38, acc=T["warn"], bg=T["bg"], size=9).pack(side="left", padx=2)

    def on_show(self):
        self.reload()

    def go(self, path):
        p = norm_remote(path)
        if not p:
            self.app.toast("Use apenas a memória interna (/sdcard).", "err")
            return
        self.cur = p
        self.path_var.set(p)
        self.reload()

    def up(self):
        if self.cur in ALLOWED_ROOTS:
            return
        self.go(self.cur.rsplit("/", 1)[0] or "/sdcard")

    def reload(self):
        if not self.app.online:
            self.app.toast("Projetor desconectado.", "err")
            return
        self.app.bg(list_dir, self._loaded, self.cur)

    def _loaded(self, res, _err):
        entries, msg = res if res else ([], "")
        if not entries and msg:
            self.app.toast(trunc(msg, 90), "err")
        items = []
        for e in entries:
            if e["isDir"]:
                items.append({"title": e["name"], "sub": "Pasta", "letter": "▸", "color": T["acc"], "entry": e})
            else:
                ext = e["name"].rsplit(".", 1)[-1][:3].upper() if "." in e["name"] else "▤"
                items.append({"title": e["name"], "sub": human(e["size"]), "letter": ext,
                              "color": palette(e["name"]), "entry": e})
        self.list.set_items(items)

    def tap(self, it, menu=False):
        e = it["entry"]
        if e["isDir"] and not menu:
            self.go(e["path"])
            return
        Sheet(self.app, e["name"], "Pasta" if e["isDir"] else human(e["size"]), [
            ("Baixar para o PC", lambda: self.download(e), T["acc"]),
            ("Renomear", lambda: self.rename(e), None),
            ("Copiar para…", lambda: self.copy_move(e, False), None),
            ("Mover para…", lambda: self.copy_move(e, True), None),
            ("Apagar", lambda: self.delete(e), T["bad"]),
        ])

    def _guard(self, e):
        if norm_remote(e["path"]) is None or e["path"].rstrip("/") in ALLOWED_ROOTS:
            self.app.toast("Essa pasta não pode ser alterada.", "err")
            return False
        return True

    def _op_done(self, r, err):
        ok = r is not None and not err and r.returncode == 0
        if ok:
            self.app.toast("Concluído.", "ok")
            self.reload()
        else:
            detail = ((r.stderr or r.stdout) if r is not None else str(err)).strip()
            self.app.toast("Falhou: " + trunc(detail, 110), "err")

    def download(self, e):
        dest = filedialog.asksaveasfilename(parent=self.app, initialfile=e["name"])
        if dest:
            self.app.toast("Baixando…")
            self.app.bg(lambda: adb("pull", e["path"], dest, timeout=900), self._op_done)

    def upload(self):
        src = filedialog.askopenfilename(parent=self.app, title="Enviar para o projetor")
        if not src:
            return
        dest = norm_remote(self.cur.rstrip("/") + "/" + Path(src).name)
        if dest:
            self.app.toast("Enviando…")
            self.app.bg(lambda: adb("push", src, dest, timeout=1800), self._op_done)

    def install(self):
        src = filedialog.askopenfilename(parent=self.app, title="Instalar APK", filetypes=[("APK", "*.apk")])
        if src:
            self.app.toast("Instalando…")
            self.app.bg(lambda: adb("install", "-r", src, timeout=900), self._install_done)

    def _install_done(self, r, err):
        if r is not None and "Success" in (r.stdout or ""):
            self.app.toast("App instalado.", "ok")
        else:
            detail = ((r.stdout or r.stderr) if r is not None else str(err)).strip()
            self.app.toast("Falha na instalação: " + trunc(detail[-110:], 110), "err")

    def rename(self, e):
        if not self._guard(e):
            return
        new = (simpledialog.askstring("Renomear", "Novo nome:", initialvalue=e["name"], parent=self.app) or "").strip()
        if not new or new == e["name"] or "/" in new:
            return
        dst = norm_remote(e["path"].rsplit("/", 1)[0] + "/" + new)
        if dst:
            self.app.bg(lambda: shell(f"mv -f {shq(e['path'])} {shq(dst)}", 120), self._op_done)

    def copy_move(self, e, move):
        if not self._guard(e):
            return
        target = simpledialog.askstring("Mover para" if move else "Copiar para", "Pasta de destino:",
                                        initialvalue=self.cur, parent=self.app)
        dst = norm_remote(target or "")
        if not dst:
            self.app.toast("Destino inválido (use /sdcard/…).", "err")
            return
        verb = "mv -f" if move else "cp -r"
        cmd = f"{verb} {shq(e['path'])} {shq(dst.rstrip('/') + '/')}"
        self.app.bg(lambda: shell(cmd, 600), self._op_done)

    def delete(self, e):
        if not self._guard(e):
            return
        if messagebox.askyesno("Apagar", f"Apagar “{e['name']}”? Não pode ser desfeito.", parent=self.app):
            self.app.bg(lambda: shell(f"rm -rf {shq(e['path'])}", 300), self._op_done)

    def new_folder(self):
        name = (simpledialog.askstring("Nova pasta", "Nome da pasta:", parent=self.app) or "").strip()
        if not name or "/" in name:
            return
        dst = norm_remote(self.cur.rstrip("/") + "/" + name)
        if dst:
            self.app.bg(lambda: shell(f"mkdir -p {shq(dst)}", 60), self._op_done)


class SettingsPage(Scroll):
    def build(self):
        a = self.app
        p = dict(padx=sz(10), pady=sz(6))

        c = Card(self.inner, "Conexão")
        c.pack(fill="x", **p)
        row = tk.Frame(c.body, bg=T["glass"])
        row.pack(fill="x")
        self.host_var = tk.StringVar(value=PREFS["host"])
        e = tk.Entry(row, textvariable=self.host_var, bg=T["glass_hi"], fg=T["text"], insertbackground=T["text"],
                     relief="flat", bd=0, font=(FAM, sz(11)))
        e.pack(side="left", fill="x", expand=True, ipady=sz(6), padx=(0, sz(8)))
        e.bind("<Return>", lambda ev: self.save_host())
        Btn(row, "Salvar", click=self.save_host, h=34, acc=T["acc"], bg=T["glass"], size=9).pack(side="left")
        Btn(row, "Reconectar", click=lambda: a.reconnect(self.note), h=34, bg=T["glass"], size=9).pack(
            side="left", padx=(6, 0))
        self.conn_lbl = tk.Label(c.body, text="", bg=T["glass"], fg=T["sub"], font=(FAM, sz(9)), anchor="w")
        self.conn_lbl.pack(fill="x", pady=(sz(6), 0))
        self.act_lbl = tk.Label(c.body, text="", bg=T["glass"], fg=T["sub"], font=(FAM, sz(9)), anchor="w",
                                justify="left", wraplength=sz(460))
        self.act_lbl.pack(fill="x", pady=(sz(2), 0))
        rb = tk.Frame(c.body, bg=T["glass"])
        rb.pack(fill="x", pady=(sz(6), 0))
        Btn(rb, "Parear (Android 11+)", click=lambda: a.pair_wifi_adb(self.note),
            h=32, w=sz(180), acc=T["acc2"], bg=T["glass"], size=9).pack(side="left")
        Btn(rb, "Ativar Wi-Fi via USB (tcpip 5555)", click=lambda: a.enable_wifi_adb(self.note),
            h=32, w=sz(230), bg=T["glass"], size=9).pack(side="left", padx=(sz(6), 0))

        m = Card(self.inner, "Transmissão ao vivo (scrcpy)")
        m.pack(fill="x", **p)
        r1 = tk.Frame(m.body, bg=T["glass"])
        r1.pack(fill="x")
        tk.Label(r1, text="Usar espelho fluido", bg=T["glass"], fg=T["text"], font=(FAM, sz(10))).pack(side="left")
        Toggle(r1, value=PREFS["mirror"], cb=self.set_mirror, bg=T["glass"]).pack(side="right")
        self.ff_lbl = tk.Label(m.body, text="", bg=T["glass"], fg=T["sub"], font=(FAM, sz(9)), anchor="w",
                               justify="left", wraplength=sz(440))
        self.ff_lbl.pack(fill="x", pady=(sz(6), sz(6)))
        r2 = tk.Frame(m.body, bg=T["glass"])
        r2.pack(fill="x")
        Btn(r2, "Baixar transmissão ao vivo", click=lambda: a.install_live(self.note), h=40, w=sz(260),
            acc=T["acc"], bg=T["glass"], size=10).pack(side="left")
        Btn(r2, "Testar espelho", click=lambda: a.restart_mirror(self.note), h=40, w=sz(150),
            bg=T["glass"], size=10).pack(side="left", padx=(sz(8), 0))
        self.refresh_ff()


        s = Card(self.inner, "Sistema e controles")
        s.pack(fill="x", **p)
        self.info = tk.Label(s.body, text="Conecte o projetor…", bg=T["glass"], fg=T["text"], font=(FAM, sz(10)),
                             justify="left", anchor="w")
        self.info.pack(fill="x")
        r3 = tk.Frame(s.body, bg=T["glass"])
        r3.pack(fill="x", pady=(sz(6), 0))
        Btn(r3, "Processos", click=a.open_processes, h=34, bg=T["glass"], size=9).pack(side="left")
        Btn(r3, "Acordar tela", click=self._wake, h=34, acc=T["ok"], bg=T["glass"], size=9).pack(side="left")
        Btn(r3, "Atualizar info", click=self.load, h=34, bg=T["glass"], size=9).pack(side="left", padx=4)
        r4 = tk.Frame(s.body, bg=T["glass"])
        r4.pack(fill="x", pady=(sz(8), 0))
        tk.Label(r4, text="Teclado do PC controla o projetor", bg=T["glass"], fg=T["text"],
                 font=(FAM, sz(10))).pack(side="left")
        Toggle(r4, value=PREFS["kb"], cb=self.set_kb, bg=T["glass"]).pack(side="right")

    # ----------------------------------------------------------- acoes -- #
    def note(self, msg, kind="info"):
        """Mostra o resultado de uma acao direto na aba Ajustes."""
        col = {"info": T["sub"], "ok": T["ok"], "err": T["bad"]}.get(kind, T["sub"])
        self.act_lbl.configure(text=msg, fg=col)

    def save_host(self):
        global ADB_HOST
        host = self.host_var.get().strip() or DEFAULT_PREFS["host"]
        if not HOST_RE.match(host):
            self.note("Endereço inválido. Use IP:porta, ex.: 192.168.0.10:5555", "err")
            return
        if ":" not in host:
            host += ":5555"
        ADB_HOST = host
        PREFS["host"] = host
        save_prefs()
        self.host_var.set(host)
        self.note(f"Endereço salvo: {host}. Reconectando…", "info")
        self.app.reconnect(self.note)

    def _wake(self):
        if self.app.blackout_on:
            self.app.blackout(False)
        self.app.key(KEY["WAKEUP"])

    def on_show(self):
        self.load()
        self.refresh_ff()

    def refresh_ff(self):
        ff = ffmpeg_bin()
        self.ff_lbl.configure(text=f"ffmpeg: {ff}" if ff else
                              "ffmpeg não encontrado. Clique em 'Baixar transmissão ao vivo' para instalar.")

    def set_status(self, msg):
        self.ff_lbl.configure(text=msg)

    def set_mirror(self, v):
        PREFS["mirror"] = bool(v)
        save_prefs()
        if not v:
            threading.Thread(target=self.app.mirror.stop, daemon=True).start()

    def set_kb(self, v):
        PREFS["kb"] = bool(v)
        save_prefs()
        self.app.kb_on = bool(v)

    def load(self):
        self.app.bg(system_info, self._info)
        self.conn_lbl.configure(text=f"Endereço: {ADB_HOST} · {'conectado' if self.app.online else 'desconectado'}")

    def _info(self, lines, _err):
        if not lines:
            self.info.configure(text="Sem dados (projetor desconectado?)")
            return
        model = lines[0]
        android = lines[1] if len(lines) > 1 else "?"
        storage = ""
        if len(lines) > 2:
            cols = lines[2].split()
            if len(cols) >= 4:
                storage = f"\nArmazenamento livre: {cols[3]} de {cols[1]}"
        self.info.configure(text=f"Modelo: {model}\nAndroid: {android}{storage}")

    def sync_image(self, vals):
        pass

# --------------------------------------------------------------------------- #
# Aplicativo
# --------------------------------------------------------------------------- #
TABS = [("home", "⌂", "Início"), ("live", "▶", "Ao vivo"), ("apps", "▦", "Apps"),
        ("files", "▤", "Arquivos"), ("settings", "⚙", "Ajustes")]


class App(tk.Tk):
    def __init__(self):
        super().__init__()
        _ROOT[0] = self
        global SC
        sw, sh = self.winfo_screenwidth(), self.winfo_screenheight()
        SC = max(0.72, min(1.0, min(sw / 1366, sh / 768)))
        self.title("Projetor Remote")
        w = min(1100, int(sw * 0.92))
        h = min(720, int(sh * 0.86))
        self.geometry(f"{w}x{h}")
        self.minsize(sz(640), sz(480))
        self.configure(bg=T["bg"])
        self.protocol("WM_DELETE_WINDOW", self._close)
        self.report_callback_exception = self._tk_error

        self.ui_q = queue.Queue()
        self.kp = KeyPipe()
        self.latest = Coalescer()
        self.mirror = mirror
        self.toast_w = None
        self.online = False
        self.kb_on = PREFS["kb"]
        self.blackout_on = False
        self.base = {"brightness": 50, "contrast": 50, "saturation": 50}
        self.favs = load_favs()
        self.vol_max = 15
        self.vol_drag_pct = None
        self._vol_ts = 0.0
        self.media = None
        self.media_now = 0.0
        self.page = None
        self._media_busy = False
        self._vol_busy = False
        self._mirror_busy = False
        self._mirror_retry = 0.0
        self._installing = False
        self._reconnecting = False
        self.nav_btns = {}
        self._wide = None

        self._build()
        self.toast_w = Toast(self)
        self.bind_all("<Key>", self._on_key)
        self.bind_all("<MouseWheel>", self._on_wheel)
        self.bind_all("<Button-4>", lambda e: self._on_wheel(e, -1))
        self.bind_all("<Button-5>", lambda e: self._on_wheel(e, 1))
        self.bind("<Configure>", self._on_resize)
        self.show("home")
        threading.Thread(target=self._monitor, daemon=True).start()
        self.after(15, self._pump)
        self.every(MEDIA_POLL_MS, self.poll_media)
        self.every(TICK_MS, self._tick)
        self.every(FRAME_MS, self._pull_frames)
        self.every(SHOT_MS, self._auto_shot)
        self.every(ENSURE_MIRROR_MS, self._ensure_mirror)
        self.every(VOL_POLL_MS, self._poll_volume)

    # ------------------------------------------------------------ infra -- #
    def every(self, ms, fn):
        def tick():
            try:
                fn()
            except Exception:
                log(traceback.format_exc())
            self.after(ms, tick)
        self.after(ms, tick)

    def bg(self, fn, done=None, *args):
        def worker():
            try:
                res, err = fn(*args), None
            except Exception as ex:
                res, err = None, ex
                log(f"erro em segundo plano: {ex}\n{traceback.format_exc()}")
            if done:
                self.ui_q.put((done, res, err))
        threading.Thread(target=worker, daemon=True).start()

    def ui(self, fn):
        """Agenda fn() na thread da interface (seguro a partir de threads de fundo)."""
        self.ui_q.put((lambda r, e: fn(), None, None))

    def _pump(self):
        while True:
            try:
                done, res, err = self.ui_q.get_nowait()
            except queue.Empty:
                break
            try:
                done(res, err)
            except Exception:
                log(traceback.format_exc())
                try:
                    self.toast("Erro interno (veja cache/log.txt)", "err")
                except Exception:
                    pass
        self.after(15, self._pump)

    def _monitor(self):
        last = 0.0
        misses = 0
        while True:
            try:
                ok = adb_devices_online()
                if not ok and time.time() - last > 10:
                    last = time.time()
                    _run(["adb", "connect", ADB_HOST], 20)
                    ok = adb_devices_online()
            except Exception:
                log(traceback.format_exc())
                ok = False
            if ok:
                misses = 0
                self.ui_q.put((self._on_status, True, None))
            else:
                misses += 1
                if misses >= 2 or not self.online:
                    self.ui_q.put((self._on_status, False, None))
            time.sleep(2)

    def _tk_error(self, exc, val, tb):
        """Nunca pode lancar excecao (isso derrubava o programa)."""
        try:
            log("".join(traceback.format_exception(exc, val, tb)))
        except Exception:
            pass
        try:
            self.toast(f"Erro: {trunc(str(val), 80)}", "err")
        except Exception:
            pass

    def _close(self):
        try:
            t = threading.Thread(target=self.mirror.stop, daemon=True)  # nao trava a janela se o adb demorar
            t.start()
            t.join(4)
            pq.close()
            self.kp.close()
        finally:
            self.destroy()

    # --------------------------------------------------------- layout -- #
    def _build(self):
        self.grid_rowconfigure(1, weight=1)
        self.grid_columnconfigure(1, weight=1)

        head = tk.Frame(self, bg=T["bg"])
        head.grid(row=0, column=0, columnspan=2, sticky="ew", padx=sz(16), pady=(sz(10), sz(4)))
        self.title_lbl = tk.Label(head, text="Início", bg=T["bg"], fg=T["text"], font=(FAM, sz(18), "bold"))
        self.title_lbl.pack(side="left")
        self.status_btn = Btn(head, text="Conectando…", click=self.reconnect, h=30, bg=T["bg"], size=9)
        self.status_btn.pack(side="right")

        self.rail = tk.Frame(self, bg=T["bg"])
        self.dock = tk.Frame(self, bg=T["bg"])
        for i, (key, glyph, name) in enumerate(TABS):
            b = Btn(self.rail, text=name, glyph=glyph, click=lambda k=key: self.show(k), w=sz(78), h=54,
                    bg=T["bg"], size=8, big=True)
            b.pack(pady=sz(4))
            self.nav_btns[key] = b
            d = Btn(self.dock, text=name, glyph=glyph, click=lambda k=key: self.show(k), w=None, h=60,
                    bg=T["bg"], size=8, big=True)
            d.grid(row=0, column=i, sticky="ew", padx=3, pady=sz(4))
            self.dock.columnconfigure(i, weight=1)
            self.nav_btns[key + "_d"] = d

        self.content = tk.Frame(self, bg=T["bg"])
        self.content.grid(row=1, column=1, sticky="nsew")
        self.pages = {
            "home": HomePage(self.content, self),
            "live": LivePage(self.content, self),
            "apps": AppsPage(self.content, self),
            "files": FilesPage(self.content, self),
            "settings": SettingsPage(self.content, self),
        }

    def _on_resize(self, e):
        if e.widget is not self:
            return
        wide = self.winfo_width() >= sz(820)
        if wide == self._wide:
            return
        self._wide = wide
        if wide:
            self.rail.grid_forget()
            self.dock.grid(row=2, column=0, columnspan=2, sticky="ew", padx=sz(12), pady=(0, sz(10)))
            self.grid_columnconfigure(0, minsize=0)
        else:
            self.dock.grid_forget()
            self.rail.grid(row=1, column=0, sticky="ns", padx=(sz(8), 0), pady=(0, sz(8)))
            self.grid_columnconfigure(0, minsize=sz(96))

    def show(self, name):
        if self.page == name:
            return
        for p in self.pages.values():
            p.pack_forget()
        self.pages[name].pack(fill="both", expand=True)
        self.page = name
        self.title_lbl.configure(text=dict((k, n) for k, _g, n in TABS).get(name, "Início"))
        for key, btn in self.nav_btns.items():
            base = key[:-2] if key.endswith("_d") else key
            btn.sel = (base == name)
            btn.paint()
        on_show = getattr(self.pages[name], "on_show", None)
        if on_show:
            on_show()

    def toast(self, msg, kind="info"):
        if self.toast_w is None:
            return
        self.toast_w.show(msg, kind)
        self.toast_w.paint()

    def shell_toast(self, cmd, ok_msg, err_msg="Falha.", timeout=60, after=None):
        def done(r, err):
            ok = r is not None and r.returncode == 0 and not err
            if ok:
                self.toast(ok_msg, "ok")
                if after:
                    after()
            else:
                detail = (r.stderr or r.stdout).strip()[:100] if r is not None else str(err)
                self.toast(f"{err_msg} {detail}".strip(), "err")
        self.bg(shell, done, cmd, timeout)

    # ----------------------------------------------------- conexao -- #
    def _on_status(self, ok, _err):
        ok = bool(ok)
        was = self.online
        self.online = ok
        if not self._reconnecting:
            self.status_btn.text = "● Conectado" if ok else "● Desconectado"
            self.status_btn.fg = T["ok"] if ok else T["bad"]
            self.status_btn.paint()
        if ok and not was:
            self._on_connected()
        elif was and not ok:
            threading.Thread(target=self.mirror.stop, daemon=True).start()

    def _on_connected(self):
        self.bg(get_volume, self._on_volume)
        self.bg(pq.state, self._on_image)
        self._ensure_mirror()
        self.pages["settings"].load()
        if self.page == "apps":
            self.pages["apps"].on_show()
        if self.page == "files":
            self.pages["files"].reload()

    def _poll_volume(self):
        if self._vol_busy or not self.online or self.vol_drag_pct is not None:
            return
        if time.time() - self._vol_ts <= VOL_HOLD_S:
            return
        self._vol_busy = True
        self.bg(get_volume, self._on_volume)

    def _on_volume(self, res, _err):
        self._vol_busy = False
        if not res:
            return
        self.vol_max = res["max"] or 15
        if self.vol_drag_pct is not None or time.time() - self._vol_ts <= VOL_HOLD_S:
            return  # usuario acabou de mexer: nao sobrescrever o slider
        self.pages["home"].set_volume_ui(round(res["level"] / self.vol_max * 100))

    def _on_image(self, st, _err):
        if not st or self.blackout_on:
            return  # em blackout o projetor devolve tudo 0: nao pode virar o "valor normal"
        if not any(st.values()) and PREFS.get("base"):
            st = dict(PREFS["base"])  # app foi reaberto com a imagem apagada: usa o ultimo valor salvo
        self.base = dict(st)
        self.pages["settings"].sync_image(st)

    def reconnect(self, feedback=None):
        """Desconecta e reconecta o ADB; mostra o resultado (aba Ajustes ou toast)."""
        note = feedback or (lambda m, k="info": self.toast(m, k))
        if self._reconnecting:
            note("Já está reconectando…", "info")
            return
        self._reconnecting = True
        note("Reconectando ao projetor…", "info")
        self.status_btn.text = "● Conectando…"
        self.status_btn.fg = T["warn"]
        self.status_btn.paint()

        def work():
            _run(["adb", "disconnect", ADB_HOST], 10)
            r = _run(["adb", "connect", ADB_HOST], 20)
            d = _run(["adb", "devices"], 10).stdout
            st = next((p[1] for l in d.splitlines() for p in [l.split()] if len(p) >= 2 and p[0] == ADB_HOST), "")
            return st == "device", st, (r.stdout + r.stderr).strip()

        def done(res, err):
            self._reconnecting = False
            if err is not None or res is None:
                note(f"Falha ao reconectar: {err}", "err")
                self.toast("Falha ao reconectar.", "err")
                self._on_status(False, None)
                return
            ok, st, raw = res
            if ok:
                note(f"Conectado a {ADB_HOST}.", "ok")
                self.toast("Conectado.", "ok")
            elif st == "unauthorized":
                note("Autorize a depuração na tela do aparelho.", "err")
                self.toast("Autorize no aparelho.", "err")
            else:
                msg = trunc(raw or "sem resposta", 110)
                note(f"Não conectou em {ADB_HOST}: {msg} (no Android 11+ use 'Parear' antes)", "err")
                self.toast("Não conectou.", "err")
            self._on_status(ok, None)

        self.bg(work, done)

    def pair_wifi_adb(self, feedback=None):
        note = feedback or (lambda m, k="info": self.toast(m, k))
        ip_def = ADB_HOST.split(":")[0] + ":"
        hp = (simpledialog.askstring("Parear (Android 11+)",
                                     "IP:porta de pareamento (tela 'Parear dispositivo'):",
                                     initialvalue=ip_def, parent=self) or "").strip()
        if not hp or ":" not in hp:
            return
        code = (simpledialog.askstring("Parear (Android 11+)",
                                       "Código de pareamento (6 dígitos):", parent=self) or "").strip()
        if not code:
            return
        note(f"Pareando com {hp}…", "info")

        def work():
            r = _run(["adb", "pair", hp, code], 25)
            out = (r.stdout + " " + r.stderr).strip()
            ok = r.returncode == 0 and "successfully paired" in out.lower()
            conn_ok = False
            if ok:
                _run(["adb", "connect", ADB_HOST], 20)
                conn_ok = adb_devices_online()
            return ok, out, conn_ok

        def done(res, err):
            if err is not None or res is None:
                note(f"Erro ao parear: {err}", "err")
                return
            ok, out, conn_ok = res
            if ok and conn_ok:
                note(f"Pareado e conectado em {ADB_HOST}!", "ok")
                self._on_status(True, None)
            elif ok:
                note("Pareado! Agora salve o IP:porta principal da Depuração sem fio e clique Reconectar.", "ok")
            else:
                note(f"Falha no pareamento: {trunc(out, 140)}", "err")

        self.bg(work, done)

    def enable_wifi_adb(self, feedback=None):
        """Equivalente ao 'adb tcpip 5555' + 'adb connect' (para uso inicial via USB)."""
        note = feedback or (lambda m, k="info": self.toast(m, k))
        note("Ativando ADB Wi-Fi (tcpip 5555)…", "info")

        def work():
            r1 = _run(["adb", "tcpip", "5555"], 15)
            time.sleep(1.5)
            r2 = _run(["adb", "connect", ADB_HOST], 20)
            return (r1.returncode == 0, (r1.stdout + r1.stderr).strip(),
                    adb_devices_online(), (r2.stdout + r2.stderr).strip())

        def done(res, err):
            if err is not None or res is None:
                note(f"Falha: {err}", "err")
                return
            ok_tcp, out_tcp, ok_conn, out_conn = res
            if not ok_tcp:
                note(f"USB não encontrado para tcpip 5555: {trunc(out_tcp, 90)}", "err")
                return
            if ok_conn:
                note(f"ADB Wi-Fi ativo e conectado em {ADB_HOST}. Pode desligar o USB.", "ok")
                self._on_status(True, None)
            else:
                note(f"tcpip 5555 ok, mas não conectou em {ADB_HOST}: {trunc(out_conn, 90)}", "err")

        self.bg(work, done)

    def _ensure_mirror(self):
        if not (self.online and PREFS["mirror"] and ffmpeg_bin()) or self.mirror.ready or self._mirror_busy:
            return
        if time.time() < self._mirror_retry:
            return
        self._mirror_busy = True

        def done(ok, _err):
            self._mirror_busy = False
            if ok and self.blackout_on:
                self.mirror.set_display_power(False)
            if not ok:
                self._mirror_retry = time.time() + 25
                if self.page == "live":
                    self.toast(f"Espelho: {trunc(self.mirror.error, 70)}", "err")
            self.pages["live"].refresh()
        self.bg(self.mirror.start, done)

    def restart_mirror(self, feedback=None):
        """Reinicia o espelho e mostra o resultado exato (ou o erro)."""
        note = feedback or (lambda m, k="info": self.toast(m, k))
        if not self.online:
            note("Projetor desconectado. Conecte primeiro.", "err")
            return
        if not ffmpeg_bin():
            note("ffmpeg não encontrado. Use 'Baixar transmissão ao vivo'.", "err")
            return
        if self._mirror_busy:
            note("O espelho já está iniciando…", "info")
            return
        self._mirror_busy = True
        note("Iniciando espelho (pode levar alguns segundos)…", "info")

        def work():
            self.mirror.stop()
            return self.mirror.start()

        def done(ok, err):
            self._mirror_busy = False
            if ok and self.blackout_on:
                self.mirror.set_display_power(False)
            if ok:
                note("Espelho ao vivo ativo. Veja na aba Ao vivo.", "ok")
                self.toast("Espelho ativo.", "ok")
            else:
                reason = self.mirror.error or str(err) or "motivo desconhecido"
                note("Espelho falhou: " + trunc(reason, 320), "err")
                self.toast("Espelho falhou (detalhes em Ajustes).", "err")
                self._mirror_retry = time.time() + 25
        self.bg(work, done)

    # ------------------------------------------------- ferramentas -- #
    def install_live(self, feedback=None):
        note = feedback or (lambda m, k="info": self.toast(m, k))
        if self._installing:
            note("Já está baixando…", "info")
            return
        self._installing = True
        note("Iniciando download…", "info")
        settings = self.pages["settings"]

        def progress(msg):
            self.ui(lambda m=msg: (note(m, "info"), settings.set_status(m)))

        def done(res, err):
            self._installing = False
            if err is not None:
                note(f"Falhou: {trunc(str(err), 220)}", "err")
                self.toast("Falha ao baixar a transmissão.", "err")
            else:
                note(f"Pronto: {res}", "ok")
                self.toast("Transmissão ao vivo pronta.", "ok")
            settings.refresh_ff()
            self._mirror_retry = 0.0
        self.bg(install_live, done, progress)

    def open_processes(self):
        win = tk.Toplevel(self)
        win.title("Processos")
        win.configure(bg=T["bg"])
        win.geometry(f"{sz(460)}x{sz(520)}")
        lst = RowList(win, empty="Carregando…")
        lst.pack(fill="both", expand=True, padx=sz(10), pady=sz(10))

        def load():
            self.bg(list_processes, lambda r, e: show(r or []))

        def show(procs):
            items = [{"title": p["name"], "sub": f"PID {p['pid']}", "letter": (p["name"][:1] or "?").upper(),
                      "color": palette(p["name"]), "proc": p}
                     for p in procs if not p["name"].startswith(("android", "com.android", "system", "[", "zygote"))]
            lst.set_items(items)

        def tap(it, _m):
            p = it["proc"]
            pkg = p["name"].split(":")[0]
            Sheet(win, p["name"], f"PID {p['pid']}", [
                ("Encerrar processo",
                 lambda: self.shell_toast(f"kill -9 {p['pid']}", "Encerrado.", "Falha.", 20, load), T["bad"]),
                ("Forçar parada do app",
                 lambda: self.shell_toast(f"am force-stop {shq(pkg)}", "Parado.", "Falha.", 20), T["warn"]),
            ])
        lst.on_tap = tap
        load()

    # ------------------------------------------------- comandos -- #
    def key(self, code):
        if not self.online:
            self.toast("Projetor desconectado.", "err")
            return
        if self.mirror.send_keys([int(code)]):
            return
        self.kp.send(f"input keyevent {int(code)}")

    def seek(self, delta):
        delta = float(delta)
        if abs(delta) < 1:
            return
        code = KEY["FF"] if delta > 0 else KEY["REW"]
        n = max(1, min(60, round(abs(delta) / 10)))
        if not self.mirror.send_keys([code] * n):
            for _ in range(n):
                self.kp.send(f"input keyevent {code}")
        self.media_now = max(0.0, self.media_now + delta)
        if self.media:
            self.media["pos"] = self.media_now
            self.media["t"] = time.monotonic()

    def seek_to(self, frac):
        dur = (self.media or {}).get("dur") or 0
        if dur > 0:
            self.seek(frac * dur - self.media_now)

    def send_text(self, txt):
        if not self.mirror.send_text(txt):
            self.kp.send(input_text_cmd(txt))

    def ask_text(self):
        txt = simpledialog.askstring("Digitar", "Texto para enviar ao projetor:", parent=self)
        if txt:
            self.send_text(txt)

    def note_volume_change(self):
        self._vol_ts = time.time()

    def set_volume_pct(self, pct):
        self._vol_ts = time.time()
        level = round(clamp(pct) / 100 * (self.vol_max or 15))
        self.latest.submit("vol", volume_set, level)

    def volume_drag(self, f):
        pct = round(clamp(f * 100))
        self.vol_drag_pct = pct
        self.pages["home"].vol_lbl.configure(text=f"{pct}%")
        self.set_volume_pct(pct)

    def volume_release(self, f):
        pct = round(clamp(f * 100))
        self.vol_drag_pct = None
        self.set_volume_pct(pct)

    # imagem: base (ajuste do usuario) + escurecimento aplicado por cima
    def set_base(self, kind, value):
        self.base[kind] = clamp(int(value))
        if any(self.base.values()):
            PREFS["base"] = dict(self.base)
            save_prefs()
        self._push_image()

    def apply_preset(self, vals):
        self.base = dict(zip(IMG_CODE, vals))
        PREFS["base"] = dict(self.base)
        save_prefs()
        self.pages["settings"].sync_image(self.base)
        self._push_image()

    def set_dim(self, f):
        PREFS["dim"] = round(clamp(f * 100))
        save_prefs()
        self.pages["home"].set_night_ui(PREFS["dim"])
        self._push_image()

    def toggle_night(self, on):
        dim = (PREFS["dim"] or 55) if on else 0
        PREFS["dim"] = dim
        save_prefs()
        self.pages["home"].set_night_ui(dim)
        self._push_image()

    def _push_image(self):
        if self.blackout_on:
            return
        d = PREFS["dim"]
        eff = {"brightness": clamp(self.base["brightness"] - d * 0.45),
               "contrast": clamp(self.base["contrast"] - d * 0.35),
               "saturation": clamp(self.base["saturation"] - d * 0.25)}
        for kind, v in eff.items():
            self.latest.submit("pq:" + kind, pq_set, kind, round(v))

    def blackout(self, on):
        """Apaga/acende a imagem sem parar os apps.
        1) scrcpy: SET_DISPLAY_POWER (o mesmo do `scrcpy --turn-screen-off`), exige o espelho ativo;
        2) em paralelo, brilho/contraste/saturacao 0 via tvctl (se tools/tvctl.dex existir)."""
        on = bool(on)
        if not self.online:
            self.toast("Projetor desconectado.", "err")
            return
        if on:
            if any(self.base.values()):
                PREFS["base"] = dict(self.base)   # guarda o valor normal para restaurar depois
                save_prefs()
            self.blackout_on = True
            via_scrcpy = self.mirror.set_display_power(False)
            have_pq = TVCTL_DEX.exists()
            if have_pq:
                for kind in IMG_CODE:
                    self.latest.submit("pq:" + kind, pq_set, kind, 0)
            if via_scrcpy:
                self.toast("Tela apagada. Os apps continuam rodando.", "ok")
            elif have_pq:
                self.toast("Imagem apagada por brilho/contraste (espelho scrcpy inativo).", "ok")
            else:
                self.blackout_on = False
                self.toast("Não deu para apagar: espelho scrcpy inativo e tools/tvctl.dex não encontrado.", "err")
        else:
            self.blackout_on = False
            self.mirror.set_display_power(True)
            self._push_image()
            self.toast("Tela restaurada.", "ok")

    # ----------------------------------------------- midia e espelho -- #
    def poll_media(self, force=False):
        if not self.online or self._media_busy:
            return
        if self.page not in ("home", "live") and not force:
            return
        self._media_busy = True
        self.bg(media_info, self._media_got)

    def _media_got(self, info, _err):
        self._media_busy = False
        if info:
            self.media = {**info, "t": time.monotonic()}
            self.media_now = info["pos"]

    def _tick(self):
        m = self.media
        if not m:
            return
        est = m["pos"] + ((time.monotonic() - m["t"]) if m["playing"] else 0)
        if m["dur"]:
            est = min(est, m["dur"])
        self.media_now = max(0.0, est)
        if self.page in ("home", "live"):
            self.pages[self.page].show_time(self.media_now, m["dur"], m["playing"], m["title"], m["pkg"])

    def _pull_frames(self):
        if self.page == "live" and self.mirror.ready:
            self.pages["live"].pull_frame()

    def _auto_shot(self):
        if self.online and self.page == "live" and not self.mirror.ready and not self._mirror_busy:
            self.pages["live"].refresh()

    # ------------------------------------------------------ teclado -- #
    def _on_key(self, e):
        if not self.kb_on or not self.online:
            return None
        try:
            w = self.focus_get()
        except Exception:
            w = None
        if w is not None:
            if w.winfo_toplevel() is not self:
                return None
            if isinstance(w, (tk.Entry, tk.Text, tk.Spinbox)):
                return None
        special = {
            "Up": KEY["UP"], "Down": KEY["DOWN"], "Left": KEY["LEFT"], "Right": KEY["RIGHT"],
            "Return": 66, "KP_Enter": 66, "BackSpace": 67, "Delete": 112,
            "Escape": KEY["BACK"], "Tab": 61, "Home": 122, "End": 123,
        }
        if e.keysym in special:
            self.key(special[e.keysym])
            return "break"
        if e.char and len(e.char) == 1 and ord(e.char) >= 32 and not (e.state & 0xC):
            self.send_text(e.char)
            return "break"
        return None

    def _on_wheel(self, e, direction=None):
        d = direction if direction is not None else (-1 if e.delta > 0 else 1)
        try:
            w = self.winfo_containing(e.x_root, e.y_root)
        except Exception:
            w = None
        while w is not None:
            fn = getattr(w, "_wheel", None)
            if fn:
                fn(d)
                return
            w = getattr(w, "master", None)

    def run(self):
        self.mainloop()


def main():
    log("---- inicio ----")
    try:
        App().run()
    except Exception:
        msg = traceback.format_exc()
        log(msg)
        try:
            (CACHE / "erro.log").write_text(msg, encoding="utf-8")
        except Exception:
            pass
        try:
            messagebox.showerror("Projetor Remote", msg[-1200:])
        except Exception:
            pass
        raise


if __name__ == "__main__":
    main()