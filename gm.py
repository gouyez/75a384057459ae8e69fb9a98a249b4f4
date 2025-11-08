#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
gmail_hybrid_manager.py — Windows-only (v3.6.1)

This version:
- Adds a "Browse…" button to load Gmail accounts from a text file (one per line).
  * If a file is selected, the accounts textarea is disabled and ignored.
  * "Clear file" returns to manual entry.
  * Full path is shown in the UI (dark theme, integrated).
- Uses resource_path() for credentials.json so OAuth works regardless of CWD.
- GUI: separates actions into bordered boxes that match the app theme:
  * Chrome actions box (Open Gmail UI, Shorts + inline #, Click links + inline #)
  * API actions box (NOT SPAM, IMPORTANT)
  * Concurrency box at the bottom (Max concurrent Chrome sessions)
- Keeps the rest of v3.6.1 behavior intact.
- Stability:
  * Profile auto-repair (Preferences/Local State JSONs) before launch
  * Profile lock detection/wait to avoid corruption
  * Graceful Browser.close over CDP, with terminate/kill as fallback
"""

import os
import re
import json
import base64
import tkinter as tk
from tkinter import ttk, scrolledtext, filedialog, messagebox
import sys
import time
import shutil
import tempfile
import subprocess
import platform
from pathlib import Path
import random
import socket
import threading
import http.server
import urllib.parse
import requests
from dataclasses import dataclass
from typing import Optional, Callable, List, Dict, Set
from concurrent.futures import ThreadPoolExecutor, as_completed

# Optional dependency for CDP
try:
    import websocket  # pip install websocket-client
except Exception:
    websocket = None

from google.oauth2.credentials import Credentials
from google_auth_oauthlib.flow import InstalledAppFlow
from google.auth.transport.requests import Request
from googleapiclient.discovery import build

# ===== App meta =====
APP_VERSION = "3.6.1"
UPDATE_JSON_URL = "https://raw.githubusercontent.com/gouyez/75a384057459ae8e69fb9a98a249b4f4/main/version.json"

# ===== Windows-only =====
if platform.system().lower() != "windows":
    raise SystemExit("This app is Windows-only. Please run on Windows.")

# ===== OAuth / tokens =====
CREDENTIALS_FILE = "credentials.json"  # place next to the EXE/py
TOKENS_DIR = "emails"  # stored next to EXE/py
SCOPES = [
    "https://www.googleapis.com/auth/gmail.modify",
    "https://www.googleapis.com/auth/contacts",
]
EMAIL_REGEX = re.compile(r"^[^@\s]+@[^@\s]+\.[a-zA-Z0-9]+$")

# ===== App data paths =====
LOCAL_APP_ROOT = (
    Path(os.environ.get("LOCALAPPDATA", str(Path.home() / "AppData" / "Local")))
    / "GmailHybrid"
)
MASTER_CHROME_DIR = LOCAL_APP_ROOT / "chrome_master"
CHROMES_DIR = LOCAL_APP_ROOT / "chromes"
PROFILES_DIR = LOCAL_APP_ROOT / "profiles"
CHROME_MAP_FILE = LOCAL_APP_ROOT / "chrome_map.json"

for p in (LOCAL_APP_ROOT, CHROMES_DIR, PROFILES_DIR):
    p.mkdir(parents=True, exist_ok=True)

# ===== PyInstaller resource =====
def is_frozen() -> bool:
    return getattr(sys, "frozen", False) and hasattr(sys, "_MEIPASS")


def resource_path(relative: str) -> Path:
    if is_frozen():
        base = Path(sys._MEIPASS)  # type: ignore[attr-defined]
        return base / relative
    return Path(relative).absolute()


# Make a canonical credentials path that works regardless of CWD
CREDENTIALS_PATH = resource_path(CREDENTIALS_FILE)

# ===== Shorts discovery =====
SHORTS_SEARCH_QUERIES = [
    "shorts", "trending shorts", "viral shorts", "funny shorts", "music shorts",
    "gaming shorts", "tech shorts", "life hacks shorts", "satisfying shorts",
    "fails shorts", "football shorts", "basketball shorts", "soccer shorts",
    "science shorts", "learning shorts", "pet shorts", "cat shorts", "dog shorts",
    "memes shorts", "asmr shorts", "movie shorts", "clip shorts", "travel shorts",
    "food shorts", "cooking shorts", "art shorts", "animation shorts",
]
SHORTS_REGEX = re.compile(r"/shorts/([A-Za-z0-9_-]{8,})")

def fetch_shorts_links(max_links=50, log_fn=print, exclude_ids=None):
    if exclude_ids is None:
        exclude_ids = set()
    found_urls = []
    found_ids = set()
    headers = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/118.0 Safari/537.36"
    }
    queries = SHORTS_SEARCH_QUERIES[:]
    random.shuffle(queries)
    for q in queries:
        try:
            url = f"https://www.youtube.com/results?search_query={urllib.parse.quote_plus(q)}"
            log_fn(f"[SHORTS] fetching search: {q}")
            r = requests.get(url, headers=headers, timeout=10)
            if r.status_code != 200:
                log_fn(f"[SHORTS] search {q} returned {r.status_code}")
                continue
            matches = SHORTS_REGEX.findall(r.text)
            random.shuffle(matches)
            for sid in matches:
                if sid in found_ids or sid in exclude_ids:
                    continue
                found_ids.add(sid)
                found_urls.append(f"https://www.youtube.com/shorts/{sid}")
                if len(found_urls) >= max_links:
                    return found_urls
            time.sleep(0.3)
        except Exception as e:
            log_fn(f"[SHORTS][ERROR] {e}")
            continue
    return found_urls

# ===== Extract master Chrome =====
def ensure_master_extracted(log_fn=print) -> bool:
    if MASTER_CHROME_DIR.exists():
        return True
    src = resource_path("chrome_master")
    if not src.exists():
        alt = Path(__file__).with_name("chrome_master")
        if alt.exists():
            src = alt
        else:
            log_fn("[MASTER] chrome_master not found.")
            return False
    log_fn(f"[MASTER] Extracting master Chrome to: {MASTER_CHROME_DIR}")
    try:
        shutil.copytree(src, MASTER_CHROME_DIR)
    except FileExistsError:
        pass
    return True


# ===== Token helpers =====
def ensure_tokens_dir():
    Path(TOKENS_DIR).mkdir(exist_ok=True)


def token_path_for(email: str) -> str:
    safe_name = email.replace("/", "_")
    return str(Path(TOKENS_DIR) / f"{safe_name}.json")


def _safe_email_token(email: str) -> str:
    return (
        "".join(c for c in email.lower() if c.isalnum() or c in ("@", ".", "_", "-"))
        .replace("@", "_at_")
        .replace(".", "_")
    )


def profile_dir_for(email: str) -> Path:
    return PROFILES_DIR / _safe_email_token(email)


def cloned_install_dir_for(email: str) -> Path:
    return CHROMES_DIR / _safe_email_token(email)


def _load_chrome_map() -> dict:
    if CHROME_MAP_FILE.exists():
        try:
            return json.load(open(CHROME_MAP_FILE, "r", encoding="utf-8"))
        except Exception:
            return {}
    return {}


def _save_chrome_map(mapping: dict):
    CHROME_MAP_FILE.parent.mkdir(parents=True, exist_ok=True)
    tmp = CHROME_MAP_FILE.with_suffix(".json.tmp")
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(mapping, f, indent=2)
    os.replace(tmp, CHROME_MAP_FILE)


def _find_chrome_executable(base_dir: Path) -> Optional[Path]:
    candidates = [
        base_dir / "chrome.exe",
        base_dir / "Application" / "chrome.exe",
        base_dir / "Google" / "Chrome" / "Application" / "chrome.exe",
        base_dir / "Chromium" / "Application" / "chrome.exe",
        base_dir / "App" / "Chrome-bin" / "chrome.exe",
    ]
    for c in candidates:
        if c.exists():
            return c
    for root, _, files in os.walk(base_dir):
        rel = Path(root).relative_to(base_dir)
        if len(rel.parts) > 4:
            continue
        if "chrome.exe" in files:
            return Path(root) / "chrome.exe"
    return None


def _clone_master_for_email(email: str, log_fn=print) -> Path:
    ok = ensure_master_extracted(log_fn)
    if not ok:
        raise FileNotFoundError(
            "chrome_master not found. Put 'chrome_master' next to the script "
            'or build with --add-data "chrome_master;chrome_master".'
        )
    dest = cloned_install_dir_for(email)
    if not dest.exists():
        log_fn(f"[CLONE] Cloning master for {email} -> {dest}")
        try:
            shutil.copytree(MASTER_CHROME_DIR, dest)
        except FileExistsError:
            pass
        except Exception as e:
            raise RuntimeError(f"Failed to clone master Chrome for {email}: {e}")
    else:
        log_fn(f"[CLONE] Already exists for {email}: {dest}")

    exe = _find_chrome_executable(dest)
    if not exe or not exe.exists():
        raise FileNotFoundError(f"chrome.exe not found in cloned dir: {dest}")

    mapping = _load_chrome_map()
    mapping[email] = str(exe)
    _save_chrome_map(mapping)
    log_fn(f"[MAP] {email} -> {exe}")
    return exe


def _resolve_or_create_chrome_for(email: str, log_fn=print) -> str:
    mapping = _load_chrome_map()
    exe = mapping.get(email)
    if exe and Path(exe).exists():
        return exe
    return str(_clone_master_for_email(email, log_fn=log_fn))


# ===== Profile health/locks =====
def _is_json_file_valid(p: Path) -> bool:
    try:
        if not p.exists() or p.stat().st_size == 0:
            return False
        with open(p, "r", encoding="utf-8") as f:
            json.load(f)
        return True
    except Exception:
        return False


def _repair_profile_if_corrupted(profile_dir: Path, log_fn=print) -> None:
    suspects = [
        profile_dir / "Preferences",
        profile_dir / "Secure Preferences",
        profile_dir / "Local State",
    ]
    repaired = 0
    ts = int(time.time())
    for p in suspects:
        if p.exists() and not _is_json_file_valid(p):
            try:
                bak = p.with_suffix(p.suffix + f".corrupt.{ts}.bak")
                shutil.move(str(p), str(bak))
                repaired += 1
                log_fn(f"[PROFILE] Repaired corrupt file → {p.name} (moved to {bak.name})")
            except Exception as e:
                log_fn(f"[PROFILE][WARN] Could not move {p.name}: {e}")
    if repaired:
        for name in ["Last Session", "Last Tabs", "Current Session", "Current Tabs"]:
            f = profile_dir / "Default" / name
            try:
                if f.exists():
                    f.unlink()
            except Exception:
                pass


def _is_profile_locked(profile_dir: Path) -> bool:
    locks = [
        profile_dir / "SingletonLock",
        profile_dir / "SingletonCookie",
        profile_dir / "SingletonSocket",
        profile_dir / "lockfile",
    ]
    return any(l.exists() for l in locks)


def _wait_profile_unlock(profile_dir: Path, timeout: float, log_fn=print) -> bool:
    end = time.time() + timeout
    while time.time() < end:
        if not _is_profile_locked(profile_dir):
            return True
        time.sleep(0.25)
    if _is_profile_locked(profile_dir):
        log_fn("[PROFILE][WARN] Profile appears in use/locked; continuing may risk corruption.")
        return False
    return True


# Provide public wrappers matching earlier calls
def repair_profile(profile_dir: Path, log_fn=print):
    return _repair_profile_if_corrupted(profile_dir, log_fn=log_fn)


def wait_for_profile_unlock(profile_dir: Path, timeout: float = 8.0, log_fn=print):
    return _wait_profile_unlock(profile_dir, timeout=timeout, log_fn=log_fn)


# ===== CDP / Chrome session helpers =====
def _find_free_port_tcp() -> int:
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    s.bind(("127.0.0.1", 0))
    port = s.getsockname()[1]
    s.close()
    return port


def _http_json(url, timeout=6):
    try:
        r = requests.get(url, timeout=timeout)
        r.raise_for_status()
        return r.json()
    except Exception:
        return None


def _wait_for_debug_endpoint(port: int, timeout=12):
    deadline = time.time() + timeout
    while time.time() < deadline:
        try:
            r = requests.get(f"http://127.0.0.1:{port}/json", timeout=1)
            if r.status_code == 200:
                return True
        except Exception:
            time.sleep(0.2)
    return False


def _create_new_tab_and_get_ws(port: int, initial_url: str = "about:blank") -> Optional[str]:
    try:
        info = _http_json(
            f"http://127.0.0.1:{port}/json/new?{urllib.parse.quote_plus(initial_url)}",
            timeout=6,
        )
        if info and info.get("webSocketDebuggerUrl"):
            return info["webSocketDebuggerUrl"]
        info_list = _http_json(f"http://127.0.0.1:{port}/json", timeout=4)
        if not info_list:
            return None
        for entry in info_list:
            if entry.get("webSocketDebuggerUrl"):
                return entry["webSocketDebuggerUrl"]
    except Exception:
        return None
    return None


def _send_cdp_cmd(ws_conn, method: str, params: dict = None, _id_gen=[1000]):
    if params is None:
        params = {}
    _id_gen[0] += 1
    msg = {"id": _id_gen[0], "method": method, "params": params}
    ws_conn.send(json.dumps(msg))
    return _id_gen[0]


def _recv_cdp_until(ws_conn, predicate, timeout=20.0):
    deadline = time.time() + timeout
    while time.time() < deadline:
        try:
            raw = ws_conn.recv()
        except Exception:
            time.sleep(0.05)
            continue
        try:
            msg = json.loads(raw)
        except Exception:
            continue
        if predicate(msg):
            return msg
    return None


def _browser_ws_url(port: int) -> Optional[str]:
    info = _http_json(f"http://127.0.0.1:{port}/json/version", timeout=3)
    if not info:
        return None
    return info.get("webSocketDebuggerUrl")


@dataclass
class ChromeSession:
    email: str
    port: int
    proc: subprocess.Popen
    ws_url: str  # websocketDebuggerUrl of one tab


def start_chrome_session(email: str, log_fn=print) -> Optional[ChromeSession]:
    if websocket is None:
        raise RuntimeError(
            "Missing 'websocket-client'. Install: python -m pip install websocket-client"
        )

    port = _find_free_port_tcp()
    try:
        chrome_exe = _resolve_or_create_chrome_for(email, log_fn=log_fn)
    except Exception as e:
        log_fn(f"[SESSION][ERROR] resolve chrome: {e}")
        return None

    pdir = profile_dir_for(email)
    pdir.mkdir(parents=True, exist_ok=True)

    _repair_profile_if_corrupted(pdir, log_fn=log_fn)
    _wait_profile_unlock(pdir, timeout=8.0, log_fn=log_fn)

    cmd = [
        str(chrome_exe),
        f"--user-data-dir={str(pdir)}",
        f"--remote-debugging-port={port}",
        "--remote-allow-origins=*",
        "--disable-site-isolation-trials",
        "--no-first-run",
        "--no-default-browser-check",
        "--disable-default-apps",
        "--disable-translate",
        "--test-type",
        "--autoplay-policy=no-user-gesture-required",
        "--allow-insecure-localhost",
        "--ignore-certificate-errors",
        "--disable-features=BlockInsecurePrivateNetworkRequests",
    ]
    try:
        proc = subprocess.Popen(
            cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL
        )
    except Exception as e:
        log_fn(f"[SESSION][ERROR] start chrome: {e}")
        return None

    if not _wait_for_debug_endpoint(port, timeout=12):
        log_fn(f"[SESSION][ERROR] debug endpoint not ready on {port}")
        try:
            proc.terminate()
        except Exception:
            pass
        return None

    ws_url = None
    deadline = time.time() + 10
    while time.time() < deadline and not ws_url:
        ws_url = _create_new_tab_and_get_ws(port, initial_url="about:blank")
        if not ws_url:
            time.sleep(0.25)

    if not ws_url:
        log_fn("[SESSION][ERROR] Could not create initial tab")
        try:
            proc.terminate()
        except Exception:
            pass
        return None

    log_fn(f"[SESSION] started for {email} (port {port})")
    return ChromeSession(email=email, port=port, proc=proc, ws_url=ws_url)


def close_chrome_session(sess: ChromeSession, log_fn=print, natural_delay=0.4, aggressive=True):
    try:
        if natural_delay and natural_delay > 0:
            time.sleep(natural_delay)

        try:
            bws = _browser_ws_url(sess.port)
            if bws:
                ws = websocket.create_connection(bws, timeout=4)
                try:
                    _send_cdp_cmd(ws, "Browser.close", {})
                finally:
                    try:
                        ws.close()
                    except Exception:
                        pass
        except Exception as e:
            log_fn(f"[SESSION][INFO] Browser.close failed/ignored: {e}")

        try:
            sess.proc.wait(timeout=4.0)
        except Exception:
            pass

        if sess.proc.poll() is None:
            log_fn("[SESSION] Graceful close timed out → terminate()")
            try:
                sess.proc.terminate()
            except Exception:
                pass
            try:
                sess.proc.wait(timeout=1.2)
            except Exception:
                try:
                    log_fn("[SESSION] terminate timed out → kill()")
                    sess.proc.kill()
                except Exception:
                    pass

        if aggressive:
            prof_dir = profile_dir_for(sess.email)
            _aggressive_kill_chrome_for_profile(prof_dir, sess.port, log_fn=log_fn)

        time.sleep(0.2)
    except Exception as e:
        log_fn(f"[SESSION][WARN] close exception: {e}")


def _aggressive_kill_chrome_for_profile(profile_dir: Path, port: int | None, log_fn=print):
    """Windows-only: kill any chrome.exe whose CommandLine references this profile (or the remote debugging port)."""
    try:
        prof_str = str(profile_dir)
        prof_norm = prof_str.lower().replace("/", "\\")
        port_str = f"--remote-debugging-port={port}" if port else None

        # Try WMIC; if missing, fallback to PowerShell
        try:
            out = subprocess.check_output(
                [
                    "wmic",
                    "process",
                    "where",
                    "name='chrome.exe'",
                    "get",
                    "CommandLine,ProcessId",
                    "/FORMAT:CSV",
                ],
                stderr=subprocess.STDOUT,
                creationflags=0x08000000,
            ).decode("utf-8", errors="ignore")
        except Exception:
            ps = r"""
$procs = Get-CimInstance Win32_Process | Where-Object { $_.Name -eq 'chrome.exe' }
$procs | ForEach-Object { "$($_.CommandLine)|$($_.ProcessId)" }
"""
            out = subprocess.check_output(
                ["powershell", "-NoProfile", "-ExecutionPolicy", "Bypass", "-Command", ps],
                stderr=subprocess.STDOUT,
                creationflags=0x08000000,
            ).decode("utf-8", errors="ignore")

        pids_to_kill = []
        for line in out.splitlines():
            line = line.strip()
            if not line:
                continue

            cmdline = ""
            pid = None

            if "|" in line:
                parts = line.split("|")
                if len(parts) >= 2 and parts[-1].strip().isdigit():
                    cmdline = parts[0].lower()
                    pid = int(parts[-1].strip())
            else:
                if line.startswith("Node,") or ",CommandLine," in line:
                    continue
                parts = line.split(",", 2)
                if len(parts) >= 3:
                    cmdline = (parts[1] or "").lower()
                    pid_str = parts[2].strip()
                    if pid_str.isdigit():
                        pid = int(pid_str)

            if pid is None:
                continue

            hit_profile = (
                prof_norm and (
                    (prof_norm in cmdline)
                    or (f'--user-data-dir="{prof_norm}"' in cmdline)
                    or (f"--user-data-dir={prof_norm}" in cmdline)
                )
            )
            hit_port = bool(port_str and (port_str in cmdline))

            if hit_profile or hit_port:
                pids_to_kill.append(pid)

        killed = 0
        for pid in pids_to_kill:
            try:
                subprocess.run(
                    ["taskkill", "/PID", str(pid), "/T", "/F"],
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                    creationflags=0x08000000,
                )
                killed += 1
            except Exception:
                pass

        if killed:
            log_fn(f"[SESSION] Aggressively killed {killed} chrome.exe tied to this profile/port.")
    except Exception as e:
        log_fn(f"[SESSION][WARN] aggressive kill failed: {e}")


# ===== OAuth loopback handler =====
class _OAuthHandler(http.server.BaseHTTPRequestHandler):
    shared = None

    def _write(self, html: str):
        self.send_response(200)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.end_headers()
        self.wfile.write(html.encode("utf-8"))

    def do_GET(self):
        parsed = urllib.parse.urlparse(self.path)
        qs = urllib.parse.parse_qs(parsed.query)
        if parsed.path not in ("/", "/callback"):
            self.send_response(404)
            self.end_headers()
            return

        if "error" in qs:
            _OAuthHandler.shared["error"] = qs.get("error", [""])[0]
            self._write(
                """<!doctype html><meta charset="utf-8">
                <h2 style="font-family:system-ui;margin:20px;">Authorization error.</h2>
                <script>setTimeout(()=>{window.close()},1200);</script>"""
            )
            return

        code = qs.get("code", [None])[0]
        if code:
            _OAuthHandler.shared["code"] = code
            self._write(
                """<!doctype html><meta charset="utf-8">
                <h2 style="font-family:system-ui;margin:20px;">Sign-in complete. Redirecting to Gmail…</h2>
                <script>setTimeout(function(){location.replace('https://mail.google.com/mail/u/0/#inbox');},800);</script>"""
            )
        else:
            self._write(
                """<!doctype html><meta charset="utf-8">
                <h2 style="font-family:system-ui;margin:20px;">No code found.</h2>
                <script>setTimeout(()=>{window.close()},1200);</script>"""
            )

    def log_message(self, fmt, *args):
        return


def _find_free_port() -> int:
    s = socket.socket()
    s.bind(("127.0.0.1", 0))
    port = s.getsockname()[1]
    s.close()
    return port


def _oauth_once_with_session(email: str, sess: ChromeSession, log_fn):
    # Use canonical credentials path
    if not os.path.exists(CREDENTIALS_PATH):
        raise FileNotFoundError("Missing credentials.json next to the app.")

    port = _find_free_port()
    redirect_uri = f"http://127.0.0.1:{port}/callback"
    log_fn(f"[OAuth] starting on {redirect_uri}")

    flow = InstalledAppFlow.from_client_secrets_file(
        CREDENTIALS_PATH, SCOPES, redirect_uri=redirect_uri
    )
    auth_url, _ = flow.authorization_url(
        access_type="offline", prompt="consent", include_granted_scopes="true"
    )

    shared = {}
    _OAuthHandler.shared = shared

    server = http.server.HTTPServer(("127.0.0.1", port), _OAuthHandler)
    t = threading.Thread(target=server.serve_forever, daemon=True)
    t.start()

    cdp_navigate(sess.ws_url, auth_url, wait_load=False, log_fn=log_fn)

    deadline = time.time() + 600
    last_ping = 0
    while time.time() < deadline:
        now = time.time()
        if now - last_ping > 5:
            log_fn("[OAuth] awaiting callback …")
            last_ping = now
        if "error" in shared:
            server.shutdown()
            raise RuntimeError(f"OAuth error: {shared['error']}")
        if "code" in shared:
            log_fn("[OAuth] received code → exchanging token …")
            server.shutdown()
            flow.fetch_token(code=shared["code"])
            creds = flow.credentials
            tok_path = token_path_for(email)
            with open(tok_path, "w") as f:
                f.write(creds.to_json())
            log_fn(f"[TOKEN] saved: {tok_path}")
            return creds, True
        time.sleep(0.3)

    server.shutdown()
    raise TimeoutError("Timed out waiting for authorization completion.")


def oauth_first_login_in_session(email: str, sess: ChromeSession, log_fn, also_open_gmail_ui: bool):
    try:
        return _oauth_once_with_session(email, sess, log_fn)
    except Exception as e:
        log_fn(f"[OAuth] first attempt failed: {e}. Retrying once …")
        time.sleep(2)
        return _oauth_once_with_session(email, sess, log_fn)


# ===== Gmail API helpers =====
def load_credentials_for(email, log_fn):
    tok = token_path_for(email)
    creds = None
    if os.path.exists(tok):
        try:
            creds = Credentials.from_authorized_user_file(tok, SCOPES)
        except Exception as e:
            log_fn(f"[TOKEN] parse failed for {email}: {e}")
            creds = None
    if creds and creds.valid:
        log_fn("[TOKEN] valid")
        return creds
    if creds and creds.expired and creds.refresh_token:
        log_fn("[TOKEN] expired → refreshing…")
        try:
            creds.refresh(Request())
            with open(tok, "w") as f:
                f.write(creds.to_json())
            log_fn("[TOKEN] refreshed")
            return creds
        except Exception as e:
            log_fn(f"[TOKEN] refresh failed: {e}")
            raise
    raise RuntimeError("No valid token for this account.")


def build_gmail_service(creds):
    return build("gmail", "v1", credentials=creds)


def build_people_service(creds):
    return build("people", "v1", credentials=creds)


def search_messages(service, query, max_results=500, log_fn=None):
    messages = []
    try:
        req = (
            service.users()
            .messages()
            .list(userId="me", q=query, maxResults=100, includeSpamTrash=True)
        )
        while req:
            resp = req.execute()
            if resp.get("messages"):
                messages.extend(resp["messages"])
                if log_fn:
                    log_fn(f"[SEARCH] {len(messages)} found so far…")
            req = service.users().messages().list_next(req, resp)
            if len(messages) >= max_results:
                break
    except Exception as e:
        if log_fn:
            log_fn(f"[SEARCH][ERROR] {e}")
    return messages[:max_results]


def get_message_full(service, msg_id):
    return (
        service.users().messages().get(userId="me", id=msg_id, format="full").execute()
    )


def mark_as_read(service, msg_id, log_fn=None):
    try:
        service.users().messages().modify(
            userId="me", id=msg_id, body={"removeLabelIds": ["UNREAD"]}
        ).execute()
        if log_fn:
            log_fn(f"[MSG] {msg_id} marked READ")
    except Exception as e:
        if log_fn:
            log_fn(f"[MSG][ERROR] mark read {msg_id}: {e}")


# ===== Simple CDP navigate helper =====
def cdp_navigate(ws_url: str, url: str, wait_load=True, timeout=12, log_fn=print) -> bool:
    try:
        ws = websocket.create_connection(ws_url, timeout=8)
    except Exception as e:
        log_fn(f"[CDP] connect failed: {e}")
        return False
    ok = False
    try:
        _send_cdp_cmd(ws, "Page.enable")
        _send_cdp_cmd(ws, "Page.navigate", {"url": url})
        if wait_load:
            got = _recv_cdp_until(
                ws, lambda m: m.get("method") == "Page.loadEventFired", timeout=timeout
            )
            ok = got is not None
        else:
            ok = True
    except Exception as e:
        log_fn(f"[CDP] navigate error: {e}")
        ok = False
    finally:
        try:
            ws.close()
        except Exception:
            pass
    if ok:
        time.sleep(0.2)
    return ok


# ===== App GUI =====
class GmailHybridApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Gmail Hybrid Manager (Windows)")
        self.geometry("1100x780")
        self.configure(bg="#2b2b2b")

        ensure_tokens_dir()

        # File-mode holder (full path to accounts file or None)
        self.accounts_file: Optional[str] = None

        self._setup_styles()
        self._create_widgets()

        if not ensure_master_extracted(self._log_console):
            messagebox.showerror(
                "Chrome master not found",
                "Could not find embedded 'chrome_master'.\n\n"
                "Dev mode: put a 'chrome_master' folder next to this .py/.exe.\n"
                'Build mode: include with PyInstaller --add-data "chrome_master;chrome_master".',
            )

        # Safe stub to avoid NameError if updater isn't bundled
        self.after(250, lambda: check_for_update_and_prompt(self))

    def _setup_styles(self):
        style = ttk.Style(self)
        style.theme_use("default")
        style.configure(
            "Vertical.TScrollbar",
            background="#3c3f41",
            darkcolor="#3c3f41",
            lightcolor="#3c3f41",
            troughcolor="#2b2b2b",
            bordercolor="#2b2b2b",
            arrowcolor="#FFFFFF",
        )
        style.configure(
            "Horizontal.TScrollbar",
            background="#3c3f41",
            darkcolor="#3c3f41",
            lightcolor="#3c3f41",
            troughcolor="#2b2b2b",
            bordercolor="#2b2b2b",
            arrowcolor="#FFFFFF",
        )

    def _create_widgets(self):
        main_frame = tk.Frame(self, bg="#2b2b2b")
        main_frame.pack(fill=tk.BOTH, expand=True, padx=8, pady=6)

        # Left side
        left = tk.Frame(main_frame, bg="#2b2b2b")
        left.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        ttk.Label(
            left,
            text="Gmail accounts (one per line):",
            background="#2b2b2b",
            foreground="#EEEEEE",
        ).pack(anchor="w")
        self.accounts_box = scrolledtext.ScrolledText(
            left,
            height=8,
            bg="#3c3f41",
            fg="#FFFFFF",
            insertbackground="#FFFFFF",
            relief="flat",
        )
        self.accounts_box.pack(fill=tk.X, padx=2, pady=4)

        # ---- Browse/Clear row (Switch Mode) under the accounts textbox ----
        accounts_file_row = tk.Frame(left, bg="#2b2b2b")
        accounts_file_row.pack(fill=tk.X, pady=(2, 0))

        self.btn_browse_accounts = tk.Button(
            accounts_file_row,
            text="Browse…",
            command=self._browse_accounts_file,
            bg="#3c3f41",
            fg="#FFFFFF",
            relief="flat",
            padx=10, pady=2
        )
        self.btn_browse_accounts.pack(side="left")

        # FULL PATH display when a file is selected
        self.accounts_file_label = tk.Label(
            accounts_file_row,
            text="",
            bg="#2b2b2b",
            fg="#AAAAAA",
            anchor="w",
        )
        self.accounts_file_label.pack(side="left", padx=8, expand=True, fill=tk.X)

        self.btn_clear_accounts = tk.Button(
            accounts_file_row,
            text="Clear file",
            command=self._clear_accounts_file,
            bg="#3c3f41",
            fg="#FFFFFF",
            relief="flat",
            padx=10, pady=2
        )
        self.btn_clear_accounts.pack(side="right")
        self.btn_clear_accounts.pack_forget()  # hidden until a file is selected
        # -------------------------------------------------------------------

        sub = tk.Frame(left, bg="#2b2b2b")
        sub.pack(fill=tk.X, pady=6)

        ttk.Label(
            sub,
            text="Emails to add as contacts (use ; to separate):",
            background="#2b2b2b",
            foreground="#EEEEEE",
        ).grid(row=0, column=0, sticky="w")
        self.contact_entry = tk.Entry(
            sub, bg="#3c3f41", fg="#FFFFFF", insertbackground="#FFFFFF", relief="flat"
        )
        self.contact_entry.grid(row=0, column=1, sticky="we", padx=6)
        sub.columnconfigure(1, weight=1)

        ttk.Label(
            sub,
            text="Search term(s) for From/Subject (use ; to separate):",
            background="#2b2b2b",
            foreground="#EEEEEE",
        ).grid(row=1, column=0, sticky="w", pady=6)
        self.search_entry = tk.Entry(
            sub, bg="#3c3f41", fg="#FFFFFF", insertbackground="#FFFFFF", relief="flat"
        )
        self.search_entry.grid(row=1, column=1, sticky="we", padx=6)

        # Right side root (column container)
        right = tk.Frame(
            main_frame,
            bg="#2b2b2b",
        )
        right.pack(side=tk.RIGHT, fill=tk.Y, padx=6)

        # ---------- Chrome actions group ----------
        chrome_group = tk.LabelFrame(
            right,
            text="Chrome actions",
            bg="#2b2b2b",
            fg="#EEEEEE",
            padx=10,
            pady=10,
            relief="groove",
            bd=2,
        )
        chrome_group.pack(fill=tk.X, pady=(0, 10))

        self.var_open_gmail_ui = tk.BooleanVar(value=False)
        row_ui = tk.Frame(chrome_group, bg="#2b2b2b")
        row_ui.pack(fill=tk.X, pady=2)
        tk.Checkbutton(
            row_ui,
            text="Open Gmail UI (always)",
            variable=self.var_open_gmail_ui,
            bg="#2b2b2b",
            fg="#FFFFFF",
            selectcolor="#3c3f41",
            activebackground="#3c3f41",
            activeforeground="#FFFFFF",
            relief="flat",
        ).pack(side=tk.LEFT, anchor="w")

        # Shorts (checkbox + inline input)
        self.var_play_shorts = tk.BooleanVar(value=False)
        self.shorts_count_var = tk.StringVar(value="3")
        row_shorts = tk.Frame(chrome_group, bg="#2b2b2b")
        row_shorts.pack(fill=tk.X, pady=2)
        self.chk_play_shorts = tk.Checkbutton(
            row_shorts,
            text="Play YouTube Shorts",
            variable=self.var_play_shorts,
            command=self._on_action_toggled,
            bg="#2b2b2b",
            fg="#FFFFFF",
            selectcolor="#3c3f41",
            activebackground="#3c3f41",
            activeforeground="#FFFFFF",
            relief="flat",
        )
        self.chk_play_shorts.pack(side=tk.LEFT, anchor="w")
        tk.Label(row_shorts, text=" #", bg="#2b2b2b", fg="#FFFFFF").pack(side=tk.LEFT)
        self.shorts_count_entry = tk.Entry(
            row_shorts,
            textvariable=self.shorts_count_var,
            width=6,
            bg="#3c3f41",
            fg="#FFFFFF",
            relief="flat",
            state=tk.DISABLED,
        )
        self.shorts_count_entry.pack(side=tk.LEFT, padx=6)

        # Click links (checkbox + inline input)
        self.var_click_links = tk.BooleanVar(value=False)
        self.click_links_count_var = tk.StringVar(value="3")
        row_links = tk.Frame(chrome_group, bg="#2b2b2b")
        row_links.pack(fill=tk.X, pady=2)
        self.chk_click_links = tk.Checkbutton(
            row_links,
            text="Click links (from unread emails)",
            variable=self.var_click_links,
            command=self._on_action_toggled,
            bg="#2b2b2b",
            fg="#FFFFFF",
            selectcolor="#3c3f41",
            activebackground="#3c3f41",
            activeforeground="#FFFFFF",
            relief="flat",
        )
        self.chk_click_links.pack(side=tk.LEFT, anchor="w")
        tk.Label(row_links, text=" #", bg="#2b2b2b", fg="#FFFFFF").pack(side=tk.LEFT)
        self.click_links_count_entry = tk.Entry(
            row_links,
            textvariable=self.click_links_count_var,
            width=6,
            bg="#3c3f41",
            fg="#FFFFFF",
            relief="flat",
            state=tk.DISABLED,
        )
        self.click_links_count_entry.pack(side=tk.LEFT, padx=6)

        # ---------- API actions group ----------
        api_group = tk.LabelFrame(
            right,
            text="API actions",
            bg="#2b2b2b",
            fg="#EEEEEE",
            padx=10,
            pady=10,
            relief="groove",
            bd=2,
        )
        api_group.pack(fill=tk.X)

        self.var_not_spam = tk.BooleanVar(value=False)
        self.var_important = tk.BooleanVar(value=False)

        tk.Checkbutton(
            api_group,
            text="Report NOT SPAM",
            variable=self.var_not_spam,
            bg="#2b2b2b",
            fg="#FFFFFF",
            selectcolor="#3c3f41",
            activebackground="#3c3f41",
            activeforeground="#FFFFFF",
            relief="flat",
        ).pack(anchor="w", pady=2)

        tk.Checkbutton(
            api_group,
            text="Mark IMPORTANT",
            variable=self.var_important,
            bg="#2b2b2b",
            fg="#FFFFFF",
            selectcolor="#3c3f41",
            activebackground="#3c3f41",
            activeforeground="#FFFFFF",
            relief="flat",
        ).pack(anchor="w", pady=2)

        # ---------- Concurrency (bottom) ----------
        cc_frame = tk.LabelFrame(
            right,
            text="Concurrency",
            bg="#2b2b2b",
            fg="#EEEEEE",
            padx=10,
            pady=10,
            relief="groove",
            bd=2,
        )
        cc_frame.pack(side=tk.BOTTOM, fill=tk.X, pady=(10, 0))
        tk.Label(
            cc_frame,
            text="Max concurrent Chrome sessions (per batch of 10):",
            bg="#2b2b2b",
            fg="#FFFFFF",
            justify="left",
        ).pack(anchor="w")
        self.concurrent_var = tk.StringVar(value="10")
        self.concurrent_spin = tk.Spinbox(
            cc_frame,
            from_=1,
            to=50,
            textvariable=self.concurrent_var,
            width=5,
            bg="#3c3f41",
            fg="#FFFFFF",
            insertbackground="#FFFFFF",
            relief="flat",
        )
        self.concurrent_spin.pack(anchor="w", pady=4)

        # Buttons
        btn = tk.Frame(left, bg="#2b2b2b")
        btn.pack(fill=tk.X, pady=6)
        self.start_btn = tk.Button(
            btn,
            text="Start Processing",
            command=self.on_start,
            bg="#3c3f41",
            fg="#FFFFFF",
            relief="flat",
        )
        self.start_btn.pack(side="left")
        tk.Button(
            btn,
            text="Clear Log",
            command=self.clear_log,
            bg="#3c3f41",
            fg="#FFFFFF",
            relief="flat",
        ).pack(side="left", padx=6)

        # Log
        ttk.Label(left, text="Log:", background="#2b2b2b", foreground="#EEEEEE").pack(
            anchor="w", pady=(4, 0)
        )
        self.log_box = scrolledtext.ScrolledText(
            left,
            height=18,
            bg="#3c3f41",
            fg="#FFFFFF",
            insertbackground="#FFFFFF",
            relief="flat",
        )
        self.log_box.pack(fill=tk.BOTH, expand=True, pady=4)

    # === File mode handlers ===
    def _browse_accounts_file(self):
        """Switch to file mode: pick a .txt file (one email per line), disable textbox, show full path."""
        path = filedialog.askopenfilename(
            title="Select file containing Gmail accounts (one per line)",
            filetypes=(("Text Files", "*.txt"), ("All Files", "*.*")),
        )
        if not path:
            return
        self.accounts_file = path
        try:
            self.accounts_box.config(state=tk.DISABLED)
        except Exception:
            pass
        self.accounts_file_label.config(
            text=f"Loaded from: {path}  (textarea disabled)"
        )
        self.btn_clear_accounts.pack(side="right")  # reveal "Clear file" button

    def _clear_accounts_file(self):
        """Return to manual mode: clear file selection, re-enable textbox."""
        self.accounts_file = None
        self.accounts_file_label.config(text="")
        try:
            self.accounts_box.config(state=tk.NORMAL)
        except Exception:
            pass
        self.btn_clear_accounts.pack_forget()

    def _on_action_toggled(self):
        # Enable/disable numeric fields next to checkboxes
        self.shorts_count_entry.config(state=tk.NORMAL if self.var_play_shorts.get() else tk.DISABLED)
        self.click_links_count_entry.config(state=tk.NORMAL if self.var_click_links.get() else tk.DISABLED)

    # === Logging (thread-safe) ===
    def _log_console(self, msg):
        print(msg)

    def log(self, msg):
        self.log_box.insert(tk.END, msg + "\n")
        self.log_box.see(tk.END)
        self.update_idletasks()

    def log_threadsafe(self, msg):
        self.after(0, lambda: self.log(msg))

    def clear_log(self):
        self.log_box.delete("1.0", tk.END)

    # === Start button → spawn worker thread (keeps UI responsive) ===
    def on_start(self):
        self.start_btn.config(state=tk.DISABLED)
        threading.Thread(
            target=self._run_processing_parallel_worker, daemon=True
        ).start()

    def _run_processing_parallel_worker(self):
        try:
            self.run_processing_parallel()
        finally:
            self.after(0, lambda: self.start_btn.config(state=tk.NORMAL))

    # === Main processing logic ===
    def run_processing_parallel(self):
        # Read accounts (file > textbox)
        if self.accounts_file:
            try:
                with open(self.accounts_file, "r", encoding="utf-8") as f:
                    accounts = [line.strip() for line in f if line.strip()]
                self.log(
                    f"[INPUT] Loaded {len(accounts)} account(s) from file: {self.accounts_file}"
                )
            except Exception as e:
                self.log(f"[INPUT][ERROR] Could not read file: {e}")
                return
        else:
            accounts = [
                a.strip()
                for a in self.accounts_box.get("1.0", tk.END).splitlines()
                if a.strip()
            ]
            self.log(f"[INPUT] Loaded {len(accounts)} account(s) from textbox")

        if not accounts:
            self.after(
                0,
                lambda: messagebox.showwarning(
                    "No accounts", "Enter accounts or select a file."
                ),
            )
            return

        # UI option states
        do_open_gmail_ui = self.var_open_gmail_ui.get()
        do_not_spam = self.var_not_spam.get()
        do_important = self.var_important.get()
        do_play_shorts = self.var_play_shorts.get()
        do_click_links = self.var_click_links.get()

        # Counts
        try:
            shorts_count = int(self.shorts_count_var.get())
            if shorts_count < 0:
                shorts_count = 0
        except Exception:
            shorts_count = 3

        try:
            click_links_count = int(self.click_links_count_var.get())
            if click_links_count < 0:
                click_links_count = 0
        except Exception:
            click_links_count = 3

        try:
            concurrent = max(1, min(50, int(self.concurrent_var.get())))
        except Exception:
            concurrent = 10

        opts = dict(
            open_gmail_ui=do_open_gmail_ui,
            do_not_spam=do_not_spam,
            do_important=do_important,
            play_shorts=(do_play_shorts and shorts_count > 0),
            shorts_count=shorts_count,
            do_click_links=(do_click_links and click_links_count > 0),
            click_links_count=click_links_count,
        )

        # Process in batches of 10
        BATCH = 10
        total_batches = ((len(accounts) - 1) // BATCH) + 1
        for start in range(0, len(accounts), BATCH):
            batch = accounts[start: start + BATCH]
            self.log(
                f"=== Batch {start // BATCH + 1} / {total_batches} ({len(batch)} accounts) ==="
            )

            max_workers = max(1, min(concurrent, len(batch)))
            self.log(
                f"[BATCH] Running up to {max_workers} accounts in parallel (staggered launch)."
            )

            def _thread_entry(acct, delay_idx, opts_local):
                # Soft stagger to reduce simultaneous Chrome spawn spikes
                if delay_idx > 0:
                    time.sleep(0.25 * delay_idx)
                self._process_one_account(acct, opts_local, self.log_threadsafe)

            with ThreadPoolExecutor(max_workers=max_workers) as pool:
                futures = []
                for idx, acct in enumerate(batch):
                    fut = pool.submit(_thread_entry, acct, idx % max_workers, opts)
                    futures.append(fut)
                for fut in as_completed(futures):
                    try:
                        fut.result()
                    except Exception as e:
                        self.log_threadsafe(f"[THREAD][ERROR] {e}")

        self.after(
            0,
            lambda: messagebox.showinfo(
                "Done", "Processing complete for all accounts."
            ),
        )

    # === Per-account processing ===
    def _process_one_account(self, email: str, opts: dict, log_fn: Callable[[str], None]):
        try:
            log_fn(f"--- Processing: {email} ---")

            # 1) Start Chrome session (creates profile if needed)
            sess = start_chrome_session(email, log_fn=log_fn)
            if not sess:
                log_fn("[SESSION][FATAL] Could not start Chrome.")
                return

            # 2) OAuth if no valid token
            creds = None
            try:
                creds = load_credentials_for(email, log_fn)
            except Exception:
                try:
                    creds, _ = oauth_first_login_in_session(
                        email, sess, log_fn, also_open_gmail_ui=opts.get("open_gmail_ui")
                    )
                except Exception as e:
                    log_fn(f"[OAUTH][FATAL] {e}")
                    close_chrome_session(sess, log_fn)
                    return

            if not creds:
                try:
                    creds = load_credentials_for(email, log_fn)
                except Exception as e:
                    log_fn(f"[TOKEN][FATAL] {e}")
                    close_chrome_session(sess, log_fn)
                    return

            # 3) Build Gmail/People services
            try:
                gmail_svc = build_gmail_service(creds)
            except Exception as e:
                log_fn(f"[GMAIL][ERROR] build service: {e}")
                close_chrome_session(sess, log_fn)
                return

            try:
                people_svc = build_people_service(creds)
            except Exception:
                people_svc = None

            # 4) Actions
            if opts.get("open_gmail_ui"):
                cdp_navigate(sess.ws_url, "https://mail.google.com/mail/u/0/#inbox", log_fn=log_fn)
                log_fn("[UI] Gmail inbox opened and left open.")

            if opts.get("do_not_spam") or opts.get("do_important"):
                search_terms = self.search_entry.get().split(";")
                for term in search_terms:
                    t = term.strip()
                    if not t:
                        continue
                    self._apply_label_to_matching(
                        gmail_svc, t,
                        mark_not_spam=opts["do_not_spam"],
                        mark_important=opts["do_important"],
                        log_fn=log_fn
                    )

            if self.contact_entry.get().strip():
                self._add_contacts(people_svc, self.contact_entry.get(), log_fn=log_fn)

            if opts.get("play_shorts") and opts["shorts_count"] > 0:
                self._play_youtube_shorts(email, sess.ws_url, opts["shorts_count"], log_fn=log_fn)

            if opts.get("do_click_links") and opts["click_links_count"] > 0:
                self._click_unread_links(
                    email, gmail_svc, sess.ws_url, max_links=opts["click_links_count"],
                    open_interval=2.0, wait_after_open=30.0, log_fn=log_fn
                )

            # 8) All done → close or keep Chrome based on user choice
            if opts.get("open_gmail_ui"):
                log_fn(f"[SESSION] kept open for {email} (Open Gmail UI enabled)")
            else:
                close_chrome_session(sess, log_fn)
                log_fn(f"[SESSION] closed for {email} (UI not required)")
            log_fn(f"--- Done: {email} ---\n")


        except Exception as e:
            log_fn(f"[FATAL] {email}: {e}")

    # === Gmail helpers ===
    def _apply_label_to_matching(
        self, service, term, mark_not_spam=False, mark_important=False, log_fn=print
    ):
        query = f"{term}"
        msgs = search_messages(service, query, max_results=200, log_fn=log_fn)
        for m in msgs:
            mid = m["id"]
            body = {"removeLabelIds": [], "addLabelIds": []}
            if mark_not_spam:
                body["removeLabelIds"].append("SPAM")
            if mark_important:
                body["addLabelIds"].append("IMPORTANT")
            try:
                service.users().messages().modify(
                    userId="me", id=mid, body=body
                ).execute()
                if mark_not_spam:
                    log_fn(f"[LABEL] {mid} → removed SPAM")
                if mark_important:
                    log_fn(f"[LABEL] {mid} → added IMPORTANT")
            except Exception as e:
                log_fn(f"[LABEL][ERROR] {mid}: {e}")

    def _add_contacts(self, people_svc, csv_str, log_fn=print):
        if not people_svc:
            log_fn("[CONTACT] People service not available.")
            return
        addrs = [x.strip() for x in csv_str.split(";") if x.strip()]
        for addr in addrs:
            try:
                people_svc.people().createContact(
                    body={"emailAddresses": [{"value": addr}]}
                ).execute()
                log_fn(f"[CONTACT] added: {addr}")
            except Exception as e:
                log_fn(f"[CONTACT][ERROR] {addr}: {e}")

    # === YouTube Shorts Playback (basic; preserves your behavior) ===
    def _play_youtube_shorts(self, email, ws_url, count, log_fn=print):
        # Fetch some shorts links
        ids_seen: Set[str] = set()
        links = fetch_shorts_links(max_links=max(10, count*3), log_fn=log_fn, exclude_ids=ids_seen)
        if not links:
            log_fn("[SHORTS] no results")
            return
        random.shuffle(links)
        links = links[:count]
        for url in links:
            log_fn(f"[SHORTS] opening: {url}")
            cdp_navigate(ws_url, url, wait_load=True, timeout=20, log_fn=log_fn)
            # Minimal dwell consistent with prior requests
            time.sleep(2.0)

    # === Click Links from Unread Emails ===
    def _click_unread_links(
        self,
        email: str,
        gmail_svc,
        ws_url: str,
        max_links=3,
        open_interval=2.0,
        wait_after_open=30.0,
        log_fn=print,
    ):
        # Fetch unread messages in Inbox only
        messages = search_messages(gmail_svc, "is:unread in:inbox", max_results=200, log_fn=log_fn)
        if not messages:
            log_fn("[LINKS] No unread emails found.")
            return

        def extract_links_from_payload(payload):
            texts = []

            def decode_b64(s):
                try:
                    return base64.urlsafe_b64decode(s.encode("ASCII")).decode(
                        "utf-8", errors="replace"
                    )
                except Exception:
                    return ""

            def walk(part):
                mime = (part.get("mimeType") or "").lower()
                body = part.get("body", {})
                data = body.get("data")
                if mime in ("text/html", "text/plain") and data:
                    texts.append(decode_b64(data))
                for p in part.get("parts", []) or []:
                    walk(p)

            walk(payload)
            all_text = "\n".join(texts)
            # crude URL extraction
            links = re.findall(r'(https?://[^\s"\'<>]+)', all_text)
            cleaned = []
            for u in links:
                cleaned.append(u.rstrip(").,;'\"!?]"))
            # Dedup preserve order
            seen = set()
            uniq = []
            for u in cleaned:
                if u not in seen:
                    seen.add(u)
                    uniq.append(u)
            return uniq

        # Gather valid URLs from unread messages
        urls: List[str] = []
        for itm in messages:
            try:
                full = get_message_full(gmail_svc, itm["id"])
            except Exception as e:
                log_fn(f"[LINKS][ERROR] fetch {itm.get('id')}: {e}")
                continue
            links = extract_links_from_payload(full.get("payload", {}))
            for u in links:
                if self._is_valid_web_link(u):
                    urls.append(u)
                    if len(urls) >= max_links:
                        break
            if len(urls) >= max_links:
                break

        urls = urls[:max_links]
        if not urls:
            log_fn("[LINKS] no valid URLs found.")
            return

        log_fn(f"[LINKS] Found {len(urls)} link(s) — opening them 2s apart…")

        # Open Gmail inbox first and keep it open
        cdp_navigate(ws_url, "https://mail.google.com/mail/u/0/#inbox", log_fn=log_fn)

        # Use window.open to force new tabs (inline JS via CDP)
        def _cdp_eval(ws_url: str, js: str, wait=6.0):
            try:
                ws = websocket.create_connection(ws_url, timeout=8)
            except Exception as e:
                log_fn(f"[CDP] eval connect failed: {e}")
                return None
            try:
                _send_cdp_cmd(ws, "Runtime.enable")
                eval_id = _send_cdp_cmd(
                    ws,
                    "Runtime.evaluate",
                    {"expression": js, "awaitPromise": True, "returnByValue": True},
                )
                deadline = time.time() + wait
                while time.time() < deadline:
                    try:
                        msg = ws.recv()
                        m = json.loads(msg)
                    except Exception:
                        continue
                    if m.get("id") == eval_id:
                        return (m.get("result", {}) or {}).get("result", {}).get("value")
            except Exception as e:
                log_fn(f"[CDP] eval error: {e}")
            finally:
                try:
                    ws.close()
                except Exception:
                    pass
            return None

            try:
                ws = websocket.create_connection(ws_url, timeout=10)
            except Exception as e:
                log_fn(f"[CDP] Could not connect to CDP for link opening: {e}")
                return

            for i, u in enumerate(urls):
                if i > 0:
                    time.sleep(open_interval)
                try:
                    log_fn(f"[LINKS] Opening in new tab via CDP: {u}")
                    _send_cdp_cmd(ws, "Target.createTarget", {"url": u})
                except Exception as e:
                    log_fn(f"[LINKS][ERROR] {u}: {e}")

            ws.close()
            
        # Wait for tabs to load (best-effort): wait a fixed window
        log_fn("[LINKS] waiting on all tabs to load…")
        time.sleep(wait_after_open)

    @staticmethod
    def _is_valid_web_link(url: str) -> bool:
        url_l = url.lower()
        if not url_l.startswith("http"):
            return False
        # Filter out common media extensions
        bad_ext = (".jpg", ".jpeg", ".png", ".gif", ".svg", ".webp", ".mp4", ".mov", ".avi", ".mkv")
        return not any(url_l.endswith(ext) for ext in bad_ext)

    # ===== End of class =====


# ===== Simple update checker (stub to avoid NameError if referenced) =====
def check_for_update_and_prompt(parent_window=None):
    """Stubbed during development; no-op to avoid NameError in GUI init."""
    return


# ===== Run App =====
if __name__ == "__main__":
    try:
        if websocket is None:
            print("Missing dependency 'websocket-client'. Install with:")
            print("  python -m pip install websocket-client")
            sys.exit(1)
        app = GmailHybridApp()
        app.mainloop()
    except Exception as e:
        print("Fatal error:", e)
        sys.exit(1)
