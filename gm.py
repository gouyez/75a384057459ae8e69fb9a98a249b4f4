#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
gmail_hybrid_manager.py — Windows-only (v3.6.1)

This version:
- Removes "Open email" and "Open email and click first link".
- Click-links behavior:
  * Open all target links first in NEW tabs via CDP, 2s apart (skip image/media links)
  * Then wait until all opened tabs finish loading (document.readyState == 'complete')
  * Close Chrome when all loaded, or after 30s total timeout
- GUI:
  * Numeric inputs sit next to the checkboxes for Shorts and Click-links
  * Inputs are disabled unless their checkbox is checked
- Stability:
  * Profile auto-repair (Preferences/Local State JSONs) before launch
  * Profile lock detection/wait to avoid corruption
  * Graceful Browser.close over CDP, with terminate/kill only as fallback
"""

import os
import re
import json
import base64
import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox
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


def fetch_shorts_links(max_links=50, log_fn=print, exclude_ids: Set[str] | None = None):
    exclude_ids = exclude_ids or set()
    found_urls: List[str] = []
    found_ids: Set[str] = set()
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


# ===== CDP utilities =====
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


def _wait_for_debug_endpoint(port: int, timeout=10):
    deadline = time.time() + timeout
    while time.time() < deadline:
        try:
            r = requests.get(f"http://127.0.0.1:{port}/json", timeout=1)
            if r.status_code == 200:
                return True
        except Exception:
            time.sleep(0.2)
    return False


def _create_new_tab_and_get_ws(
    port: int, initial_url: str = "about:blank"
) -> Optional[str]:
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


def _send_cdp_cmd_wait(ws_conn, method: str, params: dict | None = None, timeout=6.0):
    """Send a CDP command and wait for the response with matching id."""
    if params is None:
        params = {}
    msg_id = _send_cdp_cmd(ws_conn, method, params)
    resp = _recv_cdp_until(ws_conn, lambda m: m.get("id") == msg_id, timeout=timeout)
    return resp


@dataclass
class ChromeSession:
    email: str
    port: int
    proc: subprocess.Popen
    ws_url: str  # websocketDebuggerUrl of one tab


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
    """
    Soft auto-repair: if Preferences / Local State / Secure Preferences are corrupt,
    move them aside so Chrome regenerates clean copies on next launch.
    """
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
        # Clear volatile session files referencing stale prefs
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


def _browser_ws_url(port: int) -> Optional[str]:
    info = _http_json(f"http://127.0.0.1:{port}/json/version", timeout=3)
    if not info:
        return None
    return info.get("webSocketDebuggerUrl")


def start_chrome_session(email: str, log_fn=print) -> ChromeSession | None:
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

    # Auto-repair common corrupt files before launch
    _repair_profile_if_corrupted(pdir, log_fn=log_fn)

    # Avoid launching against a locked profile
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


def close_chrome_session(
    sess: ChromeSession, log_fn=print, natural_delay=0.4, aggressive=True
):
    """
    Gracefully close Chrome to prevent profile corruption:
      1) Try Browser.close over browser-level WS
      2) Wait for process exit up to ~4s
      3) Fallback to terminate/kill
      4) (Optional) clean up stray child processes using this profile/port
    """
    try:
        if natural_delay and natural_delay > 0:
            time.sleep(natural_delay)

        # 1) Browser.close via browser-level websocket
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

        # 2) Wait up to 4s for clean exit
        try:
            sess.proc.wait(timeout=4.0)
        except Exception:
            pass

        # 3) Fallback terminate/kill if still running
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

        # 4) Aggressive cleanup of lingering chrome.exe using this profile/port
        if aggressive:
            prof_dir = profile_dir_for(sess.email)
            _aggressive_kill_chrome_for_profile(prof_dir, sess.port, log_fn=log_fn)

        time.sleep(0.2)
    except Exception as e:
        log_fn(f"[SESSION][WARN] close exception: {e}")


def _aggressive_kill_chrome_for_profile(
    profile_dir: Path, port: int | None, log_fn=print
):
    """Windows-only: kill any chrome.exe whose CommandLine references this profile (or remote debugging port)."""
    try:
        prof_str = str(profile_dir)
        prof_norm = prof_str.lower().replace("/", "\\")
        port_str = f"--remote-debugging-port={port}" if port else None

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

        pids_to_kill = []
        for line in out.splitlines():
            line = line.strip()
            if not line or line.startswith("Node,") or ",CommandLine," in line:
                continue
            parts = line.split(",", 2)
            if len(parts) < 3:
                continue
            cmdline = parts[1].lower() if parts[1] else ""
            pid_str = parts[2].strip()
            if not pid_str.isdigit():
                continue
            pid = int(pid_str)

            hit_profile = (
                (prof_norm in cmdline)
                or (f'--user-data-dir="{prof_norm}"' in cmdline)
                or (f"--user-data-dir={prof_norm}" in cmdline)
            )
            hit_port = port_str and port_str in cmdline

            if hit_profile or hit_port:
                pids_to_kill.append(pid)

        for pid in pids_to_kill:
            try:
                subprocess.run(
                    ["taskkill", "/PID", str(pid), "/T", "/F"],
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                    creationflags=0x08000000,
                )
            except Exception:
                pass

        if pids_to_kill:
            log_fn(
                f"[SESSION] Aggressively killed {len(pids_to_kill)} chrome.exe tied to profile."
            )
    except Exception as e:
        log_fn(f"[SESSION][WARN] aggressive kill failed: {e}")


def cdp_navigate(
    ws_url: str, url: str, wait_load=True, timeout=12, log_fn=print
) -> bool:
    """Navigate the current Chrome tab to the given URL using CDP."""
    try:
        ws = websocket.create_connection(ws_url, timeout=8)
    except Exception as e:
        log_fn(f"[CDP] connect failed: {e}")
        return False
    ok = False
    try:
        _send_cdp_cmd(ws, "Page.enable")
        if wait_load:
            _send_cdp_cmd(ws, "Page.navigate", {"url": url})
            got = _recv_cdp_until(
                ws, lambda m: m.get("method") == "Page.loadEventFired", timeout=timeout
            )
            ok = got is not None
        else:
            _send_cdp_cmd(ws, "Page.navigate", {"url": url})
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


def cdp_open_new_tab(ws_url: str, target_url: str, log_fn=print) -> Optional[str]:
    """
    Open a new tab using CDP Target.createTarget (bypasses popup blockers).
    Returns the targetId on success, or None on failure.
    """
    if websocket is None:
        raise RuntimeError("websocket-client is required.")

    try:
        ws = websocket.create_connection(ws_url, timeout=10)
    except Exception as e:
        log_fn(f"[CDP] WS open failed for createTarget: {e}")
        return None

    try:
        _send_cdp_cmd(ws, "Target.setDiscoverTargets", {"discover": True})
        resp = _send_cdp_cmd_wait(ws, "Target.createTarget", {"url": target_url}, timeout=6.0)
        target_id = None
        try:
            target_id = ((resp or {}).get("result") or {}).get("targetId")
        except Exception:
            target_id = None
        log_fn(f"[CDP] New tab opened: {target_url} (targetId={target_id})")
        return target_id
    except Exception as e:
        log_fn(f"[CDP] createTarget failed: {e}")
        return None
    finally:
        try:
            ws.close()
        except Exception:
            pass


def _collect_targets(port: int) -> Dict[str, str]:
    """
    Return {targetId: wsDebuggerUrl} for all page targets known to the remote-debugger.
    """
    data = _http_json(f"http://127.0.0.1:{port}/json", timeout=3)
    out: Dict[str, str] = {}
    if not data:
        return out
    for entry in data:
        tid = entry.get("id")
        ws = entry.get("webSocketDebuggerUrl")
        typ = entry.get("type")
        if tid and ws and (typ in (None, "page", "other")):
            out[tid] = ws
    return out


def _is_target_loaded(ws_url: str) -> bool:
    """
    Query document.readyState on a target and return True if it's 'complete'.
    """
    try:
        ws = websocket.create_connection(ws_url, timeout=5)
    except Exception:
        return False
    try:
        _send_cdp_cmd(ws, "Runtime.enable")
        resp = _send_cdp_cmd_wait(
            ws,
            "Runtime.evaluate",
            {"expression": "document.readyState", "returnByValue": True},
            timeout=4.0,
        )
        value = (((resp or {}).get("result") or {}).get("result") or {}).get("value")
        return (value == "complete")
    except Exception:
        return False
    finally:
        try:
            ws.close()
        except Exception:
            pass


def wait_all_targets_loaded(port: int, target_ids: List[str], max_total_seconds: int, log_fn=print) -> None:
    """
    Poll all provided targetIds until each reports document.readyState == 'complete',
    or until max_total_seconds elapse. Returns when either condition is met.
    """
    if not target_ids:
        return
    deadline = time.time() + max_total_seconds
    pending: Set[str] = set(target_ids)

    while pending and time.time() < deadline:
        mapping = _collect_targets(port)
        done_now = []
        for tid in list(pending):
            ws = mapping.get(tid)
            if not ws:
                # If we can't see it anymore, assume it's loaded (or closed)
                done_now.append(tid)
                continue
            if _is_target_loaded(ws):
                done_now.append(tid)
        for tid in done_now:
            pending.discard(tid)
        if pending:
            time.sleep(0.5)

    if pending:
        log_fn(f"[CDP] Wait timeout; {len(pending)} tab(s) not fully loaded after {max_total_seconds}s.")
    else:
        log_fn("[CDP] All opened tabs finished loading.")


# ===== Shorts playback =====
def _play_one_short_in_tab(ws_url: str, short_url: str, log_fn=print):
    if websocket is None:
        raise RuntimeError("websocket-client is required.")

    def _cdp_recv(ws, timeout=20.0):
        deadline = time.time() + timeout
        while time.time() < deadline:
            try:
                raw = ws.recv()
            except Exception:
                time.sleep(0.05)
                continue
            try:
                return json.loads(raw)
            except Exception:
                continue
        return None

    def _get_ctx(ws, target_origin="https://www.youtube.com", timeout=6.0):
        end = time.time() + timeout
        while time.time() < end:
            msg = _cdp_recv(ws, timeout=1.0)
            if not msg:
                continue
            if msg.get("method") == "Runtime.executionContextCreated":
                ctx = (msg.get("params") or {}).get("context") or {}
                aux = ctx.get("auxData") or {}
                origin = aux.get("origin", "")
                if (
                    aux.get("isDefault", False)
                    and isinstance(origin, str)
                    and origin.startswith(target_origin)
                ):
                    return ctx.get("id")
        return None

    try:
        ws = websocket.create_connection(ws_url, timeout=10)
    except Exception as e:
        log_fn(f"[CDP] WS open failed: {e}")
        return ("error", str(e))

    try:
        _send_cdp_cmd(ws, "Page.enable")
        _send_cdp_cmd(ws, "Runtime.enable")
        _send_cdp_cmd(ws, "Page.navigate", {"url": short_url})

        got_load = False
        ctx_id = None
        load_deadline = time.time() + 12.0
        while time.time() < load_deadline and (not got_load or not ctx_id):
            msg = _cdp_recv(ws, timeout=1.0)
            if not msg:
                continue
            if msg.get("method") == "Page.loadEventFired":
                got_load = True
            elif (
                msg.get("method") == "Runtime.executionContextCreated"
                and ctx_id is None
            ):
                ctx = (msg.get("params") or {}).get("context") or {}
                aux = ctx.get("auxData") or {}
                origin = aux.get("origin", "")
                if (
                    aux.get("isDefault", False)
                    and isinstance(origin, str)
                    and origin.startswith("https://www.youtube.com")
                ):
                    ctx_id = ctx.get("id")

        if ctx_id is None:
            # fallback small window
            end2 = time.time() + 4.0
            while time.time() < end2:
                msg = _cdp_recv(ws, timeout=1.0)
                if msg and msg.get("method") == "Runtime.executionContextCreated":
                    ctx = (msg.get("params") or {}).get("context") or {}
                    aux = ctx.get("auxData") or {}
                    origin = aux.get("origin", "")
                    if aux.get("isDefault", False) and str(origin).startswith("https://www.youtube.com"):
                        ctx_id = ctx.get("id")
                        break

        eval_params = {"expression": "", "awaitPromise": True, "returnByValue": True}
        if ctx_id is not None:
            eval_params["contextId"] = ctx_id

        playback_js = r"""
(async function() {
  function q(sel, root=document){ try { return root.querySelector(sel); } catch(e){ return null; } }
  function sleep(ms){ return new Promise(r=>setTimeout(r,ms)); }
  function findVideo() {
    const reel = q('ytd-reel-video-renderer');
    if (reel && reel.shadowRoot) {
      const v = q('video', reel.shadowRoot);
      if (v) return v;
    }
    const vids = document.querySelectorAll('video');
    for (const v of vids){ if (v && v.readyState >= 1) return v; }
    return null;
  }
  async function awaitPlayableVideo(){
    const deadline = performance.now() + 18000;
    let v=null;
    while(performance.now()<deadline){
      v=findVideo();
      if(v && Number.isFinite(v.duration) && v.duration>1.5) return v;
      await sleep(250);
    }
    return null;
  }
  const v = await awaitPlayableVideo();
  if(!v) return {status:'no_metadata'};

  v.muted=true; v.playsInline=true;
  try{ const p=v.play(); if(p && p.catch) p.catch(()=>{}); }catch(e){}

  const dur=v.duration,LONG_LIMIT=40.0,SHORT_TARGET=0.90;
  async function waitUntil(pred,timeoutMs,tick=200){
    const end=performance.now()+timeoutMs;
    while(performance.now()<end){
      try{ if(pred()) return true; }catch(e){}
      await new Promise(r=>setTimeout(r,tick));
    }
    return false;
  }
  if(dur>LONG_LIMIT){
    const ok=await waitUntil(()=> (v.currentTime||0)>=LONG_LIMIT,(LONG_LIMIT+12)*1000,200);
    await new Promise(r=>setTimeout(r,1000));
    return {status: ok?'watched_long':'timeout_long', t:v.currentTime||0, d:dur};
  }else{
    const target=dur*SHORT_TARGET;
    const slack=Math.max(4.0,dur+8.0);
    const ok=await waitUntil(()=> (v.currentTime||0)>=target, slack*1000,200);
    return {status: ok?'watched_short':'timeout_short', t:v.currentTime||0, d:dur, target:target};
  }
})();
"""
        eval_params["expression"] = playback_js
        eval_id = _send_cdp_cmd(ws, "Runtime.evaluate", eval_params)

        resp = None
        deadline = time.time() + 75
        while time.time() < deadline:
            msg = _recv_cdp_until(ws, lambda m: m.get("id") == eval_id, timeout=1.0)
            if msg:
                resp = msg
                break

        if not resp:
            return ("error", "evaluate-timeout")
        if "error" in resp:
            return ("error", resp.get("error"))
        if resp.get("result", {}).get("exceptionDetails"):
            return ("error", "exception")

        res_obj = resp.get("result", {}).get("result", {})
        value = res_obj.get("value")
        if value is None and res_obj.get("subtype") == "null":
            value = None

        if not isinstance(value, dict):
            return ("error", "no-value")

        status = value.get("status", "error")
        if status == "no_metadata":
            return ("skipped", "no-metadata")
        elif status in (
            "watched_long",
            "watched_short",
            "timeout_long",
            "timeout_short",
        ):
            return ("watched", value)
        else:
            return ("error", value)

    except Exception as e:
        return ("error", str(e))
    finally:
        try:
            ws.close()
        except Exception:
            pass


def play_shorts_for(
    email: str,
    count: int,
    sess: ChromeSession,
    log_fn=print,
    max_attempts=50,
    inbox_before=True,
    dwell_before=1.0,
    dwell_inbox_after=0.5,
    dwell_blank_after=0.5,
):
    if websocket is None:
        raise RuntimeError(
            "Missing 'websocket-client'. Install with: python -m pip install websocket-client"
        )
    if count <= 0:
        return

    if inbox_before:
        cdp_navigate(
            sess.ws_url, "https://mail.google.com/mail/u/0/#inbox", log_fn=log_fn
        )
        time.sleep(max(0.0, dwell_before))

    seen_ids: Set[str] = set()
    target = count
    watched = 0
    attempts = 0
    pool_urls = fetch_shorts_links(
        max_links=max(60, target * 6), log_fn=log_fn, exclude_ids=seen_ids
    )
    random.shuffle(pool_urls)

    def _pop_next_id() -> Optional[str]:
        nonlocal pool_urls
        while pool_urls:
            u = pool_urls.pop(0)
            m = SHORTS_REGEX.search(u)
            if not m:
                continue
            sid = m.group(1)
            if sid in seen_ids:
                continue
            seen_ids.add(sid)
            return sid
        return None

    while watched < target and attempts < max_attempts:
        sid = _pop_next_id()
        if not sid:
            pool_urls = fetch_shorts_links(
                max_links=40, log_fn=log_fn, exclude_ids=seen_ids
            )
            random.shuffle(pool_urls)
            sid = _pop_next_id()
            if not sid:
                log_fn("[SHORTS] No fresh candidates; stopping.")
                break

        attempts += 1
        url = f"https://www.youtube.com/shorts/{sid}"
        log_fn(f"[SHORTS] Attempt {attempts}/{max_attempts} → {url}")

        status, detail = _play_one_short_in_tab(sess.ws_url, url, log_fn=log_fn)
        if status == "watched":
            watched += 1
            log_fn(f"[SHORTS] Counted {watched}/{target}: {sid}")
        elif status == "skipped":
            log_fn(f"[SHORTS] Skipped {sid}: {detail}")
        else:
            log_fn(f"[SHORTS] Error {sid}: {detail}")

    cdp_navigate(sess.ws_url, "https://mail.google.com/mail/u/0/#inbox", log_fn=log_fn)
    time.sleep(max(0.0, dwell_inbox_after))
    cdp_navigate(sess.ws_url, "about:blank", log_fn=log_fn)
    time.sleep(max(0.0, dwell_blank_after))

    log_fn(
        f"[SHORTS] Done: success={watched}/{target}, attempts={attempts} (limit={max_attempts})"
    )


# ===== Loopback OAuth =====
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
    if not os.path.exists(CREDENTIALS_FILE):
        raise FileNotFoundError("Missing credentials.json next to the app.")

    port = _find_free_port()
    redirect_uri = f"http://127.0.0.1:{port}/callback"
    log_fn(f"[OAuth] starting on {redirect_uri}")

    flow = InstalledAppFlow.from_client_secrets_file(
        CREDENTIALS_FILE, SCOPES, redirect_uri=redirect_uri
    )
    auth_url, _ = flow.authorization_url(
        access_type="offline", prompt="consent", include_granted_scopes="true"
    )

    shared = {}
    _OAuthHandler.shared = shared

    server = http.server.HTTPServer(("127.0.0.1", port), _OAuthHandler)
    t = threading.Thread(target=server.serve_forever, daemon=True)
    t.start()

    cdp_navigate(sess.ws_url, auth_url, log_fn=log_fn)

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


def oauth_first_login_in_session(
    email: str, sess: ChromeSession, log_fn, also_open_gmail_ui: bool
):
    try:
        return _oauth_once_with_session(email, sess, log_fn)
    except Exception as e:
        log_fn(f"[OAuth] first attempt failed: {e}. Retrying once …")
        time.sleep(2)
        return _oauth_once_with_session(email, sess, log_fn)


# ===== Updater =====
def _parse_version(v):
    return tuple(int(p) for p in re.findall(r"\d+", str(v)))


def is_newer_version(remote: str, local: str) -> bool:
    return _parse_version(remote) > _parse_version(local)


def is_running_frozen_exe() -> bool:
    return is_frozen()


def current_executable_path() -> str:
    return sys.executable if is_frozen() else os.path.abspath(sys.argv[0])


def check_for_update_and_prompt(parent_window=None):
    try:
        r = requests.get(UPDATE_JSON_URL, timeout=8)
        r.raise_for_status()
        info = r.json()
    except Exception:
        return
    remote_ver = info.get("version")
    download_url = info.get("url")
    if not remote_ver or not download_url:
        return
    if not is_newer_version(remote_ver, APP_VERSION):
        return

    if not messagebox.askyesno(
        "Update available", f"A new version ({remote_ver}) is available. Install now?"
    ):
        return

    exe_path = current_executable_path()
    is_exe = exe_path.lower().endswith(".exe") and is_running_frozen_exe()
    desired_name = f"GmailHybridManager_{remote_ver}.exe"

    try:
        tmp_dir = tempfile.mkdtemp(prefix="ghm_update_")
        tmp_file = os.path.join(tmp_dir, desired_name)
        with requests.get(download_url, stream=True, timeout=30) as resp:
            resp.raise_for_status()
            with open(tmp_file, "wb") as f:
                for chunk in resp.iter_content(chunk_size=262144):
                    if chunk:
                        f.write(chunk)
    except Exception as e:
        messagebox.showerror("Update failed", f"Could not download update:\n{e}")
        return

    if not is_exe:
        dst = os.path.join(os.path.dirname(exe_path), desired_name)
        try:
            shutil.copy2(tmp_file, dst)
            messagebox.showinfo(
                "Update downloaded", f"Downloaded {desired_name} next to your app."
            )
        except Exception as e:
            messagebox.showerror("Update failed", f"Could not place update:\n{e}")
        return

    bat_content = f"""@echo off
setlocal
set TARGET="{exe_path}"
set NEW="{tmp_file}"
set BACKUP="{exe_path}.old"
ping 127.0.0.1 -n 2 >nul
:waitloop
move /y %TARGET% %BACKUP% >nul 2>&1
if exist %TARGET% (
  ping 127.0.0.1 -n 2 >nul
  goto waitloop
)
move /y %NEW% %TARGET% >nul
start "" %TARGET%
exit
"""
    bat_path = os.path.join(tempfile.gettempdir(), f"ghm_update_{int(time.time())}.bat")
    with open(bat_path, "w", encoding="utf-8") as f:
        f.write(bat_content)

    try:
        subprocess.Popen(
            ["cmd.exe", "/C", bat_path], close_fds=True, creationflags=0x00000008
        )
    except Exception:
        subprocess.Popen(["cmd.exe", "/C", bat_path], close_fds=True)
    os._exit(0)


# ===== GUI & App =====
class GmailHybridApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Gmail Hybrid Manager (Windows)")
        self.geometry("1100x780")
        self.configure(bg="#2b2b2b")

        ensure_tokens_dir()
        self._setup_styles()
        self._create_widgets()

        if not ensure_master_extracted(self._log_console):
            messagebox.showerror(
                "Chrome master not found",
                "Could not find embedded 'chrome_master'.\n\n"
                "Dev mode: put a 'chrome_master' folder next to this .py/.exe.\n"
                'Build mode: include with PyInstaller --add-data "chrome_master;chrome_master".',
            )

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

        # Right actions/controls
        right = tk.LabelFrame(
            main_frame,
            text="Actions & Controls",
            bg="#2b2b2b",
            fg="#EEEEEE",
            padx=10,
            pady=10,
            relief="flat",
        )
        right.pack(side=tk.RIGHT, fill=tk.Y, padx=6)

        # Checkboxes with inline numeric entries (disabled unless checked)
        self.var_open_gmail_ui = tk.BooleanVar(value=False)
        self.var_not_spam = tk.BooleanVar(value=False)
        self.var_important = tk.BooleanVar(value=False)
        self.var_play_shorts = tk.BooleanVar(value=False)
        self.var_click_links = tk.BooleanVar(value=False)

        # Shorts line
        shorts_line = tk.Frame(right, bg="#2b2b2b")
        shorts_line.pack(fill=tk.X, pady=2)
        tk.Checkbutton(
            shorts_line,
            text="Play YouTube Shorts",
            variable=self.var_play_shorts,
            bg="#2b2b2b",
            fg="#FFFFFF",
            selectcolor="#3c3f41",
            activebackground="#3c3f41",
            activeforeground="#FFFFFF",
            relief="flat",
        ).pack(side=tk.LEFT)
        self.shorts_count_var = tk.StringVar(value="3")
        self.shorts_count_entry = tk.Entry(
            shorts_line,
            textvariable=self.shorts_count_var,
            width=6,
            bg="#3c3f41",
            fg="#FFFFFF",
            relief="flat",
            state="disabled",
        )
        tk.Label(shorts_line, text=" ", bg="#2b2b2b", fg="#2b2b2b").pack(side=tk.LEFT)
        self.shorts_count_entry.pack(side=tk.LEFT, padx=(6, 0))

        # Click-links line
        links_line = tk.Frame(right, bg="#2b2b2b")
        links_line.pack(fill=tk.X, pady=2)
        tk.Checkbutton(
            links_line,
            text="Click links (from unread emails)",
            variable=self.var_click_links,
            bg="#2b2b2b",
            fg="#FFFFFF",
            selectcolor="#3c3f41",
            activebackground="#3c3f41",
            activeforeground="#FFFFFF",
            relief="flat",
        ).pack(side=tk.LEFT)
        self.click_links_count_var = tk.StringVar(value="3")
        self.click_links_count_entry = tk.Entry(
            links_line,
            textvariable=self.click_links_count_var,
            width=6,
            bg="#3c3f41",
            fg="#FFFFFF",
            relief="flat",
            state="disabled",
        )
        tk.Label(links_line, text=" ", bg="#2b2b2b", fg="#2b2b2b").pack(side=tk.LEFT)
        self.click_links_count_entry.pack(side=tk.LEFT, padx=(6, 0))

        # Rest of actions
        for label, var in [
            ("Open Gmail UI (always)", self.var_open_gmail_ui),
            ("Report NOT SPAM", self.var_not_spam),
            ("Mark IMPORTANT", self.var_important),
        ]:
            tk.Checkbutton(
                right,
                text=label,
                variable=var,
                bg="#2b2b2b",
                fg="#FFFFFF",
                selectcolor="#3c3f41",
                activebackground="#3c3f41",
                activeforeground="#FFFFFF",
                relief="flat",
            ).pack(anchor="w", pady=2)

        # Concurrency control
        cc_frame = tk.Frame(right, bg="#2b2b2b")
        cc_frame.pack(fill=tk.X, pady=(6, 10))
        tk.Label(
            cc_frame,
            text="Max concurrent Chrome sessions (per batch of 10):",
            bg="#2b2b2b",
            fg="#FFFFFF",
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
        self.concurrent_spin.pack(anchor="w", pady=2)

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

        # Bind enable/disable for numeric inputs
        def sync_entries(*_):
            self.shorts_count_entry.config(state=("normal" if self.var_play_shorts.get() else "disabled"))
            self.click_links_count_entry.config(state=("normal" if self.var_click_links.get() else "disabled"))

        self.var_play_shorts.trace_add("write", sync_entries)
        self.var_click_links.trace_add("write", sync_entries)
        sync_entries()

    # Logging (thread-safe)
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

    # Start button → spawn worker thread (keeps UI responsive)
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

    # Helper eval (rarely used now)
    def _cdp_eval(self, ws_url: str, js: str, wait=8.0, log_fn=print):
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
                except Exception:
                    continue
                try:
                    m = json.loads(msg)
                except:
                    continue
                if m.get("id") == eval_id:
                    return m.get("result", {}).get("result", {}).get("value")
        except Exception as e:
            log_fn(f"[CDP] eval error: {e}")
        finally:
            try:
                ws.close()
            except:
                pass
        return None

    # Worker for one account (runs in thread)
    def _process_one_account(
        self, account: str, opts: dict, log_fn: Callable[[str], None]
    ):
        """
        Per-account pipeline (v3.6.1):
          - Ensure token (OAuth inside dedicated Chrome if needed)
          - Optionally open Gmail UI (if chosen)
          - Shorts flow (if chosen) → always closes Chrome after
          - Inbox-scoped search (if keywords provided) → labels only
          - Click links (unread inbox) → single Chrome session:
                * Open Gmail inbox and KEEP it open
                * Open up to N links in NEW TABS via CDP, 2s apart (skip image/media)
                * Mark message READ after successful open
                * After all opens: wait until ALL opened tabs loaded or 30s total
                * Close entire window at end
        """
        def _ensure_session():
            s = start_chrome_session(account, log_fn=log_fn)
            if not s:
                log_fn(f"[SESSION][FATAL] could not start chrome for {account}")
            return s

        try:
            log_fn(f"--- Processing account: {account} ---")

            # Decide if UI is needed up-front
            need_ui = False
            token_ok = False
            creds = None
            try:
                creds = load_credentials_for(account, log_fn)
                token_ok = True
            except Exception as e:
                log_fn(f"[TOKEN] missing/invalid: {e}")
                need_ui = True  # OAuth requires UI

            if opts["open_gmail_ui"] or opts["play_shorts"]:
                need_ui = True

            sess = None

            # Start session if any UI needed (or OAuth required)
            if need_ui:
                sess = _ensure_session()
                if not sess:
                    return

                if not token_ok:
                    try:
                        creds, _ = oauth_first_login_in_session(
                            account, sess, log_fn, also_open_gmail_ui=True
                        )
                        token_ok = True
                    except Exception as e2:
                        log_fn(f"[OAuth][FATAL] {e2}")
                        close_chrome_session(sess, log_fn)
                        return
                elif opts["open_gmail_ui"]:
                    cdp_navigate(
                        sess.ws_url,
                        "https://mail.google.com/mail/u/0/#inbox",
                        log_fn=log_fn,
                    )

                # Shorts flow runs first and always closes Chrome afterwards
                if opts["play_shorts"] and opts["shorts_count"] > 0:
                    try:
                        log_fn(
                            f"[SHORTS] Playing {opts['shorts_count']} shorts with duration rules"
                        )
                        play_shorts_for(
                            account,
                            opts["shorts_count"],
                            sess,
                            log_fn=log_fn,
                            max_attempts=50,
                            inbox_before=True,
                            dwell_before=1.0,
                            dwell_inbox_after=0.5,
                            dwell_blank_after=0.5,
                        )
                    except Exception as e:
                        log_fn(f"[SHORTS][ERROR] {e}")
                    close_chrome_session(sess, log_fn)
                    sess = None

            # If still no token, API cannot be used
            if not token_ok:
                log_fn("[TOKEN][FATAL] No valid token; skipping API actions.")
                if sess:
                    close_chrome_session(sess, log_fn)
                return

            # Gmail service
            try:
                gmail_service = build_gmail_service(creds)
            except Exception as e:
                log_fn(f"[GMAIL][ERROR] service build: {e}")
                if sess:
                    close_chrome_session(sess, log_fn)
                return

            # Contacts (multi-; validated individually)
            contact_raw = opts["contact_to_add"]
            if contact_raw:
                valids = []
                invalids = []
                for c in [x.strip() for x in contact_raw.split(";") if x.strip()]:
                    (valids if EMAIL_REGEX.match(c) else invalids).append(c)
                for bad in invalids:
                    log_fn(f"[CONTACT][WARN] invalid address skipped: {bad}")
                if valids:
                    try:
                        people_service = build_people_service(creds)
                    except Exception as e:
                        people_service = None
                        log_fn(f"[PEOPLE][ERROR] build: {e}")
                    if people_service:
                        for c in valids:
                            try:
                                log_fn(f"[CONTACT] adding {c} …")
                                people_service.people().createContact(
                                    body={"emailAddresses": [{"value": c}]}
                                ).execute()
                                log_fn(f"[CONTACT] added: {c}")
                            except Exception as e:
                                log_fn(f"[CONTACT][ERROR] {c}: {e}")

            # Inbox-scoped search (from/subject only). Labels only.
            msgs = []
            raw_search = opts["raw_search"]
            keywords = [k.strip() for k in raw_search.split(";") if k.strip()]
            if keywords:
                parts = []
                for kw in keywords:
                    parts.append(f'from:"{kw}"')
                    parts.append(f'subject:"{kw}"')
                gmail_query = "(" + " OR ".join(parts) + ") in:inbox"
                log_fn(f"[SEARCH] {gmail_query}")
                msgs = search_messages(gmail_service, gmail_query, log_fn=log_fn)
                log_fn(f"[SEARCH] total {len(msgs)} (inbox)")

                if msgs:
                    for m in msgs:
                        mid = m.get("id")
                        if opts["do_not_spam"]:
                            try:
                                gmail_service.users().messages().modify(
                                    userId="me",
                                    id=mid,
                                    body={"removeLabelIds": ["SPAM"], "addLabelIds": ["INBOX"]},
                                ).execute()
                                log_fn("[LABEL] NOT SPAM → INBOX")
                            except Exception as e:
                                log_fn(f"[LABEL][ERROR] not spam: {e}")

                        if opts["do_important"]:
                            try:
                                gmail_service.users().messages().modify(
                                    userId="me", id=mid, body={"addLabelIds": ["IMPORTANT"]}
                                ).execute()
                                log_fn("[LABEL] IMPORTANT")
                            except Exception as e:
                                log_fn(f"[LABEL][ERROR] important: {e}")
                else:
                    if keywords:
                        log_fn("[SEARCH] No messages matched in inbox.")

            # --- Click links (unread inbox): open-first, then wait-all ---
            if opts["do_click_links"] and opts["click_links_count"] > 0:
                target_n = opts["click_links_count"]
                opened_count = 0
                log_fn(
                    f"[CLINK] Target: open {target_n} links from unread INBOX (one per email)."
                )

                IMAGE_EXTS = (".jpg", ".jpeg", ".png", ".gif", ".webp", ".svg", ".ico", ".bmp", ".tiff", ".apng", ".avif")
                def looks_like_image_url(u: str) -> bool:
                    lu = u.lower()
                    if lu.startswith(("data:", "cid:")):
                        return True
                    if any(lu.endswith(ext) for ext in IMAGE_EXTS):
                        return True
                    if any(k in lu for k in ["=image", "format=image", "mime=image", "media=photo"]):
                        return True
                    return False

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
                    links = re.findall(r'(https?://[^\s"\'<>]+)', all_text)
                    cleaned = [u.rstrip(").,;'\"!?]") for u in links]
                    seen = set()
                    uniq = []
                    for u in cleaned:
                        if looks_like_image_url(u):
                            continue
                        if u not in seen:
                            seen.add(u)
                            uniq.append(u)
                    return uniq

                # Dedicated session for clicking links
                sess_click = start_chrome_session(account, log_fn=log_fn)
                if not sess_click:
                    log_fn("[CLINK][FATAL] Could not start Chrome session for clicking.")
                else:
                    # Inbox stays open
                    cdp_navigate(
                        sess_click.ws_url,
                        "https://mail.google.com/mail/u/0/#inbox",
                        log_fn=log_fn,
                    )
                    time.sleep(0.8)

                    opened_target_ids: List[str] = []

                    # 1) Open links first (2s apart), marking messages as read upon successful tab creation
                    while opened_count < target_n:
                        unread_msgs = search_messages(
                            gmail_service, "is:unread in:inbox", max_results=50, log_fn=log_fn
                        )
                        if not unread_msgs:
                            log_fn("[CLINK] No unread messages left; stopping open phase.")
                            break

                        any_opened_this_round = False
                        for itm in unread_msgs:
                            if opened_count >= target_n:
                                break
                            mid = itm.get("id")
                            try:
                                full = get_message_full(gmail_service, mid)
                            except Exception as e:
                                log_fn(f"[CLINK][ERROR] fetch {mid}: {e}")
                                continue

                            links = extract_links_from_payload(full.get("payload", {}))
                            if not links:
                                log_fn(f"[CLINK] message {mid}: no non-image links → skipping")
                                continue

                            target_link = random.choice(links)
                            log_fn(f"[CLINK] opening: {target_link}")

                            tid = cdp_open_new_tab(sess_click.ws_url, target_link, log_fn=log_fn)
                            if tid:
                                opened_target_ids.append(tid)
                                opened_count += 1
                                any_opened_this_round = True
                                try:
                                    mark_as_read(gmail_service, mid, log_fn=log_fn)
                                except Exception:
                                    pass
                                time.sleep(2.0)  # open next after 2s
                            else:
                                log_fn(f"[CLINK] failed to open via CDP → {target_link}")

                        if not any_opened_this_round:
                            log_fn("[CLINK] No usable links in unread; stopping open phase.")
                            break

                    # 2) After all opens → wait for all opened tabs to finish loading (max 30s total)
                    if opened_target_ids:
                        log_fn(f"[CLINK] Waiting for {len(opened_target_ids)} tab(s) to finish loading (max 30s).")
                        wait_all_targets_loaded(sess_click.port, opened_target_ids, max_total_seconds=30, log_fn=log_fn)
                    else:
                        log_fn("[CLINK] No tabs were opened; skipping wait phase.")

                    # 3) Close the window now
                    cdp_navigate(sess_click.ws_url, "about:blank", log_fn=log_fn)
                    close_chrome_session(sess_click, log_fn, natural_delay=0.0)

                log_fn(f"[CLINK] Completed: {opened_count}/{target_n} links opened.")

            log_fn(f"Finished account: {account}")

        except Exception as e:
            log_fn(f"[FATAL] {account}: {e}")

    def run_processing_parallel(self):
        # Read accounts
        accounts = [
            a.strip()
            for a in self.accounts_box.get("1.0", tk.END).splitlines()
            if a.strip()
        ]
        if not accounts:
            self.after(
                0,
                lambda: messagebox.showwarning(
                    "No accounts", "Enter one or more Gmail addresses."
                ),
            )
            return

        # UI options
        contact_to_add = self.contact_entry.get().strip()
        raw_search = self.search_entry.get().strip()
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
            contact_to_add=contact_to_add,
            raw_search=raw_search,
        )

        # Process in batches of 10
        BATCH = 10
        total_batches = ((len(accounts) - 1) // BATCH) + 1
        for start in range(0, len(accounts), BATCH):
            batch = accounts[start : start + BATCH]
            self.log(
                f"=== Batch {start//BATCH + 1} / {total_batches} ({len(batch)} accounts) ==="
            )

            max_workers = max(1, min(concurrent, len(batch)))
            self.log(
                f"[BATCH] Running up to {max_workers} accounts in parallel (staggered launch)."
            )

            def _thread_entry(acct, delay_idx, opts_local):
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


# ===== Runner =====
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
