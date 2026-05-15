#!/usr/bin/env python3
"""
Civ7 Multiplayer Lag Monitor v2 — macOS
================================
Single unified mode for both host and players.
- Live player stats from net_message_debug.log
- Self-diagnostics from Engine/Startup/General/Modding/Memory logs
- Press S to save a report snapshot at any time

Usage:
  python civ7_monitor.py
  python civ7_monitor.py --log "C:/custom/path/net_message_debug.log"
"""

import sys, os, re, time, threading, argparse, subprocess
from datetime import datetime
from collections import defaultdict

# ── Paths ─────────────────────────────────────────────────────────────────────

LOG_DIR  = os.path.join(os.path.expanduser("~"), "Library", "Application Support",
                        "Sid Meier's Civilization VII", "Logs")

LOG_NET  = os.path.join(LOG_DIR, "net_message_debug.log")
LOG_CONN = os.path.join(LOG_DIR, "net_connection_debug.log")
LOG_TRAN = os.path.join(LOG_DIR, "net_transport_debug.log")
LOG_ENG  = os.path.join(LOG_DIR, "Engine.log")
LOG_STA  = os.path.join(LOG_DIR, "Startup.log")
LOG_GEN  = os.path.join(LOG_DIR, "General.log")
LOG_MOD  = os.path.join(LOG_DIR, "Modding.log")
LOG_MEM  = os.path.join(LOG_DIR, "MemoryUsage.log")
LOG_LUA  = os.path.join(LOG_DIR, "Lua.log")
CRASH_DIR = os.path.join(os.path.expanduser("~"), "Library", "Application Support", "Firaxis Games",
                         "Sid Meier's Civilization VII", "CrashReports")

REFRESH_NET  = 3   # seconds between net log reads
REFRESH_DIAG = 30  # seconds between self-diagnostics refresh

OOS_FROM_TURN_THRESHOLD = 10  # show [from tN] only if OOS > this

# ── Official DLC (not mods) ───────────────────────────────────────────────────

OFFICIAL_DLC = {
    'ada-lovelace','age-antiquity','age-exploration','age-modern',
    'ashoka-himiko-alt','asia-wonders','assyria','base-standard',
    'bolivar','bulgaria','carthage','core','dai-viet','edward-teach',
    'friedrich-xerxes-alt','genghis-khan','gilgamesh','great-britain',
    'iceland','lakshmibai','mountain-natural-wonders','napoleon',
    'napoleon-alt','nepal','ottomans','pirate-republic','qajar',
    'sayyida-al-hurra','shawnee-tecumseh','silla','tonga','trung-nhi',
    'water-wonders'
}

# ── Regex ─────────────────────────────────────────────────────────────────────

RE_TS        = re.compile(r'\[(\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2})\]')
RE_CREATE    = re.compile(r"Player created for (.+?) / iID: (\d+)")
RE_TURN      = re.compile(r"Game Turn: (\d+)")
RE_ACTIVE    = re.compile(r"Player (\d+) set TurnActive (\d)")
RE_DONE_RECV = re.compile(r"GameCore RECV \((\d+)\): PlayerTurnComplete: ePlayer=(\d+)")
RE_DONE_SEND = re.compile(r"GameCore SEND: PlayerTurnComplete: ePlayer=(\d+)")
RE_OOS       = re.compile(r"AutoArchive out of sync.*?Player=(\d+)")
RE_LNK_OPEN  = re.compile(r"FireWire Link Created: (\d+)")
RE_LNK_CLOSE = re.compile(r"FireWire Link Closed: (\d+)")
RE_CONN_CLOSED = re.compile(r"ConnectionClosed Player\((\d+)\)\r?$")
RE_SYNC_S    = re.compile(r"TurnSynchronizationBarrier")
RE_SYNC_E    = re.compile(r"GameSyncComplete")
RE_TIMER_EXP = re.compile(r"PlayerTurnComplete: ePlayer=(\d+), eReason=0x4601eac9")
RE_SNAPSHOT  = re.compile(r"PlayerSnapshotStatus: ePlayer=(\d+), snapShotProcessed=0")
RE_HOSTED    = re.compile(r"Network Session Hosted")

# ── Game state ────────────────────────────────────────────────────────────────

class CivGameState:
    def __init__(self):
        self.players          = {}
        self.current_turn     = 0
        self.turn_start_ts    = None
        self.turn_times       = []
        self.turn_order       = []
        self.turn_finish_ts   = {}
        self.turn_finish_secs = {}
        self.last_order_names = []
        self.oos_count        = defaultdict(int)
        self.oos_first_turn   = {}
        self.recv_count       = defaultdict(int)
        self.normal_pkts      = defaultdict(int)
        self.reconnects       = defaultdict(int)
        self.reconnect_log    = defaultdict(list)  # iID -> [(ts_str, turn)]
        self.last_place       = defaultdict(int)   # iID -> times finished last
        self.turns_counted    = 0                  # total turns with finish data
        self.sync_start_ts    = None
        self.sync_times       = []
        self.game_started     = False
        self._last_error      = ""
        self.is_host          = False              # set when "Network Session Hosted" seen
        self.self_iid         = None               # iID of the player running this program
        self.alerted_critical = set()             # iIDs already beeped
        # Turn time tracking
        self.player_turn_start  = {}
        self.player_turn_times  = defaultdict(list)
        self.player_last5_times = defaultdict(list)
        self.timer_expired      = defaultdict(int)
        self.snapshot_fail      = defaultdict(int) # iID -> loading screen count
        self.oos_history        = defaultdict(list) # iID -> [(turn, ts_str, obj_type)]

    def pname(self, iid):
        return self.players.get(int(iid), f"P{iid}")

    def reset_turn(self):
        self.turn_order        = []
        self.turn_finish_ts    = {}
        self.turn_finish_secs  = {}
        self.player_turn_start = {}

def get_ts(line):
    m = RE_TS.search(line)
    return datetime.strptime(m.group(1), "%Y-%m-%d %H:%M:%S") if m else None

def process_net_line(line, s):
    t = get_ts(line)

    # Detect if running as host
    if RE_HOSTED.search(line):
        s.is_host = True
        return

    m = RE_CREATE.search(line)
    if m:
        name, iid = m.group(1).strip(), int(m.group(2))
        if iid in s.players:
            if s.players[iid] != name:
                s.players[iid] = name
                s.oos_count[iid] = 0
                s.recv_count[iid] = 0
                s.normal_pkts[iid] = 0
                s.reconnects[iid] = 0
                s.reconnect_log[iid] = []
                if iid in s.oos_first_turn:
                    del s.oos_first_turn[iid]
            else:
                s.reconnects[iid] += 1
                if t:
                    ts_str = t.strftime('%H:%M')
                    s.reconnect_log[iid].append((ts_str, s.current_turn))
                    if len(s.reconnect_log[iid]) > 8:
                        s.reconnect_log[iid].pop(0)
        else:
            s.players[iid] = name
        return

    m = RE_TURN.search(line)
    if m and t:
        new = int(m.group(1))
        if new != s.current_turn:
            s.game_started = True
            if s.current_turn > 0 and s.turn_start_ts and s.turn_order:
                dur = (t - s.turn_start_ts).total_seconds()
                s.turn_times.append((s.current_turn, dur))
                if len(s.turn_times) > 8:
                    s.turn_times.pop(0)
                s.last_order_names = [s.pname(i) for i in s.turn_order]
                # Track who finished last
                if s.turn_order:
                    last_iid = s.turn_order[-1]
                    s.last_place[last_iid] += 1
                    s.turns_counted += 1
                for iid in s.turn_order:
                    s.normal_pkts[iid] += 1
            s.current_turn = new
            s.turn_start_ts = t
            s.reset_turn()
        return

    m = RE_DONE_RECV.search(line)
    if m and t:
        iid = int(m.group(2))
        s.recv_count[iid] += 1
        if iid not in s.turn_finish_ts:
            s.turn_finish_ts[iid] = t
            s.turn_order.append(iid)
            if s.turn_start_ts:
                s.turn_finish_secs[iid] = (t - s.turn_start_ts).total_seconds()
        return

    m = RE_DONE_SEND.search(line)
    if m and t:
        iid = int(m.group(1))
        # This player is sending — they are the one running this program
        if s.self_iid is None:
            s.self_iid = iid
        # host's own send — count but don't double-count as recv
        if iid not in s.turn_finish_ts:
            s.turn_finish_ts[iid] = t
            s.turn_order.append(iid)
            if s.turn_start_ts:
                s.turn_finish_secs[iid] = (t - s.turn_start_ts).total_seconds()
        return

    m = RE_OOS.search(line)
    if m:
        iid = int(m.group(1))
        s.oos_count[iid] += 1
        if iid not in s.oos_first_turn:
            s.oos_first_turn[iid] = s.current_turn
        # Extract object type for history: "AutoArchive=PlayerTreasury" -> "PlayerTreasury"
        obj_m = re.search(r'AutoArchive=(\w+)', line)
        obj_type = obj_m.group(1) if obj_m else 'Unknown'
        if t:
            ts_str = t.strftime('%H:%M')
            entry = (s.current_turn, ts_str, obj_type)
            s.oos_history[iid].append(entry)
            if len(s.oos_history[iid]) > 10:
                s.oos_history[iid].pop(0)
        return

    if RE_SYNC_S.search(line) and t:
        s.sync_start_ts = t
        return

    if RE_SYNC_E.search(line) and t:
        if s.sync_start_ts:
            s.sync_times.append((t - s.sync_start_ts).total_seconds())
            if len(s.sync_times) > 10:
                s.sync_times.pop(0)
            s.sync_start_ts = None
        return

    # Track per-player turn time via TurnActive events
    m = RE_ACTIVE.search(line)
    if m and t:
        iid    = int(m.group(1))
        active = int(m.group(2))
        if active == 1:
            # Only record start if player doesn't already have one this turn
            if iid not in s.player_turn_start:
                s.player_turn_start[iid] = t
        elif active == 0 and iid in s.player_turn_start:
            # Player finished their turn — record duration
            secs = (t - s.player_turn_start[iid]).total_seconds()
            if 5 <= secs <= 600:  # sanity check: between 5s and 10min
                s.player_turn_times[iid].append(secs)
                s.player_last5_times[iid].append((s.current_turn, secs))
                if len(s.player_last5_times[iid]) > 5:
                    s.player_last5_times[iid].pop(0)
            del s.player_turn_start[iid]
        return

    # Track timer expirations
    m = RE_TIMER_EXP.search(line)
    if m:
        iid = int(m.group(1))
        s.timer_expired[iid] += 1
        return

    # Track loading screen triggers (snapShotProcessed=0)
    m = RE_SNAPSHOT.search(line)
    if m:
        iid = int(m.group(1))
        s.snapshot_fail[iid] += 1
        return

def calc_dupes(state):
    """Returns dict iID -> (dupes_total, dupes_per_turn).
    Host (iid==0) excluded. Only meaningful after 3+ turns of data."""
    result = {}
    for iid in state.players:
        if iid == 0:
            result[iid] = (0, 0.0)
            continue
        recv     = state.recv_count.get(iid, 0)
        expected = state.normal_pkts.get(iid, 0)
        if expected < 3:
            result[iid] = (0, 0.0)
        else:
            total = max(0, recv - expected)
            ratio = total / expected
            result[iid] = (total, ratio)
    return result

def risk_label(oos, dpt, recon):
    """dpt = dupes per turn (ratio)"""
    score = 0
    # OOS thresholds
    if oos > 1000:  score += 3
    elif oos > 500: score += 2
    elif oos > 100: score += 1
    # Dupes per turn thresholds (based on observed data)
    if dpt > 1.0:   score += 3
    elif dpt > 0.7: score += 2
    elif dpt > 0.4: score += 1
    # Reconnects
    if recon > 15:   score += 3
    elif recon > 10: score += 2
    elif recon > 5:  score += 1
    if score >= 5: return "🔴 CRITICAL"
    if score >= 3: return "🔴 HIGH"
    if score >= 2: return "🟡 MED"
    return "🟢 OK"

# ── Self-diagnostics ──────────────────────────────────────────────────────────

def read_file(path):
    if not os.path.exists(path):
        return ""
    try:
        with open(path, 'r', encoding='utf-8', errors='replace') as f:
            return f.read()
    except Exception:
        return ""

_net_counters_prev = {}
_net_counters_time  = [0.0]

APP_VERSION    = "1.3"
VERSION_URL    = "https://raw.githubusercontent.com/yourexgirlfriend/civ7-lag-monitor/main/version.txt"
DRAFTER_URL    = "https://drafter.games"

def open_drafter_url(event=None):
    """Open drafter.games in the default browser."""
    try:
        import webbrowser
        webbrowser.open(DRAFTER_URL)
    except Exception:
        try:
            import subprocess
            subprocess.run(["open", DRAFTER_URL])
        except Exception:
            pass

def check_latest_version():
    """Returns latest version string from GitHub, or None on failure."""
    try:
        import urllib.request
        with urllib.request.urlopen(VERSION_URL, timeout=5) as r:
            return r.read().decode().strip()
    except Exception:
        return None

def run_self_diagnostics():
    """Returns (hw_lines, status_lines, warning_lines)
    hw_lines     — hardware specs (CPU, RAM, GPU)
    status_lines — status indicators with icons (mods, vpn)
    warning_lines — problems that affect stability
    """
    hw     = []
    status = []
    warn   = []

    eng = read_file(LOG_ENG)
    sta = read_file(LOG_STA)
    gen = read_file(LOG_GEN)
    tra = read_file(LOG_TRAN)
    mod = read_file(LOG_MOD)
    mem = read_file(LOG_MEM)

    # ── Hardware ──
    m = re.search(r'Physical system memory size: ([\d.]+)GB', eng)
    if m:
        ram = float(m.group(1))
        hw.append(f"RAM: {ram:.0f} GB")
        if ram < 16:
            warn.append(f"🔴 RAM {ram:.0f} GB — critically low for Civ7")
        elif ram == 16:
            warn.append(f"⚠️  RAM 16 GB — minimum, risk in long games")

    m = re.search(r'Physical processor count: (\d+)', eng)
    cpu_cores = int(m.group(1)) if m else 0
    # ── CPU name from sysctl (macOS) ──
    cpu_name = ""
    try:
        import subprocess as _sp
        r = _sp.run(["sysctl", "-n", "machdep.cpu.brand_string"],
                    capture_output=True, text=True, timeout=3)
        cpu_name = r.stdout.strip()
    except Exception:
        pass
    if cpu_name and cpu_cores:
        hw.append(f"CPU: {cpu_name} ({cpu_cores} cores)")
    elif cpu_name:
        hw.append(f"CPU: {cpu_name}")
    elif cpu_cores:
        hw.append(f"CPU: {cpu_cores} cores")

    if 'IsLaptopOrTablet: 1' in eng:
        hw.append("Device: Laptop")
        # ── Energy Saver check (macOS) ──
        try:
            import subprocess as _sp
            r = _sp.run(["pmset", "-g"], capture_output=True, text=True, timeout=3)
            if "lowpowermode" in r.stdout and "1" in r.stdout.split("lowpowermode")[-1][:5]:
                hw.append("Power: Low Power Mode ON")
                warn.append("⚠️  Low Power Mode is ON — disable for better multiplayer stability")
            else:
                hw.append("Power: Normal")
        except Exception:
            hw.append("Power: Unknown")

    m = re.search(r'Selected graphics device is: (.+)', sta)
    gpu_vram_mb = 0
    if m:
        gpu = m.group(1).strip()
        # ── VRAM from system_profiler (macOS) ──
        try:
            import subprocess as _sp
            r = _sp.run(
                ["system_profiler", "SPDisplaysDataType"],
                capture_output=True, text=True, timeout=5
            )
            m_vram = re.search(r'VRAM.*?:\s*(\d+)\s*MB', r.stdout, re.IGNORECASE)
            if m_vram:
                gpu_vram_mb = int(m_vram.group(1))
        except Exception:
            pass
        vram_str = f" {gpu_vram_mb} MB VRAM" if gpu_vram_mb else ""
        hw.append(f"GPU: {gpu}{vram_str}")
        INTEGRATED_KW = ['Radeon(TM)', 'Intel(R) UHD', 'Intel(R) HD', 'Iris']
        if any(k in gpu for k in INTEGRATED_KW):
            warn.append(f"⚠️  Integrated GPU ({gpu}) — weak for Civ7 multiplayer")
        elif gpu_vram_mb and gpu_vram_mb < 2048:
            warn.append(f"⚠️  Low VRAM ({gpu_vram_mb} MB) — may cause issues in long games")

    # ── PC Rating — right after GPU ──
    rating_str, _ = pc_rating(hw)
    hw.append(f"PC Rating: {rating_str}")

    # ── OS detection from net_connection_debug.log ──
    conn = read_file(LOG_CONN)
    os_str = "Unknown"
    if conn:
        m_os = re.search(r'SetConnectionInfo commandline arg = (.+)', conn)
        if m_os:
            path = m_os.group(1).strip().strip('"')
            if 'Win64_DX12' in path:
                os_str = "Windows"
            elif 'MacOS' in path or '.app/Contents' in path:
                os_str = "macOS"
            elif 'linux' in path.lower():
                os_str = "Linux"
    hw.append(f"OS: {os_str}")

    # ── Connection type (WiFi / Ethernet) + channel load ──
    try:
        import psutil as _ps
        addrs = _ps.net_if_addrs()
        stats = _ps.net_if_stats()
        conn_type = None
        active_if = None
        VIRTUAL = ('loopback', 'virtual', 'vmware', 'vbox', 'tunnel',
                   'tap', 'tun', 'pseudo', 'outline', 'nordvpn',
                   'expressvpn', 'proton', 'wireguard', 'wintun')
        WIFI_KW  = ('wi-fi', 'wifi', 'wlan', 'wireless', 'airport', '802.11')

        candidates = []
        for iface, addr_list in addrs.items():
            iface_lower = iface.lower()
            if iface_lower in ('lo',) or any(x in iface_lower for x in VIRTUAL):
                continue
            has_ipv4 = any(a.family == 2 and not a.address.startswith('127.')
                           for a in addr_list)
            is_up = iface in stats and stats[iface].isup
            if has_ipv4 and is_up:
                is_wifi = any(k in iface_lower for k in WIFI_KW)
                candidates.append((iface, is_wifi))

        if candidates:
            # Prefer named physical interfaces (Ethernet/Wi-Fi) over generic ones
            iface, is_wifi = candidates[0]
            conn_type = 'WiFi' if is_wifi else 'Ethernet'
            active_if = iface

        if conn_type:
            icon = "🟡" if conn_type == 'WiFi' else "🟢"
            hw.append(f"Connection: {icon} {conn_type}")
            if conn_type == 'WiFi':
                warn.append("⚠️  WiFi detected — cable recommended for multiplayer")


    except Exception:
        pass

    # ── Engine version ──
    m = re.search(r'Engine Version: ([\d.]+)', eng)
    if m:
        hw.append(f"Game: v{m.group(1)}")

    # ── Device type ──
    is_laptop = 'IsLaptopOrTablet: 1' in eng

    # ── Memory usage from MemoryUsage.log ──
    mem_current_mb = 0
    mem_peak_mb    = 0
    mem_spikes     = []
    mem_total_mb   = int(ram * 1024) if ram else 32768

    if mem:
        rows = []
        for line in mem.splitlines():
            parts = [p.strip() for p in line.split('|')]
            if len(parts) >= 4 and parts[0].isdigit():
                try:
                    ts_unix = int(parts[0])
                    turn    = int(parts[1])
                    cur_mb  = int(parts[3])
                    rows.append((ts_unix, turn, cur_mb))
                except ValueError:
                    pass

        if rows:
            mem_current_mb = rows[-1][2]
            mem_peak_mb    = max(r[2] for r in rows)
            peak_pct = mem_peak_mb / mem_total_mb * 100 if mem_total_mb else 0

            # Detect spikes — find the row with peak value for accurate reporting
            peak_row = max(rows, key=lambda r: r[2])

            # First: check if peak is at session start (save load)
            if rows.index(peak_row) <= 1 and peak_row[2] > 500:
                mem_spikes.append((peak_row[1], peak_row[2], peak_row[2], "save load"))
            else:
                # Mid-session spikes: jump > 200 MB between consecutive turns
                for i in range(1, len(rows)):
                    delta = rows[i][2] - rows[i-1][2]
                    if delta > 200:
                        prev_turn = rows[i-1][1]
                        cur_turn  = rows[i][1]
                        if prev_turn > cur_turn:
                            action = "save reload"
                        elif cur_turn - prev_turn > 5:
                            action = "reconnect/reload"
                        else:
                            action = f"turn {cur_turn}"
                        mem_spikes.append((cur_turn, rows[i][2], delta, action))

            # Add memory info to hardware display
            hw.append(f"Civ7 RAM usage: {mem_current_mb/1024:.1f} GB now / {mem_peak_mb/1024:.1f} GB peak")

            # Warnings — percentage based, only yellow (50%) and red (70%)
            if peak_pct > 70:
                warn.append(f"🔴 Civ7 memory peak {mem_peak_mb/1024:.1f} GB "
                            f"({peak_pct:.0f}% of RAM) — crash risk on next load")
                for turn, mb, delta, action in mem_spikes[-5:]:
                    warn.append(f"    Turn {turn:>3}  +{mb/1024:.1f} GB peak  [{action}]")
            elif peak_pct > 50:
                warn.append(f"⚠️  Civ7 memory peak {mem_peak_mb/1024:.1f} GB "
                            f"({peak_pct:.0f}% of RAM) — monitor closely")
                for turn, mb, delta, action in mem_spikes[-5:]:
                    warn.append(f"    Turn {turn:>3}  +{mb/1024:.1f} GB peak  [{action}]")

    # ── Ping to relay server ──
    relay_host = None
    relay_ping_ms = None
    if tra:
        m_relay = re.search(r'host:([a-f0-9]+\.inv-prd\.firaxislive\.net)', tra)
        if m_relay:
            relay_host = m_relay.group(1)
            try:
                import socket
                t0 = time.time()
                s = socket.create_connection((relay_host, 443), timeout=5)
                relay_ping_ms = (time.time() - t0) * 1000
                s.close()
            except Exception:
                relay_ping_ms = None

    if relay_ping_ms is not None:
        if relay_ping_ms < 200:
            ping_icon = "🟢"
        elif relay_ping_ms < 400:
            ping_icon = "🟡"
        else:
            ping_icon = "🔴"
        ping_str = f"{relay_ping_ms:.0f}ms {ping_icon}"
        hw.append(f"Relay ping: {ping_str}")
        if relay_ping_ms >= 400:
            warn.append(f"🔴 Relay ping {relay_ping_ms:.0f}ms — very high, expect disconnects")
        elif relay_ping_ms >= 200:
            warn.append(f"⚠️  Relay ping {relay_ping_ms:.0f}ms — above normal")
    elif relay_host:
        hw.append("Relay ping: measuring failed")

    # ── Lua.log errors ──
    lua = read_file(LOG_LUA)
    if lua:
        lua_errors = re.findall(r'(?:Error|ERROR|error)[^\n]*', lua)
        # Filter noise — only real script errors
        real_errors = [e.strip() for e in lua_errors
                       if any(x in e for x in ['attempt to', 'stack overflow',
                                                'bad argument', 'nil value',
                                                'table index', 'global'])]
        if len(real_errors) >= 3:
            warn.append(f"⚠️  Lua script errors this session: {len(real_errors)}")
            warn.append("    May cause OOS if mods alter gameplay logic")
            for e in real_errors[-3:]:
                warn.append(f"    {e[:80]}")
        elif len(real_errors) > 0:
            warn.append(f"⚠️  Lua script errors: {len(real_errors)} (minor)")

    # ── Crashpad / CrashReports ──
    crash_info = []
    if os.path.isdir(CRASH_DIR):
        import json, glob
        meta_files = sorted(
            glob.glob(os.path.join(CRASH_DIR, "**", "metadata.json"), recursive=True),
            key=os.path.getmtime, reverse=True
        )
        for mf in meta_files[:3]:  # last 3 crashes
            try:
                with open(mf, encoding='utf-8', errors='replace') as f2:
                    meta = json.load(f2)
                crash_type = meta.get('crash_type') or meta.get('exception_code', 'Unknown')
                crash_time = meta.get('creation_time') or meta.get('timestamp', '')
                crash_module = meta.get('crashing_module', '')
                crash_info.append((crash_time, crash_type, crash_module))
            except Exception:
                # Try reading as plain text
                try:
                    raw = open(mf, encoding='utf-8', errors='replace').read()
                    # Look for exception type patterns
                    m_exc = re.search(r'EXCEPTION_\w+|ACCESS_VIOLATION|OUT_OF_MEMORY', raw)
                    exc = m_exc.group(0) if m_exc else 'Unknown'
                    crash_info.append(('', exc, ''))
                except Exception:
                    pass

    if crash_info:
        warn.append(f"💥 Game crashed {len(crash_info)} time(s) recently:")
        for ct, ctype, cmod in crash_info:
            time_str = f" ({ct})" if ct else ""
            mod_str  = f" in {cmod}" if cmod else ""
            if 'ACCESS_VIOLATION' in ctype or 'access_violation' in ctype.lower():
                desc = "memory access error — verify game files"
            elif 'OUT_OF_MEMORY' in ctype or 'out_of_memory' in ctype.lower():
                desc = "ran out of RAM — close background apps"
            elif 'STACK_OVERFLOW' in ctype or 'stack_overflow' in ctype.lower():
                desc = "stack overflow — likely a mod conflict"
            else:
                desc = "unknown cause"
            warn.append(f"    {ctype}{mod_str}{time_str} — {desc}")

    # ── Steam path ──
    if 'SteamApp' in gen and 'Prebuilt database not found' in gen:
        warn.append("⚠️  Non-standard Steam path — databases rebuilt every launch")
        warn.append("    Fix: reinstall Steam to C:/Program Files (x86)/Steam/")

    timeouts = len(re.findall(r'has not shut down, it timed out', gen))
    if timeouts > 3:
        warn.append(f"⚠️  {timeouts} thread timeouts last session")

    # ── VPN detection (TAP/TUN adapter with active IP + routing table) ──
    vpn_detected    = False
    vpn_uncertain   = False
    tap_tun_active  = False
    default_via_vpn = False

    try:
        ipconfig = subprocess.check_output(
            ["ipconfig", "/all"], text=True, stderr=subprocess.DEVNULL,
            creationflags=subprocess.CREATE_NO_WINDOW
        )
        tap_keywords = ["tap-windows", "tap adapter", "tun adapter", "wireguard",
                        "wintun", "utun", "vpn tunnel", "virtual private"]

        # Parse ipconfig into adapter blocks, check each for VPN keywords + active IP
        blocks = []
        current_block = []
        for line in ipconfig.splitlines():
            if line and not line.startswith(' ') and not line.startswith('\t') and ':' in line:
                if current_block:
                    blocks.append('\n'.join(current_block))
                current_block = [line]
            else:
                current_block.append(line)
        if current_block:
            blocks.append('\n'.join(current_block))

        for block in blocks:
            block_lower = block.lower()
            if any(kw in block_lower for kw in tap_keywords):
                # Check if this adapter has an active IP (not disconnected)
                has_ip = ('ipv4 address' in block_lower or
                          'ip address' in block_lower)
                is_disconnected = ('media disconnected' in block_lower or
                                   'media state' in block_lower and 'disconnected' in block_lower)
                if has_ip and not is_disconnected:
                    tap_tun_active = True
                    break
    except Exception:
        pass

    try:
        route = subprocess.check_output(
            ["route", "print", "0.0.0.0"], text=True, stderr=subprocess.DEVNULL,
            creationflags=subprocess.CREATE_NO_WINDOW
        )
        default_routes = [l for l in route.splitlines() if l.strip().startswith("0.0.0.0")]
        if len(default_routes) > 1:
            default_via_vpn = True
        elif tap_tun_active and default_routes:
            default_via_vpn = True
    except Exception:
        pass

    if tap_tun_active and default_via_vpn:
        vpn_detected = True
        warn.append("⚠️  VPN detected (active tunnel adapter + routed traffic)")
        warn.append("    Disable VPN before playing multiplayer — causes lag and OOS")
    elif tap_tun_active:
        vpn_uncertain = True
        warn.append("⚠️  VPN adapter active but routing unclear")
        warn.append("    If VPN is enabled — disable before playing multiplayer")
    elif default_via_vpn:
        vpn_uncertain = True
        warn.append("⚠️  Unusual network routing — possible VPN or corporate network")

    if vpn_detected:
        status.append("🔴 VPN: detected — disable before playing")
    elif vpn_uncertain:
        status.append("🟡 VPN: possible — unable to confirm")
    else:
        status.append("🟢 VPN: not detected")

    # ── Mods ──
    ingame  = []
    blocked = []
    if mod:
        # Check mods enabled at launch via Initial Boot Configuration
        # Always use the LAST occurrence — this reflects the current/most recent launch
        menu_mods = set()
        last_boot = None
        for ms in re.finditer(r'Initial Boot Configuration', mod):
            last_boot = ms.start()
        if last_boot is not None:
            chunk = mod[last_boot:last_boot+3000]
            for m2 in re.finditer(r'\t([A-Za-z][A-Za-z0-9_\-]+) \(([^)]+)\)', chunk):
                if m2.group(1) not in OFFICIAL_DLC:
                    menu_mods.add((m2.group(1), m2.group(2)))

        # Workshop subscriptions installed
        subs = re.findall(r'Subscription (\d+) - Installed\? 1', mod)

        if menu_mods:
            names = ", ".join(f"'{n}'" for _, n in sorted(menu_mods))
            status.append(f"🔴 Mods: ENABLED IN MAIN MENU — {names}")
            warn.append(f"🔴 YOU HAVE MODS ENABLED! Disable before playing multiplayer:")
            for _, mname in sorted(menu_mods):
                warn.append(f"    • {mname}")
        elif subs:
            status.append(f"🟢 Mods: {len(subs)} installed, all disabled")
        else:
            status.append("🟢 Mods: none detected")

        # Load errors
        errors  = mod.count('ERROR: Failed to load mod')
        deleted = sum(int(d) for d in re.findall(r'Deleted (\d+) mods', mod) if int(d) > 0)
        if errors > 1:
            warn.append(f"⚠️  {errors} mod load error(s) — {deleted} file(s) auto-deleted")
            warn.append("    Fix: verify game files via Steam")
    else:
        status.append("🟢 Mods: none detected")

    # ── Memory ──
    if mem:
        rows = []
        for line in mem.strip().split('\n')[1:]:
            parts = [p.strip() for p in line.split('|')]
            if len(parts) >= 5:
                try:
                    rows.append((int(parts[1]), int(parts[3]), int(parts[4])))
                except ValueError:
                    pass
        if rows:
            t50 = [m2 for t, m2, _ in rows if t == 50]
            if t50 and t50[0] > 8000:
                warn.append(f"⚠️  High memory at turn 50: {t50[0]} MB (normal ~4-5k)")
            spikes = sum(1 for i in range(1, len(rows))
                        if abs(rows[i][1] - rows[i-1][1]) > 2000)
            if spikes > 2:
                warn.append(f"⚠️  {spikes} abnormal memory spikes — check power settings")

    return hw, status, warn


# ── Display helpers ───────────────────────────────────────────────────────────

def bar(val, max_val, w=16):
    if max_val == 0:
        return '░' * w
    n = int(min(val / max_val, 1.0) * w)
    return '█' * n + '░' * (w - n)

def fmt_sec(s):
    m, sec = divmod(int(s), 60)
    return f"{m}:{sec:02d}"

def risk_label(oos, dupes, recon):
    score = 0
    if oos > 1000:  score += 3
    elif oos > 500: score += 2
    elif oos > 100: score += 1
    if dupes > 20:  score += 2
    elif dupes > 5: score += 1
    if recon > 2:   score += 2
    elif recon > 0: score += 1
    if score >= 5: return "🔴 CRITICAL"
    if score >= 3: return "🔴 HIGH"
    if score >= 2: return "🟡 MED"
    return "🟢 OK"

def pc_rating(hw_lines):
    """Returns (rating_str, rating_level) based on hardware info.
    rating_level: 0=good, 1=borderline, 2=weak"""
    score = 0
    ram   = 0
    gpu_integrated = False
    laptop = False
    vram_mb = 0
    cpu_name = ""

    INTEGRATED_KW = ['Radeon(TM)', 'Intel(R) UHD', 'Intel(R) HD', 'Iris']
    WEAK_CPU_KW   = ['Celeron', 'Pentium', 'Atom', 'i3-', 'i3 ']
    OLD_CPU_KW    = ['i5-6', 'i5-7', 'i5-8', 'i7-6', 'i7-7',
                     'Ryzen 3', 'Ryzen 5 1', 'Ryzen 5 2']

    for h in hw_lines:
        m = re.match(r'RAM: (\d+)', h)
        if m: ram = int(m.group(1))
        if any(k in h for k in INTEGRATED_KW):
            gpu_integrated = True
        if 'Device: Laptop' in h:
            laptop = True
        m = re.search(r'(\d+) MB VRAM', h)
        if m: vram_mb = int(m.group(1))
        if h.startswith('CPU:'):
            cpu_name = h

    # RAM
    if ram > 0 and ram < 16: score += 3
    elif ram == 16:           score += 1

    # GPU
    if gpu_integrated:               score += 2
    elif vram_mb and vram_mb < 2048: score += 2
    elif vram_mb and vram_mb < 4096: score += 1

    # CPU
    if any(k in cpu_name for k in WEAK_CPU_KW): score += 2
    elif any(k in cpu_name for k in OLD_CPU_KW): score += 1

    # Laptop
    if laptop: score += 1

    if score >= 5: return "🔴 Weak for Civ7 MP", 2
    if score >= 2: return "🟡 Borderline", 1
    return "🟢 Good", 0

def player_label(name, iid, state):
    """Returns player name with appropriate suffix."""
    if state.self_iid is not None:
        if iid == state.self_iid:
            return f"{name} (you)"
        elif iid == 0 and not state.is_host:
            return f"{name} (host)"
    else:
        # Fallback: iid==0 is host
        if iid == 0:
            return f"{name} (you)" if state.is_host else f"{name} (host)"
    return name

def clear():
    os.system('cls' if os.name == 'nt' else 'clear')

# ── Render ────────────────────────────────────────────────────────────────────

# ── Save report ───────────────────────────────────────────────────────────────

def _get_desktop():
    try:
        d = os.path.join(os.path.expanduser("~"), "Desktop")
        if os.path.exists(d):
            return d
    except Exception:
        pass
    for candidate in [
        os.path.join(os.path.expanduser("~"), "Desktop"),
        os.path.join(os.path.expanduser("~"), "Työpöytä"),
        os.path.join(os.path.expanduser("~"), "Bureau"),
        os.path.expanduser("~"),
    ]:
        if os.path.exists(candidate):
            return candidate
    return os.path.expanduser("~")


def build_report(state, diag_hw, diag_status, diag_warn, log_path):
    SEP  = "=" * 70
    sep2 = "-" * 70
    out  = []

    player_name = state.players.get(state.self_iid, "Unknown") \
                  if state.self_iid is not None else "Unknown"
    out += [
        SEP,
        "  CIV7 LAG MONITOR — PLAYER REPORT",
        f"  Player:  {player_name}",
        f"  Date:    {datetime.now().strftime('%d-%m-%Y %H:%M:%S')}",
        SEP, "",
    ]

    # Diagnostics
    out += ["-- DIAGNOSTICS " + "-" * 55, ""]
    if diag_hw:
        out.append("  Hardware:")
        for h in diag_hw:
            out.append(f"    {h}")
    out.append("")
    if diag_status:
        out.append("  Status:")
        for s in diag_status:
            out.append(f"    {s}")
    out.append("")
    if diag_warn:
        out.append("  Warnings:")
        for w in diag_warn:
            out.append(f"    {w}")
    else:
        out.append("  No stability issues detected.")
    out.append("")

    # Game data
    dupes = calc_dupes(state)
    out += ["-- GAME DATA " + "-" * 57, ""]
    if state.players:
        out.append(f"  Turn: {state.current_turn}")
        out.append(f"  {'PLAYER':<18} {'OOS':>6} {'':10} {'D/T':>5} {'RECON':>5} {'DESYNC':>6}  RISK")
        out.append("  " + sep2)
        sorted_p = sorted(state.players.items(),
                          key=lambda x: state.oos_count.get(x[0], 0), reverse=True)
        for iid, name in sorted_p:
            oos            = state.oos_count.get(iid, 0)
            dup_total, dpt = dupes.get(iid, (0, 0.0))
            recon          = state.reconnects.get(iid, 0)
            desync         = state.snapshot_fail.get(iid, 0)
            r              = risk_label(oos, dpt, recon)
            label          = player_label(name, iid, state)
            ft = f"[from t{state.oos_first_turn[iid]}]" \
                 if oos > OOS_FROM_TURN_THRESHOLD and iid in state.oos_first_turn else ""
            dpt_str    = f"{dpt:.2f}" if dpt > 0 else "-"
            desync_str = str(desync) if desync else "-"
            out.append(f"  {label:<18} {oos:>6} {ft:<10} {dpt_str:>5} {recon:>5} {desync_str:>6}  {r}")
        out.append("")
        out.append("  Reconnect history:")
        for iid, name in sorted_p:
            log = state.reconnect_log[iid]
            if log:
                entries = "  ".join(f"{ts}(t{tn})" for ts, tn in log)
                out.append(f"    {name:<18} {entries}")
    else:
        out.append("  No game data captured.")
    out.append("")

    # Log files
    log_files = [
        ("net_message_debug.log",   LOG_NET),
        ("net_connection_debug.log", LOG_CONN),
        ("net_transport_debug.log",  LOG_TRAN),
        ("Modding.log",              LOG_MOD),
        ("Engine.log",               LOG_ENG),
        ("Startup.log",              LOG_STA),
        ("MemoryUsage.log",          LOG_MEM),
        ("General.log",              LOG_GEN),
        ("Lua.log",                  LOG_LUA),
    ]
    for log_name, log_fpath in log_files:
        out.append(f"-- {log_name} " + "-" * max(1, 66 - len(log_name)))
        out.append("")
        c = read_file(log_fpath)
        out.append(c if c else "  [file not found or empty]")
        out.append("")

    return "\n".join(out)


def save_report(state, diag_hw, diag_status, diag_warn, log_path):
    import tkinter.filedialog as fd
    player_name = state.players.get(state.self_iid, "report") \
                  if state.self_iid is not None else "report"
    safe_name  = re.sub(r'[^\w\s\-]', '', player_name).strip()
    game_date  = datetime.now().strftime("%d-%m-%Y")
    default_name = f"{safe_name} report, game {game_date}.txt"
    desktop = _get_desktop()
    path = fd.asksaveasfilename(
        initialdir=desktop,
        initialfile=default_name,
        defaultextension=".txt",
        filetypes=[("Text files", "*.txt"), ("All files", "*.*")],
        title="Save Report"
    )
    if not path:
        return None
    report_text = build_report(state, diag_hw, diag_status, diag_warn, log_path)
    try:
        with open(path, 'w', encoding='utf-8') as f:
            f.write(report_text)
        return path
    except Exception:
        return None


# ── GUI ───────────────────────────────────────────────────────────────────────

import customtkinter as ctk
import tkinter as tk
try:
    import pyperclip
    HAS_PYPERCLIP = True
except ImportError:
    HAS_PYPERCLIP = False

ctk.set_appearance_mode("dark")
ctk.set_default_color_theme("dark-blue")

# ── Palette ───────────────────────────────────────────────────────────────────
BG_MAIN    = "#1a1710"
BG_CARD    = "#252118"
BG_PANEL   = "#1e1b12"
GOLD       = "#c9a84c"
GOLD_DIM   = "#7a6428"
GOLD_LIGHT = "#e8c96a"
TEXT_MAIN  = "#e8dcc8"
TEXT_DIM   = "#8a7a68"

FS         = 18   # base font size

RISK_COLORS = {
    "CRITICAL": "#e05050",
    "HIGH":     "#e05050",
    "MED":      "#d4983a",
    "OK":       "#6aad6a",
}

def risk_color(label):
    for k, v in RISK_COLORS.items():
        if k in label:
            return v
    return "#6aad6a"

def fmt_sec(s):
    s = int(s)
    return f"{s//60}:{s%60:02d}" if s >= 60 else f"{s}s"

def BA(size, bold=False):
    return ("Book Antiqua", size, "bold") if bold else ("Book Antiqua", size)

def MONO(size, bold=False):
    return ("Courier New", size, "bold") if bold else ("Courier New", size)


class GoldSep(ctk.CTkFrame):
    def __init__(self, master, **kwargs):
        super().__init__(master, height=1, fg_color=GOLD_DIM, **kwargs)


# Global cache for last selected text across all readonly widgets
_READONLY_LAST_SEL    = [""]
_READONLY_LAST_WIDGET = [None]


def make_readonly_text(parent, height):
    """Tk Text: invisible cursor, selectable+copyable via pyperclip."""
    t = tk.Text(parent,
                height=height,
                font=BA(FS),
                bg=BG_PANEL,
                fg=TEXT_MAIN,
                insertwidth=0,
                selectbackground=GOLD_DIM,
                selectforeground=TEXT_MAIN,
                relief="flat",
                bd=0,
                highlightthickness=1,
                highlightbackground=GOLD_DIM,
                highlightcolor=GOLD,
                wrap="none",
                state="normal",
                cursor="arrow",
                exportselection=False)

    # Track selection in global cache for window-level Ctrl+C
    t._is_readonly = True

    def _cache_selection(e):
        try:
            sel = t.get("sel.first", "sel.last")
            if sel:
                _READONLY_LAST_SEL[0] = sel
                _READONLY_LAST_WIDGET[0] = t
        except tk.TclError:
            pass

    def _on_key(e):
        if e.keysym in ("Left","Right","Up","Down","Home","End",
                        "Prior","Next","shift_L","shift_R",
                        "control_L","control_R","Alt_L","Alt_R"):
            return None
        if e.state & 0x4 and e.keysym.lower() == "a":
            t.tag_add("sel", "1.0", "end")
            try:
                _READONLY_LAST_SEL[0] = t.get("1.0", "end-1c")
                _READONLY_LAST_WIDGET[0] = t
            except Exception:
                pass
            return "break"
        return "break"

    t.bind("<ButtonRelease-1>", _cache_selection)
    t.bind("<B1-Motion>",       _cache_selection)
    t.bind("<Key>",             _on_key)
    t.bind("<BackSpace>",       lambda e: "break")
    t.bind("<Delete>",          lambda e: "break")
    t.bind("<Button-3>",        lambda e: "break")
    return t


def set_readonly_text(widget, text, color_rules=None):
    # Save selection so clipboard isn't cleared on refresh
    try:
        sel_start = widget.index("sel.first")
        sel_end   = widget.index("sel.last")
        had_sel   = True
    except tk.TclError:
        had_sel = False

    widget.delete("1.0", "end")
    widget.insert("1.0", text)

    if color_rules:
        txt_lines = text.splitlines()
        for i, line in enumerate(txt_lines):
            for kw, col in color_rules:
                if kw in line:
                    tag = f"c{col[1:]}"
                    widget.tag_config(tag, foreground=col)
                    pos = line.find(kw)
                    if pos >= 0:
                        widget.tag_add(tag, f"{i+1}.{pos}", f"{i+1}.{pos+2}")
                    break

    # Restore selection so user can still Ctrl+C after refresh
    if had_sel:
        try:
            widget.tag_add("sel", sel_start, sel_end)
        except tk.TclError:
            pass


class PlayerCard(ctk.CTkFrame):
    def __init__(self, master, **kwargs):
        super().__init__(master, corner_radius=8, border_width=2,
                         fg_color=BG_CARD, border_color=GOLD_DIM, **kwargs)

        self.name_label = ctk.CTkLabel(
            self, text="", font=("Georgia", FS + 2, "bold"),
            anchor="w", text_color=GOLD_LIGHT)
        self.name_label.pack(fill="x", padx=14, pady=(14, 4))

        GoldSep(self).pack(fill="x", padx=10, pady=(0, 6))

        stats = ctk.CTkFrame(self, fg_color="transparent")
        stats.pack(fill="x", padx=14, pady=(2, 14))

        self._vals = {}
        for key in ["Risk", "OOS", "D/T", "Recon", "Desync"]:
            row = ctk.CTkFrame(stats, fg_color="transparent")
            row.pack(fill="x", pady=4)
            ctk.CTkLabel(row, text=f"{key}:", width=90,
                         font=BA(FS), anchor="w",
                         text_color=TEXT_MAIN).pack(side="left")
            val = ctk.CTkLabel(row, text="—",
                               font=BA(FS, bold=True),
                               anchor="w", text_color=TEXT_MAIN)
            val.pack(side="left")
            self._vals[key] = val

    def update_card(self, name, oos, dpt, recon, desync, risk,
                    is_self=False, is_host_player=False):
        suffix = " (you)" if is_self else (" (host)" if is_host_player else "")
        self.name_label.configure(text=f"{name}{suffix}")
        rc = risk_color(risk)
        self._vals["Risk"].configure(text=risk, text_color=rc)
        self._vals["OOS"].configure(text=str(oos) if oos else "—", text_color=TEXT_MAIN)
        self._vals["D/T"].configure(text=f"{dpt:.2f}" if dpt > 0 else "—", text_color=TEXT_MAIN)
        self._vals["Recon"].configure(text=str(recon) if recon else "—", text_color=TEXT_MAIN)
        self._vals["Desync"].configure(text=str(desync) if desync else "—", text_color=TEXT_MAIN)
        danger = "CRITICAL" in risk or "HIGH" in risk
        self.configure(border_color=rc if danger else GOLD_DIM)


def make_section_label(parent, text):
    ctk.CTkLabel(parent, text=text,
                 font=("Georgia", FS + 2, "bold"),
                 text_color=GOLD_LIGHT, anchor="w").pack(
        fill="x", padx=16, pady=(16, 4))
    GoldSep(parent).pack(fill="x", padx=12, pady=(0, 6))


class App(ctk.CTk):
    def __init__(self, log_path):
        super().__init__()
        self.log_path    = log_path
        self.gs          = CivGameState()
        self.file_pos    = 0
        self.diag_hw     = []
        self.diag_status = []
        self.diag_warn   = []
        self._last_diag  = datetime.now()
        self._cards      = {}

        self.title("CIV7 LAG MONITOR")
        try:
            from PIL import Image, ImageTk
            base = getattr(sys, "_MEIPASS", os.path.dirname(os.path.abspath(__file__)))
            img = Image.open(os.path.join(base, "icon.icns"))
            photo = ImageTk.PhotoImage(img)
            self.wm_iconphoto(True, photo)
            self._icon_ref = photo  # prevent GC
        except Exception:
            pass
        self.geometry("1100x960")
        self.minsize(900, 780)
        self.configure(fg_color=BG_MAIN)

        self._build_ui()
        self._init_data()
        self.after(500, self._schedule_refresh)
        # Poll for Ctrl+C via Windows API (works with any keyboard layout)
        self._start_copy_poll()

    # ── Build UI ──────────────────────────────────────────────────────────────

    def _build_ui(self):
        self._build_header()
        GoldSep(self).pack(fill="x")
        self._build_turn_bar()
        self._build_tab_bar()
        self._build_tab_area()
        self._build_footer()

    def _build_header(self):
        hdr = ctk.CTkFrame(self, fg_color="#141208", corner_radius=0, height=96)
        hdr.pack(fill="x")
        hdr.pack_propagate(False)

        # Left: version
        ctk.CTkLabel(hdr, text=f"v{APP_VERSION}",
            font=BA(12), text_color=GOLD_DIM).place(relx=0.0, rely=0.0, anchor="nw", x=12, y=8)

        # Right: clock + mode
        right = ctk.CTkFrame(hdr, fg_color="transparent")
        right.place(relx=1.0, rely=0.5, anchor="e", x=-24)
        self.time_label = ctk.CTkLabel(right, text="",
            font=BA(20, bold=True), text_color=GOLD_LIGHT)
        self.time_label.pack(anchor="e")
        self.mode_label = ctk.CTkLabel(right, text="",
            font=BA(15, bold=True), text_color=TEXT_MAIN)
        self.mode_label.pack(anchor="e", pady=(4, 0))

        # Centre: title
        centre = ctk.CTkFrame(hdr, fg_color="transparent")
        centre.place(relx=0.5, rely=0.5, anchor="center")
        ctk.CTkLabel(centre,
            text="CIVILIZATION  VII  LAG  MONITOR",
            font=("Georgia", 24, "bold"), text_color=GOLD).pack()
        ctk.CTkLabel(centre,
            text="from good old uncle Voltage",
            font=("Georgia", 18, "bold"), text_color=GOLD_LIGHT).pack(pady=(5, 0))

    def _build_turn_bar(self):
        self.turn_bar = ctk.CTkLabel(self,
            text="Waiting for game to start...",
            font=BA(17, bold=True), text_color=TEXT_MAIN, anchor="w")
        self.turn_bar.pack(fill="x", padx=22, pady=(12, 8))

    def _build_tab_bar(self):
        bar = ctk.CTkFrame(self, fg_color="#0e0c08", corner_radius=0, height=52)
        bar.pack(fill="x")
        bar.pack_propagate(False)

        self._tab_btns   = {}
        self._tab_frames = {}
        self._active_tab = None

        for name, icon in [("Players", "⚔"), ("Info", "ℹ")]:
            btn = ctk.CTkButton(bar,
                text=f"  {icon}   {name}  ",
                font=BA(16, bold=True),
                fg_color="#1e1a10",
                hover_color="#2e2810",
                text_color=TEXT_DIM,
                border_width=2,
                border_color=GOLD_DIM,
                corner_radius=5,
                height=38,
                command=lambda n=name: self._switch_tab(n))
            btn.pack(side="left", padx=(14, 4), pady=7)
            self._tab_btns[name] = btn

    def _build_tab_area(self):
        self._tab_area = ctk.CTkFrame(self, fg_color=BG_MAIN, corner_radius=0)
        self._tab_area.pack(fill="both", expand=True)
        self._build_players_frame()
        self._build_info_frame()
        self._switch_tab("Players")

    def _switch_tab(self, name):
        for n, f in self._tab_frames.items():
            f.pack_forget()
            self._tab_btns[n].configure(
                fg_color="#1e1a10", text_color=TEXT_DIM, border_color=GOLD_DIM)
        self._tab_frames[name].pack(fill="both", expand=True)
        self._tab_btns[name].configure(
            fg_color=GOLD, text_color="#1a1710", border_color=GOLD_LIGHT)
        self._active_tab = name

    def _build_players_frame(self):
        frame = ctk.CTkFrame(self._tab_area, fg_color=BG_MAIN, corner_radius=0)
        self._tab_frames["Players"] = frame

        self.cards_scroll = ctk.CTkScrollableFrame(frame,
            fg_color=BG_MAIN,
            scrollbar_button_color=GOLD_DIM,
            scrollbar_button_hover_color=GOLD)
        self.cards_scroll.pack(fill="both", expand=True, padx=8, pady=8)

        self.cards_frame = ctk.CTkFrame(self.cards_scroll, fg_color="transparent")
        self.cards_frame.pack(fill="both", expand=True)

        make_section_label(frame, "RECONNECT HISTORY")

        # Reconnect table header — tk.Text with tab stops for alignment
        self.recon_box = make_readonly_text(frame, 6)
        # Set tab stops: player=250px, time=150px, turn=100px
        self.recon_box.configure(tabs=("250", "400", "500"))
        self.recon_box.pack(fill="x", padx=12, pady=(0, 8))

    def _build_info_frame(self):
        frame = ctk.CTkFrame(self._tab_area, fg_color=BG_MAIN, corner_radius=0)
        self._tab_frames["Info"] = frame

        make_section_label(frame, "HARDWARE")
        self.hw_box = make_readonly_text(frame, 8)
        self.hw_box.pack(fill="x", padx=12, pady=(0, 4))

        make_section_label(frame, "MY DIAGNOSTICS")
        self.diag_box = make_readonly_text(frame, 10)
        self.diag_box.pack(fill="x", padx=12, pady=(0, 4))

    def _build_footer(self):
        foot = ctk.CTkFrame(self, fg_color="#0e0c08", corner_radius=0, height=52)
        foot.pack(fill="x", side="bottom")
        foot.pack_propagate(False)

        self.save_label = ctk.CTkLabel(foot, text="",
            font=BA(13), text_color="#6aad6a")
        self.save_label.pack(side="right", padx=14)

        ctk.CTkButton(foot, text="💾   Save Report",
            width=190, height=36,
            font=BA(15, bold=True),
            fg_color=GOLD, hover_color=GOLD_LIGHT,
            text_color="#1a1710",
            command=self._save_report).pack(side="right", padx=10, pady=8)

        # Centre: drafter.games link
        link = tk.Label(foot, text="drafter.games",
            font=("Georgia", 13, "bold", "underline"),
            fg=GOLD_DIM, bg="#0e0c08", cursor="hand2")
        link.place(relx=0.5, rely=0.5, anchor="center")
        link.bind("<Button-1>", open_drafter_url)
        link.bind("<Enter>",    lambda e: link.configure(fg=GOLD_LIGHT))
        link.bind("<Leave>",    lambda e: link.configure(fg=GOLD_DIM))

    # ── Data & refresh ────────────────────────────────────────────────────────

    def _start_copy_poll(self):
        """On macOS, Cmd+C works natively in tk widgets.
        This method binds Cmd+C globally to copy selected readonly text."""
        def _on_copy(event=None):
            try:
                text = _READONLY_LAST_SEL[0]
                if text and HAS_PYPERCLIP:
                    pyperclip.copy(text)
            except Exception:
                pass
        self.bind_all("<Command-c>", _on_copy)

    def _init_data(self):
        self.diag_hw, self.diag_status, self.diag_warn = run_self_diagnostics()
        self._check_version()
        self._refresh_info_tab()

    def _check_version(self):
        import threading
        def _fetch():
            latest = check_latest_version()
            if latest and latest != APP_VERSION:
                self.after(0, lambda: self._show_update_popup(latest))
        threading.Thread(target=_fetch, daemon=True).start()

    def _show_update_popup(self, latest_version):
        popup = tk.Toplevel(self)
        popup.title("Update Available")
        popup.configure(bg=BG_MAIN)
        popup.resizable(False, False)
        popup.grab_set()  # block interaction with main window
        popup.lift()
        popup.focus_force()

        # Centre popup on main window
        self.update_idletasks()
        w, h = 480, 200
        x = self.winfo_x() + (self.winfo_width()  - w) // 2
        y = self.winfo_y() + (self.winfo_height() - h) // 2
        popup.geometry(f"{w}x{h}+{x}+{y}")

        # Gold separator top
        tk.Frame(popup, bg=GOLD_DIM, height=2).pack(fill="x")

        # Message frame
        msg_frame = tk.Frame(popup, bg=BG_MAIN)
        msg_frame.pack(fill="both", expand=True, padx=24, pady=(20, 10))

        tk.Label(msg_frame,
            text=f"New version v{latest_version} has been released!",
            font=("Georgia", 14, "bold"),
            fg=GOLD_LIGHT, bg=BG_MAIN).pack(anchor="w", pady=(0, 8))

        tk.Label(msg_frame,
            text="Your current data may be incorrect.",
            font=("Georgia", 12),
            fg=TEXT_MAIN, bg=BG_MAIN).pack(anchor="w")

        # "Go to [drafter.games] to download..." with clickable link
        link_frame = tk.Frame(msg_frame, bg=BG_MAIN)
        link_frame.pack(anchor="w", pady=(4, 0))

        tk.Label(link_frame, text="Go to ",
            font=("Georgia", 12), fg=TEXT_MAIN, bg=BG_MAIN).pack(side="left")

        link = tk.Label(link_frame, text="drafter.games",
            font=("Georgia", 12, "underline"),
            fg=GOLD, bg=BG_MAIN, cursor="hand2")
        link.pack(side="left")
        link.bind("<Button-1>", open_drafter_url)
        link.bind("<Enter>",    lambda e: link.configure(fg=GOLD_LIGHT))
        link.bind("<Leave>",    lambda e: link.configure(fg=GOLD))

        tk.Label(link_frame, text=" to download the latest version.",
            font=("Georgia", 12), fg=TEXT_MAIN, bg=BG_MAIN).pack(side="left")

        # Gold separator + OK button
        tk.Frame(popup, bg=GOLD_DIM, height=1).pack(fill="x", pady=(8, 0))

        btn_frame = tk.Frame(popup, bg="#0e0c08")
        btn_frame.pack(fill="x", pady=0)

        ctk.CTkButton(btn_frame, text="OK", width=100, height=34,
            font=BA(14, bold=True),
            fg_color=GOLD, hover_color=GOLD_LIGHT,
            text_color="#1a1710",
            command=popup.destroy).pack(pady=10)

    def _schedule_refresh(self):
        self._read_log()
        self._update_ui()
        self.after(3000, self._schedule_refresh)

    def _read_log(self):
        try:
            with open(self.log_path, 'rb') as f:
                f.seek(self.file_pos)
                raw = f.read()
                self.file_pos = f.tell()
            if raw:
                for line in raw.decode('utf-8', errors='replace').splitlines(keepends=True):
                    process_net_line(line, self.gs)
        except Exception as e:
            self.gs._last_error = str(e)
        if (datetime.now() - self._last_diag).total_seconds() > 30:
            hw_new, self.diag_status, self.diag_warn = run_self_diagnostics()
            # Re-apply hw only when OS was Unknown or power plan changed
            if hw_new:
                old_os = next((l for l in self.diag_hw if l.startswith("OS:")), None)
                new_os = next((l for l in hw_new if l.startswith("OS:")), None)
                if old_os == "OS: Unknown" or old_os != new_os:
                    self.diag_hw = hw_new
            self._last_diag = datetime.now()
            self._refresh_info_tab()

    def _update_ui(self):
        s = self.gs
        self.time_label.configure(text=datetime.now().strftime("%H:%M:%S"))
        self.mode_label.configure(
            text="HOST MODE" if s.is_host else "PLAYER MODE")

        if not s.players:
            msg = ("⚠  " + s._last_error) if getattr(s, '_last_error', '') else \
                  "Waiting for game to start..."
            self.turn_bar.configure(text=msg)
            self._clear_cards()
            return

        turn_text = f"Turn:  {s.current_turn}"
        if s.sync_times:
            avg_s  = sum(s.sync_times) / len(s.sync_times)
            recent = "   ".join(f"{t:.1f}s" for t in s.sync_times[-3:])
            turn_text += f"     Sync avg:  {avg_s:.1f}s     Recent:  {recent}"
        self.turn_bar.configure(text=turn_text)

        dupes    = calc_dupes(s)
        sorted_p = sorted(s.players.items(),
                          key=lambda x: self._risk_score(x[0], s, dupes),
                          reverse=True)

        if s.is_host:
            self._update_cards(sorted_p, s, dupes)
        else:
            self._clear_cards()
            iid = s.self_iid
            if iid is not None and iid in s.players:
                oos  = s.oos_count.get(iid, 0)
                _, dpt = dupes.get(iid, (0, 0.0))
                recon  = s.reconnects.get(iid, 0)
                snap   = s.snapshot_fail.get(iid, 0)
                risk   = risk_label(oos, dpt, recon)
                card   = self._get_card(iid)
                card.update_card(s.players[iid], oos, dpt, recon, snap, risk,
                                 is_self=True)
                card.grid(row=0, column=0, padx=8, pady=6, sticky="nsew")

        # Reconnect history — fixed-width columns
        recon_lines = []
        for iid, name in sorted_p:
            log = s.reconnect_log[iid]
            if not log:
                continue
            for ts, tn in log[-5:]:
                recon_lines.append(
                    f"  {name}\t{ts}\t{tn}")
        header = "  PLAYER\tTIME\tTURN"
        body = "\n".join(recon_lines) if recon_lines else "  No reconnects this session"
        self.recon_box.delete("1.0", "end")
        self.recon_box.insert("1.0", header + "\n")
        self.recon_box.tag_config("hdr", foreground=GOLD_LIGHT, font=MONO(FS - 1, bold=True))
        self.recon_box.tag_add("hdr", "1.0", "1.end")
        self.recon_box.insert("end", body)

    def _refresh_info_tab(self):
        hw_lines = [f"  {h}" for h in self.diag_hw] if self.diag_hw else ["  No hardware data"]
        self.hw_box.configure(height=len(hw_lines) + 1)
        # Colour only the icon (chars 2-4 of each line)
        hw_rules = [
            ("✅", "#6aad6a"), ("🟢", "#6aad6a"),
            ("🟡", "#d4983a"),
            ("🔴", "#e05050"),
        ]
        set_readonly_text(self.hw_box, "\n".join(hw_lines), hw_rules)

        d_lines = [f"  {s}" for s in self.diag_status]
        if self.diag_warn:
            d_lines.append("")
            d_lines += [f"  {w}" for w in self.diag_warn]
        else:
            d_lines.append("  ✅ No stability issues detected")
        diag_rules = [
            ("🟢", "#6aad6a"), ("✅", "#6aad6a"),
            ("🟡", "#d4983a"), ("⚠",  "#d4983a"),
            ("🔴", "#e05050"), ("💥", "#e05050"),
        ]
        set_readonly_text(self.diag_box, "\n".join(d_lines), diag_rules)

    def _risk_score(self, iid, s, dupes):
        oos        = s.oos_count.get(iid, 0)
        _, dpt     = dupes.get(iid, (0, 0.0))
        recon      = s.reconnects.get(iid, 0)
        score = 0
        if oos > 50:      score += 3
        elif oos > 10:    score += 2
        elif oos > 3:     score += 1
        if dpt > 1.0:     score += 3
        elif dpt > 0.7:   score += 2
        elif dpt > 0.4:   score += 1
        if recon > 15:    score += 3
        elif recon > 10:  score += 2
        elif recon > 5:   score += 1
        return score

    def _get_card(self, iid):
        if iid not in self._cards:
            self._cards[iid] = PlayerCard(self.cards_frame)
        return self._cards[iid]

    def _clear_cards(self):
        for card in self._cards.values():
            card.grid_forget()

    def _update_cards(self, sorted_p, s, dupes):
        self._clear_cards()
        cols = 4
        for idx, (iid, name) in enumerate(sorted_p):
            oos        = s.oos_count.get(iid, 0)
            _, dpt     = dupes.get(iid, (0, 0.0))
            recon      = s.reconnects.get(iid, 0)
            snap       = s.snapshot_fail.get(iid, 0)
            risk       = risk_label(oos, dpt, recon)
            is_self    = (iid == s.self_iid)
            is_host_p  = (iid == 0 and not s.is_host)
            card       = self._get_card(iid)
            card.update_card(name, oos, dpt, recon, snap, risk,
                             is_self=is_self, is_host_player=is_host_p)
            row, col = divmod(idx, cols)
            card.grid(row=row, column=col, padx=8, pady=6, sticky="nsew")
        for c in range(cols):
            self.cards_frame.grid_columnconfigure(c, weight=1)

    def _save_report(self):
        path = save_report(self.gs, self.diag_hw, self.diag_status,
                           self.diag_warn, self.log_path)
        msg = f"✅  {os.path.basename(path)}" if path else "❌  Save failed"
        self.save_label.configure(text=msg)
        self.after(5000, lambda: self.save_label.configure(text=""))


# ── Main ──────────────────────────────────────────────────────────────────────

def main():
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('--log', type=str, default=LOG_NET)
    args = parser.parse_args()
    log_path = args.log

    if not os.path.exists(log_path):
        root = ctk.CTk()
        root.title("Civ7 Monitor")
        root.geometry("520x170")
        root.configure(fg_color=BG_MAIN)
        ctk.CTkLabel(root,
            text=f"Log file not found:\n{log_path}\n\nLaunch Civ7 first.",
            font=BA(14), text_color=TEXT_MAIN).pack(expand=True, pady=20)
        ctk.CTkButton(root, text="Exit",
            fg_color=GOLD_DIM, hover_color=GOLD, text_color="#1a1710",
            command=root.destroy).pack(pady=8)
        root.mainloop()
        sys.exit(1)

    app = App(log_path)
    app.mainloop()

if __name__ == "__main__":
    main()
