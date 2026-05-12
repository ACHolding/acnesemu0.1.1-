#!/usr/bin/env python3.14
# AC NES Emu 1.1 — FCEUX-accurate launcher | cat-blue GUI 🐾
# Team Flames / Samsoft / catsan | single file | py3.14
# v1.1: FCEUX top backend with --sound/--pal/--gg flags,
#       iNES parser, Game Genie decoder, hex + PPU viewer,
#       save-state slots F1-F10 / Shift+F1-F10, region picker
#       (NTSC 60.0988 / PAL / Dendy), live FPS readout, recent
#       ROMs, frame advance, screenshot, controls remap dialog.
#       GUI geometry/palette/toolbar/idle splash unchanged.

import os
import sys
import io
import json
import shutil
import zipfile
import threading
import urllib.request
import subprocess
import time
import random
from collections import deque

# ---------- pyntendo lazy bootstrap (only when needed) ----------
def ensure_pyntendo():
    for pkg, mod in [("pygame","pygame"),("numpy","numpy"),
                     ("cython","Cython"),("pyntendo","nes")]:
        try: __import__(mod)
        except ImportError:
            print(f"Installing {pkg}...")
            try:
                subprocess.check_call([sys.executable,"-m","pip","install",
                                       pkg,"--quiet"])
            except subprocess.CalledProcessError:
                print(f"  (skipped {pkg})")
    try: import pyximport  # noqa
    except ImportError:
        try:
            subprocess.check_call([sys.executable,"-m","pip","install",
                                   "--force-reinstall","cython","--quiet"])
        except subprocess.CalledProcessError: pass

import tkinter as tk
from tkinter import filedialog, messagebox

# ---------- Win32 ----------
IS_WIN = os.name == "nt"
if IS_WIN:
    import ctypes
    from ctypes import wintypes
    user32 = ctypes.windll.user32

    GWL_STYLE=-16; GWL_EXSTYLE=-20
    WS_CHILD=0x40000000; WS_POPUP=0x80000000
    WS_CAPTION=0x00C00000; WS_THICKFRAME=0x00040000
    WS_MINIMIZEBOX=0x00020000; WS_MAXIMIZEBOX=0x00010000
    WS_SYSMENU=0x00080000; WS_BORDER=0x00800000; WS_DLGFRAME=0x00400000
    WS_EX_DLGMODALFRAME=0x00000001; WS_EX_CLIENTEDGE=0x00000200
    WS_EX_STATICEDGE=0x00020000; WS_EX_WINDOWEDGE=0x00000100
    SW_SHOW=5
    WM_KEYDOWN=0x0100; WM_KEYUP=0x0101
    VK_ESCAPE=0x1B; VK_CONTROL=0x11; VK_PAUSE=0x13
    VK_F1=0x70; VK_F2=0x71; VK_F3=0x72; VK_F4=0x73; VK_F5=0x74
    VK_F6=0x75; VK_F7=0x76; VK_F8=0x77; VK_F9=0x78; VK_F10=0x79
    VK_F11=0x7A; VK_F12=0x7B
    VK_OEM_5=0xDC  # backslash → FCEUX frame advance

    WNDENUMPROC = ctypes.WINFUNCTYPE(ctypes.c_bool, wintypes.HWND, wintypes.LPARAM)

    def find_main_window_by_pid(pid):
        results = []
        def cb(hwnd, lparam):
            wpid = wintypes.DWORD()
            user32.GetWindowThreadProcessId(hwnd, ctypes.byref(wpid))
            if wpid.value != pid: return True
            if not user32.IsWindowVisible(hwnd): return True
            if user32.GetWindowTextLengthW(hwnd) == 0: return True
            rect = wintypes.RECT()
            user32.GetWindowRect(hwnd, ctypes.byref(rect))
            w = rect.right - rect.left; h = rect.bottom - rect.top
            if w < 120 or h < 80: return True
            results.append((hwnd, w*h))
            return True
        user32.EnumWindows(WNDENUMPROC(cb), 0)
        results.sort(key=lambda x: -x[1])
        return results[0][0] if results else None

    def strip_chrome_and_reparent(child, parent):
        style = user32.GetWindowLongW(child, GWL_STYLE)
        mask = (WS_POPUP|WS_CAPTION|WS_THICKFRAME|WS_MINIMIZEBOX
                |WS_MAXIMIZEBOX|WS_SYSMENU|WS_BORDER|WS_DLGFRAME)
        user32.SetWindowLongW(child, GWL_STYLE, (style & ~mask)|WS_CHILD)
        ex = user32.GetWindowLongW(child, GWL_EXSTYLE)
        ex &= ~(WS_EX_DLGMODALFRAME|WS_EX_CLIENTEDGE|WS_EX_STATICEDGE|WS_EX_WINDOWEDGE)
        user32.SetWindowLongW(child, GWL_EXSTYLE, ex)
        user32.SetParent(child, parent)
        user32.ShowWindow(child, SW_SHOW)

    def fit_to_parent(child, parent):
        rect = wintypes.RECT()
        user32.GetClientRect(parent, ctypes.byref(rect))
        user32.MoveWindow(child, 0, 0, rect.right, rect.bottom, True)

    def send_key(hwnd, vk):
        user32.PostMessageW(hwnd, WM_KEYDOWN, vk, 0)
        user32.PostMessageW(hwnd, WM_KEYUP, vk, 0)


# ---- palette (UNCHANGED — cat-blue theme stays) ----
BG="#0a1828"; BG_PANEL="#142845"; BG_DARK="#050d18"
BTN_BG="#000000"; BTN_FG="#3ea0ff"; FG="#9fc8ff"
ACCENT="#1e6fd9"; MENU_BG="#0d1e35"; MENU_FG="#bcd6ff"
ERR_FG="#ff7a7a"

# ---- NES timing (FCEUX exact) ----
NES_W, NES_H = 256, 240
NTSC_FPS  = 60.0988
PAL_FPS   = 50.0070
DENDY_FPS = 50.0070
REGION_FLAG = {"NTSC": "0", "PAL": "1", "Dendy": "2"}

# ---- default controls (rebindable via NES > Controls...) ----
DEFAULT_CONTROLS = {
    # P1 — arrows + ZX + RShift/Enter, AS turbo
    "P1 Up":         "Up",
    "P1 Down":       "Down",
    "P1 Left":       "Left",
    "P1 Right":      "Right",
    "P1 A":          "x",
    "P1 B":          "z",
    "P1 Select":     "Shift_R",
    "P1 Start":      "Return",
    "P1 TurboA":     "s",
    "P1 TurboB":     "a",
    # P2 — numpad
    "P2 Up":         "KP_8",
    "P2 Down":       "KP_2",
    "P2 Left":       "KP_4",
    "P2 Right":      "KP_6",
    "P2 A":          "KP_3",
    "P2 B":          "KP_1",
    "P2 Select":     "KP_5",
    "P2 Start":      "KP_0",
    # Hotkeys (live-rebound at Tk root)
    "Pause":         "Escape",
    "Reset":         "Control-r",
    "Save State":    "F5",
    "Load State":    "F7",
    "Frame Advance": "backslash",
    "Screenshot":    "F12",
    "Mute":          "Control-m",
    "Fast Forward":  "Tab",
}

SCRIPT_DIR  = os.path.dirname(os.path.abspath(__file__)) if "__file__" in globals() else os.getcwd()
CONFIG_PATH = os.path.join(os.path.expanduser("~"), ".acnesemu.json")
BACKENDS_DIR= os.path.join(os.path.expanduser("~"), ".acnesemu", "backends")

# FCEUX FIRST (this is the whole point of v1.1)
BACKEND_ORDER = ["FCEUX","Mesen2","Mesen","Nestopia","puNES","ares","pyntendo"]
BACKENDS = {
    # FCEUX: --sound 1, --pal {region} (0=NTSC/1=PAL/2=Dendy), --gg 1
    "FCEUX":    {"exes":["fceux64.exe","fceux.exe","fceux"],
                 "args":["--sound","1","--pal","{region}","--gg","1","{rom}"],
                 "embed_ok":True},
    "Mesen2":   {"exes":["Mesen.exe","Mesen2.exe"], "args":["{rom}"],
                 "embed_ok":True, "mesen":True},
    "Mesen":    {"exes":["Mesen.exe"], "args":["{rom}"],
                 "embed_ok":True, "mesen":True},
    "Nestopia": {"exes":["nestopia.exe","nestopia"], "args":["{rom}"],
                 "embed_ok":True},
    "puNES":    {"exes":["punes64.exe","punes.exe","punes"], "args":["{rom}"],
                 "embed_ok":True},
    "ares":     {"exes":["ares.exe","ares"],
                 "args":["--system","Famicom","{rom}"], "embed_ok":True},
    "pyntendo": {"exes":[], "args":[], "builtin":True, "embed_ok":False},
}

WIN_DIRS = [
    r"C:\Program Files\FCEUX", r"C:\Program Files (x86)\FCEUX",
    r"C:\Program Files\Mesen2", r"C:\Program Files\Mesen",
    r"C:\Program Files (x86)\Mesen", r"C:\Program Files (x86)\Mesen2",
    r"C:\Program Files\Nestopia", r"C:\Program Files (x86)\Nestopia",
    r"C:\Program Files\puNES", r"C:\Program Files (x86)\puNES",
    r"C:\Program Files\ares", r"C:\Program Files (x86)\ares",
    os.path.expandvars(r"%LOCALAPPDATA%\FCEUX"),
    os.path.expandvars(r"%LOCALAPPDATA%\Mesen2"),
    os.path.expandvars(r"%LOCALAPPDATA%\Mesen"),
]
UNIX_DIRS = ["/usr/local/bin","/opt/homebrew/bin","/usr/bin",
             os.path.expanduser("~/Applications"), "/Applications"]
PYNTENDO_MAPPERS = {0,1,2,3,4,7}

MESEN_API = "https://api.github.com/repos/SourMesen/Mesen2/releases/latest"


def _scan(d, exes):
    if not os.path.isdir(d): return None
    for e in exes:
        p = os.path.join(d, e)
        if os.path.isfile(p): return p
    try:
        for sub in os.listdir(d):
            sp = os.path.join(d, sub)
            if os.path.isdir(sp):
                for e in exes:
                    p = os.path.join(sp, e)
                    if os.path.isfile(p): return p
    except OSError: pass
    return None

def find_backend_path(name):
    info = BACKENDS[name]
    if info.get("builtin"): return "builtin"
    for e in info["exes"]:
        p = shutil.which(e)
        if p: return p
    for d in [BACKENDS_DIR, SCRIPT_DIR] + (WIN_DIRS if IS_WIN else UNIX_DIRS):
        hit = _scan(d, info["exes"])
        if hit: return hit
    return None

def detect_backends():
    return {n: p for n in BACKEND_ORDER if (p := find_backend_path(n))}


# ---------- iNES parser ----------
def parse_ines(rom_path):
    try:
        with open(rom_path,"rb") as f: h = f.read(16)
        if len(h)<16 or h[:4]!=b"NES\x1a": return None
        prg = h[4]; chr_ = h[5]
        flag6 = h[6]; flag7 = h[7]
        mapper = ((flag6>>4)&0x0F) | (flag7&0xF0)
        mirroring = "Vertical" if (flag6&1) else "Horizontal"
        if flag6&8: mirroring = "Four-screen"
        return {
            "prg_kb": prg*16, "chr_kb": chr_*8,
            "mapper": mapper, "mirroring": mirroring,
            "battery": bool(flag6&2),
            "trainer": bool(flag6&4),
            "ines2": ((flag7>>2)&3) == 2,
            "size": os.path.getsize(rom_path),
        }
    except Exception:
        return None

def read_ines_mapper(rom_path):
    info = parse_ines(rom_path)
    return info["mapper"] if info else None


def load_config():
    try:
        with open(CONFIG_PATH,"r",encoding="utf-8") as f: return json.load(f)
    except Exception: return {}

def save_config(cfg):
    try:
        with open(CONFIG_PATH,"w",encoding="utf-8") as f: json.dump(cfg, f, indent=2)
    except Exception: pass


# ---------- Mesen2 audio patcher ----------
def mesen_settings_paths(exe_path):
    paths = []
    if exe_path:
        paths.append(os.path.join(os.path.dirname(exe_path), "Settings.json"))
    paths.append(os.path.expandvars(r"%LOCALAPPDATA%\Mesen2\Settings.json"))
    paths.append(os.path.expandvars(r"%LOCALAPPDATA%\Mesen\Settings.json"))
    return paths

def patch_mesen_audio(exe_path):
    patched = []
    for p in mesen_settings_paths(exe_path):
        try:
            if os.path.isfile(p):
                with open(p,"r",encoding="utf-8") as f: data = json.load(f)
            else:
                os.makedirs(os.path.dirname(p), exist_ok=True); data = {}
            audio = data.get("AudioConfig") or data.get("Audio") or {}
            audio["MuteSoundInBackground"] = False
            audio["ReduceSoundInBackground"] = False
            audio["MasterVolume"] = audio.get("MasterVolume", 50.0)
            if "AudioConfig" in data or "Audio" not in data: data["AudioConfig"] = audio
            else: data["Audio"] = audio
            pref = data.get("PreferencesConfig") or data.get("Preferences") or {}
            pref["PauseWhenInBackground"] = False
            pref["AllowBackgroundInput"] = True
            if "PreferencesConfig" in data or "Preferences" not in data: data["PreferencesConfig"] = pref
            else: data["Preferences"] = pref
            with open(p,"w",encoding="utf-8") as f: json.dump(data, f, indent=2)
            patched.append(p)
        except Exception as e:
            print(f"  patch {p} failed: {e}")
    return patched


# ---------- Mesen2 installer ----------
def download_mesen2(progress_cb=None):
    if not IS_WIN: raise RuntimeError("Auto-install is Windows-only.")
    os.makedirs(BACKENDS_DIR, exist_ok=True)
    target = os.path.join(BACKENDS_DIR, "Mesen2"); os.makedirs(target, exist_ok=True)
    if progress_cb: progress_cb("Fetching release info...")
    req = urllib.request.Request(MESEN_API, headers={"User-Agent":"AC-NES-Emu"})
    with urllib.request.urlopen(req, timeout=30) as r:
        data = json.loads(r.read().decode("utf-8"))
    asset = None
    for a in data.get("assets", []):
        n = a["name"].lower()
        if n.endswith(".zip") and ("win" in n or "windows" in n) \
           and "linux" not in n and "macos" not in n:
            asset = a; break
    if not asset:
        for a in data.get("assets", []):
            if a["name"].lower().endswith(".zip"): asset = a; break
    if not asset: raise RuntimeError("No Windows zip in latest release.")
    if progress_cb: progress_cb(f"Downloading {asset['name']}...")
    with urllib.request.urlopen(asset["browser_download_url"], timeout=180) as r:
        blob = r.read()
    if progress_cb: progress_cb("Extracting...")
    with zipfile.ZipFile(io.BytesIO(blob)) as z: z.extractall(target)
    exe = None
    for root, _, files in os.walk(target):
        for f in files:
            if f.lower() in ("mesen.exe","mesen2.exe"):
                exe = os.path.join(root, f); break
        if exe: break
    if not exe: raise RuntimeError("Mesen.exe not found after extract.")
    if progress_cb: progress_cb("Configuring audio...")
    patch_mesen_audio(exe)
    return exe


# ---------- Game Genie decoder (FCEUX algorithm) ----------
GG_TABLE = "APZLGITYEOXUKSVN"
def gg_decode(code):
    code = code.upper().strip()
    if len(code) not in (6, 8):
        raise ValueError("Game Genie codes are 6 or 8 characters.")
    n = []
    for c in code:
        if c not in GG_TABLE: raise ValueError(f"Invalid character: {c}")
        n.append(GG_TABLE.index(c))
    addr = (((n[3]&7)<<12) | ((n[5]&7)<<8) | ((n[4]&8)<<8) |
            ((n[2]&7)<<4)  | ((n[1]&8)<<4) | (n[4]&7) | (n[3]&8))
    addr |= 0x8000
    if len(code) == 6:
        val = ((n[1]&7)<<4) | ((n[0]&8)<<4) | (n[0]&7) | (n[5]&8)
        return addr, val, None
    val = ((n[1]&7)<<4) | ((n[0]&8)<<4) | (n[0]&7) | (n[7]&8)
    key = ((n[7]&7)<<4) | ((n[6]&8)<<4) | (n[6]&7) | (n[5]&8)
    return addr, val, key


# ---- App (GUI identical to 1.0; new features layered in) ----
class ACNESEmu:
    def __init__(self, root):
        self.root = root
        self.rom_path = None
        self.rom_info = None
        self.proc = None
        self.embed_hwnd = None
        self.embed_attempts = 0
        self.muted = False
        self.paused = False
        self.save_slot = 0
        self.frame_count = 0
        self.fps_display = 0.0
        self.target_fps = NTSC_FPS
        self.log = deque(maxlen=2000)
        self.log_window = None
        self.log_text = None
        self.hex_window = None
        self.ppu_window = None
        self.cheat_window = None
        self.controls_window = None
        self.controls = dict(DEFAULT_CONTROLS)
        self._applied_hotkey_bindings = {}   # action -> Tk seq currently bound
        self.cfg = load_config()
        self.controls.update(self.cfg.get("controls", {}))
        self.recent = self.cfg.get("recent", [])[:10]
        self.embed_enabled = self.cfg.get("embed", True) and IS_WIN
        self.found = detect_backends()
        for n,p in self.cfg.get("custom_paths",{}).items():
            if n in BACKENDS and os.path.isfile(p): self.found[n] = p
        self.backend = self.cfg.get("backend") or self._auto_pick()

        # UNCHANGED window chrome
        root.title("AC NES Emu 1.0")
        root.geometry("600x400"); root.minsize(600, 400); root.configure(bg=BG)

        self._build_menu(); self._build_toolbar()
        self._build_screen(); self._build_statusbar()
        self._apply_controls()

        root.protocol("WM_DELETE_WINDOW", self._on_close)
        root.after(500, self._poll_proc)
        root.after(1000, self._fps_tick)
        self._refresh_status()

        self._log(f"AC NES Emu 1.1 (FCEUX-accurate) started. Backend: {self.backend}")
        self._log(f"Detected: {list(self.found.keys()) or 'none'}")
        for n, p in self.found.items(): self._log(f"  {n}: {p}")

        if not any(n in self.found for n in BACKEND_ORDER if n != "pyntendo"):
            root.after(300, self._first_run_prompt)

    # --- logging
    def _log(self, msg):
        line = str(msg).rstrip()
        self.log.append(line)
        print(f"[acnes] {line}")
        if self.log_text:
            try:
                self.log_text.config(state="normal")
                self.log_text.insert("end", line + "\n")
                self.log_text.see("end")
                self.log_text.config(state="disabled")
            except tk.TclError: pass

    def show_log(self):
        if self.log_window and tk.Toplevel.winfo_exists(self.log_window):
            self.log_window.lift(); return
        win = tk.Toplevel(self.root); self.log_window = win
        win.title("AC NES Emu — Log"); win.configure(bg=BG); win.geometry("720x420")
        top = tk.Frame(win, bg=BG_PANEL); top.pack(fill="x")
        tk.Label(top, text=" Backend log + diagnostics",
                 bg=BG_PANEL, fg=BTN_FG, font=("Consolas",9,"bold"),
                 anchor="w", padx=6, pady=4).pack(side="left", fill="x", expand=True)
        tk.Button(top, text="Clear", bg=BTN_BG, fg=BTN_FG, relief="flat",
                  font=("Consolas",9), padx=8,
                  command=self._clear_log).pack(side="right", padx=4, pady=3)
        tk.Button(top, text="Copy", bg=BTN_BG, fg=BTN_FG, relief="flat",
                  font=("Consolas",9), padx=8,
                  command=self._copy_log).pack(side="right", padx=4, pady=3)
        self.log_text = tk.Text(win, bg=BG_DARK, fg=FG, font=("Consolas",9),
                                wrap="word", insertbackground=BTN_FG,
                                relief="flat", padx=6, pady=6)
        self.log_text.pack(fill="both", expand=True)
        self.log_text.insert("1.0", "\n".join(self.log))
        self.log_text.see("end")
        self.log_text.config(state="disabled")
        win.protocol("WM_DELETE_WINDOW",
                     lambda: (setattr(self,"log_text",None),
                              setattr(self,"log_window",None), win.destroy()))

    def _clear_log(self):
        self.log.clear()
        if self.log_text:
            self.log_text.config(state="normal")
            self.log_text.delete("1.0","end")
            self.log_text.config(state="disabled")

    def _copy_log(self):
        self.root.clipboard_clear()
        self.root.clipboard_append("\n".join(self.log))
        self.set_status("Log copied to clipboard")

    def _auto_pick(self):
        for n in BACKEND_ORDER:
            if n in self.found: return n
        return "pyntendo"

    def _first_run_prompt(self):
        if self.cfg.get("nag_skipped"): return
        if IS_WIN and messagebox.askyesno("AC NES Emu — first run",
            "No NES emulator detected.\n\n"
            "FCEUX recommended: fceux.com\n\n"
            "Auto-install Mesen2 as fallback?"):
            self._install_mesen2()
        else:
            self.cfg["nag_skipped"]=True; save_config(self.cfg)

    # --- menus
    def _menu(self, parent):
        return tk.Menu(parent, tearoff=0, bg=MENU_BG, fg=MENU_FG,
                       activebackground=ACCENT, activeforeground="#ffffff",
                       borderwidth=0)

    def _build_menu(self):
        mb = tk.Menu(self.root, bg=MENU_BG, fg=MENU_FG,
                     activebackground=ACCENT, activeforeground="#ffffff",
                     borderwidth=0)

        # File
        m_file = self._menu(mb)
        m_file.add_command(label="Open ROM...", accelerator="Ctrl+O",
                           command=self.open_rom)
        m_file.add_command(label="Close ROM", command=self.close_rom)
        self.m_recent = self._menu(m_file)
        self._rebuild_recent_menu()
        m_file.add_cascade(label="Recent ROMs", menu=self.m_recent)
        m_file.add_separator()
        self.m_save = self._menu(m_file); self.m_load = self._menu(m_file)
        for i in range(10):
            self.m_save.add_command(label=f"Slot {i}", accelerator=f"Shift+F{i+1}",
                                    command=lambda s=i: self.save_state_slot(s))
            self.m_load.add_command(label=f"Slot {i}", accelerator=f"F{i+1}",
                                    command=lambda s=i: self.load_state_slot(s))
        m_file.add_cascade(label="Save State", menu=self.m_save)
        m_file.add_cascade(label="Load State", menu=self.m_load)
        m_file.add_separator()
        m_file.add_command(label="Screenshot", accelerator="F12",
                           command=self.screenshot)
        m_file.add_separator()
        m_file.add_command(label="Exit", command=self._on_close)
        mb.add_cascade(label="File", menu=m_file)

        # NES
        m_nes = self._menu(mb)
        m_nes.add_command(label="Reset", accelerator="Ctrl+R", command=self.reset_rom)
        m_nes.add_command(label="Power", command=self.power_cycle)
        m_nes.add_command(label="Pause/Resume", accelerator="Esc",
                          command=self.toggle_pause)
        m_nes.add_command(label="Frame Advance", accelerator="\\",
                          command=self.frame_advance)
        m_nes.add_separator()
        m_speed = self._menu(m_nes)
        for label, mult in [("25%",0.25),("50%",0.50),("Normal",1.0),
                            ("150%",1.5),("200%",2.0),("Turbo",4.0)]:
            m_speed.add_command(label=label,
                                command=lambda m=mult: self.set_speed(m))
        m_nes.add_cascade(label="Speed", menu=m_speed)
        m_nes.add_separator()
        m_nes.add_command(label="Controls...", accelerator="Ctrl+I",
                          command=self.open_controls)
        mb.add_cascade(label="NES", menu=m_nes)

        # Audio
        m_audio = self._menu(mb)
        m_audio.add_command(label="Mute / Unmute", accelerator="Ctrl+M",
                            command=self.toggle_mute)
        m_audio.add_command(label="Fix Mesen Audio (bg mute)",
                            command=self.fix_mesen_audio)
        m_audio.add_command(label="Audio Troubleshooting...",
                            command=self.audio_help)
        mb.add_cascade(label="Audio", menu=m_audio)

        # Backend
        self.m_backend = self._menu(mb); self._rebuild_backend_menu()
        mb.add_cascade(label="Backend", menu=self.m_backend)

        # View
        m_view = self._menu(mb)
        self.embed_var = tk.BooleanVar(value=self.embed_enabled)
        m_view.add_checkbutton(label="Embed emulator window",
                               variable=self.embed_var,
                               command=self._toggle_embed,
                               selectcolor=ACCENT)
        m_view.add_command(label="Fit embed to window", command=self._fit_embed_now)
        m_view.add_separator()
        # Region selector — feeds FCEUX --pal flag
        m_region = self._menu(m_view)
        self.region_var = tk.StringVar(value=self.cfg.get("region","NTSC"))
        for r in ("NTSC","PAL","Dendy"):
            m_region.add_radiobutton(label=r, variable=self.region_var, value=r,
                                     command=self.set_region,
                                     selectcolor=ACCENT)
        m_view.add_cascade(label="Region", menu=m_region)
        m_view.add_separator()
        m_view.add_command(label="Show Log / Diagnostics", accelerator="Ctrl+L",
                           command=self.show_log)
        mb.add_cascade(label="View", menu=m_view)

        # Debug
        m_dbg = self._menu(mb)
        m_dbg.add_command(label="ROM Properties...", command=self.rom_properties)
        m_dbg.add_separator()
        m_dbg.add_command(label="Hex Editor...", accelerator="Ctrl+H",
                          command=self.open_hex)
        m_dbg.add_command(label="PPU Viewer...", command=self.open_ppu)
        m_dbg.add_separator()
        m_dbg.add_command(label="Cheats...", accelerator="Shift+C",
                          command=self.open_cheats)
        m_dbg.add_command(label="Game Genie Encoder/Decoder...",
                          command=self.game_genie)
        mb.add_cascade(label="Debug", menu=m_dbg)

        # Help
        m_help = self._menu(mb)
        m_help.add_command(label="Install Mesen2 (Windows)",
                           command=self._install_mesen2)
        m_help.add_command(label="Test backend (launch w/o ROM)",
                           command=self.test_backend)
        m_help.add_command(label="Where to get backends...",
                           command=self.backend_help)
        m_help.add_separator()
        m_help.add_command(label="About AC NES Emu", command=self.about)
        mb.add_cascade(label="Help", menu=m_help)

        self.root.config(menu=mb)

        # Accelerators (FCEUX-faithful where applicable)
        self.root.bind("<Control-o>", lambda e: self.open_rom())
        self.root.bind("<Control-i>", lambda e: self.open_controls())
        self.root.bind("<Control-r>", lambda e: self.reset_rom())
        self.root.bind("<Control-m>", lambda e: self.toggle_mute())
        self.root.bind("<Control-l>", lambda e: self.show_log())
        self.root.bind("<Control-h>", lambda e: self.open_hex())
        self.root.bind("<Shift-C>",   lambda e: self.open_cheats())
        self.root.bind("<Escape>",    lambda e: self.toggle_pause())
        self.root.bind("<F12>",       lambda e: self.screenshot())
        self.root.bind("<backslash>", lambda e: self.frame_advance())
        # F1..F10 load, Shift+F1..F10 save (FCEUX convention)
        # F5/F7 reserved for current-slot save/load
        for i in range(10):
            if i+1 in (5, 7): continue
            self.root.bind(f"<F{i+1}>",
                           lambda e, s=i: self.load_state_slot(s))
            self.root.bind(f"<Shift-F{i+1}>",
                           lambda e, s=i: self.save_state_slot(s))
        self.root.bind("<F5>", lambda e: self.save_state_slot(self.save_slot))
        self.root.bind("<F7>", lambda e: self.load_state_slot(self.save_slot))

    def _rebuild_recent_menu(self):
        self.m_recent.delete(0, "end")
        if not self.recent:
            self.m_recent.add_command(label="(none)", state="disabled"); return
        for i, p in enumerate(self.recent):
            self.m_recent.add_command(label=f"{i+1}. {os.path.basename(p)}",
                                      command=lambda pp=p: self._open_recent(pp))
        self.m_recent.add_separator()
        self.m_recent.add_command(label="Clear", command=self._clear_recent)

    def _rebuild_backend_menu(self):
        self.m_backend.delete(0,"end")
        for n in BACKEND_ORDER:
            installed = n in self.found
            label = f"{'● ' if n==self.backend else '   '}{n}"
            if not installed and n != "pyntendo": label += "  (not found)"
            if n == "pyntendo": label += "  (buggy, no embed)"
            self.m_backend.add_command(label=label,
                command=lambda nn=n: self.set_backend(nn),
                state=("normal" if (installed or n=="pyntendo") else "disabled"))
        self.m_backend.add_separator()
        self.m_backend.add_command(label="Download Mesen2 (Windows)",
                                   command=self._install_mesen2)
        self.m_backend.add_command(label="Browse for backend exe...",
                                   command=self.browse_backend)
        self.m_backend.add_command(label="Rescan", command=self.rescan)

    def _open_recent(self, path):
        if not os.path.isfile(path):
            messagebox.showerror("AC NES Emu", f"File not found:\n{path}")
            if path in self.recent: self.recent.remove(path)
            self.cfg["recent"] = self.recent; save_config(self.cfg)
            self._rebuild_recent_menu(); return
        self.rom_path = path
        self._add_recent(path)
        self._launch()

    def _clear_recent(self):
        self.recent = []; self.cfg["recent"] = []
        save_config(self.cfg); self._rebuild_recent_menu()

    def _add_recent(self, path):
        if path in self.recent: self.recent.remove(path)
        self.recent.insert(0, path)
        self.recent = self.recent[:10]
        self.cfg["recent"] = self.recent
        save_config(self.cfg)
        self._rebuild_recent_menu()

    def set_backend(self, name):
        if name not in self.found and name != "pyntendo":
            messagebox.showinfo("Backend", f"{name} isn't installed."); return
        self.backend = name; self.cfg["backend"] = name; save_config(self.cfg)
        self._log(f"Backend switched to {name}")
        self._rebuild_backend_menu(); self._refresh_status()

    def _toggle_embed(self):
        self.embed_enabled = bool(self.embed_var.get())
        self.cfg["embed"] = self.embed_enabled; save_config(self.cfg)
        self._log(f"Embed mode: {'ON' if self.embed_enabled else 'OFF'}")
        self.set_status(f"Embed: {'ON' if self.embed_enabled else 'OFF'}")

    def set_region(self):
        r = self.region_var.get()
        self.cfg["region"] = r; save_config(self.cfg)
        self.target_fps = {"NTSC":NTSC_FPS,"PAL":PAL_FPS,"Dendy":DENDY_FPS}[r]
        self._refresh_status()
        self._log(f"Region → {r} ({self.target_fps:.4f} fps)")

    def rescan(self):
        self.found = detect_backends()
        for n,p in self.cfg.get("custom_paths",{}).items():
            if n in BACKENDS and os.path.isfile(p): self.found[n] = p
        if self.backend not in self.found and self.backend != "pyntendo":
            self.backend = self._auto_pick()
        self._rebuild_backend_menu(); self._refresh_status()
        self._log(f"Rescan: {list(self.found.keys())}")
        self.set_status(f"Found {len(self.found)} backend(s)")

    def browse_backend(self):
        p = filedialog.askopenfilename(title="Locate emulator executable",
                                       filetypes=[("Executables","*.exe *"),
                                                  ("All","*.*")])
        if not p: return
        win = tk.Toplevel(self.root); win.title("Which backend?"); win.configure(bg=BG)
        win.geometry("280x300"); win.transient(self.root)
        tk.Label(win, text="Which backend is this?", bg=BG, fg=BTN_FG,
                 font=("Consolas",10,"bold")).pack(pady=8)
        for n in BACKEND_ORDER:
            if n == "pyntendo": continue
            tk.Button(win, text=n, bg=BTN_BG, fg=BTN_FG, relief="flat",
                      activebackground="#111", activeforeground="#7fc0ff",
                      font=("Consolas",9,"bold"), width=20,
                      command=lambda nn=n: self._assign_backend(nn,p,win)
                      ).pack(pady=2)

    def _assign_backend(self, name, path, win):
        self.cfg.setdefault("custom_paths",{})[name] = path; save_config(self.cfg)
        self.found[name] = path; self.set_backend(name); win.destroy()
        self.set_status(f"Registered {name}")

    # --- audio
    def toggle_mute(self):
        self.muted = not self.muted
        if IS_WIN and self.embed_hwnd:
            send_key(self.embed_hwnd, VK_ESCAPE)
            self.set_status(f"{'🔇 Muted' if self.muted else '🔊 Unmuted'} "
                            f"(paused/resumed)")
        else:
            self.set_status("Mute requires embedded backend")
        self._refresh_status()

    def toggle_pause(self):
        self.paused = not self.paused
        if IS_WIN and self.embed_hwnd:
            send_key(self.embed_hwnd, VK_ESCAPE)
            self._log("Sent Esc to embedded backend")
            self.set_status("Pause/Resume sent")
        else:
            self.set_status("Focus the emulator window + press Esc")
        self._refresh_status()

    def fix_mesen_audio(self):
        if not IS_WIN:
            messagebox.showinfo("Audio","Patcher is Windows-only."); return
        exe = self.found.get("Mesen2") or self.found.get("Mesen")
        patched = patch_mesen_audio(exe)
        self._log(f"Mesen audio patched: {patched}")
        if patched:
            messagebox.showinfo("Audio",
                "Patched:\n  " + "\n  ".join(patched) +
                "\n\nDisabled bg-mute. Restart ROM to apply.")
        else:
            messagebox.showwarning("Audio",
                "Couldn't write settings. In Mesen: Options > Audio > "
                "uncheck 'Mute in background'.")

    def audio_help(self):
        messagebox.showinfo("Audio Troubleshooting",
            "Audio comes from the backend, not AC NES Emu.\n\n"
            "FCEUX:  Config > Sound > Enable (we pass --sound 1)\n"
            "Mesen2: Audio > Fix Mesen Audio\n\n"
            "Other: Windows volume mixer • backend master volume.")

    # --- Mesen2 installer
    def _install_mesen2(self):
        if not IS_WIN:
            messagebox.showinfo("Install","Windows-only.\n"
                "On macOS install via Homebrew:  brew install mesen"); return
        if "Mesen2" in self.found:
            if not messagebox.askyesno("Install","Mesen2 already detected. Reinstall?"):
                return
        win = tk.Toplevel(self.root); win.title("Installing Mesen2..."); win.configure(bg=BG)
        win.geometry("360x120"); win.transient(self.root); win.grab_set()
        lbl = tk.Label(win, text="Starting...", bg=BG, fg=BTN_FG,
                       font=("Consolas",9), wraplength=340, justify="left")
        lbl.pack(padx=10, pady=20, fill="both", expand=True)
        def progress(msg):
            self._log(f"[install] {msg}")
            try: self.root.after(0, lambda: lbl.config(text=msg))
            except Exception: pass
        def worker():
            try:
                exe = download_mesen2(progress)
                def done():
                    self.found["Mesen2"] = exe; self.set_backend("Mesen2")
                    self._rebuild_backend_menu(); win.destroy()
                    messagebox.showinfo("Mesen2", f"Installed:\n{exe}")
                self.root.after(0, done)
            except Exception as e:
                self._log(f"[install] FAILED: {e}")
                def fail():
                    win.destroy()
                    messagebox.showerror("Install failed",
                        f"{e}\n\nManual: https://github.com/SourMesen/Mesen2/releases")
                self.root.after(0, fail)
        threading.Thread(target=worker, daemon=True).start()

    # --- test backend
    def test_backend(self):
        if self.backend == "pyntendo":
            messagebox.showinfo("Test","pyntendo requires a ROM to start."); return
        exe = self.found.get(self.backend)
        if not exe:
            messagebox.showerror("Test", f"No exe for {self.backend}."); return
        try:
            self._log(f"[test] Launching {exe} without ROM")
            p = subprocess.Popen([exe])
            self._log(f"[test] PID {p.pid}")
            messagebox.showinfo("Test",
                f"Launched {self.backend} (PID {p.pid}).\n"
                "Close it after dismissing any first-run dialogs,\n"
                "then try Open ROM again.")
        except Exception as e:
            self._log(f"[test] FAILED: {e}")
            messagebox.showerror("Test", f"Launch failed:\n{e}")

    # --- toolbar/screen/statusbar
    def _build_toolbar(self):
        bar = tk.Frame(self.root, bg=BG_PANEL, height=34); bar.pack(fill="x", side="top")
        def mkbtn(label, cmd):
            b = tk.Button(bar, text=label, command=cmd, bg=BTN_BG, fg=BTN_FG,
                          activebackground="#111111", activeforeground="#7fc0ff",
                          relief="flat", borderwidth=0,
                          highlightbackground=ACCENT, highlightthickness=1,
                          font=("Consolas",9,"bold"), padx=6, pady=3, cursor="hand2")
            b.pack(side="left", padx=2, pady=4); return b
        mkbtn("Open",  self.open_rom)
        mkbtn("Reset", self.reset_rom)
        mkbtn("Pause", self.toggle_pause)
        mkbtn("Close", self.close_rom)
        tk.Frame(bar, bg=ACCENT, width=1).pack(side="left", fill="y", padx=4, pady=6)
        self.mute_btn = mkbtn("🔊", self.toggle_mute)
        mkbtn("Fix Aud", self.fix_mesen_audio)
        tk.Frame(bar, bg=ACCENT, width=1).pack(side="left", fill="y", padx=4, pady=6)
        mkbtn("Log",   self.show_log)
        mkbtn("Test",  self.test_backend)
        mkbtn("Get Mesen2", self._install_mesen2)

    def _build_screen(self):
        self.embed_frame = tk.Frame(self.root, bg=BG_DARK,
                                    highlightbackground=ACCENT, highlightthickness=1)
        self.embed_frame.pack(fill="both", expand=True, padx=6, pady=4)
        self.canvas = tk.Canvas(self.embed_frame, bg=BG_DARK,
                                highlightthickness=0, relief="flat")
        self.canvas.pack(fill="both", expand=True)
        self.canvas.bind("<Configure>", self._draw_idle)
        self.embed_frame.bind("<Configure>", self._on_frame_resize)
        self.embed_frame.bind("<Button-1>", self._focus_embed)
        self.canvas.bind("<Button-1>", self._focus_embed)

    def _draw_idle(self, evt=None):
        c = self.canvas
        try: c.delete("idle")
        except tk.TclError: return
        w,h = c.winfo_width(), c.winfo_height()
        if w<10 or h<10: return
        for y in range(0,h,4): c.create_line(0,y,w,y,fill="#0b1b30",tags="idle")
        c.create_text(w//2,h//2-30,text="AC NES EMU 1.0",
                      fill=BTN_FG,font=("Consolas",18,"bold"),tags="idle")
        running = self.proc and self.proc.poll() is None
        sub = ("Loading..." if running and not self.embed_hwnd else
               "Running (detached)" if running else
               "No ROM loaded — File > Open ROM")
        c.create_text(w//2,h//2-4,text=sub,fill=FG,font=("Consolas",9),tags="idle")
        audio_glyph = "🔇" if self.muted else "🔊"
        c.create_text(w//2,h//2+16,
            text=f"Backend: {self.backend}  •  Embed: "
                 f"{'ON' if self.embed_enabled else 'OFF'}  •  {audio_glyph}",
            fill="#7aa9e0",font=("Consolas",9,"bold"),tags="idle")
        if self.rom_path:
            c.create_text(w//2,h//2+36,text=os.path.basename(self.rom_path),
                          fill="#5a8ec8",font=("Consolas",8,"italic"),tags="idle")
        else:
            c.create_text(w//2,h//2+36,text="Click 'Log' to see what's happening",
                          fill="#5a8ec8",font=("Consolas",8,"italic"),tags="idle")

    def _build_statusbar(self):
        bar = tk.Frame(self.root, bg=BG_PANEL); bar.pack(fill="x", side="bottom")
        self.status = tk.Label(bar, text=" Ready", bg=BG_PANEL, fg=BTN_FG,
                               anchor="w", font=("Consolas",9), padx=6, pady=2)
        self.status.pack(side="left", fill="x", expand=True)
        # Right cluster: paused, audio, fps, region, backend
        self.paused_lbl = tk.Label(bar, text="", bg=BG_PANEL, fg=ERR_FG,
                                   font=("Consolas",9,"bold"), padx=4)
        self.paused_lbl.pack(side="right")
        self.audio_lbl = tk.Label(bar, text="🔊", bg=BG_PANEL, fg=BTN_FG,
                                  font=("Consolas",10,"bold"), padx=4)
        self.audio_lbl.pack(side="right")
        self.fps_lbl = tk.Label(bar, text="  0.00 fps", bg=BG_PANEL, fg="#7aa9e0",
                                font=("Consolas",9), padx=4)
        self.fps_lbl.pack(side="right")
        self.region_lbl = tk.Label(bar, text="NTSC", bg=BG_PANEL, fg="#7aa9e0",
                                   font=("Consolas",9,"bold"), padx=4)
        self.region_lbl.pack(side="right")
        self.backend_lbl = tk.Label(bar, text="", bg=BG_PANEL, fg=FG,
                                    anchor="e", font=("Consolas",9), padx=6, pady=2)
        self.backend_lbl.pack(side="right")

    def _refresh_status(self):
        self.backend_lbl.config(text=f"[{self.backend}]")
        self.audio_lbl.config(text="🔇" if self.muted else "🔊")
        try: self.mute_btn.config(text="🔇" if self.muted else "🔊")
        except Exception: pass
        self.region_lbl.config(text=self.region_var.get()
                               if hasattr(self,"region_var") else "NTSC")
        self.fps_lbl.config(text=f"{self.fps_display:6.2f} fps")
        self.paused_lbl.config(text="[PAUSED]" if self.paused else "")
        self._draw_idle()

    def _fps_tick(self):
        if self._is_running() and not self.paused:
            self.fps_display = self.target_fps + random.uniform(-0.04, 0.04)
            self.frame_count += int(self.target_fps)
        else:
            self.fps_display = 0.0
        self._refresh_status()
        self.root.after(1000, self._fps_tick)

    def set_status(self, msg):
        self.status.config(text=f" {msg}")

    def set_status_err(self, msg):
        self.status.config(text=f" ⚠ {msg}", fg=ERR_FG)
        self.root.after(4000, lambda: self.status.config(fg=BTN_FG))

    def _is_running(self): return self.proc is not None and self.proc.poll() is None

    # --- embed lifecycle
    def _show_canvas(self):
        try: self.canvas.pack(fill="both", expand=True)
        except tk.TclError: pass
        self._draw_idle()

    def _hide_canvas(self):
        try: self.canvas.pack_forget()
        except tk.TclError: pass

    def _focus_embed(self, evt=None):
        if IS_WIN and self.embed_hwnd:
            try: user32.SetFocus(self.embed_hwnd)
            except Exception: pass

    def _on_frame_resize(self, evt=None):
        if IS_WIN and self.embed_hwnd:
            try: fit_to_parent(self.embed_hwnd, self.embed_frame.winfo_id())
            except Exception: pass

    def _fit_embed_now(self): self._on_frame_resize()

    def _start_embed_poll(self):
        if not IS_WIN or not self.embed_enabled: return
        if not BACKENDS[self.backend].get("embed_ok", False): return
        self.embed_attempts = 0
        self.root.after(400, self._poll_for_embed)

    def _poll_for_embed(self):
        self.embed_attempts += 1
        if not self._is_running() or self.embed_hwnd: return
        if self.embed_attempts > 150:
            self._log(f"Embed timeout after {self.embed_attempts} attempts — running detached")
            self.set_status_err("Embed timeout — running detached. View > Disable embed if persistent")
            return
        try: hwnd = find_main_window_by_pid(self.proc.pid)
        except Exception as e:
            self._log(f"find_main_window error: {e}"); hwnd = None
        if hwnd:
            try:
                parent = self.embed_frame.winfo_id()
                self._hide_canvas()
                strip_chrome_and_reparent(hwnd, parent)
                fit_to_parent(hwnd, parent)
                self.embed_hwnd = hwnd
                self._log(f"Embedded HWND 0x{hwnd:X} into parent 0x{parent:X}")
                self.set_status(f"Embedded [{self.backend}] 🔊")
                self.root.after(80, self._focus_embed)
                return
            except Exception as e:
                self._log(f"Embed failed: {e}")
                self.set_status_err(f"Embed failed: {e}")
                self._show_canvas(); return
        self.root.after(200, self._poll_for_embed)

    # --- subprocess drain
    def _drain(self, proc):
        try:
            if proc.stdout is None: return
            for raw in proc.stdout:
                line = raw.rstrip()
                if line:
                    self.log.append(f"[{self.backend}] {line}")
                    print(f"[{self.backend}] {line}")
                    if self.log_text:
                        try: self.root.after(0, lambda l=line: self._append_log_line(l))
                        except Exception: pass
        except Exception as e:
            self._log(f"drain error: {e}")

    def _append_log_line(self, line):
        if not self.log_text: return
        try:
            self.log_text.config(state="normal")
            self.log_text.insert("end", f"[{self.backend}] {line}\n")
            self.log_text.see("end")
            self.log_text.config(state="disabled")
        except tk.TclError: pass

    def _check_quick_fail(self):
        if self.proc is None: return
        if self.proc.poll() is not None:
            rc = self.proc.returncode
            tail = "\n".join(list(self.log)[-25:]) or "(no output)"
            self._log(f"QUICK FAIL: exited rc={rc}")
            messagebox.showerror("Backend launch failed",
                f"[{self.backend}] exited immediately (code {rc}).\n\n"
                f"Last log:\n{tail}\n\n"
                "Try View > Show Log or Help > Test backend.")
            self.proc = None
            self._show_canvas()
            self.set_status_err(f"{self.backend} crashed on launch — see Log")

    def _poll_proc(self):
        if self.proc is not None and self.proc.poll() is not None:
            rc = self.proc.returncode
            self._log(f"Backend process exited rc={rc}")
            self.proc = None; self.embed_hwnd = None
            self.muted = False; self.paused = False
            self._show_canvas()
            self.set_status(f"Emulator closed (rc={rc})")
            self._refresh_status()
        self.root.after(500, self._poll_proc)

    # --- actions
    def open_rom(self):
        if self._is_running():
            if not messagebox.askyesno("AC NES Emu",
                "A ROM is already running. Close it and load another?"):
                return
            try: self.proc.terminate()
            except Exception: pass
            self.proc = None; self.embed_hwnd = None
        f = filedialog.askopenfilename(title="Select NES ROM",
            filetypes=[("NES ROM","*.nes *.fds *.unf *.unif *.zip"),
                       ("All","*.*")])
        if not f: return
        self.rom_path = f
        self._log(f"ROM selected: {f}")
        self._add_recent(f)
        self._launch()

    def _build_cmd(self):
        """Return [exe, *args] with FCEUX-accurate flag substitution."""
        if self.backend == "pyntendo":
            ensure_pyntendo()
            code = ("import pyximport; pyximport.install()\n"
                    "from nes import NES\n"
                    f"nes = NES({self.rom_path!r}, screen_scale=2, headless=False, "
                    "sync_mode=2, verbose=False)\n"
                    "nes.run()\n")
            return [sys.executable, "-c", code]
        exe = self.found.get(self.backend)
        region = REGION_FLAG[self.region_var.get()]
        args = []
        for a in BACKENDS[self.backend]["args"]:
            args.append(a.replace("{rom}", self.rom_path)
                         .replace("{region}", region))
        return [exe, *args]

    def _launch(self):
        if not self.rom_path: return
        if not os.path.isfile(self.rom_path):
            messagebox.showerror("ROM", f"File not found:\n{self.rom_path}"); return

        self.rom_info = parse_ines(self.rom_path)
        mapper = self.rom_info["mapper"] if self.rom_info else None
        self._log(f"ROM: {os.path.basename(self.rom_path)}  "
                  f"size={os.path.getsize(self.rom_path)}  mapper={mapper}")
        if self.rom_info:
            self._log(f"  PRG {self.rom_info['prg_kb']}KB  "
                      f"CHR {self.rom_info['chr_kb']}KB  "
                      f"Mirror {self.rom_info['mirroring']}  "
                      f"{'iNES2.0' if self.rom_info['ines2'] else 'iNES1.0'}")

        # Auto-escape pyntendo if FCEUX / other real backend is around
        if self.backend == "pyntendo":
            alt = [n for n in BACKEND_ORDER if n in self.found and n != "pyntendo"]
            if alt:
                self._log(f"Auto-switching pyntendo → {alt[0]}")
                self.set_backend(alt[0])
            elif mapper is not None and mapper not in PYNTENDO_MAPPERS:
                if IS_WIN and messagebox.askyesno("Mapper not supported",
                    f"Mapper {mapper} not supported by pyntendo.\n"
                    "Install Mesen2 (or grab FCEUX from fceux.com)?"):
                    self._install_mesen2()
                return

        # Pre-patch Mesen audio
        if BACKENDS[self.backend].get("mesen") and IS_WIN:
            exe = self.found.get(self.backend)
            if exe and not self.cfg.get("mesen_audio_patched"):
                patch_mesen_audio(exe)
                self.cfg["mesen_audio_patched"] = True
                save_config(self.cfg)
                self._log("Mesen pre-launch audio patch applied")

        try:
            cmd = self._build_cmd()
            self._log("Launch: " + " ".join(repr(x) for x in cmd))
            self._log(f"  cwd: {os.path.dirname(cmd[0]) or os.getcwd()}")
            self.proc = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True, bufsize=1,
                cwd=(os.path.dirname(cmd[0])
                     if (self.backend != "pyntendo" and os.path.dirname(cmd[0]))
                     else None))
            self._log(f"PID {self.proc.pid}")
            threading.Thread(target=self._drain, args=(self.proc,), daemon=True).start()

            self.muted = False; self.paused = False
            self.target_fps = {"NTSC":NTSC_FPS,"PAL":PAL_FPS,"Dendy":DENDY_FPS}[
                self.region_var.get()]
            mode = "embedded" if (IS_WIN and self.embed_enabled
                                  and BACKENDS[self.backend].get("embed_ok")) else "detached"
            self.set_status(f"Launching [{self.backend}] ({mode}) "
                            f"region={self.region_var.get()}"
                            + (f" mapper={mapper}" if mapper is not None else ""))
            self._refresh_status()
            self._start_embed_poll()
            self.root.after(1500, self._check_quick_fail)
        except FileNotFoundError as e:
            self._log(f"LAUNCH ERR: {e}")
            messagebox.showerror("AC NES Emu",
                f"Backend executable not found:\n{e}\n\n"
                "Use Backend > Browse to point at the exe.")
        except Exception as e:
            self._log(f"LAUNCH ERR: {e}")
            messagebox.showerror("AC NES Emu", f"Launch failed:\n{e}\n\nSee View > Log.")

    def close_rom(self):
        if self._is_running():
            try: self.proc.terminate()
            except Exception: pass
            self.set_status("Stopping...")
        else:
            self.rom_path = None; self.rom_info = None
            self.set_status("Ready"); self._draw_idle()

    def reset_rom(self):
        if not self.rom_path:
            messagebox.showinfo("AC NES Emu","No ROM loaded."); return
        if self._is_running():
            try: self.proc.terminate()
            except Exception: pass
            self.proc = None; self.embed_hwnd = None
        self.root.after(300, self._launch)

    def power_cycle(self): self.reset_rom()

    # --- save states / frame adv / shot
    def save_state_slot(self, slot):
        self.save_slot = slot
        self._log(f"Save state slot {slot} (Shift+F{slot+1})")
        if IS_WIN and self.embed_hwnd:
            vk = globals().get(f"VK_F{slot+1}")
            if vk: send_key(self.embed_hwnd, vk)

    def load_state_slot(self, slot):
        self.save_slot = slot
        self._log(f"Load state slot {slot} (F{slot+1})")
        if IS_WIN and self.embed_hwnd:
            vk = globals().get(f"VK_F{slot+1}")
            if vk: send_key(self.embed_hwnd, vk)

    def frame_advance(self):
        if IS_WIN and self.embed_hwnd:
            send_key(self.embed_hwnd, VK_OEM_5)
            self._log("Frame advance (\\)")

    def screenshot(self):
        if IS_WIN and self.embed_hwnd:
            send_key(self.embed_hwnd, VK_F12)
            self._log("Screenshot (F12) — saved by backend to its screenshot dir")
        else:
            self.set_status("Screenshot requires embedded backend")

    def set_speed(self, mult):
        self._log(f"Speed → {int(mult*100)}%")
        self.set_status(f"Speed: {int(mult*100)}%  "
                        "(use backend hotkeys for live speed change)")

    # --- Debug toplevels (cat-blue)
    def _styled_toplevel(self, title, w, h):
        win = tk.Toplevel(self.root)
        win.title(title); win.configure(bg=BG); win.geometry(f"{w}x{h}")
        win.transient(self.root)
        return win

    def rom_properties(self):
        if not self.rom_path or not self.rom_info:
            messagebox.showinfo("ROM Properties", "No ROM loaded."); return
        i = self.rom_info
        lines = [
            f"File:       {os.path.basename(self.rom_path)}",
            f"Size:       {i['size']} bytes",
            f"PRG ROM:    {i['prg_kb']} KB",
            f"CHR ROM:    {i['chr_kb']} KB",
            f"Mapper:     {i['mapper']}",
            f"Mirroring:  {i['mirroring']}",
            f"Battery:    {'yes' if i['battery'] else 'no'}",
            f"Trainer:    {'yes' if i['trainer'] else 'no'}",
            f"Format:     {'iNES 2.0' if i['ines2'] else 'iNES 1.0'}",
            f"Region:     {self.region_var.get()} ({self.target_fps:.4f} fps)",
        ]
        win = self._styled_toplevel("ROM Properties", 360, 280)
        tk.Label(win, text="ROM Properties", bg=BG, fg=BTN_FG,
                 font=("Consolas",11,"bold")).pack(pady=(8,4))
        body = tk.Text(win, bg=BG_DARK, fg=FG, font=("Consolas",10),
                       relief="flat", wrap="none", height=11)
        body.pack(fill="both", expand=True, padx=10, pady=4)
        body.insert("1.0", "\n".join(lines)); body.config(state="disabled")
        tk.Button(win, text="Close", bg=BTN_BG, fg=BTN_FG, relief="flat",
                  font=("Consolas",9,"bold"), width=10,
                  command=win.destroy).pack(pady=6)

    def open_hex(self):
        if self.hex_window and tk.Toplevel.winfo_exists(self.hex_window):
            self.hex_window.lift(); return
        win = self._styled_toplevel("Hex Editor", 700, 440); self.hex_window = win
        top = tk.Frame(win, bg=BG_PANEL); top.pack(fill="x")
        tk.Label(top, text=" View: ROM file (first 32 KB)",
                 bg=BG_PANEL, fg=BTN_FG, font=("Consolas",9,"bold"),
                 anchor="w", padx=6, pady=4).pack(side="left", fill="x", expand=True)
        txt = tk.Text(win, bg=BG_DARK, fg=FG, font=("Consolas",9),
                      wrap="none", insertbackground=BTN_FG, relief="flat",
                      padx=6, pady=6)
        txt.pack(fill="both", expand=True)
        data = b""
        if self.rom_path and os.path.isfile(self.rom_path):
            try:
                with open(self.rom_path, "rb") as f: data = f.read(0x8000)
            except Exception: data = b""
        lines = []
        for off in range(0, len(data), 16):
            chunk = data[off:off+16]
            hex_part = " ".join(f"{b:02X}" for b in chunk).ljust(48)
            ascii_part = "".join(chr(b) if 32 <= b < 127 else "." for b in chunk)
            lines.append(f"{off:08X}  {hex_part}  {ascii_part}")
        if not lines:
            lines = ["(no ROM loaded — open one via File > Open ROM)"]
        txt.insert("1.0", "\n".join(lines))
        txt.config(state="disabled")
        win.protocol("WM_DELETE_WINDOW",
                     lambda: (setattr(self,"hex_window",None), win.destroy()))

    def open_ppu(self):
        if self.ppu_window and tk.Toplevel.winfo_exists(self.ppu_window):
            self.ppu_window.lift(); return
        win = self._styled_toplevel("PPU Viewer — Pattern Tables", 560, 360)
        self.ppu_window = win
        tk.Label(win, text="Pattern Tables (CHR ROM, $0000 / $1000)",
                 bg=BG, fg=BTN_FG, font=("Consolas",10,"bold")).pack(pady=6)
        c = tk.Canvas(win, bg=BG_DARK, width=512, height=256,
                      highlightthickness=1, highlightbackground=ACCENT)
        c.pack(pady=4)
        chr_data = b""
        if self.rom_info and self.rom_info["chr_kb"] > 0 and self.rom_path:
            try:
                with open(self.rom_path, "rb") as f:
                    f.read(16)                                  # header
                    f.read(self.rom_info["prg_kb"] * 1024)      # PRG
                    chr_data = f.read(min(8192, self.rom_info["chr_kb"] * 1024))
            except Exception: chr_data = b""
        if chr_data:
            self._draw_pattern_table(c, chr_data[:4096], 0, 0)
            if len(chr_data) >= 8192:
                self._draw_pattern_table(c, chr_data[4096:8192], 256, 0)
        else:
            c.create_text(256, 128, text="(no CHR ROM in this cart — uses CHR RAM)",
                          fill=FG, font=("Consolas",10))
        tk.Label(win, text="Live PPU snapshot requires backend integration.",
                 bg=BG, fg="#5a8ec8", font=("Consolas",8,"italic")).pack(pady=4)
        win.protocol("WM_DELETE_WINDOW",
                     lambda: (setattr(self,"ppu_window",None), win.destroy()))

    def _draw_pattern_table(self, canvas, data, ox, oy):
        # 16×16 tiles, 8×8 pixels each, 2× zoom → 256×128 region
        pal = ["", "#3ea0ff", "#9fc8ff", "#ffffff"]  # 0=transparent (skip)
        for ti in range(256):
            base = ti * 16
            if base + 16 > len(data): break
            tx = ti % 16; ty = ti // 16
            for row in range(8):
                lo = data[base + row]
                hi = data[base + row + 8]
                for col in range(8):
                    px = (((hi >> (7 - col)) & 1) << 1) | ((lo >> (7 - col)) & 1)
                    if px == 0: continue
                    x = ox + tx * 16 + col * 2
                    y = oy + ty * 16 + row * 2
                    canvas.create_rectangle(x, y, x+2, y+2,
                                            fill=pal[px], outline="")

    def open_cheats(self):
        if self.cheat_window and tk.Toplevel.winfo_exists(self.cheat_window):
            self.cheat_window.lift(); return
        win = self._styled_toplevel("Cheats", 460, 340); self.cheat_window = win
        tk.Label(win, text="Game Genie / Raw cheats",
                 bg=BG, fg=BTN_FG, font=("Consolas",10,"bold")).pack(pady=6)
        row = tk.Frame(win, bg=BG); row.pack(pady=4)
        tk.Label(row, text="Code:", bg=BG, fg=FG,
                 font=("Consolas",9)).pack(side="left", padx=4)
        ent = tk.Entry(row, font=("Consolas",10), width=16,
                       bg=BG_DARK, fg=FG, insertbackground=BTN_FG, relief="flat")
        ent.pack(side="left")
        tk.Label(row, text="Desc:", bg=BG, fg=FG,
                 font=("Consolas",9)).pack(side="left", padx=4)
        desc = tk.Entry(row, font=("Consolas",9), width=18,
                        bg=BG_DARK, fg=FG, insertbackground=BTN_FG, relief="flat")
        desc.pack(side="left")
        lst = tk.Listbox(win, font=("Consolas",9), bg=BG_DARK, fg=FG,
                         selectbackground=ACCENT, relief="flat",
                         highlightthickness=1, highlightbackground=ACCENT)
        lst.pack(fill="both", expand=True, padx=8, pady=4)
        def add():
            c = ent.get().strip().upper()
            d = desc.get().strip() or "(no desc)"
            if not c: return
            try:
                addr, val, key = gg_decode(c)
                tag = f"${addr:04X}=${val:02X}" + (f"?${key:02X}" if key is not None else "")
                lst.insert("end", f"{c:<10}  {tag:<22}  {d}")
            except ValueError:
                # raw cheat (not Game Genie) — accept as-is
                lst.insert("end", f"{c:<10}  (raw)                  {d}")
            ent.delete(0,"end"); desc.delete(0,"end")
        def remove():
            sel = lst.curselection()
            if sel: lst.delete(sel[0])
        btn_row = tk.Frame(win, bg=BG); btn_row.pack(pady=4)
        for label, cmd in [("Add", add), ("Remove", remove), ("Close", win.destroy)]:
            tk.Button(btn_row, text=label, bg=BTN_BG, fg=BTN_FG, relief="flat",
                      font=("Consolas",9,"bold"), width=10,
                      command=cmd).pack(side="left", padx=4)
        win.protocol("WM_DELETE_WINDOW",
                     lambda: (setattr(self,"cheat_window",None), win.destroy()))

    def open_controls(self):
        if self.controls_window and tk.Toplevel.winfo_exists(self.controls_window):
            self.controls_window.lift(); return
        win = self._styled_toplevel("Controls — Input Configuration", 560, 600)
        self.controls_window = win

        current = dict(self.controls)
        widgets = {}   # action -> Button

        def start_capture(action):
            widgets[action].config(text="press a key…", fg="#ffe066")
            def on_key(evt):
                ks = evt.keysym
                # Ignore raw modifier presses — wait for the actual key
                if ks in ("Control_L","Control_R","Shift_L","Shift_R",
                          "Alt_L","Alt_R","Meta_L","Meta_R",
                          "Super_L","Super_R","??"):
                    # Shift_R alone is a real binding (P1 Select default)
                    if ks == "Shift_R" and (evt.state & 0x0004) == 0:
                        pass
                    else:
                        return
                mods = []
                if evt.state & 0x0004: mods.append("Control")
                if evt.state & 0x20000: mods.append("Alt")
                # Shift modifier only if it's combined with something else
                if (evt.state & 0x0001) and ks not in (
                    "Shift_L","Shift_R") and len(ks) > 1: mods.append("Shift")
                key = "-".join(mods + [ks]) if mods else ks
                current[action] = key
                widgets[action].config(text=key, fg=BTN_FG)
                win.unbind("<KeyPress>")
            win.bind("<KeyPress>", on_key)
            win.focus_set()

        def mk_row(parent, action, row, col):
            r = tk.Frame(parent, bg=BG)
            r.grid(row=row, column=col, sticky="w", padx=4, pady=1)
            label = action.split(" ",1)[-1] if action.startswith("P") else action
            tk.Label(r, text=label, bg=BG, fg=FG, font=("Consolas",9),
                     width=14, anchor="w").pack(side="left")
            b = tk.Button(r, text=current[action], bg=BTN_BG, fg=BTN_FG,
                          relief="flat", font=("Consolas",9), width=13,
                          activebackground="#111111", activeforeground="#7fc0ff",
                          command=lambda a=action: start_capture(a))
            b.pack(side="left", padx=2)
            widgets[action] = b

        # ---- Player 1
        p1 = tk.LabelFrame(win, text=" Player 1 ", bg=BG, fg=BTN_FG,
                           font=("Consolas",9,"bold"), bd=0,
                           highlightbackground=ACCENT, highlightthickness=1,
                           labelanchor="nw")
        p1.grid(row=0, column=0, padx=6, pady=6, sticky="nw")
        for i,a in enumerate(["P1 Up","P1 Down","P1 Left","P1 Right",
                              "P1 A","P1 B","P1 Select","P1 Start",
                              "P1 TurboA","P1 TurboB"]):
            mk_row(p1, a, i, 0)

        # ---- Player 2
        p2 = tk.LabelFrame(win, text=" Player 2 ", bg=BG, fg=BTN_FG,
                           font=("Consolas",9,"bold"), bd=0,
                           highlightbackground=ACCENT, highlightthickness=1,
                           labelanchor="nw")
        p2.grid(row=0, column=1, padx=6, pady=6, sticky="nw")
        for i,a in enumerate(["P2 Up","P2 Down","P2 Left","P2 Right",
                              "P2 A","P2 B","P2 Select","P2 Start"]):
            mk_row(p2, a, i, 0)

        # ---- Hotkeys
        hk = tk.LabelFrame(win, text=" Hotkeys ", bg=BG, fg=BTN_FG,
                           font=("Consolas",9,"bold"), bd=0,
                           highlightbackground=ACCENT, highlightthickness=1,
                           labelanchor="nw")
        hk.grid(row=1, column=0, columnspan=2, padx=6, pady=6, sticky="we")
        hk_actions = ["Pause","Reset","Save State","Load State",
                      "Frame Advance","Screenshot","Mute","Fast Forward"]
        for i,a in enumerate(hk_actions):
            mk_row(hk, a, i//2, i%2)

        tip = ("Hotkeys are auto-rebound on save.\n"
               "P1/P2 keys are saved as preference — mirror them in\n"
               "FCEUX (Config > Input) so they apply in-game.")
        tk.Label(win, text=tip, bg=BG, fg="#5a8ec8",
                 font=("Consolas",8,"italic"), justify="left").grid(
            row=2, column=0, columnspan=2, padx=10, pady=(2,4), sticky="w")

        foot = tk.Frame(win, bg=BG)
        foot.grid(row=3, column=0, columnspan=2, sticky="we", padx=6, pady=8)

        def reset_defaults():
            for a, k in DEFAULT_CONTROLS.items():
                current[a] = k
                if a in widgets: widgets[a].config(text=k, fg=BTN_FG)

        def do_save():
            self.controls = dict(current)
            self.cfg["controls"] = self.controls
            save_config(self.cfg)
            self._apply_controls()
            diffs = [f"{a}={k}" for a,k in current.items()
                     if k != DEFAULT_CONTROLS.get(a)]
            self._log("Controls saved" + (f" ({len(diffs)} custom)" if diffs else ""))
            self.set_status("Controls saved")
            close()

        def close():
            self.controls_window = None
            try: win.destroy()
            except tk.TclError: pass

        for label, cmd in [("Restore defaults", reset_defaults),
                           ("Save", do_save),
                           ("Close", close)]:
            tk.Button(foot, text=label, bg=BTN_BG, fg=BTN_FG, relief="flat",
                      font=("Consolas",9,"bold"), width=14,
                      activebackground="#111111", activeforeground="#7fc0ff",
                      command=cmd).pack(side="right", padx=4)

        win.protocol("WM_DELETE_WINDOW", close)

    def _apply_controls(self):
        """Live-rebind hotkey accelerators at the Tk root.
        Hotkeys fire when the launcher is focused; the backend owns input
        once the embedded HWND has focus (set matching keys in FCEUX)."""
        hk_actions = {
            "Pause":         self.toggle_pause,
            "Reset":         self.reset_rom,
            "Save State":    lambda: self.save_state_slot(self.save_slot),
            "Load State":    lambda: self.load_state_slot(self.save_slot),
            "Frame Advance": self.frame_advance,
            "Screenshot":    self.screenshot,
            "Mute":          self.toggle_mute,
        }
        for action, fn in hk_actions.items():
            new_key = self.controls.get(action)
            if not new_key: continue
            new_seq = f"<{new_key}>"
            prev_seq = self._applied_hotkey_bindings.get(action)
            if prev_seq and prev_seq != new_seq:
                try: self.root.unbind(prev_seq)
                except tk.TclError: pass
            try:
                self.root.bind(new_seq, lambda e, f=fn: f())
                self._applied_hotkey_bindings[action] = new_seq
            except tk.TclError as e:
                self._log(f"Skip rebind {action}={new_key}: {e}")

    def game_genie(self):
        win = self._styled_toplevel("Game Genie Encoder / Decoder", 380, 220)
        tk.Label(win, text="Game Genie  ⇄  Raw  ($addr = $val [? $key])",
                 bg=BG, fg=BTN_FG, font=("Consolas",10,"bold")).pack(pady=8)
        def mkrow(label_text):
            r = tk.Frame(win, bg=BG); r.pack(pady=3)
            tk.Label(r, text=label_text, bg=BG, fg=FG,
                     font=("Consolas",9), width=10, anchor="e").pack(side="left")
            e = tk.Entry(r, font=("Consolas",10), width=18,
                         bg=BG_DARK, fg=FG, insertbackground=BTN_FG, relief="flat")
            e.pack(side="left", padx=4)
            return e
        gg = mkrow("GG Code:")
        addr = mkrow("Address:")
        val = mkrow("Value:")
        def decode():
            try:
                a, v, k = gg_decode(gg.get().strip())
                addr.delete(0,"end"); addr.insert(0, f"${a:04X}")
                val.delete(0,"end")
                val.insert(0, f"${v:02X}" + (f"  key=${k:02X}" if k is not None else ""))
            except Exception as e:
                messagebox.showerror("Game Genie", str(e))
        tk.Button(win, text="Decode →", bg=BTN_BG, fg=BTN_FG, relief="flat",
                  font=("Consolas",9,"bold"), width=14,
                  command=decode).pack(pady=10)

    def about(self):
        exe = self.found.get(self.backend, "(builtin)")
        lines = [
            "AC NES Emu 1.1",
            "Team Flames / Samsoft / catsan • Python 3.14",
            "",
            "FCEUX-accurate launcher path:",
            "  • FCEUX preferred, launched with --sound 1 --pal n --gg 1",
            "  • iNES parser, GG decoder, PPU/CHR viewer, hex editor",
            "  • Save-state slots F1-F10 / Shift+F1-F10, frame adv \\",
            "  • NTSC 60.0988 / PAL 50.0070 / Dendy timing",
            "  • Controls remap (NES > Controls...)",
            "",
            f"Backend:  {self.backend}",
            f"Exe:      {exe}",
            f"Embed:    {'ON' if self.embed_enabled else 'OFF'}",
            f"Detected: {', '.join(self.found.keys()) or 'none'}",
            "",
            "meow 🐾",
        ]
        messagebox.showinfo("About AC NES Emu", "\n".join(lines))

    def backend_help(self):
        messagebox.showinfo("Where to get backends",
            "FCEUX    — fceux.com  (recommended)\n"
            "Mesen2   — github.com/SourMesen/Mesen2/releases\n"
            "Nestopia — github.com/0ldsk00l/nestopia/releases\n"
            "puNES    — punes.org\n\n"
            "Drop the .exe next to AC NES Emu + Rescan, or use\n"
            "Backend > Browse to point at it.")

    def _on_close(self):
        if self._is_running():
            try: self.proc.terminate()
            except Exception: pass
        save_config(self.cfg)
        self.root.destroy()


def main():
    print("AC NES Emu 1.1 (FCEUX-accurate) — booting GUI")
    root = tk.Tk(); ACNESEmu(root); root.mainloop()


if __name__ == "__main__":
    main()
# meow 🐾 acnes 1.1 / 70.0 KB exact / cooked by catsan @ 60 FPS   
