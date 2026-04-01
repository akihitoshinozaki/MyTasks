import tkinter as tk
from tkinter import font, messagebox
import os
import json
import threading
import time
import subprocess
import re
import calendar as _cal
from datetime import date, timedelta
from pynput import keyboard as pynput_kb
from AppKit import NSApp, NSWindowCollectionBehaviorMoveToActiveSpace, NSWindowCollectionBehaviorFullScreenAuxiliary, NSStatusWindowLevel

from google.oauth2.credentials import Credentials
from google_auth_oauthlib.flow import InstalledAppFlow
from google.auth.transport.requests import Request
from googleapiclient.discovery import build

# --- Config ---
CREDENTIALS_FILE = os.path.expanduser("~/credentials.json")
TOKEN_FILE        = os.path.expanduser("~/.todo_token.json")
SCOPES            = ["https://www.googleapis.com/auth/tasks"]
SYNC_INTERVAL     = 15

# --- Colors ---
BG_COLOR      = "#f5e6d3"
HEADER_COLOR  = "#dfc9a8"
ACCENT_COLOR  = "#9b5e2e"
TEXT_COLOR    = "#2d1a0e"
DONE_COLOR    = "#a08866"
ENTRY_BG      = "#ede2cc"
BUTTON_COLOR  = "#b8935a"
DELETE_COLOR  = "#b84a3a"
SYNC_COLOR    = "#4e7a42"
TAB_ACTIVE_BG = "#c9a97c"
STEP_EMPTY    = "#c0a07a"
STEP_FILL     = "#9b5e2e"
UNTIL_COLOR   = "#5e7a9b"
TAB_BG        = "#f5e6d3"
# Segmented control (Apple-style tabs)
SEG_CONTAINER = "#ccab84"
SEG_ACTIVE_BG = "#fdf8f0"
SEG_BORDER    = "#b8905a"
TIMER_COLOR   = "#3d7a5e"
WINDOW_WIDTH  = 300
# Card UI
CARD_RADIUS   = 10
CARD_SHADOW   = "#c0a070"
CARD_LIFT_SHADOW = "#a08050"
# Card backgrounds per nesting depth
DEPTH_BG      = ["#fdf6ec", "#f5e6d3", "#ecdcca", "#e3d2ba", "#dad0ae"]

TABS            = ["Today", "Incomplete", "Stats"]
STUDY_LOG_PATH  = os.path.join(os.path.dirname(os.path.abspath(__file__)), "study_log.json")
TIMER_PRESETS   = [0, 5, 10, 15, 20, 25, 30, 45, 60]
INDENT_THRESHOLD = 70   # px from window left edge to trigger indent zone


# ── Google Auth ──────────────────────────────────────────────────────────────

def get_google_service():
    creds = None
    if os.path.exists(TOKEN_FILE):
        creds = Credentials.from_authorized_user_file(TOKEN_FILE, SCOPES)
    if not creds or not creds.valid:
        if creds and creds.expired and creds.refresh_token:
            creds.refresh(Request())
        else:
            flow = InstalledAppFlow.from_client_secrets_file(CREDENTIALS_FILE, SCOPES)
            creds = flow.run_local_server(port=0)
        with open(TOKEN_FILE, "w") as f:
            f.write(creds.to_json())
    return build("tasks", "v1", credentials=creds)


def get_or_create_tasklist(service, name="My Tasks"):
    lists = service.tasklists().list().execute().get("items", [])
    for tl in lists:
        if tl["title"] == name:
            return tl["id"]
    if lists:
        return lists[0]["id"]
    return service.tasklists().insert(body={"title": name}).execute()["id"]


def fetch_google_tasks(service, tasklist_id):
    result = service.tasks().list(
        tasklist=tasklist_id, showCompleted=True,
        showHidden=True, maxResults=100
    ).execute()
    return result.get("items", [])


# ── Card drawing helper ───────────────────────────────────────────────────────

def _rounded_rect(canvas, x1, y1, x2, y2, r=CARD_RADIUS, **kw):
    pts = [
        x1+r, y1,   x2-r, y1,
        x2,   y1,   x2,   y1+r,
        x2,   y2-r, x2,   y2,
        x2-r, y2,   x1+r, y2,
        x1,   y2,   x1,   y2-r,
        x1,   y1+r, x1,   y1,
    ]
    return canvas.create_polygon(pts, smooth=True, **kw)


# ── App ──────────────────────────────────────────────────────────────────────

class ToDoApp:
    def __init__(self, root):
        self.root = root
        self.root.title("To-Do")
        self.root.configure(bg=BG_COLOR)
        self.root.attributes("-topmost", True)
        self.root.resizable(False, True)

        self.service      = None
        self.tasklist_id  = None
        self.tasks        = []
        self.active_tab   = "Today"
        self._stop_sync   = False
        self.new_task_steps   = 1
        self.pending_until_date = None
        self._cal_popup   = None

        self.new_task_minutes     = 0
        self._active_timer        = None   # {"task": task, "after_id": id, "running": bool}
        self._total_study_seconds = 0
        self._timer_label_widget  = None
        self._summary_label       = None

        self._stats_view         = "week"   # "day" | "week" | "month" | "year"
        self._stats_week_offset  = 0        # 0=current week, -1=last week …
        self._stats_month_offset = 0
        self._stats_year_offset  = 0
        self._study_log          = self._load_study_log()

        self._task_rows        = []
        self._drag_task        = None
        self._drag_source_idx  = None
        self._drag_target_idx  = None
        self._drag_indent      = False
        self._ghost            = None
        self._ghost_frame      = None
        self._ghost_text_lbl   = None
        self._ghost_w         = 0
        self._ghost_h         = 0

        self._build_ui()
        self._position_window()
        threading.Thread(target=self._init_google, daemon=True).start()

    # ── Build UI ─────────────────────────────────────────────────────────────

    def _build_ui(self):
        # Title bar (contains normal header and focus header, only one visible at a time)
        title_bar = tk.Frame(self.root, bg=HEADER_COLOR)
        title_bar.pack(fill="x")
        self._title_bar = title_bar

        # ── Normal header ──────────────────────────────────────────────────────
        self._normal_header = tk.Frame(title_bar, bg=HEADER_COLOR)
        self._normal_header.pack(fill="x")
        tk.Label(
            self._normal_header, text="  To-Do List", bg=HEADER_COLOR,
            fg=ACCENT_COLOR, font=("Helvetica", 13, "bold"), pady=8
        ).pack(side="left")
        self.sync_label = tk.Label(
            self._normal_header, text="⟳ Connecting...", bg=HEADER_COLOR,
            fg=DONE_COLOR, font=("Helvetica", 9), padx=8
        )
        self.sync_label.pack(side="right")

        # ── Focus header (hidden until timer starts) ───────────────────────────
        self._focus_header = tk.Frame(title_bar, bg=HEADER_COLOR)

        # Row 1: "Today • 集中中" + sync
        fh_row1 = tk.Frame(self._focus_header, bg=HEADER_COLOR)
        fh_row1.pack(fill="x")
        tk.Label(fh_row1, text="  Today  •  集中中", bg=HEADER_COLOR,
                 fg=ACCENT_COLOR, font=("Helvetica", 11, "bold"), pady=5).pack(side="left")
        self._focus_sync_lbl = tk.Label(fh_row1, text="", bg=HEADER_COLOR,
                                        fg=DONE_COLOR, font=("Helvetica", 9), padx=8)
        self._focus_sync_lbl.pack(side="right")

        # Row 2: task name
        self._focus_task_lbl = tk.Label(self._focus_header, text="", bg=HEADER_COLOR,
                                        fg=ACCENT_COLOR, font=("Helvetica", 10, "bold"),
                                        padx=10, pady=0, anchor="w")
        self._focus_task_lbl.pack(fill="x")

        # Row 3: big time + elapsed (centred)
        fh_time_row = tk.Frame(self._focus_header, bg=HEADER_COLOR)
        fh_time_row.pack(fill="x", pady=(4, 0))
        self._focus_remaining_lbl = tk.Label(
            fh_time_row, text="--:--", bg=HEADER_COLOR, fg=TIMER_COLOR,
            font=("Helvetica", 22, "bold"))
        self._focus_remaining_lbl.pack(side="left", expand=True)
        self._focus_elapsed_lbl = tk.Label(
            fh_time_row, text="経過\n0:00", bg=HEADER_COLOR, fg=DONE_COLOR,
            font=("Helvetica", 8), padx=10, justify="center")
        self._focus_elapsed_lbl.pack(side="right")

        # Row 4: circular buttons (centred)
        fh_btn_row = tk.Frame(self._focus_header, bg=HEADER_COLOR)
        fh_btn_row.pack(pady=(6, 8))
        R = 18   # circle radius
        D = R * 2
        def _circle_btn(parent, text, fill, fg, command, font_size=10):
            cv = tk.Canvas(parent, width=D + 4, height=D + 4,
                           bg=HEADER_COLOR, highlightthickness=0, cursor="hand2")
            oid = cv.create_oval(2, 2, D + 2, D + 2, fill=fill, outline="", width=0)
            tid = cv.create_text(D // 2 + 2, D // 2 + 2, text=text,
                                 fill=fg, font=("Helvetica", font_size, "bold"))
            cv.bind("<Button-1>", lambda e: command())
            cv.bind("<Enter>",  lambda e: cv.itemconfig(oid, fill=_lighten(fill)))
            cv.bind("<Leave>",  lambda e: cv.itemconfig(oid, fill=fill))
            return cv, oid, tid

        def _lighten(hex_color):
            r = min(255, int(hex_color[1:3], 16) + 25)
            g = min(255, int(hex_color[3:5], 16) + 25)
            b = min(255, int(hex_color[5:7], 16) + 25)
            return f"#{r:02x}{g:02x}{b:02x}"

        pp_cv, self._pp_oval, self._pp_text = _circle_btn(
            fh_btn_row, "⏸", TIMER_COLOR, "white", self._header_playpause, font_size=11)
        pp_cv.pack(side="left", padx=6)
        self._focus_playpause_btn = pp_cv
        self._focus_playpause_fill_normal = TIMER_COLOR

        stop_cv, _, _ = _circle_btn(
            fh_btn_row, "■", DELETE_COLOR, "white", self._header_stop_timer, font_size=10)
        stop_cv.pack(side="left", padx=6)

        add5_cv, _, _ = _circle_btn(
            fh_btn_row, "+5", BUTTON_COLOR, "white", self._header_add_5, font_size=9)
        add5_cv.pack(side="left", padx=6)

        # Study time summary bar
        summary_bar = tk.Frame(self.root, bg=HEADER_COLOR)
        summary_bar.pack(fill="x")
        self._summary_label = tk.Label(
            summary_bar, text="今日の学習: 0分", bg=HEADER_COLOR,
            fg=TIMER_COLOR, font=("Helvetica", 9, "bold"), padx=8, pady=2
        )
        self._summary_label.pack(side="left")

        # Tab bar
        # Apple-style segmented control
        seg_outer = tk.Frame(self.root, bg=HEADER_COLOR, pady=5)
        seg_outer.pack(fill="x")
        self._seg_canvas = tk.Canvas(
            seg_outer, bg=HEADER_COLOR, highlightthickness=0,
            width=WINDOW_WIDTH, height=32
        )
        self._seg_canvas.pack()
        self._seg_canvas.bind("<Button-1>", self._seg_click)
        self.tab_buttons = {}

        tk.Frame(self.root, bg=ACCENT_COLOR, height=1).pack(fill="x")

        # Scrollable task area
        container = tk.Frame(self.root, bg=BG_COLOR)
        container.pack(fill="both", expand=True)

        self.canvas = tk.Canvas(container, bg=BG_COLOR, highlightthickness=0, width=WINDOW_WIDTH)
        scrollbar = tk.Scrollbar(container, orient="vertical", command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=scrollbar.set)

        self.task_frame = tk.Frame(self.canvas, bg=BG_COLOR)
        self.canvas_window = self.canvas.create_window(
            (0, 0), window=self.task_frame, anchor="nw", width=WINDOW_WIDTH
        )
        self.canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")

        self.task_frame.bind("<Configure>", lambda e: self.canvas.configure(
            scrollregion=self.canvas.bbox("all")))
        self.canvas.bind("<Configure>", lambda e: self.canvas.itemconfig(
            self.canvas_window, width=e.width))
        self.canvas.bind("<MouseWheel>", self._on_scroll)
        self.task_frame.bind("<MouseWheel>", self._on_scroll)

        # ── Input area ───────────────────────────────────────────────────────
        input_frame = tk.Frame(self.root, bg=HEADER_COLOR, pady=6)
        input_frame.pack(fill="x")
        self._input_frame = input_frame

        self.entry = tk.Entry(
            input_frame, bg=ENTRY_BG, fg=TEXT_COLOR,
            insertbackground=TEXT_COLOR, relief="flat",
            font=("Helvetica", 11), width=10
        )
        self.entry.pack(side="left", padx=(6, 3), ipady=5)
        self.entry.bind("<Return>", self._add_task)
        self.entry.focus_set()

        tk.Button(
            input_frame, text="Add", bg=ACCENT_COLOR, fg="black",
            relief="flat", font=("Helvetica", 10, "bold"),
            cursor="hand2", command=self._add_task,
            padx=5, pady=5, bd=0, activebackground=ACCENT_COLOR,
            activeforeground="black"
        ).pack(side="left", padx=(0, 3))

        # Until button — opens calendar date picker
        self.until_btn = tk.Button(
            input_frame, text="Until", bg=BUTTON_COLOR, fg="black",
            relief="flat", font=("Helvetica", 10, "bold"),
            cursor="hand2", command=self._show_calendar_picker,
            padx=4, pady=5, bd=0, activebackground=BUTTON_COLOR,
            activeforeground="black"
        )
        self.until_btn.pack(side="left", padx=(0, 3))

        # Steps toggle button — cycles 1× → 2× → 3× → 1×
        self.steps_btn = tk.Button(
            input_frame, text="1×", bg=BUTTON_COLOR, fg="black",
            relief="flat", font=("Helvetica", 10, "bold"),
            cursor="hand2", command=self._cycle_steps,
            padx=4, pady=5, bd=0, activebackground=BUTTON_COLOR,
            activeforeground="black", width=2
        )
        self.steps_btn.pack(side="left", padx=(0, 3))

        # Timer preset button — cycles off → 5m → 10m → … → 60m → off
        self.timer_btn = tk.Button(
            input_frame, text="⏱", bg=BUTTON_COLOR, fg="black",
            relief="flat", font=("Helvetica", 10, "bold"),
            cursor="hand2", command=self._cycle_timer_preset,
            padx=3, pady=5, bd=0, activebackground=BUTTON_COLOR,
            activeforeground="black", width=3
        )
        self.timer_btn.pack(side="left", padx=(0, 4))

        self._switch_tab("Today")
        self._setup_global_hotkey()
        self.root.after(100, self._set_all_spaces)

    def _setup_global_hotkey(self):
        cmd_held = {"val": False}

        def on_press(key):
            if key in (pynput_kb.Key.cmd, pynput_kb.Key.cmd_l, pynput_kb.Key.cmd_r):
                cmd_held["val"] = True
            try:
                if cmd_held["val"] and hasattr(key, "char") and key.char == "'":
                    self.root.after(0, self._toggle_window)
            except AttributeError:
                pass

        def on_release(key):
            if key in (pynput_kb.Key.cmd, pynput_kb.Key.cmd_l, pynput_kb.Key.cmd_r):
                cmd_held["val"] = False

        listener = pynput_kb.Listener(on_press=on_press, on_release=on_release)
        listener.daemon = True
        listener.start()

    def _set_all_spaces(self):
        for window in NSApp.windows():
            window.setLevel_(NSStatusWindowLevel)
            window.setCollectionBehavior_(
                NSWindowCollectionBehaviorMoveToActiveSpace
                | NSWindowCollectionBehaviorFullScreenAuxiliary
            )

    def _toggle_window(self):
        if self.root.state() == "withdrawn":
            self.root.deiconify()
            for window in NSApp.windows():
                window.setLevel_(NSStatusWindowLevel)
                window.orderFrontRegardless()
            NSApp.activateIgnoringOtherApps_(True)
            # Restore focus header if a timer is still running
            if self._active_timer:
                self._enter_focus_mode()
                self._update_focus_header()
        else:
            self.root.withdraw()

    def _position_window(self):
        self.root.update_idletasks()
        sw = self.root.winfo_screenwidth()
        x = sw - WINDOW_WIDTH - 20
        self.root.geometry(f"{WINDOW_WIDTH}x460+{x}+50")

    def _set_sync_status(self, text, color=DONE_COLOR):
        def _apply():
            self.sync_label.config(text=text, fg=color)
            self._focus_sync_lbl.config(text=text, fg=color)
        self.root.after(0, _apply)

    # ── Steps toggle ─────────────────────────────────────────────────────────

    def _cycle_steps(self):
        self.new_task_steps = (self.new_task_steps % 3) + 1
        label = f"{self.new_task_steps}×"
        active = self.new_task_steps > 1
        self.steps_btn.config(
            text=label,
            fg="black",
            bg=ACCENT_COLOR if active else BUTTON_COLOR
        )

    # ── Timer preset toggle ───────────────────────────────────────────────────

    def _cycle_timer_preset(self):
        idx = TIMER_PRESETS.index(self.new_task_minutes) if self.new_task_minutes in TIMER_PRESETS else 0
        self.new_task_minutes = TIMER_PRESETS[(idx + 1) % len(TIMER_PRESETS)]
        if self.new_task_minutes == 0:
            self.timer_btn.config(text="⏱", fg="black", bg=BUTTON_COLOR)
        else:
            self.timer_btn.config(
                text=f"{self.new_task_minutes}m",
                fg=BG_COLOR, bg=TIMER_COLOR
            )

    # ── Timer helpers ─────────────────────────────────────────────────────────

    def _format_time(self, seconds):
        m, s = divmod(max(0, int(seconds)), 60)
        return f"{m}:{s:02d}"

    def _format_study_time(self, seconds):
        total_min = seconds // 60
        if total_min < 60:
            return f"{total_min}分"
        h = total_min // 60
        m = total_min % 60
        return f"{h}時間{m}分" if m else f"{h}時間"

    def _update_summary(self):
        if self._summary_label and self._summary_label.winfo_exists():
            self._summary_label.config(
                text=f"今日の学習: {self._format_study_time(self._total_study_seconds)}"
            )

    # ── Timer control ─────────────────────────────────────────────────────────

    def _toggle_timer(self, task):
        if self._active_timer and self._active_timer["task"] is task:
            if self._active_timer["running"]:
                self._pause_timer()
            else:
                self._resume_timer()
        else:
            self._start_timer(task)

    def _start_timer(self, task):
        if self._active_timer:
            if self._active_timer.get("after_id"):
                self.root.after_cancel(self._active_timer["after_id"])
            self._active_timer["running"] = False
        self._active_timer = {"task": task, "running": True, "after_id": None}
        self._timer_label_widget = None
        self._enter_focus_mode()
        threading.Thread(
            target=lambda: subprocess.run(
                ["afplay", "/System/Library/Sounds/Tink.aiff"],
                capture_output=True
            ),
            daemon=True
        ).start()
        self._tick()
        self._refresh_tasks()

    def _pause_timer(self):
        if not self._active_timer or not self._active_timer["running"]:
            return
        if self._active_timer.get("after_id"):
            self.root.after_cancel(self._active_timer["after_id"])
        self._active_timer["running"] = False
        self._active_timer["after_id"] = None
        self._update_focus_header()
        task = self._active_timer["task"]
        rem = task.get("timer_remaining_seconds", 0)
        if self._timer_label_widget and self._timer_label_widget.winfo_exists():
            self._timer_label_widget.config(text=f"▶ {self._format_time(rem)}")
        else:
            self._refresh_tasks()

    def _resume_timer(self):
        if not self._active_timer or self._active_timer["running"]:
            return
        self._active_timer["running"] = True
        self._tick()
        self._update_focus_header()
        task = self._active_timer["task"]
        rem = task.get("timer_remaining_seconds", 0)
        if self._timer_label_widget and self._timer_label_widget.winfo_exists():
            self._timer_label_widget.config(text=f"⏸ {self._format_time(rem)}")
        else:
            self._refresh_tasks()

    def _add_timer_time(self, task, minutes=5):
        task["timer_remaining_seconds"] = task.get("timer_remaining_seconds", 0) + minutes * 60
        task["estimated_minutes"] = task.get("estimated_minutes", 0) + minutes
        running = self._active_timer and self._active_timer["task"] is task and self._active_timer["running"]
        icon = "⏸" if running else "▶"
        rem = task.get("timer_remaining_seconds", 0)
        if self._timer_label_widget and self._timer_label_widget.winfo_exists():
            self._timer_label_widget.config(text=f"{icon} {self._format_time(rem)}")
        else:
            self._refresh_tasks()

    def _tick(self):
        if not self._active_timer or not self._active_timer["running"]:
            return
        task = self._active_timer["task"]
        rem = task.get("timer_remaining_seconds", 0) - 1
        task["timer_remaining_seconds"] = max(0, rem)
        task["timer_elapsed_seconds"] = task.get("timer_elapsed_seconds", 0) + 1
        self._total_study_seconds += 1
        self._update_summary()
        self._update_focus_header()
        if self._timer_label_widget and self._timer_label_widget.winfo_exists():
            self._timer_label_widget.config(
                text=f"⏸ {self._format_time(task['timer_remaining_seconds'])}"
            )
        if task["timer_remaining_seconds"] <= 0:
            self._timer_complete(task)
        else:
            after_id = self.root.after(1000, self._tick)
            self._active_timer["after_id"] = after_id

    # ── Notes encoding ────────────────────────────────────────────────────────

    def _parse_notes(self, notes):
        result = {}
        for m in re.finditer(r'\[(\w+):([^\]]+)\]', notes or ''):
            result[m.group(1)] = m.group(2)
        return result

    def _build_notes(self, task):
        parts = []
        if task.get("until_date"):
            parts.append(f"[until:{task['until_date']}]")
        if task.get("parent_id"):
            parts.append(f"[parent:{task['parent_id']}]")
        return "".join(parts) if parts else None

    # ── Subtask ordering & helpers ────────────────────────────────────────────

    def _ordered_visible_tasks(self, tasks):
        gid_set = {id(t) for t in tasks}
        gid_map = {t.get("google_id"): t for t in self.tasks if t.get("google_id")}
        children_map = {}
        roots = []
        for t in tasks:
            pid = t.get("parent_id")
            parent = gid_map.get(pid) if pid else None
            # Only group under parent when parent is visible AND undone
            if parent and id(parent) in gid_set and not self._task_done_today(parent):
                children_map.setdefault(pid, []).append(t)
            else:
                roots.append(t)
        roots.sort(key=self._task_done_today)
        result = []
        def flatten(t):
            result.append(t)
            for c in sorted(children_map.get(t.get("google_id"), []), key=self._task_done_today):
                flatten(c)
        for r in roots:
            flatten(r)
        return result

    def _task_depth(self, task, _visited=None):
        pid = task.get("parent_id")
        if not pid:
            return 0
        if _visited is None:
            _visited = set()
        if pid in _visited:
            return 0  # circular protection
        _visited.add(pid)
        gid_map = {t.get("google_id"): t for t in self.tasks if t.get("google_id")}
        parent = gid_map.get(pid)
        if not parent:
            return 0
        return 1 + self._task_depth(parent, _visited)

    def _parent_done(self, task):
        gid_map = {t.get("google_id"): t for t in self.tasks if t.get("google_id")}
        current = task
        visited = set()
        while True:
            pid = current.get("parent_id")
            if not pid or pid in visited:
                return True
            visited.add(pid)
            parent = gid_map.get(pid)
            if not parent:
                return True
            if not self._task_done_today(parent):
                return False
            current = parent

    def _indent_task(self, task):
        visible = self._ordered_visible_tasks(self._visible_tasks_flat())
        idx = next((i for i, t in enumerate(visible) if t is task), -1)
        if idx <= 0:
            return
        above = visible[idx - 1]
        new_pid = above.get("google_id")
        if not new_pid or new_pid == task.get("parent_id"):
            return
        # Prevent circular: above can't already be a subtask of task
        if above.get("parent_id") == task.get("google_id"):
            return
        task["parent_id"] = new_pid
        self._refresh_tasks()
        if self.service:
            threading.Thread(target=self._update_task_on_google, args=(task,), daemon=True).start()

    def _outdent_task(self, task):
        pid = task.get("parent_id")
        if not pid:
            return
        gid_map = {t.get("google_id"): t for t in self.tasks if t.get("google_id")}
        parent = gid_map.get(pid)
        if parent and parent.get("parent_id"):
            task["parent_id"] = parent["parent_id"]  # go up one level
        else:
            task.pop("parent_id", None)  # become root
        self._refresh_tasks()
        if self.service:
            threading.Thread(target=self._update_task_on_google, args=(task,), daemon=True).start()

    def _visible_tasks_flat(self):
        """Return visible tasks without subtask ordering (for indent logic)."""
        today = str(date.today())
        if self.active_tab == "Today":
            tasks = []
            for t in self.tasks:
                if t.get("until_date"):
                    if today <= t["until_date"]:
                        tasks.append(t)
                else:
                    if t.get("created_date") == today:
                        tasks.append(t)
        else:
            tasks = []
            for t in self.tasks:
                if t.get("until_date"):
                    if not t.get("permanently_done") and today <= t["until_date"] and not self._task_done_today(t):
                        tasks.append(t)
                else:
                    if not t.get("done"):
                        tasks.append(t)
        return tasks

    def _show_task_timer_picker(self, task, anchor_widget):
        popup = tk.Toplevel(self.root)
        popup.title("")
        popup.resizable(False, False)
        popup.configure(bg=HEADER_COLOR)
        popup.attributes("-topmost", True)
        popup.overrideredirect(True)

        row_frame = tk.Frame(popup, bg=HEADER_COLOR, padx=6, pady=6)
        row_frame.pack()

        def pick(minutes):
            task["estimated_minutes"] = minutes
            task["timer_remaining_seconds"] = minutes * 60
            task["timer_elapsed_seconds"] = 0
            popup.destroy()
            self._refresh_tasks()

        for m in [5, 10, 15, 20, 25, 30, 45, 60]:
            btn = tk.Button(
                row_frame, text=f"{m}m", bg=BUTTON_COLOR, fg=TEXT_COLOR,
                relief="flat", font=("Helvetica", 10, "bold"),
                cursor="hand2", padx=5, pady=4, bd=0,
                activebackground=ACCENT_COLOR, activeforeground=BG_COLOR,
                command=lambda v=m: pick(v)
            )
            btn.pack(side="left", padx=2)

        popup.update_idletasks()
        ax = anchor_widget.winfo_rootx()
        ay = anchor_widget.winfo_rooty()
        pw = popup.winfo_width()
        ph = popup.winfo_height()
        popup.geometry(f"+{ax - pw + anchor_widget.winfo_width()}+{ay - ph - 4}")
        popup.bind("<FocusOut>", lambda e: popup.destroy())
        popup.focus_set()

        for window in NSApp.windows():
            window.setLevel_(NSStatusWindowLevel + 1)

    def _stop_active_timer(self):
        if self._active_timer:
            task = self._active_timer["task"]
            elapsed = task.get("timer_elapsed_seconds", 0)
            if elapsed >= 30:
                self._record_study_session(task, elapsed)
            if self._active_timer.get("after_id"):
                self.root.after_cancel(self._active_timer["after_id"])
            self._active_timer = None
            self._timer_label_widget = None
            self._exit_focus_mode()

    # ── Focus header helpers ──────────────────────────────────────────────────

    def _enter_focus_mode(self):
        task = self._active_timer["task"] if self._active_timer else None
        if not task:
            return
        name = task["text"]
        if len(name) > 28:
            name = name[:27] + "…"
        self._focus_task_lbl.config(text=f"📚 {name}")
        self._focus_sync_lbl.config(text=self.sync_label.cget("text"))
        self._update_focus_header()
        self._normal_header.pack_forget()
        self._focus_header.pack(fill="x")

    def _exit_focus_mode(self):
        self._focus_header.pack_forget()
        self._normal_header.pack(fill="x")

    def _update_focus_header(self):
        if not self._active_timer:
            return
        task = self._active_timer["task"]
        rem     = task.get("timer_remaining_seconds", 0)
        elapsed = task.get("timer_elapsed_seconds", 0)
        running = self._active_timer.get("running", False)
        self._focus_remaining_lbl.config(text=self._format_time(rem))
        self._focus_elapsed_lbl.config(text=f"経過\n{self._format_time(elapsed)}")
        # Update circular play/pause button
        if self._focus_playpause_btn.winfo_exists():
            if running:
                self._focus_playpause_btn.itemconfig(self._pp_oval, fill=TIMER_COLOR)
                self._focus_playpause_btn.itemconfig(self._pp_text, text="⏸")
            else:
                self._focus_playpause_btn.itemconfig(self._pp_oval, fill=ACCENT_COLOR)
                self._focus_playpause_btn.itemconfig(self._pp_text, text="▶")

    def _header_playpause(self):
        if not self._active_timer:
            return
        if self._active_timer["running"]:
            self._pause_timer()
        else:
            self._resume_timer()

    def _header_stop_timer(self):
        self._stop_active_timer()
        self._refresh_tasks()

    def _header_add_5(self):
        if self._active_timer:
            self._add_timer_time(self._active_timer["task"], 5)
            self._update_focus_header()

    def _timer_complete(self, task):
        elapsed = task.get("timer_elapsed_seconds", 0)
        self._record_study_session(task, elapsed)
        today = str(date.today())
        if task.get("until_date"):
            current = task.get("daily_done", {}).get(today, 0)
            steps = task.get("steps", 1)
            new_done = current + 1
            task.setdefault("daily_done", {})[today] = new_done
            all_done = new_done >= steps
        else:
            steps = task.get("steps", 1)
            new_done = task.get("steps_done", 0) + 1
            task["steps_done"] = new_done
            all_done = new_done >= steps
            if all_done:
                task["done"] = True

        if all_done:
            self._active_timer = None
            self._timer_label_widget = None
            self._exit_focus_mode()
        else:
            estimated = task.get("estimated_minutes", 0)
            if estimated:
                task["timer_remaining_seconds"] = estimated * 60
                task["timer_elapsed_seconds"] = 0
                self._active_timer = {"task": task, "running": True, "after_id": None}
                self._timer_label_widget = None
                self._tick()
            else:
                self._active_timer = None
                self._timer_label_widget = None
                self._exit_focus_mode()

        self._refresh_tasks()
        if self.service:
            threading.Thread(target=self._update_task_on_google, args=(task,), daemon=True).start()
        title = task["text"]
        threading.Thread(
            target=lambda: subprocess.run(
                ["osascript", "-e",
                 f'display notification "タイマー完了: {title}" with title "MyTasks" sound name "Glass"'],
                capture_output=True
            ),
            daemon=True
        ).start()

    # ── Calendar picker ───────────────────────────────────────────────────────

    def _show_calendar_picker(self):
        if self._cal_popup and self._cal_popup.winfo_exists():
            self._cal_popup.destroy()
            self._cal_popup = None
            return

        popup = tk.Toplevel(self.root)
        popup.title("")
        popup.resizable(False, False)
        popup.configure(bg=HEADER_COLOR)
        popup.attributes("-topmost", True)
        self._cal_popup = popup

        today = date.today()
        view = {"year": today.year, "month": today.month}

        def render():
            for w in popup.winfo_children():
                w.destroy()

            year, month = view["year"], view["month"]
            month_name = date(year, month, 1).strftime("%B %Y")

            # Navigation header
            nav = tk.Frame(popup, bg=ACCENT_COLOR)
            nav.pack(fill="x")
            prev_lbl = tk.Label(nav, text="  ‹  ", bg=ACCENT_COLOR, fg=BG_COLOR,
                                font=("Helvetica", 14, "bold"), cursor="hand2", pady=6)
            prev_lbl.pack(side="left")
            prev_lbl.bind("<Button-1>", lambda e: go_prev())
            tk.Label(nav, text=month_name, bg=ACCENT_COLOR, fg=BG_COLOR,
                     font=("Helvetica", 12, "bold"), pady=6).pack(side="left", expand=True)
            next_lbl = tk.Label(nav, text="  ›  ", bg=ACCENT_COLOR, fg=BG_COLOR,
                                font=("Helvetica", 14, "bold"), cursor="hand2", pady=6)
            next_lbl.pack(side="right")
            next_lbl.bind("<Button-1>", lambda e: go_next())

            # Day-of-week headers
            dow_row = tk.Frame(popup, bg=HEADER_COLOR)
            dow_row.pack(fill="x", padx=8, pady=(8, 2))
            for d in ["Su", "Mo", "Tu", "We", "Th", "Fr", "Sa"]:
                tk.Label(dow_row, text=d, bg=HEADER_COLOR, fg=DONE_COLOR,
                         font=("Helvetica", 10), width=4, anchor="center").pack(side="left")

            # Calendar grid
            grid = tk.Frame(popup, bg=HEADER_COLOR)
            grid.pack(padx=8, pady=(0, 4))
            for week in _cal.monthcalendar(year, month):
                week_row = tk.Frame(grid, bg=HEADER_COLOR)
                week_row.pack()
                for day in week:
                    if day == 0:
                        tk.Label(week_row, text="", width=4, bg=HEADER_COLOR,
                                 font=("Helvetica", 11)).pack(side="left")
                    else:
                        d_obj = date(year, month, day)
                        d_str = str(d_obj)
                        is_selected = d_str == self.pending_until_date
                        is_today    = d_obj == today
                        is_past     = d_obj < today

                        if is_selected:
                            bg, fg, weight = ACCENT_COLOR, BG_COLOR, "bold"
                        elif is_today:
                            bg, fg, weight = BUTTON_COLOR, TEXT_COLOR, "bold"
                        elif is_past:
                            bg, fg, weight = HEADER_COLOR, STEP_EMPTY, "normal"
                        else:
                            bg, fg, weight = HEADER_COLOR, TEXT_COLOR, "normal"

                        day_lbl = tk.Label(
                            week_row, text=str(day), width=4,
                            bg=bg, fg=fg,
                            font=("Helvetica", 11, weight),
                            cursor="hand2" if not is_past else "arrow",
                            anchor="center", pady=4
                        )
                        day_lbl.pack(side="left")
                        if not is_past:
                            day_lbl.bind("<Button-1>", lambda e, ds=d_str: select_date(ds))

            # Clear button
            clear_row = tk.Frame(popup, bg=HEADER_COLOR)
            clear_row.pack(fill="x", padx=8, pady=(0, 8))
            clear_lbl = tk.Label(clear_row, text="Clear date", bg=HEADER_COLOR,
                                 fg=DELETE_COLOR, font=("Helvetica", 9), cursor="hand2")
            clear_lbl.pack(side="right")
            clear_lbl.bind("<Button-1>", lambda e: select_date(None))

            # Position above the Until button after layout is computed
            popup.update_idletasks()
            bx = self.until_btn.winfo_rootx()
            by = self.until_btn.winfo_rooty()
            pw = popup.winfo_width()
            ph = popup.winfo_height()
            x  = bx - pw + self.until_btn.winfo_width()
            y  = by - ph - 4
            popup.geometry(f"+{x}+{y}")

        def go_prev():
            if view["month"] == 1:
                view["month"], view["year"] = 12, view["year"] - 1
            else:
                view["month"] -= 1
            render()

        def go_next():
            if view["month"] == 12:
                view["month"], view["year"] = 1, view["year"] + 1
            else:
                view["month"] += 1
            render()

        def select_date(d_str):
            self.pending_until_date = d_str
            if d_str:
                d = date.fromisoformat(d_str)
                self.until_btn.config(
                    text=d.strftime("%b %-d"),
                    fg=BG_COLOR, bg=UNTIL_COLOR
                )
            else:
                self.until_btn.config(text="Until", fg=TEXT_COLOR, bg=BUTTON_COLOR)
            popup.destroy()
            self._cal_popup = None

        render()
        # Elevate popup above the main window (which sits at NSStatusWindowLevel)
        popup.update_idletasks()
        for window in NSApp.windows():
            window.setLevel_(NSStatusWindowLevel + 1)

    # ── Tabs ─────────────────────────────────────────────────────────────────

    def _draw_tab_bar(self):
        c = self._seg_canvas
        c.delete("all")
        n = len(TABS)
        pad = 8
        h = 28
        y0 = 2
        y1 = y0 + h
        r_outer = 14
        r_inner = 11
        total_w = WINDOW_WIDTH - pad * 2
        seg_w = total_w / n

        # Outer container pill
        _rounded_rect(c, pad, y0, pad + total_w, y1, r=r_outer,
                      fill=SEG_CONTAINER, outline="")

        # Active segment pill (shadow then fill for depth)
        ai = TABS.index(self.active_tab)
        ax0 = pad + ai * seg_w + 3
        ax1 = ax0 + seg_w - 6
        _rounded_rect(c, ax0, y0 + 2, ax1 + 1, y1 - 1, r=r_inner,
                      fill=SEG_BORDER, outline="")
        _rounded_rect(c, ax0, y0 + 1, ax1, y1 - 2, r=r_inner,
                      fill=SEG_ACTIVE_BG, outline="")

        # Dividers between inactive segments
        for i in range(1, n):
            if i != ai and i != ai + 1:
                dx = pad + i * seg_w
                c.create_line(dx, y0 + 6, dx, y1 - 6,
                              fill=SEG_BORDER, width=1)

        # Labels
        for i, tab in enumerate(TABS):
            tx = pad + (i + 0.5) * seg_w
            ty = (y0 + y1) / 2
            active = tab == self.active_tab
            c.create_text(
                tx, ty, text=tab,
                fill=ACCENT_COLOR if active else TEXT_COLOR,
                font=("Helvetica", 10, "bold") if active else ("Helvetica", 10)
            )

    def _seg_click(self, event):
        n = len(TABS)
        pad = 8
        seg_w = (WINDOW_WIDTH - pad * 2) / n
        i = int((event.x - pad) / seg_w)
        if 0 <= i < n:
            self._switch_tab(TABS[i])

    def _switch_tab(self, tab):
        self.active_tab = tab
        self._draw_tab_bar()
        self.canvas.yview_moveto(0)
        if tab == "Stats":
            self._input_frame.pack_forget()
        else:
            self._input_frame.pack(fill="x")
        self._refresh_tasks()

    def _task_done_today(self, task):
        """Return whether the task is considered done for today."""
        if task.get("until_date"):
            if task.get("permanently_done"):
                return True
            today = str(date.today())
            steps = task.get("steps", 1)
            return task.get("daily_done", {}).get(today, 0) >= steps
        return task.get("done", False)

    def _visible_tasks(self):
        today = str(date.today())
        if self.active_tab == "Today":
            tasks = []
            for t in self.tasks:
                if t.get("until_date"):
                    if today <= t["until_date"]:  # show permanently_done as crossed out
                        tasks.append(t)
                else:
                    if t.get("created_date") == today:
                        tasks.append(t)
        else:  # Incomplete
            tasks = []
            for t in self.tasks:
                if t.get("until_date"):
                    if not t.get("permanently_done") and today <= t["until_date"] and not self._task_done_today(t):
                        tasks.append(t)
                else:
                    if not t.get("done"):
                        tasks.append(t)
        return self._ordered_visible_tasks(tasks)

    # ── Google ────────────────────────────────────────────────────────────────

    def _init_google(self):
        try:
            self._set_sync_status("⟳ Connecting...", DONE_COLOR)
            self.service = get_google_service()
            self.tasklist_id = get_or_create_tasklist(self.service)
            self._pull_from_google()
            self._set_sync_status("✓ Synced", SYNC_COLOR)
            threading.Thread(target=self._sync_loop, daemon=True).start()
        except Exception as e:
            self._set_sync_status("✕ Offline", DELETE_COLOR)
            self.root.after(0, lambda: messagebox.showerror("Google Auth Error", str(e)))

    def _sync_loop(self):
        while not self._stop_sync:
            time.sleep(SYNC_INTERVAL)
            if not self._stop_sync:
                self._pull_from_google()

    def _pull_from_google(self):
        try:
            self._set_sync_status("⟳ Syncing...", DONE_COLOR)
            google_tasks = fetch_google_tasks(self.service, self.tasklist_id)
            google_map = {t["id"]: t for t in google_tasks if "id" in t}
            existing_ids = {t["google_id"] for t in self.tasks if t.get("google_id")}

            new_tasks = []
            for task in self.tasks:
                gid = task.get("google_id")
                if gid and gid in google_map:
                    gt = google_map[gid]
                    task["text"] = gt.get("title", task["text"])
                    parsed = self._parse_notes(gt.get("notes", ""))
                    if parsed.get("until"):
                        task["until_date"] = parsed["until"]
                        task.setdefault("daily_done", {})
                    if parsed.get("parent"):
                        task["parent_id"] = parsed["parent"]
                    elif "parent_id" in task and not parsed.get("parent"):
                        task.pop("parent_id", None)
                    # Only sync done state for non-recurring tasks
                    if not task.get("until_date"):
                        g_done = gt.get("status") == "completed"
                        if g_done and not task.get("done"):
                            task["steps_done"] = task.get("steps", 1)
                            task["done"] = True
                        elif not g_done and task.get("done"):
                            task["steps_done"] = 0
                            task["done"] = False
                    new_tasks.append(task)
                elif not gid:
                    new_tasks.append(task)

            for gt in google_tasks:
                gid = gt.get("id")
                if gid and gid not in existing_ids and gt.get("title"):
                    parsed = self._parse_notes(gt.get("notes", ""))
                    g_date = gt.get("updated", "")[:10]
                    entry = {
                        "text": gt["title"],
                        "done": gt.get("status") == "completed",
                        "google_id": gid,
                        "created_date": g_date,
                        "steps": 1,
                        "steps_done": 1 if gt.get("status") == "completed" else 0
                    }
                    if parsed.get("until"):
                        entry["until_date"] = parsed["until"]
                        entry["daily_done"] = {}
                        entry["done"] = False
                        entry["steps_done"] = 0
                    if parsed.get("parent"):
                        entry["parent_id"] = parsed["parent"]
                    new_tasks.append(entry)

            self.tasks = new_tasks
            self.root.after(0, self._refresh_tasks)
            self._set_sync_status("✓ Synced", SYNC_COLOR)
        except Exception:
            self._set_sync_status("✕ Sync failed", DELETE_COLOR)

    def _due_date_str(self, task):
        d = task.get("until_date") or task.get("created_date")
        return f"{d}T00:00:00.000Z" if d else None

    def _push_task_to_google(self, task):
        try:
            body = {"title": task["text"], "status": "needsAction"}
            due = self._due_date_str(task)
            if due:
                body["due"] = due
            notes = self._build_notes(task)
            if notes:
                body["notes"] = notes
            result = self.service.tasks().insert(
                tasklist=self.tasklist_id, body=body
            ).execute()
            task["google_id"] = result["id"]
        except Exception:
            pass

    def _update_task_on_google(self, task):
        try:
            gid = task.get("google_id")
            if not gid:
                return
            # Multi-day tasks stay as needsAction in Google (completion is daily/local)
            if task.get("until_date"):
                status = "needsAction"
            else:
                status = "completed" if task["done"] else "needsAction"
            body = {"id": gid, "title": task["text"], "status": status}
            due = self._due_date_str(task)
            if due:
                body["due"] = due
            notes = self._build_notes(task)
            if notes:
                body["notes"] = notes
            self.service.tasks().update(
                tasklist=self.tasklist_id, task=gid, body=body
            ).execute()
        except Exception:
            pass

    def _delete_task_on_google(self, google_id):
        try:
            self.service.tasks().delete(
                tasklist=self.tasklist_id, task=google_id
            ).execute()
        except Exception:
            pass

    # ── Task Actions ──────────────────────────────────────────────────────────

    def _add_task(self, event=None):
        text = self.entry.get().strip()
        if not text:
            return
        steps = self.new_task_steps
        task = {
            "text": text,
            "done": False,
            "google_id": None,
            "created_date": str(date.today()),
            "steps": steps,
            "steps_done": 0
        }
        if self.pending_until_date:
            task["until_date"] = self.pending_until_date
            task["daily_done"] = {}
            self.pending_until_date = None
            self.until_btn.config(text="Until", fg=TEXT_COLOR, bg=BUTTON_COLOR)

        if self.new_task_minutes > 0:
            task["estimated_minutes"] = self.new_task_minutes
            task["timer_remaining_seconds"] = self.new_task_minutes * 60
            task["timer_elapsed_seconds"] = 0

        self.tasks.insert(0, task)
        self.entry.delete(0, "end")
        self.new_task_steps = 1
        self.steps_btn.config(text="1×", fg="black", bg=BUTTON_COLOR)
        self.new_task_minutes = 0
        self.timer_btn.config(text="⏱", fg="black", bg=BUTTON_COLOR)
        self._switch_tab("Today")
        if self.service:
            threading.Thread(target=self._push_task_to_google, args=(task,), daemon=True).start()

    def _advance_step(self, task):
        if not self._parent_done(task):
            return
        if task.get("until_date"):
            today = str(date.today())
            daily = task.setdefault("daily_done", {})
            steps = task.get("steps", 1)
            current = daily.get(today, 0)
            if current >= steps:
                daily[today] = 0  # reset for today
            else:
                daily[today] = current + 1
        else:
            steps = task.get("steps", 1)
            if task.get("done"):
                task["steps_done"] = 0
                task["done"] = False
            else:
                task["steps_done"] = task.get("steps_done", 0) + 1
                if task["steps_done"] >= steps:
                    task["steps_done"] = steps
                    task["done"] = True
        if self._active_timer and self._active_timer["task"] is task:
            self._stop_active_timer()
        if self._task_done_today(task):
            self._release_subtasks(task)
        self._refresh_tasks()
        if self.service:
            threading.Thread(target=self._update_task_on_google, args=(task,), daemon=True).start()

    def _move_to_today(self, task):
        task["created_date"] = str(date.today())
        self._refresh_tasks()
        if self.service:
            threading.Thread(target=self._update_task_on_google, args=(task,), daemon=True).start()

    def _cycle_task_steps(self, task):
        new_steps = (task.get("steps", 1) % 3) + 1
        task["steps"] = new_steps
        if task.get("until_date"):
            today = str(date.today())
            task.setdefault("daily_done", {})[today] = min(
                task["daily_done"].get(today, 0), new_steps
            )
        else:
            task["steps_done"] = min(task.get("steps_done", 0), new_steps)
            task["done"] = task["steps_done"] >= new_steps
        self._refresh_tasks()
        if self.service:
            threading.Thread(target=self._update_task_on_google, args=(task,), daemon=True).start()

    def _finish_recurring(self, task):
        task["permanently_done"] = not task.get("permanently_done", False)
        self._refresh_tasks()

    def _delete_task(self, task):
        if self._active_timer and self._active_timer["task"] is task:
            self._stop_active_timer()
        self.tasks.remove(task)
        self._refresh_tasks()
        gid = task.get("google_id")
        if self.service and gid:
            threading.Thread(target=self._delete_task_on_google, args=(gid,), daemon=True).start()

    def _clear_completed(self):
        to_delete = [t for t in self.tasks if t.get("done")]
        self.tasks  = [t for t in self.tasks if not t.get("done")]
        self._refresh_tasks()
        if self.service:
            for task in to_delete:
                gid = task.get("google_id")
                if gid:
                    threading.Thread(target=self._delete_task_on_google, args=(gid,), daemon=True).start()

    def _start_edit(self, task, row, text_lbl):
        text_lbl.pack_forget()
        edit_entry = tk.Entry(
            row, bg=ENTRY_BG, fg=TEXT_COLOR,
            insertbackground=TEXT_COLOR, relief="flat",
            font=("Helvetica", 11)
        )
        edit_entry.insert(0, task["text"])
        edit_entry.pack(side="left", fill="x", expand=True, ipady=3)
        edit_entry.focus_set()
        edit_entry.select_range(0, "end")

        def save(event=None):
            new_text = edit_entry.get().strip()
            if new_text:
                task["text"] = new_text
                if self.service:
                    threading.Thread(target=self._update_task_on_google, args=(task,), daemon=True).start()
            edit_entry.destroy()
            done = self._task_done_today(task)
            text_lbl.config(
                text=task["text"],
                fg=DONE_COLOR if done else TEXT_COLOR,
                font=font.Font(family="Helvetica", size=11, overstrike=done)
            )
            text_lbl.pack(side="left", fill="x", expand=True)

        edit_entry.bind("<Return>", save)
        edit_entry.bind("<Escape>", lambda e: save())
        edit_entry.bind("<FocusOut>", save)

    # ── Card canvas factory ───────────────────────────────────────────────────

    def _make_card_canvas(self, depth=0, lifted=False):
        """Return (canvas, inner_frame) for a rounded-card task row."""
        depth_bg = DEPTH_BG[min(depth, len(DEPTH_BG) - 1)]
        card_w   = WINDOW_WIDTH - 22 - depth * 16
        sh_off   = 4 if lifted else 2
        sh_col   = CARD_LIFT_SHADOW if lifted else CARD_SHADOW

        cv = tk.Canvas(self.task_frame, bg=BG_COLOR,
                       highlightthickness=0, bd=0,
                       width=card_w + sh_off + 4, height=52)
        cv.pack(fill="x", padx=(8 + depth * 16, 8), pady=(5, 0))

        frame = tk.Frame(cv, bg=depth_bg)
        cv.create_window(2, 2, window=frame, anchor="nw",
                         width=card_w - 4, tags="content")

        def redraw(event=None):
            fh = frame.winfo_reqheight()
            if fh < 4:
                return
            h = fh + 8
            cv.configure(height=h + sh_off + 4)
            cv.delete("shapes")
            _rounded_rect(cv, sh_off + 1, sh_off + 1,
                          card_w + sh_off - 1, h + sh_off - 1,
                          r=CARD_RADIUS, fill=sh_col, outline="", tags="shapes")
            _rounded_rect(cv, 1, 1, card_w - 1, h,
                          r=CARD_RADIUS, fill=depth_bg, outline="", tags="shapes")
            cv.tag_lower("shapes")

        frame.bind("<Configure>", redraw)
        return cv, frame

    # ── Subtask release ───────────────────────────────────────────────────────

    def _release_subtasks(self, task):
        """When a task is completed, remove parent_id from its direct children."""
        gid = task.get("google_id")
        if not gid:
            return
        for t in self.tasks:
            if t.get("parent_id") == gid:
                t.pop("parent_id", None)
                if self.service:
                    threading.Thread(
                        target=self._update_task_on_google, args=(t,), daemon=True
                    ).start()

    # ── Study log ────────────────────────────────────────────────────────────

    def _load_study_log(self):
        try:
            with open(STUDY_LOG_PATH) as f:
                return json.load(f)
        except Exception:
            return {}

    def _save_study_log(self):
        try:
            with open(STUDY_LOG_PATH, "w") as f:
                json.dump(self._study_log, f)
        except Exception:
            pass

    def _record_study_session(self, task, elapsed_seconds):
        if elapsed_seconds < 30:
            return
        today = str(date.today())
        self._study_log.setdefault(today, []).append({
            "task":    task.get("text", ""),
            "seconds": int(elapsed_seconds),
        })
        threading.Thread(target=self._save_study_log, daemon=True).start()

    # ── Stats rendering ───────────────────────────────────────────────────────

    def _log_day_seconds(self, d):
        """Total study seconds for a date string YYYY-MM-DD."""
        return sum(s.get("seconds", 0) for s in self._study_log.get(d, []))

    def _log_day_sessions(self, d):
        return len(self._study_log.get(d, []))

    def _set_stats_view(self, view):
        self._stats_view = view
        self._refresh_tasks()

    def _render_stats(self):
        W = WINDOW_WIDTH - 16

        # ── Sub-view toggle ────────────────────────────────────────────────
        nav = tk.Frame(self.task_frame, bg=BG_COLOR)
        nav.pack(fill="x", padx=8, pady=(10, 6))
        for v in ("Day", "Week", "Month", "Year"):
            active = (v.lower() == self._stats_view)
            lbl = tk.Label(nav, text=v,
                           bg=ACCENT_COLOR if active else HEADER_COLOR,
                           fg="white" if active else TEXT_COLOR,
                           font=("Helvetica", 10, "bold" if active else "normal"),
                           padx=10, pady=4, cursor="hand2", relief="flat")
            lbl.pack(side="left", padx=2)
            lbl.bind("<Button-1>", lambda e, vv=v.lower(): self._set_stats_view(vv))

        if   self._stats_view == "day":   self._render_stats_day(W)
        elif self._stats_view == "week":  self._render_stats_week(W)
        elif self._stats_view == "month": self._render_stats_month(W)
        elif self._stats_view == "year":  self._render_stats_year(W)

    # ── Day ───────────────────────────────────────────────────────────────────
    def _render_stats_day(self, W):
        today = date.today() + timedelta(days=self._stats_week_offset)  # reuse offset
        d = str(today)
        sessions = self._study_log.get(d, [])
        total_sec = sum(s.get("seconds", 0) for s in sessions)

        # Navigation row
        self._stats_nav_row(
            f"{today.strftime('%B %-d, %Y')}",
            lambda: self._stats_nav(-1, "day"), lambda: self._stats_nav(1, "day")
        )

        # Summary
        summary = tk.Label(self.task_frame,
                           text=f"Total: {self._format_study_time(total_sec)}  •  {len(sessions)} sessions",
                           bg=BG_COLOR, fg=TIMER_COLOR,
                           font=("Helvetica", 11, "bold"))
        summary.pack(pady=(4, 8))

        if not sessions:
            tk.Label(self.task_frame, text="No study sessions recorded.",
                     bg=BG_COLOR, fg=DONE_COLOR, font=("Helvetica", 10)).pack(pady=20)
            return

        for s in sessions:
            row = tk.Frame(self.task_frame, bg=HEADER_COLOR, pady=4, padx=8)
            row.pack(fill="x", padx=8, pady=2)
            tk.Label(row, text=s.get("task", ""), bg=HEADER_COLOR,
                     fg=TEXT_COLOR, font=("Helvetica", 10),
                     anchor="w").pack(side="left", fill="x", expand=True)
            tk.Label(row, text=self._format_study_time(s.get("seconds", 0)),
                     bg=HEADER_COLOR, fg=TIMER_COLOR,
                     font=("Helvetica", 10, "bold")).pack(side="right")

    # ── Week ──────────────────────────────────────────────────────────────────
    def _render_stats_week(self, W):
        today = date.today()
        week_start = today - timedelta(days=today.weekday()) + timedelta(weeks=self._stats_week_offset)
        week_end   = week_start + timedelta(days=6)

        self._stats_nav_row(
            f"{week_start.strftime('%b %-d')} – {week_end.strftime('%b %-d, %Y')}",
            lambda: self._stats_nav(-1, "week"), lambda: self._stats_nav(1, "week")
        )

        days     = [week_start + timedelta(days=i) for i in range(7)]
        day_secs = [self._log_day_seconds(str(d)) for d in days]
        day_sess = [self._log_day_sessions(str(d)) for d in days]
        max_sec  = max(day_secs) if any(day_secs) else 1

        BAR_H    = 90
        bar_w    = (W - 16) // 7
        cv_w     = bar_w * 7 + 16
        cv_h     = BAR_H + 44
        cv = tk.Canvas(self.task_frame, bg=BG_COLOR, width=cv_w, height=cv_h,
                       highlightthickness=0)
        cv.pack(pady=(6, 4))

        day_names = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"]
        for i, (d, secs, sess) in enumerate(zip(days, day_secs, day_sess)):
            x0 = 8 + i * bar_w
            x_mid = x0 + bar_w // 2
            is_today = (d == today)
            label_fg = ACCENT_COLOR if is_today else DONE_COLOR

            # bar
            if secs > 0:
                bh = max(6, int(BAR_H * secs / max_sec))
                cv.create_rectangle(x0 + 4, BAR_H - bh + 2, x0 + bar_w - 4, BAR_H + 2,
                                    fill=TIMER_COLOR, outline="", width=0)
                # session count
                cv.create_text(x_mid, BAR_H - bh - 4, text=str(sess),
                               fill=ACCENT_COLOR, font=("Helvetica", 8, "bold"))

            # day name
            cv.create_text(x_mid, BAR_H + 12, text=day_names[i],
                           fill=label_fg,
                           font=("Helvetica", 9, "bold" if is_today else "normal"))
            # time label
            cv.create_text(x_mid, BAR_H + 26, text=self._fmt_mins(secs) if secs else "",
                           fill=TIMER_COLOR, font=("Helvetica", 8))

        # week total
        total_sec = sum(day_secs)
        tk.Label(self.task_frame,
                 text=f"Week total: {self._format_study_time(total_sec)}",
                 bg=BG_COLOR, fg=DONE_COLOR, font=("Helvetica", 9)).pack(pady=(0, 8))

    # ── Month ─────────────────────────────────────────────────────────────────
    def _render_stats_month(self, W):
        today = date.today()
        # derive target month
        y, m = today.year, today.month
        offset = self._stats_month_offset
        m += offset
        while m > 12: m -= 12; y += 1
        while m < 1:  m += 12; y -= 1

        self._stats_nav_row(
            f"{date(y, m, 1).strftime('%B %Y')}",
            lambda: self._stats_nav(-1, "month"), lambda: self._stats_nav(1, "month")
        )

        _, days_in_month = _cal.monthrange(y, m)
        first_wd = date(y, m, 1).weekday()   # 0=Mon

        cell_w = (W - 16) // 7
        cell_h = 34
        rows   = (first_wd + days_in_month + 6) // 7
        cv_h   = 20 + rows * cell_h + 4
        cv = tk.Canvas(self.task_frame, bg=BG_COLOR, width=W, height=cv_h,
                       highlightthickness=0)
        cv.pack(pady=(4, 4))

        # Day-of-week headers
        for i, dn in enumerate(["Mo", "Tu", "We", "Th", "Fr", "Sa", "Su"]):
            cv.create_text(8 + i * cell_w + cell_w // 2, 10,
                           text=dn, fill=DONE_COLOR, font=("Helvetica", 8, "bold"))

        # Find max seconds this month for intensity scaling
        month_secs = []
        for day in range(1, days_in_month + 1):
            month_secs.append(self._log_day_seconds(str(date(y, m, day))))
        max_sec = max(month_secs) if any(month_secs) else 1

        def intensity_color(secs):
            if secs == 0:
                return HEADER_COLOR
            ratio = min(1.0, secs / max_sec)
            # blend from HEADER_COLOR to TIMER_COLOR (#3d7a5e)
            r0, g0, b0 = 0xdf, 0xc9, 0xa8
            r1, g1, b1 = 0x3d, 0x7a, 0x5e
            r = int(r0 + (r1 - r0) * ratio)
            g = int(g0 + (g1 - g0) * ratio)
            b = int(b0 + (b1 - b0) * ratio)
            return f"#{r:02x}{g:02x}{b:02x}"

        for day in range(1, days_in_month + 1):
            wd     = (first_wd + day - 1) % 7
            row_i  = (first_wd + day - 1) // 7
            x0     = 8 + wd * cell_w
            y0     = 20 + row_i * cell_h
            d_str  = str(date(y, m, day))
            secs   = self._log_day_seconds(d_str)
            sess   = self._log_day_sessions(d_str)
            is_today_cell = (date(y, m, day) == today)
            bg = intensity_color(secs)

            cv.create_rectangle(x0 + 1, y0 + 1, x0 + cell_w - 1, y0 + cell_h - 1,
                                 fill=bg, outline=ACCENT_COLOR if is_today_cell else "",
                                 width=2 if is_today_cell else 0)
            cv.create_text(x0 + cell_w // 2, y0 + 10,
                           text=str(day),
                           fill="white" if secs > max_sec * 0.5 else TEXT_COLOR,
                           font=("Helvetica", 9, "bold" if is_today_cell else "normal"))
            if sess:
                cv.create_text(x0 + cell_w // 2, y0 + 23,
                               text=f"{sess}x",
                               fill="white" if secs > max_sec * 0.5 else TIMER_COLOR,
                               font=("Helvetica", 7))

        # month total
        total_sec = sum(month_secs)
        tk.Label(self.task_frame,
                 text=f"Month total: {self._format_study_time(total_sec)}",
                 bg=BG_COLOR, fg=DONE_COLOR, font=("Helvetica", 9)).pack(pady=(0, 8))

    # ── Year ──────────────────────────────────────────────────────────────────
    def _render_stats_year(self, W):
        today = date.today()
        y = today.year + self._stats_year_offset

        self._stats_nav_row(
            str(y),
            lambda: self._stats_nav(-1, "year"), lambda: self._stats_nav(1, "year")
        )

        month_secs  = []
        month_sess  = []
        for m in range(1, 13):
            _, days_in = _cal.monthrange(y, m)
            secs = sum(self._log_day_seconds(str(date(y, m, d))) for d in range(1, days_in + 1))
            sess = sum(self._log_day_sessions(str(date(y, m, d))) for d in range(1, days_in + 1))
            month_secs.append(secs)
            month_sess.append(sess)

        max_sec = max(month_secs) if any(month_secs) else 1

        BAR_H   = 80
        bar_w   = (W - 16) // 12
        cv_w    = bar_w * 12 + 16
        cv_h    = BAR_H + 44
        cv = tk.Canvas(self.task_frame, bg=BG_COLOR, width=cv_w, height=cv_h,
                       highlightthickness=0)
        cv.pack(pady=(6, 4))

        month_names = ["Jan","Feb","Mar","Apr","May","Jun",
                       "Jul","Aug","Sep","Oct","Nov","Dec"]
        for i, (secs, sess) in enumerate(zip(month_secs, month_sess)):
            x0 = 8 + i * bar_w
            x_mid = x0 + bar_w // 2
            is_cur = (i + 1 == today.month and y == today.year)
            if secs > 0:
                bh = max(4, int(BAR_H * secs / max_sec))
                cv.create_rectangle(x0 + 2, BAR_H - bh + 2, x0 + bar_w - 2, BAR_H + 2,
                                    fill=TIMER_COLOR, outline="")
                cv.create_text(x_mid, BAR_H - bh - 5, text=str(sess),
                               fill=ACCENT_COLOR, font=("Helvetica", 7, "bold"))
            cv.create_text(x_mid, BAR_H + 12, text=month_names[i],
                           fill=ACCENT_COLOR if is_cur else DONE_COLOR,
                           font=("Helvetica", 8, "bold" if is_cur else "normal"))
            if secs:
                cv.create_text(x_mid, BAR_H + 26, text=self._fmt_mins(secs),
                               fill=TIMER_COLOR, font=("Helvetica", 7))

        total_sec = sum(month_secs)
        tk.Label(self.task_frame,
                 text=f"Year total: {self._format_study_time(total_sec)}",
                 bg=BG_COLOR, fg=DONE_COLOR, font=("Helvetica", 9)).pack(pady=(0, 8))

    # ── Stats helpers ─────────────────────────────────────────────────────────
    def _stats_nav_row(self, title, on_prev, on_next):
        row = tk.Frame(self.task_frame, bg=BG_COLOR)
        row.pack(fill="x", padx=8, pady=(2, 0))
        tk.Label(row, text="‹", bg=BG_COLOR, fg=ACCENT_COLOR,
                 font=("Helvetica", 16), cursor="hand2").pack(side="left", padx=4)
        tk.Label(row, text=title, bg=BG_COLOR, fg=TEXT_COLOR,
                 font=("Helvetica", 11, "bold")).pack(side="left", expand=True)
        tk.Label(row, text="›", bg=BG_COLOR, fg=ACCENT_COLOR,
                 font=("Helvetica", 16), cursor="hand2").pack(side="right", padx=4)
        # bind after packing so we can reference the labels
        row.winfo_children()[0].bind("<Button-1>", lambda e: on_prev())
        row.winfo_children()[2].bind("<Button-1>", lambda e: on_next())

    def _stats_nav(self, delta, view):
        if view == "day":
            self._stats_week_offset += delta   # reuse for day
        elif view == "week":
            self._stats_week_offset += delta
        elif view == "month":
            self._stats_month_offset += delta
        elif view == "year":
            self._stats_year_offset += delta
        self._refresh_tasks()

    def _fmt_mins(self, seconds):
        m = seconds // 60
        if m >= 60:
            return f"{m//60}h{m%60:02d}m" if m % 60 else f"{m//60}h"
        return f"{m}m"

    # ── Render ────────────────────────────────────────────────────────────────

    def _refresh_tasks(self):
        for widget in self.task_frame.winfo_children():
            widget.destroy()

        self._task_rows = []

        if self.active_tab == "Stats":
            self._render_stats()
            return

        visible = self._visible_tasks()

        if self._drag_task is not None and self._drag_task in visible:
            drag_task = self._drag_task
            tgt = self._drag_target_idx if self._drag_target_idx is not None else self._drag_source_idx
            display = [t for t in visible if t is not drag_task]
            tgt = max(0, min(tgt, len(display)))
            display.insert(tgt, None)
            for item in display:
                if item is None:
                    if self._drag_indent:
                        visible_without = [t for t in visible if t is not drag_task]
                        tgt_c = max(0, min(tgt, len(visible_without)))
                        above = visible_without[tgt_c - 1] if tgt_c > 0 else None
                        tdepth = (self._task_depth(above) + 1) if above else 0
                    else:
                        tdepth = self._task_depth(drag_task)
                    self._make_lifted_task_row(drag_task, target_depth=tdepth)
                else:
                    self._make_task_row(item)
        elif not visible:
            empty_msgs = {
                "Today":      "No tasks for today.\nAdd one below!",
                "Incomplete": "No incomplete tasks.",
                "Done":       "No completed tasks yet.",
                "Stats":      "",
            }
            lbl = tk.Label(
                self.task_frame, text=empty_msgs[self.active_tab],
                bg=BG_COLOR, fg=DONE_COLOR, font=("Helvetica", 10),
                wraplength=WINDOW_WIDTH - 20, pady=16, justify="center"
            )
            lbl.pack()
            lbl.bind("<MouseWheel>", self._on_scroll)
        else:
            for task in visible:
                self._make_task_row(task)

    def _days_left_text(self, until_date_str):
        until = date.fromisoformat(until_date_str)
        delta = (until - date.today()).days
        if delta == 0:
            return "last day"
        elif delta == 1:
            return "1 day left"
        else:
            return f"{delta} days left"

    def _make_task_row(self, task):
        is_recurring = bool(task.get("until_date"))
        today_str    = str(date.today())

        if is_recurring:
            steps      = task.get("steps", 1)
            if task.get("permanently_done"):
                steps_done = steps
                done       = True
            else:
                steps_done = task.get("daily_done", {}).get(today_str, 0)
                done       = steps_done >= steps
        else:
            steps      = task.get("steps", 1)
            steps_done = task.get("steps_done", 0)
            done       = task.get("done", False)

        depth       = self._task_depth(task)
        is_subtask  = depth > 0
        is_locked   = is_subtask and not self._parent_done(task)
        row_bg      = DEPTH_BG[min(depth, len(DEPTH_BG) - 1)]

        card_cv, row = self._make_card_canvas(depth=depth, lifted=False)
        self._task_rows.append((task, row))

        # ── Outdent button (subtasks only) ───────────────────────────────────
        if is_subtask:
            indent_btn = tk.Label(
                row, text="⇤", bg=row_bg, fg=ACCENT_COLOR,
                font=("Helvetica", 10), cursor="hand2", padx=2
            )
            indent_btn.pack(side="left")
            indent_btn.bind("<Button-1>", lambda e, t=task: self._outdent_task(t))
            indent_btn.bind("<MouseWheel>", self._on_scroll)
        else:
            indent_btn = tk.Label(row, text="", bg=row_bg, width=1)
            indent_btn.pack(side="left")

        # ── Drag handle ───────────────────────────────────────────────────────
        drag_handle = tk.Label(
            row, text="⠿", bg=row_bg, fg=DONE_COLOR,
            font=("Helvetica", 12), cursor="fleur", padx=2
        )
        drag_handle.pack(side="left")
        drag_handle.bind("<ButtonPress-1>", lambda e, t=task: self._drag_start(e, t))
        drag_handle.bind("<MouseWheel>", self._on_scroll)

        # ── Progress indicator ────────────────────────────────────────────────
        prog_cursor = "arrow" if is_locked else "hand2"
        prog_frame = tk.Frame(row, bg=row_bg, cursor=prog_cursor)
        prog_frame.pack(side="left", padx=(0, 6))

        if is_locked:
            tk.Label(prog_frame, text="🔒", bg=row_bg,
                     font=("Helvetica", 11)).pack()
        elif steps == 1:
            sym = tk.Label(
                prog_frame,
                text="✓" if done else "○",
                bg=row_bg,
                fg=ACCENT_COLOR if done else DONE_COLOR,
                font=("Helvetica", 12),
                cursor="hand2"
            )
            sym.pack()
        else:
            for i in range(steps):
                filled = i < steps_done
                dot = tk.Label(
                    prog_frame,
                    text="●" if filled else "○",
                    bg=row_bg,
                    fg=ACCENT_COLOR if filled else STEP_EMPTY,
                    font=("Helvetica", 11),
                    cursor="hand2"
                )
                dot.pack(side="left")
                if not is_locked:
                    dot.bind("<Button-1>", lambda e, t=task: self._advance_step(t))
                dot.bind("<MouseWheel>", self._on_scroll)

        if not is_locked:
            prog_frame.bind("<Button-1>", lambda e, t=task: self._advance_step(t))
            for child in prog_frame.winfo_children():
                child.bind("<Button-1>", lambda e, t=task: self._advance_step(t))

        # ── Delete button (pack right first so text doesn't push it off) ──────
        del_btn = tk.Label(
            row, text="✕", bg=row_bg, fg=DELETE_COLOR,
            font=("Helvetica", 10), cursor="hand2", padx=4
        )
        del_btn.pack(side="right")
        del_btn.bind("<Button-1>", lambda e, t=task: self._delete_task(t))

        # ── Per-task steps cycle ───────────────────────────────────────────────
        steps_lbl = tk.Label(
            row, text=f"{steps}×", bg=row_bg,
            fg=ACCENT_COLOR if steps > 1 else DONE_COLOR,
            font=("Helvetica", 9, "bold"), cursor="hand2", padx=2
        )
        steps_lbl.pack(side="right")
        steps_lbl.bind("<Button-1>", lambda e, t=task: self._cycle_task_steps(t))

        # ── Days left badge + finish button (recurring tasks only) ───────────
        if is_recurring:
            finish_btn = tk.Label(
                row, text="✓✓", bg=row_bg, fg=SYNC_COLOR,
                font=("Helvetica", 9, "bold"), cursor="hand2", padx=2
            )
            finish_btn.pack(side="right")
            finish_btn.bind("<Button-1>", lambda e, t=task: self._finish_recurring(t))
            finish_btn.bind("<MouseWheel>", self._on_scroll)

            days_text = self._days_left_text(task["until_date"])
            days_lbl = tk.Label(
                row, text=days_text, bg=row_bg, fg=UNTIL_COLOR,
                font=("Helvetica", 8), padx=2
            )
            days_lbl.pack(side="right")
            days_lbl.bind("<MouseWheel>", self._on_scroll)

        # ── Timer display ─────────────────────────────────────────────────────
        extra_widgets = []
        timer_widgets = []
        if not task.get("estimated_minutes"):
            add_timer_lbl = tk.Label(
                row, text="⏱", bg=row_bg, fg=DONE_COLOR,
                font=("Helvetica", 10), cursor="hand2", padx=2
            )
            add_timer_lbl.pack(side="right")
            add_timer_lbl.bind("<Button-1>", lambda e, t=task, w=add_timer_lbl: self._show_task_timer_picker(t, w))
            add_timer_lbl.bind("<MouseWheel>", self._on_scroll)
            timer_widgets.append(add_timer_lbl)
        elif task.get("estimated_minutes"):
            is_active  = self._active_timer and self._active_timer["task"] is task
            is_running = is_active and self._active_timer["running"]
            rem        = task.get("timer_remaining_seconds", 0)

            if is_active:
                add_btn = tk.Label(
                    row, text="+5", bg=row_bg, fg=TIMER_COLOR,
                    font=("Helvetica", 9), cursor="hand2", padx=2
                )
                add_btn.pack(side="right")
                add_btn.bind("<Button-1>", lambda e, t=task: self._add_timer_time(t, 5))
                add_btn.bind("<MouseWheel>", self._on_scroll)
                timer_widgets.append(add_btn)

                icon = "⏸" if is_running else "▶"
                timer_lbl = tk.Label(
                    row, text=f"{icon} {self._format_time(rem)}", bg=row_bg,
                    fg=TIMER_COLOR, font=("Helvetica", 9, "bold"), cursor="hand2", padx=2
                )
                timer_lbl.pack(side="right")
                timer_lbl.bind("<Button-1>", lambda e, t=task: self._toggle_timer(t))
                timer_lbl.bind("<MouseWheel>", self._on_scroll)
                timer_widgets.append(timer_lbl)
                self._timer_label_widget = timer_lbl
            else:
                est = task.get("estimated_minutes", 0)
                timer_lbl = tk.Label(
                    row, text=f"⏱{est}m", bg=row_bg, fg=DONE_COLOR,
                    font=("Helvetica", 9), cursor="hand2", padx=2
                )
                timer_lbl.pack(side="right")
                timer_lbl.bind("<Button-1>", lambda e, t=task: self._toggle_timer(t))
                timer_lbl.bind("<MouseWheel>", self._on_scroll)
                timer_widgets.append(timer_lbl)

        # ── Move to Today button (Incomplete tab, non-recurring) ──────────────
        if self.active_tab == "Incomplete" and not is_recurring and task.get("created_date") != today_str:
            today_btn = tk.Label(
                row, text="→ Today", bg=row_bg, fg=SYNC_COLOR,
                font=("Helvetica", 9, "bold"), cursor="hand2", padx=4
            )
            today_btn.pack(side="right")
            today_btn.bind("<Button-1>", lambda e, t=task: self._move_to_today(t))
            today_btn.bind("<MouseWheel>", self._on_scroll)
            extra_widgets.append(today_btn)

        # ── Task text ─────────────────────────────────────────────────────────
        text_color = DONE_COLOR if done else TEXT_COLOR
        text_font  = font.Font(family="Helvetica", size=11, overstrike=done)
        text_lbl = tk.Label(
            row, text=task["text"], bg=row_bg, fg=text_color,
            font=text_font, anchor="w", wraplength=130,
            justify="left", cursor="xterm"
        )
        text_lbl.pack(side="left", fill="x", expand=True)
        text_lbl.bind("<Button-1>", lambda e, t=task, r=row, l=text_lbl: self._start_edit(t, r, l))

        for w in (card_cv, row, prog_frame, text_lbl, del_btn, steps_lbl, indent_btn, *extra_widgets, *timer_widgets):
            w.bind("<MouseWheel>", self._on_scroll)

    def _make_lifted_task_row(self, task, target_depth=None):
        is_recurring = bool(task.get("until_date"))
        today_str    = str(date.today())

        if is_recurring:
            steps      = task.get("steps", 1)
            steps_done = task.get("daily_done", {}).get(today_str, 0)
            done       = steps_done >= steps
        else:
            steps      = task.get("steps", 1)
            steps_done = task.get("steps_done", 0)
            done       = task.get("done", False)

        depth  = target_depth if target_depth is not None else self._task_depth(task)
        row_bg = DEPTH_BG[min(depth, len(DEPTH_BG) - 1)]

        card_cv, row = self._make_card_canvas(depth=depth, lifted=True)

        if depth > 0:
            tk.Label(row, text="↳", bg=row_bg, fg=ACCENT_COLOR,
                     font=("Helvetica", 11, "bold"), padx=4).pack(side="left")

        tk.Label(row, text="⠿", bg=row_bg, fg=ACCENT_COLOR,
                 font=("Helvetica", 12), padx=2).pack(side="left")

        if steps == 1:
            tk.Label(row, text="✓" if done else "○",
                     bg=row_bg, fg=ACCENT_COLOR if done else DONE_COLOR,
                     font=("Helvetica", 13)).pack(side="left", padx=(0, 6))
        else:
            for i in range(steps):
                tk.Label(row, text="●" if i < steps_done else "○",
                         bg=row_bg,
                         fg=ACCENT_COLOR if i < steps_done else STEP_EMPTY,
                         font=("Helvetica", 12)).pack(side="left")

        lf = font.Font(family="Helvetica", size=12, overstrike=done)
        tk.Label(row, text=task["text"], bg=row_bg,
                 fg=DONE_COLOR if done else TEXT_COLOR,
                 font=lf, anchor="w", wraplength=190,
                 justify="left").pack(side="left", fill="x", expand=True, padx=4)

        for w in (card_cv, row):
            w.bind("<MouseWheel>", self._on_scroll)

    # ── Drag and drop ─────────────────────────────────────────────────────────

    def _drag_start(self, event, task):
        visible = self._visible_tasks()
        if task not in visible:
            return
        self._drag_task = task
        self._drag_source_idx = visible.index(task)
        self._drag_target_idx = self._drag_source_idx
        self._drag_indent = False
        self._create_ghost(task, event)
        self.root.bind("<B1-Motion>", self._drag_motion)
        self.root.bind("<ButtonRelease-1>", self._drag_end)
        self._refresh_tasks()

    def _create_ghost(self, task, event):
        if self._ghost:
            self._ghost.destroy()
        ghost = tk.Toplevel(self.root)
        ghost.overrideredirect(True)
        ghost.attributes("-alpha", 0.88)
        ghost.attributes("-topmost", True)
        ghost.configure(bg=DEPTH_BG[0])

        is_recurring = bool(task.get("until_date"))
        today_str    = str(date.today())

        if is_recurring:
            steps      = task.get("steps", 1)
            steps_done = task.get("daily_done", {}).get(today_str, 0)
            done       = steps_done >= steps
        else:
            steps      = task.get("steps", 1)
            steps_done = task.get("steps_done", 0)
            done       = task.get("done", False)

        ghost_bg = DEPTH_BG[0]
        frame = tk.Frame(ghost, bg=ghost_bg, pady=6, padx=8)
        frame.pack()
        self._ghost_frame = frame

        tk.Label(frame, text="⠿", bg=ghost_bg, fg=DONE_COLOR,
                 font=("Helvetica", 12), padx=2).pack(side="left")

        if steps == 1:
            tk.Label(frame, text="✓" if done else "○",
                     bg=ghost_bg, fg=ACCENT_COLOR if done else DONE_COLOR,
                     font=("Helvetica", 12)).pack(side="left", padx=(0, 6))
        else:
            for i in range(steps):
                tk.Label(frame, text="●" if i < steps_done else "○",
                         bg=ghost_bg,
                         fg=ACCENT_COLOR if i < steps_done else STEP_EMPTY,
                         font=("Helvetica", 11)).pack(side="left")

        gf = font.Font(family="Helvetica", size=12, overstrike=done)
        text_lbl = tk.Label(frame, text=task["text"], bg=ghost_bg,
                            fg=DONE_COLOR if done else TEXT_COLOR,
                            font=gf, wraplength=180)
        text_lbl.pack(side="left", padx=4)
        self._ghost_text_lbl = text_lbl

        ghost.update_idletasks()
        self._ghost_w = max(ghost.winfo_reqwidth(), 180)
        self._ghost_h = ghost.winfo_reqheight()
        cx = event.widget.winfo_pointerx()
        cy = event.widget.winfo_pointery()
        ghost.geometry(f"{self._ghost_w}x{self._ghost_h}+{cx - self._ghost_w//2}+{cy - self._ghost_h//2}")
        ghost.lift()
        self._ghost = ghost

    def _drag_motion(self, event):
        if self._drag_task is None:
            return
        cx = event.widget.winfo_pointerx()
        cy = event.widget.winfo_pointery()

        if self._ghost:
            self._ghost.geometry(f"+{cx - self._ghost_w//2}+{cy - self._ghost_h//2}")

        target_idx = len(self._task_rows)
        for i, (_, row) in enumerate(self._task_rows):
            if cy < row.winfo_rooty() + row.winfo_height() / 2:
                target_idx = i
                break

        new_indent = (cx - self.root.winfo_rootx()) > INDENT_THRESHOLD

        changed = (target_idx != self._drag_target_idx or new_indent != self._drag_indent)
        if changed:
            self._drag_target_idx = target_idx
            self._drag_indent = new_indent
            self._update_ghost_indent()
            self._refresh_tasks()

    def _update_ghost_indent(self):
        if not self._ghost or not self._ghost.winfo_exists():
            return
        indent = self._drag_indent
        bg = DEPTH_BG[1] if indent else DEPTH_BG[0]
        self._ghost.configure(bg=bg)
        if self._ghost_frame and self._ghost_frame.winfo_exists():
            self._ghost_frame.configure(bg=bg)
            for child in self._ghost_frame.winfo_children():
                try:
                    child.configure(bg=bg)
                except Exception:
                    pass
        if self._ghost_text_lbl and self._ghost_text_lbl.winfo_exists():
            prefix = "↳ " if indent else ""
            self._ghost_text_lbl.configure(text=prefix + self._drag_task["text"])

    def _drag_end(self, event):
        if self._drag_task is None:
            return
        self.root.unbind("<B1-Motion>")
        self.root.unbind("<ButtonRelease-1>")
        if self._ghost:
            self._ghost.destroy()
            self._ghost = None
        self._ghost_frame    = None
        self._ghost_text_lbl = None

        visible   = self._visible_tasks()
        drag_task = self._drag_task
        did_indent = self._drag_indent
        tgt = self._drag_target_idx if self._drag_target_idx is not None else self._drag_source_idx

        visible_without = [t for t in visible if t is not drag_task]
        tgt = max(0, min(tgt, len(visible_without)))

        if did_indent and tgt > 0:
            parent_task = visible_without[tgt - 1]
            pid = parent_task.get("google_id")
            if pid and pid != drag_task.get("google_id"):
                drag_task["parent_id"] = pid
                if self.service:
                    threading.Thread(
                        target=self._update_task_on_google, args=(drag_task,), daemon=True
                    ).start()

        new_visible = visible_without[:tgt] + [drag_task] + visible_without[tgt:]
        visible_indices = sorted(self.tasks.index(t) for t in visible)
        for i, idx in enumerate(visible_indices):
            self.tasks[idx] = new_visible[i]

        self._drag_task        = None
        self._drag_source_idx  = None
        self._drag_target_idx  = None
        self._drag_indent      = False
        self._refresh_tasks()

    # ── Scroll ────────────────────────────────────────────────────────────────

    def _on_scroll(self, event):
        top, bottom = self.canvas.yview()
        if top <= 0.0 and bottom >= 1.0:
            return
        if abs(event.delta) >= 120:
            self.canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
        else:
            self.canvas.yview_scroll(int(-1 * event.delta), "units")

    def on_close(self):
        self._stop_sync = True
        self.root.destroy()


if __name__ == "__main__":
    root = tk.Tk()
    app = ToDoApp(root)
    root.protocol("WM_DELETE_WINDOW", app.on_close)
    root.mainloop()
