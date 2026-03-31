import tkinter as tk
from tkinter import font, messagebox
import os
import threading
import time
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
BUTTON_COLOR  = "#c9a97c"
DELETE_COLOR  = "#b84a3a"
SYNC_COLOR    = "#4e7a42"
TAB_ACTIVE_BG = "#c9a97c"
STEP_EMPTY    = "#c0a07a"
STEP_FILL     = "#9b5e2e"
UNTIL_COLOR   = "#5e7a9b"
TAB_BG        = "#f5e6d3"
TIMER_COLOR   = "#3d7a5e"
WINDOW_WIDTH  = 300

TABS          = ["Today", "Incomplete"]
TIMER_PRESETS = [0, 5, 10, 15, 20, 25, 30, 45, 60]


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

        self._task_rows       = []
        self._drag_task       = None
        self._drag_source_idx = None
        self._drag_target_idx = None
        self._ghost           = None
        self._ghost_w         = 0
        self._ghost_h         = 0

        self._build_ui()
        self._position_window()
        threading.Thread(target=self._init_google, daemon=True).start()

    # ── Build UI ─────────────────────────────────────────────────────────────

    def _build_ui(self):
        # Title bar
        title_bar = tk.Frame(self.root, bg=HEADER_COLOR)
        title_bar.pack(fill="x")
        tk.Label(
            title_bar, text="  To-Do List", bg=HEADER_COLOR,
            fg=ACCENT_COLOR, font=("Helvetica", 13, "bold"), pady=8
        ).pack(side="left")
        self.sync_label = tk.Label(
            title_bar, text="⟳ Connecting...", bg=HEADER_COLOR,
            fg=DONE_COLOR, font=("Helvetica", 9), padx=8
        )
        self.sync_label.pack(side="right")

        # Study time summary bar
        summary_bar = tk.Frame(self.root, bg=HEADER_COLOR)
        summary_bar.pack(fill="x")
        self._summary_label = tk.Label(
            summary_bar, text="今日の学習: 0分", bg=HEADER_COLOR,
            fg=TIMER_COLOR, font=("Helvetica", 9, "bold"), padx=8, pady=2
        )
        self._summary_label.pack(side="left")

        # Tab bar
        tab_bar = tk.Frame(self.root, bg=HEADER_COLOR)
        tab_bar.pack(fill="x")
        self.tab_buttons = {}
        for tab in TABS:
            btn = tk.Label(
                tab_bar, text=tab, bg=TAB_BG, fg=DONE_COLOR,
                font=("Helvetica", 10), cursor="hand2",
                padx=0, pady=6, anchor="center"
            )
            btn.pack(side="left", expand=True, fill="x")
            btn.bind("<Button-1>", lambda e, t=tab: self._switch_tab(t))
            self.tab_buttons[tab] = btn

        tk.Frame(self.root, bg=ACCENT_COLOR, height=2).pack(fill="x")

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

        self.entry = tk.Entry(
            input_frame, bg=ENTRY_BG, fg=TEXT_COLOR,
            insertbackground=TEXT_COLOR, relief="flat",
            font=("Helvetica", 11), width=10
        )
        self.entry.pack(side="left", padx=(6, 3), ipady=5)
        self.entry.bind("<Return>", self._add_task)
        self.entry.focus_set()

        tk.Button(
            input_frame, text="Add", bg=ACCENT_COLOR, fg=BG_COLOR,
            relief="flat", font=("Helvetica", 10, "bold"),
            cursor="hand2", command=self._add_task,
            padx=5, pady=5, bd=0, activebackground=ACCENT_COLOR
        ).pack(side="left", padx=(0, 3))

        # Until button — opens calendar date picker
        self.until_btn = tk.Button(
            input_frame, text="Until", bg=BUTTON_COLOR, fg=TEXT_COLOR,
            relief="flat", font=("Helvetica", 10),
            cursor="hand2", command=self._show_calendar_picker,
            padx=4, pady=5, bd=0, activebackground=BUTTON_COLOR
        )
        self.until_btn.pack(side="left", padx=(0, 3))

        # Steps toggle button — cycles 1× → 2× → 3× → 1×
        self.steps_btn = tk.Button(
            input_frame, text="1×", bg=BUTTON_COLOR, fg=TEXT_COLOR,
            relief="flat", font=("Helvetica", 10, "bold"),
            cursor="hand2", command=self._cycle_steps,
            padx=4, pady=5, bd=0, activebackground=BUTTON_COLOR,
            width=2
        )
        self.steps_btn.pack(side="left", padx=(0, 3))

        # Timer preset button — cycles off → 5m → 10m → … → 60m → off
        self.timer_btn = tk.Button(
            input_frame, text="⏱", bg=BUTTON_COLOR, fg=TEXT_COLOR,
            relief="flat", font=("Helvetica", 10),
            cursor="hand2", command=self._cycle_timer_preset,
            padx=3, pady=5, bd=0, activebackground=BUTTON_COLOR,
            width=3
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
        else:
            self.root.withdraw()

    def _position_window(self):
        self.root.update_idletasks()
        sw = self.root.winfo_screenwidth()
        x = sw - WINDOW_WIDTH - 20
        self.root.geometry(f"{WINDOW_WIDTH}x460+{x}+50")

    def _set_sync_status(self, text, color=DONE_COLOR):
        self.root.after(0, lambda: self.sync_label.config(text=text, fg=color))

    # ── Steps toggle ─────────────────────────────────────────────────────────

    def _cycle_steps(self):
        self.new_task_steps = (self.new_task_steps % 3) + 1
        label = f"{self.new_task_steps}×"
        active = self.new_task_steps > 1
        self.steps_btn.config(
            text=label,
            fg=ACCENT_COLOR if active else TEXT_COLOR,
            bg=TAB_ACTIVE_BG if active else BUTTON_COLOR
        )

    # ── Timer preset toggle ───────────────────────────────────────────────────

    def _cycle_timer_preset(self):
        idx = TIMER_PRESETS.index(self.new_task_minutes) if self.new_task_minutes in TIMER_PRESETS else 0
        self.new_task_minutes = TIMER_PRESETS[(idx + 1) % len(TIMER_PRESETS)]
        if self.new_task_minutes == 0:
            self.timer_btn.config(text="⏱", fg=TEXT_COLOR, bg=BUTTON_COLOR)
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
        self._tick()
        self._refresh_tasks()

    def _pause_timer(self):
        if not self._active_timer or not self._active_timer["running"]:
            return
        if self._active_timer.get("after_id"):
            self.root.after_cancel(self._active_timer["after_id"])
        self._active_timer["running"] = False
        self._active_timer["after_id"] = None
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
        if self._timer_label_widget and self._timer_label_widget.winfo_exists():
            self._timer_label_widget.config(
                text=f"⏸ {self._format_time(task['timer_remaining_seconds'])}"
            )
        if task["timer_remaining_seconds"] <= 0:
            self._timer_complete(task)
        else:
            after_id = self.root.after(1000, self._tick)
            self._active_timer["after_id"] = after_id

    def _stop_active_timer(self):
        if self._active_timer:
            if self._active_timer.get("after_id"):
                self.root.after_cancel(self._active_timer["after_id"])
            self._active_timer = None
            self._timer_label_widget = None

    def _timer_complete(self, task):
        self._active_timer = None
        self._timer_label_widget = None
        today = str(date.today())
        if task.get("until_date"):
            steps = task.get("steps", 1)
            task.setdefault("daily_done", {})[today] = steps
        else:
            task["steps_done"] = task.get("steps", 1)
            task["done"] = True
        self._refresh_tasks()
        if self.service:
            threading.Thread(target=self._update_task_on_google, args=(task,), daemon=True).start()

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

    def _switch_tab(self, tab):
        self.active_tab = tab
        for name, btn in self.tab_buttons.items():
            if name == tab:
                btn.config(bg=TAB_ACTIVE_BG, fg=ACCENT_COLOR, font=("Helvetica", 10, "bold"))
            else:
                btn.config(bg=TAB_BG, fg=DONE_COLOR, font=("Helvetica", 10))
        self.canvas.yview_moveto(0)
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
        return sorted(tasks, key=self._task_done_today)

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
                    # Parse until_date from notes if present
                    notes = gt.get("notes", "")
                    if notes.startswith("[until:") and len(notes) >= 17:
                        task["until_date"] = notes[7:17]
                        task.setdefault("daily_done", {})
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
                    notes = gt.get("notes", "")
                    until_date = None
                    if notes.startswith("[until:") and len(notes) >= 17:
                        until_date = notes[7:17]
                    g_date = gt.get("updated", "")[:10]
                    entry = {
                        "text": gt["title"],
                        "done": gt.get("status") == "completed",
                        "google_id": gid,
                        "created_date": g_date,
                        "steps": 1,
                        "steps_done": 1 if gt.get("status") == "completed" else 0
                    }
                    if until_date:
                        entry["until_date"] = until_date
                        entry["daily_done"] = {}
                        entry["done"] = False
                        entry["steps_done"] = 0
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
            if task.get("until_date"):
                body["notes"] = f"[until:{task['until_date']}]"
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
            if task.get("until_date"):
                body["notes"] = f"[until:{task['until_date']}]"
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
        self.steps_btn.config(text="1×", fg=TEXT_COLOR, bg=BUTTON_COLOR)
        self.new_task_minutes = 0
        self.timer_btn.config(text="⏱", fg=TEXT_COLOR, bg=BUTTON_COLOR)
        self._switch_tab("Today")
        if self.service:
            threading.Thread(target=self._push_task_to_google, args=(task,), daemon=True).start()

    def _advance_step(self, task):
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

    # ── Render ────────────────────────────────────────────────────────────────

    def _refresh_tasks(self):
        for widget in self.task_frame.winfo_children():
            widget.destroy()

        self._task_rows = []
        visible = self._visible_tasks()

        if self._drag_task is not None and self._drag_task in visible:
            drag_task = self._drag_task
            tgt = self._drag_target_idx if self._drag_target_idx is not None else self._drag_source_idx
            display = [t for t in visible if t is not drag_task]
            tgt = max(0, min(tgt, len(display)))
            display.insert(tgt, None)
            for item in display:
                if item is None:
                    self._make_lifted_task_row(drag_task)
                else:
                    self._make_task_row(item)
        elif not visible:
            empty_msgs = {
                "Today":      "No tasks for today.\nAdd one below!",
                "Incomplete": "No incomplete tasks.",
                "Done":       "No completed tasks yet.",
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

        row = tk.Frame(self.task_frame, bg=BG_COLOR, pady=4)
        row.pack(fill="x", padx=8)
        self._task_rows.append((task, row))

        # ── Drag handle ───────────────────────────────────────────────────────
        drag_handle = tk.Label(
            row, text="⠿", bg=BG_COLOR, fg=DONE_COLOR,
            font=("Helvetica", 12), cursor="fleur", padx=2
        )
        drag_handle.pack(side="left")
        drag_handle.bind("<ButtonPress-1>", lambda e, t=task: self._drag_start(e, t))
        drag_handle.bind("<MouseWheel>", self._on_scroll)

        # ── Progress indicator ────────────────────────────────────────────────
        prog_frame = tk.Frame(row, bg=BG_COLOR, cursor="hand2")
        prog_frame.pack(side="left", padx=(0, 6))

        if steps == 1:
            sym = tk.Label(
                prog_frame,
                text="✓" if done else "○",
                bg=BG_COLOR,
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
                    bg=BG_COLOR,
                    fg=ACCENT_COLOR if filled else STEP_EMPTY,
                    font=("Helvetica", 11),
                    cursor="hand2"
                )
                dot.pack(side="left")
                dot.bind("<Button-1>", lambda e, t=task: self._advance_step(t))
                dot.bind("<MouseWheel>", self._on_scroll)

        prog_frame.bind("<Button-1>", lambda e, t=task: self._advance_step(t))
        for child in prog_frame.winfo_children():
            child.bind("<Button-1>", lambda e, t=task: self._advance_step(t))

        # ── Delete button (pack right first so text doesn't push it off) ──────
        del_btn = tk.Label(
            row, text="✕", bg=BG_COLOR, fg=DELETE_COLOR,
            font=("Helvetica", 10), cursor="hand2", padx=4
        )
        del_btn.pack(side="right")
        del_btn.bind("<Button-1>", lambda e, t=task: self._delete_task(t))

        # ── Per-task steps cycle ───────────────────────────────────────────────
        steps_lbl = tk.Label(
            row, text=f"{steps}×", bg=BG_COLOR,
            fg=ACCENT_COLOR if steps > 1 else DONE_COLOR,
            font=("Helvetica", 9, "bold"), cursor="hand2", padx=2
        )
        steps_lbl.pack(side="right")
        steps_lbl.bind("<Button-1>", lambda e, t=task: self._cycle_task_steps(t))

        # ── Days left badge + finish button (recurring tasks only) ───────────
        if is_recurring:
            finish_btn = tk.Label(
                row, text="✓✓", bg=BG_COLOR, fg=SYNC_COLOR,
                font=("Helvetica", 9, "bold"), cursor="hand2", padx=2
            )
            finish_btn.pack(side="right")
            finish_btn.bind("<Button-1>", lambda e, t=task: self._finish_recurring(t))
            finish_btn.bind("<MouseWheel>", self._on_scroll)

            days_text = self._days_left_text(task["until_date"])
            days_lbl = tk.Label(
                row, text=days_text, bg=BG_COLOR, fg=UNTIL_COLOR,
                font=("Helvetica", 8), padx=2
            )
            days_lbl.pack(side="right")
            days_lbl.bind("<MouseWheel>", self._on_scroll)

        # ── Timer display ─────────────────────────────────────────────────────
        extra_widgets = []
        timer_widgets = []
        if task.get("estimated_minutes"):
            is_active  = self._active_timer and self._active_timer["task"] is task
            is_running = is_active and self._active_timer["running"]
            rem        = task.get("timer_remaining_seconds", 0)

            if is_active:
                add_btn = tk.Label(
                    row, text="+5", bg=BG_COLOR, fg=TIMER_COLOR,
                    font=("Helvetica", 9), cursor="hand2", padx=2
                )
                add_btn.pack(side="right")
                add_btn.bind("<Button-1>", lambda e, t=task: self._add_timer_time(t, 5))
                add_btn.bind("<MouseWheel>", self._on_scroll)
                timer_widgets.append(add_btn)

                icon = "⏸" if is_running else "▶"
                timer_lbl = tk.Label(
                    row, text=f"{icon} {self._format_time(rem)}", bg=BG_COLOR,
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
                    row, text=f"⏱{est}m", bg=BG_COLOR, fg=DONE_COLOR,
                    font=("Helvetica", 9), cursor="hand2", padx=2
                )
                timer_lbl.pack(side="right")
                timer_lbl.bind("<Button-1>", lambda e, t=task: self._toggle_timer(t))
                timer_lbl.bind("<MouseWheel>", self._on_scroll)
                timer_widgets.append(timer_lbl)

        # ── Move to Today button (Incomplete tab, non-recurring) ──────────────
        if self.active_tab == "Incomplete" and not is_recurring and task.get("created_date") != today_str:
            today_btn = tk.Label(
                row, text="→ Today", bg=BG_COLOR, fg=SYNC_COLOR,
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
            row, text=task["text"], bg=BG_COLOR, fg=text_color,
            font=text_font, anchor="w", wraplength=140,
            justify="left", cursor="xterm"
        )
        text_lbl.pack(side="left", fill="x", expand=True)
        text_lbl.bind("<Button-1>", lambda e, t=task, r=row, l=text_lbl: self._start_edit(t, r, l))

        sep = tk.Frame(self.task_frame, bg=HEADER_COLOR, height=1)
        sep.pack(fill="x", padx=8)

        for w in (row, prog_frame, text_lbl, del_btn, steps_lbl, sep, *extra_widgets, *timer_widgets):
            w.bind("<MouseWheel>", self._on_scroll)

    def _make_lifted_task_row(self, task):
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

        outer = tk.Frame(self.task_frame, bg=ACCENT_COLOR, pady=1)
        outer.pack(fill="x", padx=6)

        row = tk.Frame(outer, bg=HEADER_COLOR, pady=6)
        row.pack(fill="x", padx=1)

        tk.Label(row, text="⠿", bg=HEADER_COLOR, fg=ACCENT_COLOR,
                 font=("Helvetica", 12), padx=2).pack(side="left")

        if steps == 1:
            tk.Label(row, text="✓" if done else "○",
                     bg=HEADER_COLOR, fg=ACCENT_COLOR if done else DONE_COLOR,
                     font=("Helvetica", 13)).pack(side="left", padx=(0, 6))
        else:
            for i in range(steps):
                tk.Label(row, text="●" if i < steps_done else "○",
                         bg=HEADER_COLOR,
                         fg=ACCENT_COLOR if i < steps_done else STEP_EMPTY,
                         font=("Helvetica", 12)).pack(side="left")

        lf = font.Font(family="Helvetica", size=12, overstrike=done)
        tk.Label(row, text=task["text"], bg=HEADER_COLOR,
                 fg=DONE_COLOR if done else TEXT_COLOR,
                 font=lf, anchor="w", wraplength=190,
                 justify="left").pack(side="left", fill="x", expand=True, padx=4)

        sep = tk.Frame(self.task_frame, bg=HEADER_COLOR, height=1)
        sep.pack(fill="x", padx=8)
        for w in (outer, row, sep):
            w.bind("<MouseWheel>", self._on_scroll)

    # ── Drag and drop ─────────────────────────────────────────────────────────

    def _drag_start(self, event, task):
        visible = self._visible_tasks()
        if task not in visible:
            return
        self._drag_task = task
        self._drag_source_idx = visible.index(task)
        self._drag_target_idx = self._drag_source_idx
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
        ghost.configure(bg=HEADER_COLOR)

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

        frame = tk.Frame(ghost, bg=HEADER_COLOR, pady=4, padx=6)
        frame.pack()

        tk.Label(frame, text="⠿", bg=HEADER_COLOR, fg=DONE_COLOR,
                 font=("Helvetica", 12), padx=2).pack(side="left")

        if steps == 1:
            tk.Label(frame, text="✓" if done else "○",
                     bg=HEADER_COLOR, fg=ACCENT_COLOR if done else DONE_COLOR,
                     font=("Helvetica", 12)).pack(side="left", padx=(0, 6))
        else:
            for i in range(steps):
                tk.Label(frame, text="●" if i < steps_done else "○",
                         bg=HEADER_COLOR,
                         fg=ACCENT_COLOR if i < steps_done else STEP_EMPTY,
                         font=("Helvetica", 11)).pack(side="left")

        gf = font.Font(family="Helvetica", size=12, overstrike=done)
        tk.Label(frame, text=task["text"], bg=HEADER_COLOR,
                 fg=DONE_COLOR if done else TEXT_COLOR,
                 font=gf, wraplength=180).pack(side="left", padx=4)

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

        if target_idx != self._drag_target_idx:
            self._drag_target_idx = target_idx
            self._refresh_tasks()

    def _drag_end(self, event):
        if self._drag_task is None:
            return
        self.root.unbind("<B1-Motion>")
        self.root.unbind("<ButtonRelease-1>")
        if self._ghost:
            self._ghost.destroy()
            self._ghost = None

        visible  = self._visible_tasks()
        drag_task = self._drag_task
        tgt = self._drag_target_idx if self._drag_target_idx is not None else self._drag_source_idx

        visible_without = [t for t in visible if t is not drag_task]
        tgt = max(0, min(tgt, len(visible_without)))
        new_visible = visible_without[:tgt] + [drag_task] + visible_without[tgt:]

        visible_indices = sorted(self.tasks.index(t) for t in visible)
        for i, idx in enumerate(visible_indices):
            self.tasks[idx] = new_visible[i]

        self._drag_task = None
        self._drag_source_idx = None
        self._drag_target_idx = None
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
