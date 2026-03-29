import tkinter as tk
from tkinter import font, messagebox
import os
import threading
import time
from datetime import date

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
TAB_BG        = "#f5e6d3"
STEP_EMPTY    = "#c0a07a"
STEP_FILL     = "#9b5e2e"
WINDOW_WIDTH  = 300

TABS = ["Today", "Incomplete"]


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
        self.new_task_steps = 1   # controlled by the steps toggle

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
            font=("Helvetica", 11), width=17
        )
        self.entry.pack(side="left", padx=(8, 4), ipady=5)
        self.entry.bind("<Return>", self._add_task)
        self.entry.focus_set()

        tk.Button(
            input_frame, text="Add", bg=ACCENT_COLOR, fg=BG_COLOR,
            relief="flat", font=("Helvetica", 10, "bold"),
            cursor="hand2", command=self._add_task,
            padx=6, pady=5, bd=0, activebackground=ACCENT_COLOR
        ).pack(side="left", padx=(0, 4))

        # Steps toggle button — cycles 1× → 2× → 3× → 1×
        self.steps_btn = tk.Button(
            input_frame, text="1×", bg=BUTTON_COLOR, fg=DONE_COLOR,
            relief="flat", font=("Helvetica", 10, "bold"),
            cursor="hand2", command=self._cycle_steps,
            padx=6, pady=5, bd=0, activebackground=BUTTON_COLOR,
            width=2
        )
        self.steps_btn.pack(side="left", padx=(0, 8))

        # Clear completed (Done tab only)
        self.clear_btn = tk.Button(
            self.root, text="Clear completed", bg=BUTTON_COLOR, fg=TEXT_COLOR,
            relief="flat", font=("Helvetica", 9), cursor="hand2",
            command=self._clear_completed, pady=4, bd=0,
            activebackground=BUTTON_COLOR
        )
        self.clear_btn.pack(fill="x", padx=8, pady=6)

        self._switch_tab("Today")

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
            fg=ACCENT_COLOR if active else DONE_COLOR,
            bg=TAB_ACTIVE_BG if active else BUTTON_COLOR
        )

    # ── Tabs ─────────────────────────────────────────────────────────────────

    def _switch_tab(self, tab):
        self.active_tab = tab
        for name, btn in self.tab_buttons.items():
            if name == tab:
                btn.config(bg=TAB_ACTIVE_BG, fg=ACCENT_COLOR, font=("Helvetica", 10, "bold"))
            else:
                btn.config(bg=TAB_BG, fg=DONE_COLOR, font=("Helvetica", 10))
        if tab == "Done":
            self.clear_btn.pack(fill="x", padx=8, pady=6)
        else:
            self.clear_btn.pack_forget()
        self.canvas.yview_moveto(0)
        self._refresh_tasks()

    def _visible_tasks(self):
        today = str(date.today())
        if self.active_tab == "Today":
            tasks = [t for t in self.tasks if t.get("created_date") == today]
        elif self.active_tab == "Incomplete":
            tasks = [t for t in self.tasks if not t.get("done")]
        else:
            tasks = [t for t in self.tasks if t.get("done")]
        return sorted(tasks, key=lambda t: t.get("done", False))

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
                    g_done = gt.get("status") == "completed"
                    # If Google marked it done but we have steps, complete all steps
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
                    g_date = gt.get("updated", "")[:10]
                    new_tasks.append({
                        "text": gt["title"],
                        "done": gt.get("status") == "completed",
                        "google_id": gid,
                        "created_date": g_date,
                        "steps": 1,
                        "steps_done": 1 if gt.get("status") == "completed" else 0
                    })

            self.tasks = new_tasks
            self.root.after(0, self._refresh_tasks)
            self._set_sync_status("✓ Synced", SYNC_COLOR)
        except Exception:
            self._set_sync_status("✕ Sync failed", DELETE_COLOR)

    def _push_task_to_google(self, task):
        try:
            result = self.service.tasks().insert(
                tasklist=self.tasklist_id,
                body={"title": task["text"], "status": "needsAction"}
            ).execute()
            task["google_id"] = result["id"]
        except Exception:
            pass

    def _update_task_on_google(self, task):
        try:
            gid = task.get("google_id")
            if not gid:
                return
            self.service.tasks().update(
                tasklist=self.tasklist_id, task=gid,
                body={"id": gid, "title": task["text"],
                      "status": "completed" if task["done"] else "needsAction"}
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
        self.tasks.append(task)
        self.entry.delete(0, "end")
        # Reset steps toggle back to 1×
        self.new_task_steps = 1
        self.steps_btn.config(text="1×", fg=DONE_COLOR, bg=BUTTON_COLOR)
        self._switch_tab("Today")
        if self.service:
            threading.Thread(target=self._push_task_to_google, args=(task,), daemon=True).start()

    def _advance_step(self, task):
        """Click on the progress indicator — advance one step, or reset if done."""
        steps = task.get("steps", 1)
        done  = task.get("done", False)
        if done:
            # Reset
            task["steps_done"] = 0
            task["done"] = False
        else:
            task["steps_done"] = task.get("steps_done", 0) + 1
            if task["steps_done"] >= steps:
                task["steps_done"] = steps
                task["done"] = True
        self._refresh_tasks()
        if self.service:
            threading.Thread(target=self._update_task_on_google, args=(task,), daemon=True).start()

    def _move_to_today(self, task):
        task["created_date"] = str(date.today())
        self._refresh_tasks()

    def _cycle_task_steps(self, task):
        new_steps = (task.get("steps", 1) % 3) + 1
        task["steps"] = new_steps
        task["steps_done"] = min(task.get("steps_done", 0), new_steps)
        task["done"] = task["steps_done"] >= new_steps
        self._refresh_tasks()
        if self.service:
            threading.Thread(target=self._update_task_on_google, args=(task,), daemon=True).start()

    def _delete_task(self, task):
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
        """Replace the text label with an inline entry for editing."""
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
            # Restore label with updated text
            done = task.get("done", False)
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
            display.insert(tgt, None)  # None = placeholder slot
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

    def _make_task_row(self, task):
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

        # ── Progress indicator (left, clickable) ─────────────────────────────
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
            # Show a row of dots: filled = done step, empty = pending
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

        # ── Task text (clickable to edit) ─────────────────────────────────────
        text_color  = DONE_COLOR if done else TEXT_COLOR
        text_font   = font.Font(family="Helvetica", size=11, overstrike=done)

        text_lbl = tk.Label(
            row, text=task["text"], bg=BG_COLOR, fg=text_color,
            font=text_font, anchor="w", wraplength=200,
            justify="left", cursor="xterm"
        )
        text_lbl.pack(side="left", fill="x", expand=True)
        text_lbl.bind("<Button-1>", lambda e, t=task, r=row, l=text_lbl: self._start_edit(t, r, l))

        # ── Delete button ─────────────────────────────────────────────────────
        del_btn = tk.Label(
            row, text="✕", bg=BG_COLOR, fg=DELETE_COLOR,
            font=("Helvetica", 10), cursor="hand2", padx=4
        )
        del_btn.pack(side="right")
        del_btn.bind("<Button-1>", lambda e, t=task: self._delete_task(t))

        # ── Per-task steps cycle button ────────────────────────────────────────
        steps_lbl = tk.Label(
            row, text=f"{steps}×", bg=BG_COLOR,
            fg=ACCENT_COLOR if steps > 1 else DONE_COLOR,
            font=("Helvetica", 9, "bold"), cursor="hand2", padx=2
        )
        steps_lbl.pack(side="right")
        steps_lbl.bind("<Button-1>", lambda e, t=task: self._cycle_task_steps(t))

        # ── Move to Today button (Incomplete tab only, for non-today tasks) ────
        today = str(date.today())
        extra_widgets = []
        if self.active_tab == "Incomplete" and task.get("created_date") != today:
            today_btn = tk.Label(
                row, text="→ Today", bg=BG_COLOR, fg=SYNC_COLOR,
                font=("Helvetica", 9, "bold"), cursor="hand2", padx=4
            )
            today_btn.pack(side="right")
            today_btn.bind("<Button-1>", lambda e, t=task: self._move_to_today(t))
            today_btn.bind("<MouseWheel>", self._on_scroll)
            extra_widgets.append(today_btn)

        sep = tk.Frame(self.task_frame, bg=HEADER_COLOR, height=1)
        sep.pack(fill="x", padx=8)

        for w in (row, prog_frame, text_lbl, del_btn, steps_lbl, sep, *extra_widgets):
            w.bind("<MouseWheel>", self._on_scroll)

    def _make_lifted_task_row(self, task):
        """Placeholder shown in the list at the drop target — looks like the task, slightly enlarged."""
        steps      = task.get("steps", 1)
        steps_done = task.get("steps_done", 0)
        done       = task.get("done", False)

        # Accent-coloured border wrapper
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
        # Bind to root so events survive widget destruction during refresh
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
