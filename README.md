# MyTasks

A lightweight personal to-do app built with Python and Tkinter, synced with Google Tasks.

## Features

- **Today / Incomplete / Done tabs** — organise tasks by status
- **Google Tasks sync** — tasks stay in sync with your Google account automatically every 15 seconds
- **Multi-step tasks** — assign 1×, 2×, or 3× steps to a task and track progress with dot indicators
- **Drag and drop reordering** — grab the ⠿ handle to reorder tasks within any tab
- **Move to Today** — send older incomplete tasks to today's list with one click
- **Inline editing** — click any task name to rename it
- **Completed tasks sink to bottom** — crossed-out tasks automatically move to the bottom of the list
- **Light brown theme** — warm, easy-on-the-eyes colour palette

## Requirements

- Python 3
- Google OAuth credentials (`credentials.json`) placed in your home directory

### Python dependencies

```bash
pip install google-auth google-auth-oauthlib google-auth-httplib2 google-api-python-client
```

## Running the app

```bash
python3 MyTasks.py
```

On first launch, a browser window will open to authenticate with your Google account.

## File structure

```
MyTasks/
├── MyTasks.py        # Main application
├── .gitignore        # Keeps credentials out of git
└── README.md
```

> **Note:** `credentials.json` and `.todo_token.json` are excluded from the repo and never pushed to GitHub.
