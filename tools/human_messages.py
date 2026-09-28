#!/usr/bin/env python3
"""Brandon's direct messages about this repository, from both harnesses' local logs.

CLAUDE.md and AGENTS.md ("Evidence"): Brandon's direct messages govern, and they live in the
harnesses' private logs. This prints them in time order, so that recovering them is one command
instead of a fresh parse of two log formats each time. It reads only the local logs, writes
nothing, and is never run in CI. Its output is private conversation: read it, and never commit it,
paste it into a public file or send it to an outside service.

    python3 tools/human_messages.py                      # every message, oldest first
    python3 tools/human_messages.py --since 2026-09-27   # from a UTC date or time on
    python3 tools/human_messages.py --last 20            # the newest 20
    python3 tools/human_messages.py --grep 'athena|release'
    python3 tools/human_messages.py --count              # counts only, no text

What is a human message:
- **Claude Code** (`~/.claude/projects/<this checkout's project directories>/*.jsonl`, top-level
  sessions only). A `user` record's text, or a `queued_command` attachment in `prompt` mode (a
  message typed while a turn ran, which exists only as the attachment). Tool results, task
  notifications, local-command echoes, meta records, compaction summaries and
  `<system-reminder>` text are the harness's.
- **Codex** (`~/.codex/sessions/**/rollout-*.jsonl`). Only Brandon's interactive threads (the
  terminal, `codex-tui`/`cli`, and Codex Desktop, `vscode`) whose working directory is this
  checkout. Workers, `codex exec` consultations and threads launched by Claude are agents'. A
  `user` message's text, less the injected AGENTS.md, environment, plugin, image and `/goal`
  continuation wrappers. A message with attached files keeps only its "My request" part.

**The evaluation window is never read.** The private conversation dataset's evaluation partition
(families at or after its 2026-09-04 temporal cut, captured 2026-09-06) was drawn from these
conversations. THE_REBUILD's forward plan spends it once, in F5, so agents do not read it before
then: every message timestamped in `EVALUATION_WINDOW` (a half day of margin on each side, UTC) is
skipped and only counted.
"""

import argparse
import glob
import hashlib
import json
import os
import re
import subprocess
import sys
from datetime import datetime, timezone

def main_checkout():
    """The main checkout, also from a worktree under `.local/wt/`: the parent of the common git
    directory."""
    here = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    try:
        common = subprocess.run(["git", "-C", here, "rev-parse", "--path-format=absolute",
                                 "--git-common-dir"], capture_output=True, text=True, check=True)
        return os.path.dirname(common.stdout.strip())
    except (OSError, subprocess.CalledProcessError):
        return here


ROOT = main_checkout()
EVALUATION_WINDOW = ("2026-09-03T12:00:00", "2026-09-07T12:00:00")

CLAUDE_HARNESS = ("<local-command", "<command-name>", "<command-message>", "<command-args>",
                  "<task-notification>", "<bash-input>", "<bash-stdout>", "<bash-stderr>",
                  "Caveat:", "This session is being continued", "[Request interrupted")
CODEX_HARNESS = ("<codex_internal_context", "<environment_context", "<user_instructions",
                 "<user_shell_command", "<recommended_plugins", "<INSTRUCTIONS>", "# AGENTS.md",
                 "<image", "</image>", "<turn_aborted")
CODEX_HUMAN_THREADS = {("codex-tui", "cli"), ("Codex Desktop", "vscode")}
REMINDER = re.compile(r"<system-reminder>.*?</system-reminder>", re.S)
REQUEST = re.compile(r"^## My request[^\n]*:\s*$", re.M)
BARE_COMMAND = re.compile(r"^/[\w:-]+$")  # `/compact` alone: an operation, not a message


def claude_text(content):
    blocks = [content] if isinstance(content, str) else [
        block.get("text", "") for block in content if block.get("type") == "text"]
    kept = []
    for text in blocks:
        text = REMINDER.sub("", text).strip()
        if text and not text.startswith(CLAUDE_HARNESS):
            kept.append(text)
    return "\n\n".join(kept)


def claude_messages(since):
    base = os.path.expanduser("~/.claude/projects")
    # The checkout's project directory, and those of sessions opened inside it (`.local/wt/…`
    # becomes `--local-wt-…`), but not a sibling such as `holonics-other`.
    name = re.sub(r"[^A-Za-z0-9]", "-", ROOT)
    directories = [os.path.join(base, name)] + glob.glob(os.path.join(base, glob.escape(name) + "--*"))
    for directory in sorted(d for d in directories if os.path.isdir(d)):
        for path in sorted(glob.glob(os.path.join(directory, "*.jsonl"))):
            if since and mtime(path) < since:
                continue
            session = os.path.basename(path)[:8]
            with open(path, encoding="utf-8") as handle:
                for record in records(handle):
                    kind = record.get("type")
                    if kind == "user" and not record.get("isMeta") \
                            and not record.get("isCompactSummary"):
                        text = claude_text(record.get("message", {}).get("content", ""))
                    elif kind == "attachment" and record.get("attachment", {}).get("type") \
                            == "queued_command" and record["attachment"].get("commandMode") == "prompt":
                        text = claude_text(record["attachment"].get("prompt", ""))
                    else:
                        continue
                    if text:
                        yield record.get("timestamp", ""), "claude", session, text


def codex_text(content):
    kept = []
    for block in content:
        text = block.get("text", "").strip()
        if text.startswith("# Files mentioned by the user"):
            found = REQUEST.search(text)
            text = text[found.end():].strip() if found else ""
        if text and not text.startswith(CODEX_HARNESS):
            kept.append(text)
    return "\n\n".join(kept)


def codex_messages(since):
    base = os.path.expanduser("~/.codex/sessions")
    for path in sorted(glob.glob(os.path.join(base, "**", "rollout-*.jsonl"), recursive=True)):
        if since and mtime(path) < since:
            continue
        with open(path, encoding="utf-8") as handle:
            meta = next(records(handle), {}).get("payload", {})
            cwd = str(meta.get("cwd", ""))
            source = meta.get("source")  # a worker's is a dict naming its parent
            if not isinstance(source, str) or (meta.get("originator"), source) not in CODEX_HUMAN_THREADS \
                    or not (cwd == ROOT or cwd.startswith(ROOT + "/")):
                continue
            session = str(meta.get("id", ""))[:8]
            for record in records(handle, '"role":"user"'):
                payload = record.get("payload", {})
                if record.get("type") != "response_item" or payload.get("type") != "message":
                    continue
                text = codex_text(payload.get("content", []))
                if text:
                    yield record.get("timestamp", ""), "codex", session, text


def records(handle, needle=None):
    """The file's JSON records; a live log's half-written last line is skipped."""
    for line in handle:
        if needle and needle not in line:
            continue
        try:
            yield json.loads(line)
        except json.JSONDecodeError:
            continue


def mtime(path):
    return datetime.fromtimestamp(os.path.getmtime(path), timezone.utc).strftime("%Y-%m-%dT%H:%M:%S")


def main():
    parser = argparse.ArgumentParser(description=(__doc__ or "").split("\n\n")[0])
    parser.add_argument("--since", help="UTC date or time, e.g. 2026-09-27 or 2026-09-27T15:00")
    parser.add_argument("--until", help="UTC date or time, exclusive")
    parser.add_argument("--harness", choices=("claude", "codex"))
    parser.add_argument("--grep", help="case-insensitive regular expression over the text")
    parser.add_argument("--last", type=int, help="only the newest N")
    parser.add_argument("--count", action="store_true", help="counts only, no text")
    args = parser.parse_args()
    pattern = re.compile(args.grep, re.I) if args.grep else None

    sources = []
    if args.harness in (None, "claude"):
        sources.append(claude_messages(args.since))
    if args.harness in (None, "codex"):
        sources.append(codex_messages(args.since))
    seen, messages, withheld = set(), [], 0
    for source in sources:
        for stamp, harness, session, text in source:
            key = hashlib.sha256((stamp[:19] + "\0" + text).encode("utf-8")).digest()
            if key in seen:
                continue
            seen.add(key)
            if not stamp or EVALUATION_WINDOW[0] <= stamp[:19] < EVALUATION_WINDOW[1]:  # fail closed
                withheld += 1
                continue
            if (args.since and stamp < args.since) or (args.until and stamp >= args.until):
                continue
            if BARE_COMMAND.match(text):
                continue
            if pattern and not pattern.search(text):
                continue
            messages.append((stamp, harness, session, text))
    messages.sort()
    if args.last is not None:
        messages = messages[max(0, len(messages) - args.last):]

    if args.count:
        for harness in ("claude", "codex"):
            print(harness, sum(1 for m in messages if m[1] == harness))
    else:
        for stamp, harness, session, text in messages:
            print(f"== {stamp[:19]}Z {harness} {session}\n{text}\n")
    print(f"withheld in the evaluation window (of the files read): {withheld}", file=sys.stderr)


if __name__ == "__main__":
    main()
