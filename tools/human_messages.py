#!/usr/bin/env python3
"""Brandon's messages about this repository, with their provenance, from local logs.

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
  `<system-reminder>` text are the harness's. A `<wake>` envelope contributes only explicit
  `from="human" trust="principal"` messages, at their `sent-at` times. Coordinator relays are
  not direct messages: their user citations are labelled `claude-relayed`, at their `at` times;
  coordinator notes are omitted. Unrecognized or malformed envelopes are preserved as
  `claude-ambiguous`, with a diagnostic, rather than attributed to Brandon. These labels do not
  establish fresh user authorization. Envelope-like quotations inside ordinary prose stay prose.
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
import xml.etree.ElementTree as ET
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
CLAUDE_ENVELOPE = re.compile(r"^<(wake|project_claude_message|relay)(?=[\s/>])")


def envelope_stamp(value):
    """Envelope times must declare their zone; comparisons and display use UTC."""
    try:
        stamp = datetime.fromisoformat(value.replace("Z", "+00:00"))
        if stamp.tzinfo is not None:
            return stamp.astimezone(timezone.utc).isoformat().replace("+00:00", "Z")
    except (AttributeError, ValueError):
        pass
    return ""


def claude_entries(content, record_stamp):
    """Return (time, provenance, text) entries and metadata-only ambiguity diagnostics.

    Agent-inferred: parse only a whole, anchored envelope and its declared paths. Searching
    arbitrary descendants would promote quoted tags or coordinator notes into principal input.
    """
    blocks = [content] if isinstance(content, str) else [
        block.get("text", "") for block in content if block.get("type") == "text"]
    entries, ordinary, diagnostics = [], [], []

    def ambiguous(text, reason, stamp=record_stamp):
        entries.append((stamp, "claude-ambiguous", text))
        diagnostics.append(reason)

    def ambiguous_envelope(root, text, reason, fallback_stamp=record_stamp):
        # An unrecognized path can still carry an evaluation citation. Fail closed on its
        # inner times before preserving the whole envelope at the outer record's time.
        stamps = [envelope_stamp(node.get("sent-at" if node.tag == "message" else "at"))
                  for node in root.iter() if node.tag in ("message", "cited")]
        safe = all(stamp and not EVALUATION_WINDOW[0] <= stamp[:19] < EVALUATION_WINDOW[1]
                   for stamp in stamps)
        ambiguous(text, reason, fallback_stamp if safe else "")

    for text in blocks:
        text = REMINDER.sub("", text).strip()
        if not text or text.startswith(CLAUDE_HARNESS):
            continue
        if not CLAUDE_ENVELOPE.match(text):
            ordinary.append(text)
            continue
        try:
            if "<!DOCTYPE" in text or "<!ENTITY" in text:
                raise ET.ParseError("declaration")
            root = ET.fromstring(text)
        except ET.ParseError:
            ambiguous(text, "malformed or unsupported envelope; inner time cannot be verified", "")
            continue

        if root.tag == "wake":
            messages = root.findall("./project/message") + root.findall("./project/thread/message")
            if not messages or len(messages) != len(list(root.iter("message"))):
                ambiguous_envelope(root, text, "wake has no messages at the declared principal paths")
                continue
            for message in messages:
                stamp = envelope_stamp(message.get("sent-at"))
                if message.get("from") != "human" or message.get("trust") != "principal":
                    ambiguous(ET.tostring(message, encoding="unicode"),
                              "wake message has unrecognized principal provenance", stamp)
                elif list(message):
                    ambiguous_envelope(message, ET.tostring(message, encoding="unicode"),
                                       "principal message has unrecognized nested markup", stamp)
                elif not stamp:
                    ambiguous(ET.tostring(message, encoding="unicode"),
                              "principal message has no valid zoned sent-at time", "")
                elif (message.text or "").strip():
                    entries.append((stamp, "claude", message.text.strip()))
            continue

        relay = root if root.tag == "relay" else root.find("./relay")
        if relay is None or relay.get("from") != "coordinator" \
                or (root.tag == "project_claude_message" and list(root) != [relay]) \
                or any(child.tag not in ("cited", "note") for child in relay):
            ambiguous_envelope(root, text, "unrecognized coordinator relay structure")
            continue
        # Only direct citations are relayed user content. A <cited> inside <note> is a quotation.
        for cited in relay.findall("./cited"):
            stamp = envelope_stamp(cited.get("at"))
            if cited.get("author") != "user" or list(cited) or not stamp:
                ambiguous(ET.tostring(cited, encoding="unicode"),
                          "relay citation has unrecognized author, markup or time", stamp)
            elif (cited.text or "").strip():
                entries.append((stamp, "claude-relayed", cited.text.strip()))
    if ordinary:
        entries.append((record_stamp, "claude", "\n\n".join(ordinary)))
    return entries, diagnostics


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
                        content = record.get("message", {}).get("content", "")
                    elif kind == "attachment" and record.get("attachment", {}).get("type") \
                            == "queued_command" and record["attachment"].get("commandMode") == "prompt":
                        content = record["attachment"].get("prompt", "")
                    else:
                        continue
                    entries, diagnostics = claude_entries(content, record.get("timestamp", ""))
                    for reason in diagnostics:
                        print(f"ambiguous Claude envelope: {session} "
                              f"{record.get('timestamp', '')}: {reason}", file=sys.stderr)
                    for stamp, provenance, text in entries:
                        yield stamp, provenance, session, text


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
    selected, messages, withheld = {}, [], 0
    rank = {"claude": 2, "codex": 2, "claude-relayed": 1, "claude-ambiguous": 0}
    for source in sources:
        for stamp, harness, session, text in source:
            key = hashlib.sha256((stamp[:19] + "\0" + text).encode("utf-8")).digest()
            # A relay encountered first must not hide the same directly witnessed message.
            previous = selected.get(key)
            if previous is None or rank[harness] > rank[previous[1]]:
                selected[key] = (stamp, harness, session, text)
    for stamp, harness, session, text in selected.values():
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
        for harness in ("claude", "codex", "claude-relayed", "claude-ambiguous"):
            print(harness, sum(1 for m in messages if m[1] == harness))
    else:
        for stamp, harness, session, text in messages:
            print(f"== {stamp[:19]}Z {harness} {session}\n{text}\n")
    print(f"withheld in the evaluation window (of the files read): {withheld}", file=sys.stderr)


if __name__ == "__main__":
    main()
