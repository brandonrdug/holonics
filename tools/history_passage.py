#!/usr/bin/env -S python3 -I
"""The conversation history as slices of a store (Brandon, November 23 01:37Z: the exchanges with Claude, Codex and Antigravity are a
pairwise chain in time, likely the best data there is; their parts are told apart by when and where they stand; feedback on code comes
from the logged tool calls and their results, never from a compiler loop inside a lap). A boundary codec of a private curated set (its
`strands/dialogue_turns.jsonl` and `strands/tool_events.jsonl`, the schema its `SCHEMA.md` states); nothing it writes is ever committed.

Three slices, each a document a piece, every piece in time order (`corpus_passage.py`'s files: `DOCS_*`, `IDS_*`, `HELD_*`, `HELD_IDS_*`):
- `dialogue`: one conversation a document, its turns in the chain's order. The document's title line names the platform, the machine
  and the date it opens; each turn opens with a line `[YYYY-MM-DD HH:MM UTC] SPEAKER:` (the speaker as the set names it: human, model,
  agent_prompt), then the turn's text whole. Documents are ordered by their first turn's time. Prompt-history rows that a transcript
  also holds are left out (the set marks them), so a prompt is read once.
- `acts`: one model turn's tool calls a document, in the order they were made: each call as `$ COMMAND` (a shell call's command) or
  `> TOOL ARGS` (any other tool, its arguments as logged), then its result whole, and a line `exit: N` where the log gives a nonzero
  exit code, or `error` where it flags one. Documents are ordered by their first call's time. A call whose result is longer than
  RESULT_LIMIT octets is left out whole (counted), never cut: on November 23 the shell results over 64 KB were 1% of the calls and 35%
  of the shell octets, logs a reader skims, and a cut would write a seam she never met. With ACTS_SHARE (thousandths), only the turns whose
  id's SHA-256 falls in the lowest ACTS_SHARE thousandths are kept, a keyed draw spread over every date (the strand is three times a
  whole pass of the store of November 23, so it enters by a share; a prefix of a time-ordered slice would be its oldest months alone).

- `harness`: one conversation's system-side text a document, its events in time order (the full collection, Brandon November 24).

Held: everything dated on or after HELD_FROM (a `YYYY-MM-DD` UTC date), the time cut no earlier state has read. Until November 24 the
GSM8K evaluation window (September 3 12:00 to September 7 12:00 UTC) was left out of both roles; Brandon lifted it that day (05:53Z:
"there are other yardsticks"), and nothing is left out by date now.

Usage: history_passage.py SET OUT HELD_FROM [RESULT_LIMIT [ACTS_SHARE]]

Prints the slices' `STORE.tsv` rows (train and prefix the whole slice; held the held cut) with their SHA-256, and a count line of what
was left out and why. Outside the machine: no text is changed but by the cut.
"""
import hashlib
import json
import os
import sys

INDEX_HEAD = "document\ttitle_octets\ttext_octets\topens\tcloses\n"
# [the lead, November 24] Brandon, 05:53Z: the September 3 to 7 window is no longer left out ("there are other yardsticks"); WINDOW is
# empty, so nothing is left out by date but the held cut.
WINDOW = ("", "")


class Role:
    """One role's files of one slice, written a document at a time."""

    def __init__(self, out, stem, slice_):
        ids = "HELD_IDS" if stem == "HELD" else "IDS"
        self.b = open(os.path.join(out, f"{stem}_{slice_}.bin"), "xb")
        self.t = open(os.path.join(out, f"{stem}_{slice_}.tsv"), "x")
        self.i = open(os.path.join(out, f"{ids}_{slice_}.txt"), "x")
        self.t.write(INDEX_HEAD)
        self.h = hashlib.sha256()
        self.n = self.octets = 0

    def write(self, ident, title, text):
        if not text:
            return
        self.b.write(title)
        self.b.write(text)
        self.h.update(title)
        self.h.update(text)
        self.t.write(f"{self.n}\t{len(title)}\t{len(text)}\t1\t1\n")
        self.i.write(f"{ident}\n")
        self.octets += len(title) + len(text)
        self.n += 1

    def close(self):
        for f in (self.b, self.t, self.i):
            f.close()


def in_window(ts):
    return WINDOW[0] <= (ts or "") < WINDOW[1]


def dialogue(set_dir, roles, held_from, skipped):
    convs = {}
    with open(os.path.join(set_dir, "strands", "dialogue_turns.jsonl"), encoding="utf-8") as f:
        for line in f:
            r = json.loads(line)
            ts = (r.get("when") or {}).get("ts") or ""
            if in_window(ts):
                skipped["dialogue_window"] += 1
                continue
            if (r.get("x") or {}).get("derivative_covered_by_transcript"):
                skipped["dialogue_prompt_covered"] += 1
                continue
            if not (r.get("text") or "").strip():
                skipped["dialogue_empty"] += 1
                continue
            convs.setdefault((r.get("platform"), r.get("conversation_id")), []).append((r.get("turn_index") or 0, ts, r))
    for key, turns in sorted(convs.items(), key=lambda kv: min(t[1] for t in kv[1])):
        turns.sort(key=lambda t: (t[0], t[1]))
        first = turns[0][2]
        title = f"{first.get('platform')} {first.get('machine')} {turns[0][1][:10]}\n".encode()
        body = "".join(f"[{t[1][:10]} {t[1][11:16]} UTC] {t[2].get('speaker')}:\n{t[2]['text']}\n\n" for t in turns).encode()
        role = roles["HELD"] if turns[0][1][:10] >= held_from else roles["DOCS"]
        role.write(f"{key[0]}:{key[1]}", title, body)


def acts(set_dir, roles, held_from, limit, share, skipped):
    def flush(turn, calls):
        if not calls:
            return
        if int(hashlib.sha256(str(turn).encode()).hexdigest()[:8], 16) % 1000 >= share:
            skipped["acts_turns_outside_share"] += 1
            return
        ts = calls[0][0]
        title = f"{calls[0][1].get('platform')} {calls[0][1].get('machine')} {ts[:10]}\n".encode()
        body = "".join(c[2] for c in calls).encode()
        role = roles["HELD"] if ts[:10] >= held_from else roles["DOCS"]
        role.write(str(turn), title, body)

    turn, calls = None, []
    with open(os.path.join(set_dir, "strands", "tool_events.jsonl"), encoding="utf-8") as f:
        for line in f:
            r = json.loads(line)
            w = r.get("when") or {}
            ts = w.get("call") or w.get("result") or ""
            if in_window(ts):
                skipped["acts_window"] += 1
                continue
            res = r.get("result") or {}
            text = res.get("text") or ""
            if len(text.encode()) > limit:
                skipped["acts_result_over_limit"] += 1
                continue
            if not res.get("present", True):
                skipped["acts_no_result"] += 1
                continue
            args = r.get("args")
            command = args.get("command") if isinstance(args, dict) else None
            if isinstance(command, list):
                command = " ".join(command)
            name = (r.get("tool") or {}).get("name")
            head = f"$ {command}\n" if isinstance(command, str) else f"> {name} {args if isinstance(args, str) else json.dumps(args, ensure_ascii=False)}\n"
            tail = ""
            if res.get("exit_code") not in (None, 0):
                tail = f"exit: {res.get('exit_code')}\n"
            elif res.get("is_error"):
                tail = "error\n"
            piece = head + text + ("" if text.endswith("\n") or not text else "\n") + tail + "\n"
            if r.get("turn_id") != turn:
                flush(turn, calls)
                turn, calls = r.get("turn_id"), []
            calls.append((ts, r, piece))
    flush(turn, calls)


def harness(set_dir, roles, held_from, skipped):
    """[the lead, November 24, Brandon's 05:44Z: the full collection] `harness`: one conversation's system-side text a document (the set's
    harness strand: slash-command wrappers, injected reminders, compaction summaries, checkpoints, errors, environment instructions), each
    event opening with a line `[YYYY-MM-DD HH:MM UTC] KIND:` and its text whole, documents ordered by their first event's time."""
    convs = {}
    with open(os.path.join(set_dir, "strands", "harness_events.jsonl"), encoding="utf-8") as f:
        for line in f:
            r = json.loads(line)
            w = r.get("when")
            ts = (w.get("ts") if isinstance(w, dict) else w) or ""
            if in_window(ts):
                skipped["harness_window"] += 1
                continue
            if not (r.get("text") or "").strip():
                skipped["harness_empty"] += 1
                continue
            convs.setdefault((r.get("platform"), r.get("conversation_id")), []).append((ts, r))
    for key, events in sorted(convs.items(), key=lambda kv: min(e[0] for e in kv[1])):
        events.sort(key=lambda e: e[0])
        first = events[0][1]
        title = f"{first.get('platform')} {first.get('machine')} {events[0][0][:10]}\n".encode()
        body = "".join(f"[{e[0][:10]} {e[0][11:16]} UTC] {e[1].get('kind')}:\n{e[1]['text']}\n\n" for e in events).encode()
        role = roles["HELD"] if events[0][0][:10] >= held_from else roles["DOCS"]
        role.write(f"{key[0]}:{key[1]}", title, body)


def main():
    if len(sys.argv) not in (4, 5, 6):
        sys.exit(__doc__)
    set_dir, out, held_from = sys.argv[1], sys.argv[2], sys.argv[3]
    limit = int(sys.argv[4]) if len(sys.argv) >= 5 else 65536
    share = int(sys.argv[5]) if len(sys.argv) == 6 else 1000
    os.makedirs(out, exist_ok=True)
    skipped = {k: 0 for k in ("dialogue_window", "dialogue_prompt_covered", "dialogue_empty", "acts_window", "acts_result_over_limit", "acts_no_result", "acts_turns_outside_share", "harness_window", "harness_empty")}
    for slice_, build in (("dialogue", lambda r: dialogue(set_dir, r, held_from, skipped)), ("acts", lambda r: acts(set_dir, r, held_from, limit, share, skipped)), ("harness", lambda r: harness(set_dir, r, held_from, skipped))):
        roles = {stem: Role(out, stem, slice_) for stem in ("DOCS", "HELD")}
        build(roles)
        for role in roles.values():
            role.close()
        d, h = roles["DOCS"], roles["HELD"]
        for name in ("train", "prefix"):
            print(f"{name}\t{slice_}\t0\t0\t{d.n}\t{d.n}\t{d.octets}\t{d.octets}\t{d.h.hexdigest()}")
        print(f"held\t{slice_}\t0\t0\t{h.n}\t{h.n}\t{h.octets}\t{h.octets}\t{h.h.hexdigest()}")
    print("HISTORY_PASSAGE left_out " + " ".join(f"{k}={v}" for k, v in skipped.items()), file=sys.stderr)


if __name__ == "__main__":
    main()
