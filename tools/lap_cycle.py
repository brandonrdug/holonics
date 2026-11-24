#!/usr/bin/env -S python3 -I
"""A ruler on the host: where a lap's time on the card went, read from the logs its commands wrote.

Usage: python3 tools/lap_cycle.py LOG [LOG ...]

Each LOG is the output of one athena command of a lap's cycle (the lap's `train-store`, then each read and each write after it).
The ruler reads each log's word (its `FIELD_COMMAND` line), whether it opened the card (`FIELD_CARD_OPEN`) and the time its own
closing line states (`STORE_PASS`, `CAVITY_DONE`, `LOUDNESS_DONE`, `NEXT_WRITE_DONE`, else the last `..._DONE` line; `ms=`), and
prints one line a log, then the cycle: the card's time, the share of it that trained, and the reads' time over the training's. A
held read's log (`read-cavity`) is split by its rows: P (each place alone open, `card_cK_ms`), W (whole masks), F (the frontier),
K (the known stream), S (two streams) and the host's copies and opening, which run inside the read's hold of the card.

Why (November 24, the record of that day on a lap's cycle): on the collection's line a lap trained 34 minutes and its reads held
the card 56, a control with its arm took four hours, and no report of a lap carried the split; three of the four held reads ran
rows that the fourth already computed. A lap's report that carries this ruler's lines shows a read that has outgrown the lap it
reads. The times are the commands' own counters, never a wall clock: a log's wait for the card's lock is not in them.

A log on the host (no `FIELD_CARD_OPEN`) is listed and left out of the card's time. A log with no closing line reads `ms=-` and
is named in `LAP_CYCLE_INCOMPLETE`; the cycle is then a lower bound. It refuses nothing and reads no state.
"""
import os
import re
import sys

CLOSING = ("STORE_PASS ", "CAVITY_DONE", "LOUDNESS_DONE", "NEXT_WRITE_DONE")
ROWS = (("P", "CAVITY_SLICE ", "card_cK_ms"), ("W", "CAVITY_SLICE ", "whole_ms"), ("F", "CAVITY_FRONTIER ", "ms"),
        ("K", "CAVITY_KNOWN ", "ms"), ("S", "CAVITY_STRAND ", "ms"), ("copies", "CAVITY_SLICE ", "host_copy_ms"),
        ("opening", "CAVITY_SLICE ", "host_opening_ms"))


def field(line, key):
    m = re.search(r"(?:^|\s)" + re.escape(key) + r"=(\d+)", line)
    return int(m.group(1)) if m else None


def read(path):
    """One log: its word, whether it opened the card, its own time and, for a held read, its rows' times."""
    word, card, ms, generic, rows = "-", False, None, None, {}
    with open(path, errors="replace") as f:
        for line in f:
            if line.startswith("FIELD_COMMAND "):
                word = line.split()[1]
            elif line.startswith("FIELD_CARD_OPEN"):
                card = True
            elif line.startswith(CLOSING):
                ms = field(line, "ms") if field(line, "ms") is not None else ms
            elif re.match(r"[A-Z0-9_]+_DONE\b", line) and field(line, "ms") is not None:
                generic = field(line, "ms")
            for name, start, key in ROWS:
                if line.startswith(start) and field(line, key) is not None:
                    rows[name] = rows.get(name, 0) + field(line, key)
    return {"log": os.path.basename(path), "word": word, "card": card, "ms": ms if ms is not None else generic, "rows": rows}


def cycle(logs):
    """The cycle's sums: the card's time, the training's, the reads' (every card log that did not train) and the unread logs."""
    card = [l for l in logs if l["card"] and l["ms"] is not None]
    train = sum(l["ms"] for l in card if l["word"] == "train-store")
    total = sum(l["ms"] for l in card)
    return {"card_ms": total, "train_ms": train, "reads_ms": total - train,
            "host_ms": sum(l["ms"] for l in logs if not l["card"] and l["ms"] is not None),
            "incomplete": [l["log"] for l in logs if l["ms"] is None]}


def lines(logs):
    out = []
    for l in logs:
        rows = "".join(f" {k}={l['rows'][k]}" for k, _, _ in ROWS if k in l["rows"])
        out.append(f"LAP_CYCLE log={l['log']} word={l['word']} surface={'card' if l['card'] else 'host'} "
                   f"ms={l['ms'] if l['ms'] is not None else '-'}" + (f" rows:{rows}" if rows else ""))
    c = cycle(logs)
    share = f"{c['train_ms'] / c['card_ms']:.3f}" if c["card_ms"] else "-"
    over = f"{c['reads_ms'] / c['train_ms']:.2f}" if c["train_ms"] else "-"
    out.append(f"LAP_CYCLE_TOTAL card_ms={c['card_ms']} train_ms={c['train_ms']} reads_ms={c['reads_ms']} "
               f"train_share={share} reads_over_train={over} host_ms={c['host_ms']} card_minutes={c['card_ms'] / 60000:.1f}")
    if c["incomplete"]:
        out.append("LAP_CYCLE_INCOMPLETE " + " ".join(c["incomplete"]))
    return out


if __name__ == "__main__":
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    print("\n".join(lines([read(p) for p in sys.argv[1:]])))
