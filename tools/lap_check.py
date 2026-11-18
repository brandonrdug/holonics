#!/usr/bin/env python3
"""Read a lap's run script against the lap procedure (CLAUDE.md, Method, "A line's lap"), before it is dispatched.

A ruler of practice on the host: it reads the script's text and prints one line for each read of the procedure the script
does not name. It never refuses a run and it reads no state. `runs.py start` calls it and prints its lines; a script that
trains nothing prints none.

Reason (November 18): the rule that a lap is reported with its loudness beside its nats stood in the guide from November 15,
and none of the twenty lap scripts of November 18 called `read-loudness`, so none of that day's lap records carries the reading.
A rule that nothing runs does not hold. What a script's text cannot show is left to the guess file and the report: whether an
arm has a control from the same saved state and differs from it by one change (rule 1). Twelve of those twenty scripts say
nothing of a control in their own comments, so a note on that word would read the comment's wording and is not printed.

What it reads, each from the script's own text. A command inside a function counts, a command that stands only in a comment
does not, and nothing is executed; a word inside a quoted string reads as code, which a text ruler cannot tell apart:

  rule 1   a guess is named in the comments (G-1118-16, G169, G-V1)
  rule 4   the training command stands under an outer `timeout` and the card's lock (`flock` on `gpu.lock`)
  rule 5   `read-cavity` is called, and a saved mean (`MEAN.k`) is among the states read
  rule 6   a panel is written (`write-next` or `write-store`)
  rule 7   `read-loudness` is called, or a comment names the companion script that calls it for this lap (`loudness: loud.sh`,
           a file beside the script; November 18: the line's laps L15 to L17 took their loudness from one companion script, and a
           note that prints on a lap that has its reading teaches its reader to pass over it)

  lap_check.py SCRIPT [SCRIPT ...]     print the notes; exit 0 always
"""
import re
import sys
from pathlib import Path

TRAIN = re.compile(r"\btrain-store\b")
COMPANION = re.compile(r"\bloudness:\s*([\w./-]+\.sh)\b")
GUESS = re.compile(r"\bG(?:\d{1,4}|-[0-9A-Z]{1,6}(?:-[0-9A-Z]{1,6})*)\b")


def logical_lines(text):
    """The script's lines with trailing-backslash continuations joined."""
    out, held = [], ""
    for raw in text.split("\n"):
        if raw.rstrip().endswith("\\"):
            held += raw.rstrip()[:-1] + " "
            continue
        out.append(held + raw)
        held = ""
    if held:
        out.append(held)
    return out


def split_comment(line):
    """(code, comment) of one line: a `#` opens a comment at the line's start or after a space, outside quotes."""
    quote = None
    for i, ch in enumerate(line):
        if quote:
            if ch == quote:
                quote = None
        elif ch in "'\"":
            quote = ch
        elif ch == "#" and (i == 0 or line[i - 1].isspace()):
            return line[:i], line[i + 1:]
    return line, ""


def companion_reads(name, beside):
    """Whether the companion script `name`, a file under the directory `beside`, calls `read-loudness` in its code."""
    try:
        text = (Path(beside) / name).read_text(encoding="utf-8", errors="replace")
    except OSError:
        return False
    return any(re.search(r"\bread-loudness\b", split_comment(l)[0]) for l in logical_lines(text))


def notes(text, beside=None):
    """The notes for one script's text: a list of (rule, sentence). Empty when the script trains nothing. `beside` is the script's
    directory, where a companion named in a comment is read."""
    lines = logical_lines(text)
    parts = [split_comment(l) for l in lines]
    code = [c for c, _ in parts]
    comments = "\n".join(m for _, m in parts)
    trains = [c for c in code if TRAIN.search(c)]
    if not trains:
        return []
    body = "\n".join(code)
    found = []
    guess = [g for g in GUESS.findall(comments) if any(ch.isdigit() for ch in g)]
    if not guess:
        found.append((1, "no guess is named in the comments: the guess is fixed as a number before the lap"))
    if not all(re.search(r"\btimeout\b", c) for c in trains):
        found.append((4, "a training command stands under no outer `timeout`: the deadline is fixed once, from the projection"))
    if not (re.search(r"\bflock\b", body) and "gpu.lock" in body):
        found.append((4, "the card's lock is not taken (`flock` on `.local/gpu.lock`): a line's laps take it"))
    if not re.search(r"\bread-cavity\b", body):
        found.append((5, "no `read-cavity`: a line's level is read at its lap's mean"))
    elif not re.search(r"\bMEAN\b", body):
        found.append((5, "`read-cavity` is called and no saved mean (`MEAN.k`) is named: a figure from a lap's end state says that it is one"))
    if not re.search(r"\bwrite-(next|store)\b", body):
        found.append((6, "no panel is written (`write-next` or `write-store`): a report opens with what the machine wrote"))
    if not re.search(r"\bread-loudness\b", body):
        named = COMPANION.search(comments)
        if not named:
            found.append((7, "no `read-loudness`: a lap is reported with its loudness beside its nats"))
        elif beside is not None and not companion_reads(named.group(1), beside):
            found.append((7, f"the companion named for the loudness (`{named.group(1)}`) is not beside the script or calls no `read-loudness`"))
    return found


def report(path):
    """The printed lines for one script."""
    text = Path(path).read_text(encoding="utf-8", errors="replace")
    return [f"LAP_CHECK {Path(path).name} rule={rule}: {sentence}" for rule, sentence in notes(text, Path(path).parent)]


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    for path in sys.argv[1:]:
        for line in report(path):
            print(line)


if __name__ == "__main__":
    main()
