#!/usr/bin/env -S python3 -I
"""records_index.py: research/records/INDEX.md, every dated record on one line under its month, from the file names alone (C9 of
the consolidation, #603; docs/plans/THE_CONSOLIDATION.md). A host instrument: it lists a directory and writes one file. No law, no
state.

  records_index.py [ROOT]         print the index and its summary line
  records_index.py write [ROOT]   write ROOT/research/records/INDEX.md
  records_index.py check [ROOT]   exit 1 where INDEX.md is not what the file names give today, naming the first line that differs

Reason: the directory holds more entries than GitHub's listing shows (it stops at the first 1,000), the reading routes of
research/records/README.md lead to records by subject and list a part of them, and a record is otherwise found only by a search of
file names in capitals.

A record is a file `YYYY-MM-DD_TITLE_WORDS.md` directly under research/records. Its line is its date and its title, linked to the
file. The title is the file name's words in sentence case: the first word takes a capital and the rest are lowered, but for a word
with a digit in it (`AC1`, `GSM8K`), a one-letter word other than `A`, and the names and acronyms of NAMES, which read as the
records and guides write them (a name's `S` after it is kept: `ATHENAS` reads `Athenas`). A file name carries no case and no
punctuation, so nothing else is restored. NAMES was read once from the records' and guides' own prose (the title words they write
with a capital at least twelve times in thirteen); a name it lacks reads in lower case until it is added.

A receipts directory is a dated directory beside the records, or a directory under research/records/receipts, that holds at least
one file; it is counted under the month of its date (a prefix `YYYY-MM-DD` or a suffix `-YYYYMMDD`). A dated file beside the
records that is no `.md`, and a file directly under receipts/, is a receipt file that stands alone. README.md and INDEX.md are not
read, and any other entry is counted as unread and named on the summary's side, never in the index.

ROOT defaults to the directory above this file. tools/test_records_index.py holds the controls and reads the committed index
against the tree in gate 1, so a record added without `write` fails there.
"""
import os
import re
import sys
from urllib.parse import quote

RECORDS = "research/records"
INDEX = "INDEX.md"
RECORD = re.compile(r"^(\d{4})-(\d{2})-(\d{2})_(.+)\.md$")
PREFIX = re.compile(r"^(\d{4})-(\d{2})-\d{2}(?=[_-])")
SUFFIX = re.compile(r"-(\d{4})(\d{2})\d{2}$")
MONTHS = ("January", "February", "March", "April", "May", "June", "July", "August", "September", "October", "November", "December")
NAMES = (
    "ABI", "AC", "Arakelov", "Athena", "August", "BSD", "Bayes", "Bianchi", "Bohr", "Brandon", "Bruijn", "Burgers", "Butler", "CLI",
    "CM", "CTC", "CUDA", "Cauchy", "Claude", "Codex", "Copson", "DAG", "December", "DeepSeek", "Demeter", "Einstein", "Eros",
    "Euclidean", "Euler", "Farey", "Fisher", "Floquet", "Foster", "Fourier", "Frobenius", "GPU", "Galois", "Gauss", "Gaussian",
    "Gemma", "Gram", "Gronwall", "Gross", "HNA", "HNN", "Haar", "Hadamard", "Hamiltonian", "Hankel", "Hephaestus", "Hessian",
    "Hodge", "Holarchies", "Holarchy", "Holon", "Holonic", "Holonics", "Hopf", "Hurwitz", "Jacobi", "Jacobian", "Jensen", "John",
    "July", "Kirchhoff", "Koestler", "LC", "LLM", "Landau", "Laplacian", "Lean", "Leibniz", "Lipschitz", "Lorentzian", "MNIST",
    "Markov", "Maxwell", "Mellin", "Millennium", "Mills", "Mordell", "Navier", "Newman", "Newton", "November", "OCR", "ONNX",
    "October", "PDE", "PPM", "Phoenix", "Poincare", "Poisson", "Poynting", "RH", "Ratatui", "Riccati", "Ricci", "Riemann", "Rubik",
    "Rust", "SKE", "Schur", "Schwarz", "September", "Sol", "Soulkiller", "Stirling", "Stokes", "Tunnell", "UAR", "Weil", "Weyl",
    "Yang", "Zagier",
)
WRITTEN = {name.upper(): name for name in NAMES}


def cased(part, first):
    """One word of a file name (or one side of a hyphen in it) as a title writes it."""
    upper = part.upper()
    if upper in WRITTEN:
        return WRITTEN[upper]
    if upper.endswith("S") and len(upper) > 3 and upper[:-1] in WRITTEN:
        return WRITTEN[upper[:-1]] + "s"
    if any(c.isdigit() for c in part) or (len(part) == 1 and upper != "A"):
        return part
    return part.capitalize() if first else part.lower()


def title(words):
    """`THE_LINE_FLAILS` as `The line flails`: the words of a record's file name in sentence case."""
    out = []
    for word in words.split("_"):
        if word:
            out.append("-".join(cased(part, not out and i == 0) for i, part in enumerate(word.split("-"))))
    return " ".join(out)


def holds_file(path):
    return any(files for _, _, files in os.walk(path))


def month_of(name):
    m = PREFIX.match(name) or SUFFIX.search(name)
    return (int(m.group(1)), int(m.group(2))) if m else None


def survey(root):
    """The directory read once: records as (date, file name), receipts directories by month beside the records and under receipts/,
    the receipt files that stand alone, and the entries that are none of these."""
    base = os.path.join(root, RECORDS)
    records, beside, under, alone, unread = [], {}, {}, [], []
    for name in sorted(os.listdir(base)):
        path = os.path.join(base, name)
        m = RECORD.match(name)
        if os.path.isdir(path):
            if name == "receipts":
                for entry in sorted(os.listdir(path)):
                    inner = os.path.join(path, entry)
                    if not os.path.isdir(inner):
                        alone.append("receipts/" + entry)
                    elif holds_file(inner):
                        under[month_of(entry)] = under.get(month_of(entry), 0) + 1
            elif PREFIX.match(name):
                if holds_file(path):
                    beside[month_of(name)] = beside.get(month_of(name), 0) + 1
            else:
                unread.append(name + "/")
        elif m:
            records.append((f"{m.group(1)}-{m.group(2)}-{m.group(3)}", name))
        elif PREFIX.match(name):
            alone.append(name)
        elif name not in ("README.md", INDEX):
            unread.append(name)
    return records, beside, under, alone, unread


def month_name(month):
    return f"{MONTHS[month[1] - 1]} {month[0]}" if month else "No date"


def index(root):
    """The index's text and its counts, from ROOT's file names."""
    records, beside, under, alone, unread = survey(root)
    by_month = {}
    for date, name in records:
        by_month.setdefault((int(date[:4]), int(date[5:7])), []).append((date, name))
    months = sorted(set(by_month) | {m for m in list(beside) + list(under) if m}, reverse=True)
    if None in beside or None in under:
        months.append(None)
    dirs_beside, dirs_under = sum(beside.values()), sum(under.values())
    dated = sorted(by_month)
    span = f" from {month_name(dated[0])} to {month_name(dated[-1])}" if dated else ""
    lines = [
        "# Records by date",
        "",
        "Every dated record of this directory, the newest month first, one line each: its date and its file name's words in sentence",
        "case, linked to the record. `python3 tools/records_index.py write` generates this file from the file names alone, and its",
        "control in gate 1 (`tools/test_records_index.py`) fails while the file is behind them, so no line here is edited by hand. A",
        "file name carries no case and no punctuation: a title reads without its apostrophes and commas, and a name or an acronym",
        "keeps its capitals where the tool's table holds it. The [reading routes](README.md) lead to records by subject. This list is",
        "for finding a record by its date or by a word of its title, and it reaches the entries that GitHub's listing of the",
        "directory leaves out (the listing stops at 1,000).",
        "",
        f"{len(records):,} records{span}. {dirs_beside + dirs_under:,} receipts directories: {dirs_beside:,} beside the records and "
        f"{dirs_under:,} under [`receipts/`](receipts/). Receipt files that stand alone: {len(alone):,}.",
        "",
        "| Month | Records | Receipts directories |",
        "|---|---|---|",
    ]
    for month in months:
        name = month_name(month)
        link = f"[{name}](#{name.lower().replace(' ', '-')})" if month in by_month else name
        lines.append(f"| {link} | {len(by_month.get(month, ())):,} | {beside.get(month, 0) + under.get(month, 0):,} |")
    for month in months:
        if month not in by_month:
            continue
        lines += ["", f"## {month_name(month)}", ""]
        for date, name in sorted(sorted(by_month[month], key=lambda r: r[1]), key=lambda r: r[0], reverse=True):
            lines.append(f"- {date} [{title(RECORD.match(name).group(4))}]({quote(name)})")
    text = "\n".join(lines) + "\n"
    counts = {"records": len(records), "months": len(by_month), "receipts_dirs": dirs_beside + dirs_under, "alone": len(alone),
              "unread": len(unread)}
    return text, counts, unread


def summary(counts, unread):
    print("RECORDS_INDEX " + " ".join(f"{k}={v}" for k, v in counts.items()))
    for name in unread:
        print(f"UNREAD {RECORDS}/{name}")


def write(root):
    text, counts, unread = index(root)
    with open(os.path.join(root, RECORDS, INDEX), "w", encoding="utf-8", newline="\n") as out:
        out.write(text)
    summary(counts, unread)
    return counts


def check(root):
    """True where the index on disk is what the file names give; else the first line that differs is printed."""
    text, counts, unread = index(root)
    path = os.path.join(root, RECORDS, INDEX)
    held = open(path, encoding="utf-8").read() if os.path.isfile(path) else ""
    summary(counts, unread)
    if held == text:
        return True
    want, have = text.split("\n"), held.split("\n")
    n = next((i for i, (a, b) in enumerate(zip(want, have)) if a != b), min(len(want), len(have)))
    print(f"STALE {RECORDS}/{INDEX}:{n + 1} holds `{(have[n] if n < len(have) else '')[:120]}`, "
          f"the file names give `{(want[n] if n < len(want) else '')[:120]}`; run `python3 tools/records_index.py write`")
    return False


def main(argv):
    here = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    words = argv[1:]
    mode = words.pop(0) if words and words[0] in ("write", "check") else "print"
    if len(words) > 1 or (words and not os.path.isdir(os.path.join(words[0], RECORDS))):
        sys.exit(__doc__)
    root = words[0] if words else here
    if mode == "write":
        write(root)
    elif mode == "check":
        sys.exit(0 if check(root) else 1)
    else:
        text, counts, unread = index(root)
        sys.stdout.write(text)
        summary(counts, unread)


if __name__ == "__main__":
    main(sys.argv)
