#!/usr/bin/env -S python3 -I
"""A ruler for the arithmetic world's held reads (the theory thread's anchor and answer reads of Build A, November 16).

  forms_table.py make STORE OUT     writes OUT, the table `read-forms` reads (`label<TAB>prompt<TAB>run`, a line feed written `\\n`):
                                    each held sum of two operands (`HELD_FORMS_arithmetic.tsv`) after its symbols (`a + b = `), its words
                                    (`a plus b equals `), its foil (`a plux b eqvals `), a null foil of the same lengths (letters drawn
                                    by the world's key from those its operator's word and `equals` lack) and swapped words (another
                                    operation's word: `times` before a sum's value, `plus` before a difference's, `minus` before a
                                    product's), and each held record (`HELD_arithmetic.*`) cut after its `= `; the run is the value and its
                                    line feed. The null foil and the swapped words are the theory thread's controls of 17:58 UTC: the foil
                                    is one letter from the operator's word, so for a field that reads word shapes it is a noisy source of
                                    the operator, not a null.
  forms_table.py gsm8k STORE OUT N  writes OUT from the word problems' held role (GSM8K's test split, `HELD_words.*`): the first N problems,
                                    each its question and a line feed as the prompt and GSM8K's own answer as the run.
  forms_table.py acts STORE OUT N [R]  writes OUT, the prompts of N acts for `write-forms` or `write-acts`: each R (three) held records at
                                    met lengths, one after another, as a prompt (`act:N`), and an empty run.
  forms_table.py react WRITTEN OUT   reads `write-forms`' OUT/forms.written for the acts and writes OUT, the world's reactions as a table for
                                    `read-forms`: each act's prompt and draft up to its first `= ` (or its line feed) as the prompt, the
                                    world's reaction as the run (`world:read:K` where the world read an expression, `world:refused:K` where
                                    it answered `?`), the world as crates/athena/src/world.rs reads it.
  forms_table.py sum OUT LOG        sums a `read-forms` log over the table: by form and the operands' lengths (met: one to six digits, as
                                    training; far: seven to nine), by the digit's place counted from the value's last, and for sums of two
                                    operands by whether a carry entered the digit's column. Codes in millionths of a bit a place.

A ruler on the host, outside the machine: it writes the held forms and adds up what the reading printed; it never enters a law. The world is
synthetic (tools/arithmetic_world.py), so its forms and values are printed freely."""
import hashlib
import os
import sys
from collections import defaultdict

WORDS = {"+": "plus", "-": "minus", "*": "times"}
SWAP = {"+": "*", "-": "+", "*": "-"}
KEY = "arith-2026-11-16"


def null_word(word, held, k):
    """A word of `word`'s length, its letters drawn by the world's key from those the operator's word and `equals` lack."""
    pool = sorted(set("abcdefghijklmnopqrstuvwxyz") - set(word) - set("equals"))
    out = []
    for j in range(len(word)):
        h = hashlib.sha256(f"{KEY}:null:{held}:{k}:{j}".encode()).digest()
        out.append(pool[int.from_bytes(h[:4], "big") % len(pool)])
    return "".join(out)


def esc(t):
    return t.replace("\n", "\\n")


def make(store, out):
    rows = []
    with open(os.path.join(store, "HELD_FORMS_arithmetic.tsv")) as f:
        head = f.readline().rstrip("\n").split("\t")
        for line in f:
            r = dict(zip(head, line.rstrip("\n").split("\t")))
            a, _, b = r["symbols"].split()[:3]
            word = WORDS[r["op"]]
            r["null"] = f"{a} {null_word(word, r['held'], 0)} {b} {null_word('equals', r['held'], 1)}"
            r["swapped"] = f"{a} {WORDS[SWAP[r['op']]]} {b} equals"
            for form in ("symbols", "words", "foil", "null", "swapped"):
                rows.append((f"anchor:{r['lengths']}:{r['op']}:{form}:{r['held']}", r[form] + " ", r["value"] + "\n"))
    data = open(os.path.join(store, "HELD_arithmetic.bin"), "rb").read().decode()
    with open(os.path.join(store, "HELD_IDS_arithmetic.txt")) as f:
        ids = [l.strip() for l in f]
    records = data.splitlines(keepends=True)
    assert len(records) == len(ids), "a held file whose records and identifiers differ in count"
    for ident, rec in zip(ids, records):
        expr, value = rec.split(" = ")
        rows.append((f"answer:{ident.split(':')[0].split('-')[1]}:{ident.split(':')[1]}", expr + " = ", value))
    with open(out, "x") as f:
        for label, prompt, run in rows:
            f.write(f"{label}\t{esc(prompt)}\t{esc(run)}\n")
    print(f"FORMS_TABLE rows={len(rows)}")


def gsm8k(store, out, n):
    data = open(os.path.join(store, "HELD_words.bin"), "rb").read()
    rows, at = [], 0
    with open(os.path.join(store, "HELD_words.tsv")) as f:
        f.readline()
        for k, line in enumerate(f):
            octets = int(line.split("\t")[2])
            doc = data[at:at + octets].decode()
            at += octets
            if k < n:
                question, answer = doc.split("\n", 1)
                rows.append((f"gsm8k:test:{k}", question + "\n", answer))
    with open(out, "x") as f:
        for label, prompt, run in rows:
            f.write(f"{label}\t{esc(prompt)}\t{esc(run)}\n")
    print(f"FORMS_TABLE rows={len(rows)}")


def acts(store, out, n, records=3):
    data = open(os.path.join(store, "HELD_arithmetic.bin"), "rb").read().decode()
    with open(os.path.join(store, "HELD_IDS_arithmetic.txt")) as f:
        ids = [l.strip() for l in f]
    met = [r for r, i in zip(data.splitlines(keepends=True), ids) if i.startswith("held-met")]
    with open(out, "x") as f:
        for k in range(n):
            prompt = "".join(met[(records * k + j) % len(met)] for j in range(records))
            f.write(f"act:{k}\t{esc(prompt)}\t{esc('?')}\n")
    print(f"FORMS_TABLE rows={n}")


class Refuse(Exception):
    pass


def world_value(text):
    """The world's value of an expression as crates/athena/src/world.rs reads it, or None."""
    t, at = text, [0]

    def skip():
        while at[0] < len(t) and t[at[0]] == " ":
            at[0] += 1

    def atom():
        skip()
        if at[0] < len(t) and t[at[0]] == "(":
            at[0] += 1
            v = total()
            skip()
            if at[0] >= len(t) or t[at[0]] != ")":
                raise Refuse
            at[0] += 1
            return v
        start = at[0]
        while at[0] < len(t) and t[at[0]].isdigit():
            at[0] += 1
        digits = t[start:at[0]]
        if not digits or (len(digits) > 1 and digits[0] == "0"):
            raise Refuse
        return int(digits)

    def product():
        v = atom()
        while True:
            skip()
            if at[0] < len(t) and t[at[0]] == "*":
                at[0] += 1
                v *= atom()
            else:
                return v

    def total():
        v = product()
        while True:
            skip()
            if at[0] < len(t) and t[at[0]] in "+-":
                op = t[at[0]]
                at[0] += 1
                w = product()
                v = v + w if op == "+" else v - w
            else:
                return v

    try:
        v = total()
        skip()
        if at[0] != len(t) or abs(v) >= 2**127:
            return None
        return v
    except (Refuse, RecursionError):
        return None


def react(written, out):
    rows = []
    for line in open(os.path.join(written, "forms.written")):
        label, prompt, draft, _ = line.rstrip("\n").split("\t")
        prompt, draft = prompt.replace("\\n", "\n"), draft.replace("\\n", "\n")
        eq, feed = draft.find("= "), draft.find("\n")
        if eq >= 0 and (feed < 0 or eq < feed):
            v = world_value(draft[:eq])
            read, reaction, kind = draft[:eq + 2], (f"{v}\n" if v is not None else "?\n"), ("read" if v is not None else "refused")
        elif feed >= 0:
            read, reaction, kind = draft[:feed + 1], "?\n", "refused"
        else:
            read, reaction, kind = draft, "\n?\n", "refused"
        rows.append((f"world:{kind}:{label.split(':')[1]}", prompt + read, reaction))
    with open(out, "x") as f:
        for label, prompt, run in rows:
            f.write(f"{label}\t{esc(prompt)}\t{esc(run)}\n")
    print(f"WORLD_TABLE rows={len(rows)} read={sum(1 for r in rows if ':read:' in r[0])}")


def carries(a, b, op, places):
    """For a + b (or a − b, as a borrow), whether column j (from the last digit) took a carry from column j − 1."""
    if op == "-" and a < b:
        a, b = b, a
    out = []
    for j in range(places):
        m = 10**j
        if op == "+":
            out.append(j > 0 and (a % m) + (b % m) >= m)
        elif op == "-":
            out.append(j > 0 and (a % m) < (b % m))
        else:
            out.append(None)
    return out


def total(xs):
    return sum(c for c, _ in xs), sum(n for _, n in xs)


def summ(table, log):
    rows = {}
    for line in open(table):
        label, prompt, run = line.rstrip("\n").split("\t")
        rows[label] = (prompt.replace("\\n", "\n"), run.replace("\\n", "\n"))
    sums = defaultdict(list)
    for line in open(log):
        if not line.startswith("FORMS_ROW "):
            continue
        f = dict(kv.split("=", 1) for kv in line.split()[1:])
        label = f["label"]
        prompt, run = rows[label]
        codes = [int(c) for c in f["by_place"].split(",")]
        value = run.rstrip("\n")
        digits = value.lstrip("-")
        kind = label.split(":")
        if kind[0] == "anchor":
            _, lengths, op, form, _ = kind
            key = (form, lengths)
            a, b = (int(x) for x in prompt.split()[::2][:2])
        else:
            _, lengths, _ = kind
            key = ("answer", lengths)
            op, a, b = None, None, None
            parts = prompt.split()
            if len(parts) == 4 and "(" not in prompt:
                a, op, b = int(parts[0]), parts[1], int(parts[2])
        sums[key + ("all",)].append((sum(codes), len(codes)))
        sums[key + ("feed",)].append((codes[-1], 1))
        nd = len(digits)
        cs = carries(a, b, op, nd) if op in ("+", "-") else [None] * nd
        for i, ch in enumerate(value):
            if ch == "-":
                sums[key + ("sign",)].append((codes[i], 1))
                continue
            j = len(value) - 1 - i
            sums[key + (f"digit{min(j, 6)}",)].append((codes[i], 1))
            if i == len(value) - nd:
                sums[key + ("lead",)].append((codes[i], 1))
            if op in ("+", "-") and j > 0:
                sums[key + (f"{op}carry" if cs[j] else f"{op}clear",)].append((codes[i], 1))
            if op in ("+", "-") and j == 0:
                sums[key + (f"{op}units",)].append((codes[i], 1))
    for key in sorted(sums):
        c, n = total(sums[key])
        print(f"FORMS_SUM form={key[0]} lengths={key[1]} part={key[2]} places={n} code={c // n if n else 0}")


if __name__ == "__main__":
    if sys.argv[1] == "make":
        make(sys.argv[2], sys.argv[3])
    elif sys.argv[1] == "acts":
        acts(sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5]) if len(sys.argv) > 5 else 3)
    elif sys.argv[1] == "react":
        react(sys.argv[2], sys.argv[3])
    elif sys.argv[1] == "gsm8k":
        gsm8k(sys.argv[2], sys.argv[3], int(sys.argv[4]))
    elif sys.argv[1] == "sum":
        summ(sys.argv[2], sys.argv[3])
    else:
        sys.exit(__doc__)
