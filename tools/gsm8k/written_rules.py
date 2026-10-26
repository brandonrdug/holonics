"""Written-rule reads of releases over the held-out GSM8K problems.

An exterior reading: nothing here enters the machine, and no release is graded against the answer
key (`README.md`). Record:
research/records/2026-10-26_THE_HELD_OUT_PROBLEMS_ARE_READ_BY_WRITTEN_RULES_AND_THE_MARKUP_IS_WRITTEN_AT_ITS_EQUALS.md

    python3 -I tools/gsm8k/written_rules.py HELD TRAIN DIR [DIR ...]
    python3 -I tools/gsm8k/written_rules.py HELD TRAIN pair DIR_A DIR_B
    python3 -I tools/gsm8k/written_rules.py HELD TRAIN heard DIR [DIR ...]
    python3 -I tools/gsm8k/written_rules.py HELD TRAIN rings DIR [DIR ...]

HELD is the held-out text and TRAIN the training text, each a run of problems separated by a blank
line (a question line, then its answer lines). Each DIR holds `FREE.tsv` and `MARKS.tsv` as
`read-unit-tower-written` or `ngram_release.py` writes them; the word `reference` reads the
held-out answers themselves. One line is printed per DIR. With `pair`, a `PAIRED` line follows the
two DIRs' lines: on met and on never-met calculations, how many only A writes right at the equals,
how many only B, and how many both, so two releases are compared calculation by calculation. With
`heard`, a `HEARD` line follows each DIR's line: the calculations at the equals binned by how many
times TRAIN holds their `<<expression=c>>` whole (0, 1, 2-3, 4-7, 8-15, 16 or more), right of each
bin. Read on training problems, a calculation's own place in TRAIN is one of its hearings. With
`rings`, a `RINGS` line follows each DIR's line: on the never-met sums and differences of two
whole numerals, how many written values are integers right modulo 9, 10 and 11 (the rings where the
base 10 turns, collapses and reflects), each beside its shifted foil, the written value of the next
such calculation read against this one's exact value (the last against the first), and how many
are right on all three (modulo 990). An unfinished or fractional written value is right on none.

The rules, fixed before any release was read:

- words are the lowercase runs of `a`-`z`; the common words are TRAIN's 100 most frequent words of
  at least four letters; a question's content words are its words of at least four letters that are
  not common.
- a free release's answer is its bytes up to its first blank line.
- (a) on the problem: the answer holds at least one of the question's content words.
- (b) markup: each `<<expression=c>>` in the answer whose expression is numerals, `.`, `+ - * /`
  and parentheses is right when `c` is its exact value (rationals throughout).
- (c) operands from the question: the answer's first such calculation takes every operand from the
  numerals the question writes, or from the values of the number words in `NUMBER_WORDS`.
- (b) at the equals: at each calculation of a held-out answer, the release written after its `=`
  is right when the bytes before its first `>>` are the expression's exact value; a release
  without `>>` is unfinished and not right. A calculation is met when the training text holds the
  held-out `<<expression=c>>` whole.
"""

import codecs
import re
import sys
from collections import Counter
from fractions import Fraction

NUMBER_WORDS = {
    "one": 1, "two": 2, "three": 3, "four": 4, "five": 5, "six": 6, "seven": 7, "eight": 8,
    "nine": 9, "ten": 10, "eleven": 11, "twelve": 12, "twice": 2, "double": 2, "triple": 3,
    "thrice": 3, "half": 2, "dozen": 12, "hundred": 100, "thousand": 1000, "quarter": 4,
    "third": 3,
}
WORD = re.compile(r"[a-z]+")
NUMERAL = re.compile(r"\d[\d,]*\.?\d*|\.\d+")
CALC = re.compile(r"<<([^<>=]*)=([^<>]*)>>")
# A hearing count's bin by its bit length: 0, 1, 2-3, 4-7, 8-15, and 16 or more (clamped at 16).
HEARD_BINS = ["0", "1", "2-3", "4-7", "8-15", "16+"]


def problems_of(text):
    """The problems as `read-unit-tower-written` splits them: (question, answer) pairs."""
    out = []
    for p in text.split(b"\n\n"):
        if p.strip(b"\n"):
            q, _, a = p.partition(b"\n")
            out.append((q, a + b"\n" if not a.endswith(b"\n") else a))
    return out


def calculations_of(answer):
    """Each `<<` with an `=` before its `>>`: the expression, in the reader's order."""
    found, i = [], 0
    while i + 1 < len(answer):
        if answer[i : i + 2] == b"<<":
            close = answer.find(b">>", i + 2)
            close = len(answer) if close < 0 else close
            eq = answer.find(b"=", i + 2, close)
            if eq >= 0:
                found.append(answer[i + 2 : eq])
            i = close
        else:
            i += 1
    return found


def value(expression):
    """The exact value of an expression of numerals, `.`, `+ - * /` and parentheses, else None."""
    e = expression.replace(" ", "")
    if not re.fullmatch(r"[0-9.+\-*/()]+", e) or "**" in e:
        return None
    tokens = re.findall(r"\d*\.\d+|\d+|[+\-*/()]", e)
    if "".join(tokens) != e:
        return None
    try:
        return eval("".join(f"Fraction('{t}')" if t[0].isdigit() or t[0] == "." else t for t in tokens), {"Fraction": Fraction})
    except (ZeroDivisionError, SyntaxError, ValueError, TypeError):
        # TypeError: a numeral written against a parenthesis, `8(2/3)`, reads as a call.
        return None


def number(text):
    try:
        return Fraction(text.strip().replace(",", ""))
    except (ValueError, ZeroDivisionError):
        return None


def question_numbers(question):
    found = set()
    for t in NUMERAL.findall(question):
        n = number(t.rstrip("."))
        if n is not None:
            found.add(n)
    found.update(Fraction(NUMBER_WORDS[w]) for w in WORD.findall(question.lower()) if w in NUMBER_WORDS)
    return found


def unescape(field):
    return codecs.escape_decode(field.encode("latin-1"))[0]


def read_tsv(path, columns):
    rows = []
    with open(path, encoding="latin-1") as f:
        for line in f:
            parts = line.rstrip("\n").split("\t")
            if len(parts) != columns:
                raise SystemExit(f"{path}: a line with {len(parts)} fields, not {columns}")
            rows.append(parts)
    return rows


def free_reads(problems, answers, common):
    on = calcs = right = firsts = from_question = 0
    for (q, _), answer in zip(problems, answers):
        question = q.decode("utf-8", "replace")
        text = answer.split(b"\n\n")[0].decode("utf-8", "replace")
        content = {w for w in WORD.findall(question.lower()) if len(w) >= 4 and w not in common}
        on += bool(content & set(WORD.findall(text.lower())))
        first = None
        for expression, c in CALC.findall(text):
            v, w = value(expression), number(c)
            if v is None or w is None:
                continue
            calcs += 1
            right += v == w
            if first is None:
                first = expression
        if first is not None:
            firsts += 1
            operands = [Fraction(t) for t in re.findall(r"\d*\.\d+|\d+", first)]
            from_question += all(o in question_numbers(question) for o in operands)
    return on, calcs, right, firsts, from_question


def mark_reads(problems, marks, train):
    expected = [(i, j, e) for i, (_, a) in enumerate(problems) for j, e in enumerate(calculations_of(a))]
    if [(int(r[0]), int(r[1]), unescape(r[2])) for r in marks] != expected:
        raise SystemExit("MARKS.tsv does not hold the held-out calculations in the reader's order")
    seen = {"met": [0, 0], "never": [0, 0]}
    by_op = Counter()
    each = []
    for (i, j, expression), row in zip(expected, marks):
        release = unescape(row[3])
        answer = problems[i][1].decode("utf-8", "replace")
        reference = [m for m in CALC.finditer(answer)]
        e = expression.decode()
        c = next(m.group(2) for m in reference if m.group(1) == e)
        heard = train.count(f"<<{e}={c}>>")
        kind = "met" if heard else "never"
        v = value(e)
        end = release.find(b">>")
        w = number(release[:end].decode("utf-8", "replace")) if end >= 0 else None
        good = v is not None and w is not None and v == w
        seen[kind][0] += 1
        seen[kind][1] += good
        each.append((kind, good, heard, e, v, w))
        op = re.fullmatch(r"\d*\.?\d+([+\-*/])\d*\.?\d+", e.replace(" ", ""))
        if op:
            by_op[op.group(1), "n"] += 1
            by_op[op.group(1), "right"] += good
    return seen, by_op, each


def rings_line(each):
    """The never-met sums and differences, read on the rings 9, 10 and 11 and beside their foil."""
    read = [
        (v, w) for kind, _, _, e, v, w in each
        if kind == "never" and re.fullmatch(r"\d+[+\-]\d+", e.replace(" ", ""))
    ]
    if not read:
        return "n=0"
    shifted = [(v, read[(i + 1) % len(read)][1]) for i, (v, _) in enumerate(read)]
    on = lambda m, v, w: w is not None and w.denominator == 1 and (v - w) % m == 0
    out = [f"n={len(read)}"]
    for m in (9, 10, 11, 990):
        right = sum(on(m, v, w) for v, w in read)
        foil = sum(on(m, v, w) for v, w in shifted)
        out.append(f"mod{m}={right} foil{m}={foil}")
    return " ".join(out)


def main():
    if len(sys.argv) < 4:
        raise SystemExit(__doc__)
    pair, heard, rings = sys.argv[3] == "pair", sys.argv[3] == "heard", sys.argv[3] == "rings"
    dirs = sys.argv[4:] if pair or heard or rings else sys.argv[3:]
    if pair and (len(dirs) != 2 or "reference" in dirs):
        raise SystemExit("pair reads two release directories")
    goods = []
    held, train = (open(p, "rb").read() for p in sys.argv[1:3])
    problems = problems_of(held)
    train_text = train.decode("utf-8", "replace")
    counts = Counter(w for w in WORD.findall(train_text.lower()) if len(w) >= 4)
    common = {w for w, _ in counts.most_common(100)}
    for d in dirs:
        if d == "reference":
            answers = [a for _, a in problems]
            marks = None
        else:
            free = read_tsv(f"{d}/FREE.tsv", 2)
            if [int(r[0]) for r in free] != list(range(len(problems))):
                raise SystemExit(f"{d}/FREE.tsv does not hold one release a problem in order")
            answers = [unescape(r[1]) for r in free]
            marks = read_tsv(f"{d}/MARKS.tsv", 4)
        on, calcs, right, firsts, from_question = free_reads(problems, answers, common)
        line = (
            f"WRITTEN dir={d} problems={len(problems)} a_on_problem={on} b_free_calculations={calcs} "
            f"b_free_right={right} c_first_calculations={firsts} c_from_question={from_question}"
        )
        if marks is not None:
            seen, by_op, each = mark_reads(problems, marks, train_text)
            goods.append(each)
            n, r = seen["met"][0] + seen["never"][0], seen["met"][1] + seen["never"][1]
            ops = " ".join(f"{op}={by_op[op, 'right']}/{by_op[op, 'n']}" for op in "+-*/")
            line += (
                f" b_equals={r}/{n} met={seen['met'][1]}/{seen['met'][0]} "
                f"never_met={seen['never'][1]}/{seen['never'][0]} binary {ops}"
            )
        print(line)
        if rings and marks is not None:
            print(f"RINGS dir={d} " + rings_line(each))
        if heard and marks is not None:
            bins = Counter()
            for _, good, k, *_ in each:
                b = HEARD_BINS[min(k, 16).bit_length()]
                bins[b, "n"] += 1
                bins[b, "right"] += good
            print(f"HEARD dir={d} " + " ".join(f"{b}={bins[b, 'right']}/{bins[b, 'n']}" for b in HEARD_BINS))
    if pair:
        counts = Counter((kind, a, b) for (kind, a, *_), (_, b, *_) in zip(*goods))
        print(
            "PAIRED " + " ".join(
                f"{kind}_only_a={counts[kind, True, False]} {kind}_only_b={counts[kind, False, True]} "
                f"{kind}_both={counts[kind, True, True]}" for kind in ("met", "never")
            )
        )


if __name__ == "__main__":
    main()
