"""Exterior terrain that generates its truth: similar GSM8K problems with new numbers.

    python3 -I tools/gsm8k_variants.py IN OUT --variants 2 --seed S [--tries 64]

An exterior tool (record 2026-11-01, section 15.5). It reads passages of text, writes passages of
text, and a sidecar of roles for the reading's measurement. Only the text passages ever reach the
machine, held out like their originals; the sidecar and the originals stay exterior. No solver of
the problems is written here: only the calculations already annotated in a solution are
re-evaluated, exactly, in their own order. The tool is never a receiver, a family, a stage or a
predictor (antipattern record 2026-09-29: catered machinery).

Input: problems separated by one blank line. A problem is one question line, solution lines in
which a calculation is annotated `<<expr=result>>` (`+ - * /`, parentheses, decimals), and a last
line `#### answer`.

A variant of a problem:

1. Every number of the question (a maximal digit run with an optional decimal part; commas inside
   a number such as `1,000` belong to it) is replaced by another number of the same digit count,
   the same decimal places and the same comma grouping. A leading digit is nonzero when the
   original's was, and a last decimal digit is nonzero when the original's was. Equal values in
   the question are one role (the roles are the distinct values in order of first appearance, so
   `q:0` is the first), and all their occurrences take one replacement (agent-inferred: an
   operand cannot tell two equal question numbers apart).
2. The solution's calculations are re-evaluated in order with `fractions.Fraction`. An operand
   equal as a value to an earlier calculation's original result takes that calculation's new
   result (`c:<j>`, the most recent such calculation); otherwise an operand equal to a question
   number takes that role's replacement (`q:<k>`); any other operand is a constant and stays
   (`const`). An operand that matches more than one source is counted in `ambiguous_operands`
   (once per problem, not per variant) and takes the first source in that order.
3. The solution's prose is rewritten: every number token that is an original question number or
   an original calculation result takes its new value (a token beside a calculation takes the role
   of the operand it matches there; otherwise the most recent earlier calculation result, then the
   question number, then the nearest later calculation result), the markup is written with the new
   expression and result, and `#### answer` takes the new value of the source the answer equals
   (the last calculation with that result, else the question number).
4. A draw is refused (and another is tried, up to `--tries`, default 64; then the variant slot
   reports no variant) when a re-evaluated result is fractional where the original was an integer,
   negative where the original was not, zero where the original was not, longer in decimal places
   than the original, or divides by zero; when two roles receive the same replacement; when a
   replacement is unchanged or equals an original source value (a question number or a
   calculation result) or a constant operand; when a calculation's new result is unchanged or
   equals a constant operand or another source's new value (a collision makes roles unreadable);
   or when it repeats an earlier variant of the same problem. A calculation no question number
   reaches (`24*60`, with constants only) never changes: its result counts as a constant, not as
   a source. A problem whose answer equals no source, whose markup or expression does not parse,
   or which has no calculation or no question number, has no variant at all.

The draw stream is hash-derived: SHA-256 over `gsm8k_variants:SEED:PROBLEM:VARIANT` in counter
mode, with uniform integers by rejection (no `seed ^ problem ^ variant`, whose xor collides across
pairs; no floats). It is deterministic and independent of the Python version.

Limits (stated, not repaired):
- Words for numbers ("three", "twice", "half", "dozen") are left unchanged. A question number the
  solution reaches only through such a word, or an operand that equals a source by chance, is
  mapped by value, not by meaning.
- Number tokens glued to letters before them (`B12`), ordinals (`3rd`) and clock or ratio forms
  (`10:30`) are left unchanged and are not roles; so are the same tokens in the solution.
- Noun number agreement ("1 apple" against "7 apple") and implicit relations among the numbers
  ("5 fewer than 12") are not repaired; a relation that breaks a count is refused only through
  the negative, fractional and zero rules.
- A calculation whose stated result is not the exact value of its expression (a rounded
  annotation) is recorded `orig_exact: false`; its new result is the exact value and must have no
  more decimal places than the stated one, so a rounded annotation rarely yields a variant.

Output: OUT holds each original's variants in order (the originals are not written), problems
separated by a blank line. The sidecar OUT.roles is JSON lines, one per variant: problem index,
variant index, seed, the refused draws before it, each question role with its original and new
value, each calculation with the role, original and new value of every operand and its original
and new result, and the answer's role. One line goes to stdout: counts, never text.

    VARIANTS problems=N written=N refused_draws=N no_variant=N ambiguous_operands=N elapsed_ms=N

`no_variant` counts variant slots (problem, variant) that wrote nothing. A line `DETAIL ...` of
counts by refusal reason goes to stderr.

The reading of the claim (record section 15.5, fixed before reading 10):

    python3 -I tools/gsm8k_variants.py claim ORIGINALS VARIANTS ROLES ORIG_DIR VAR_DIR
    python3 -I tools/gsm8k_variants.py show ORIGINALS VARIANTS ROLES ORIG_DIR VAR_DIR OUT_FILE

ORIGINALS is the held file, VARIANTS and ROLES the files this tool wrote from it (a path literally
named `claim` or `show` is written `./claim`), ORIG_DIR and VAR_DIR release directories holding
`FREE.tsv` as `tools/gsm8k/written_rules.py` reads it: one row a passage, in the order of ORIGINALS
and of VARIANTS. Claim: across the original releases' calculations that took an operand from the
question, the variant's release takes the variant's number in the same role in at least half.

Definition. A release is its FREE.tsv row up to the first blank line. Its calculations are, in
order, its `<<expression=c>>` markups whose expression is numerals, `.`, `+ - * /` and parentheses
and whose `c` is a number: the calculations `written_rules.py` counts as `b_free_calculations`
(this tool loads that file for `CALC`, `value`, `number`, `unescape` and `read_tsv`). The operands
of a calculation are the numerals of its expression (the reading `c_from_question` makes), each a
Fraction. Roles are the sidecar's: the digit runs of the question, never number words. For a
variant with role k, original value o_k and new value n_k:
- `of` counts each operand of the original release's calculation i whose value is o_k for some k,
  once (an operand written twice counts twice);
- `taken` counts those of them for which the variant's release has a calculation i with an operand
  equal to n_k, under any operation; a missing calculation i counts as not taken.
Totals sum over the variants, so an original with two variants enters twice. `share_millionths` is
floor(taken * 1000000 / of), 0 when `of` is 0; the claim holds when 2 * taken >= of. `problems` is
the number of distinct originals that have a variant, `calculations_original` their releases'
calculations (each original once), `calculations_variant` the calculations of all the variants'
releases. The sidecar must describe the files, or the tool stops: each variant's question reads,
number by number, the sidecar's new value for the original question's number, and its answer line
is the record's.

    VARIANTS_CLAIM taken=N of=N share_millionths=N problems=N calculations_original=N calculations_variant=N
    VARIANTS_CLAIM_PROBLEM index=N variant=N taken=N of=N      (one a variant)

`show` writes to OUT_FILE (refused unless it lies under a `.local` directory: it holds private
text) three held problems, each as its question and release followed by each of its two variants'
question and release, verbatim. They are the first three indices that have two variants and whose
original release has `of` above zero (a calculation that took a question number). Only counts
reach stdout (`VARIANTS_SHOW shown=N indices=...`).

Importable: `parse_problems`, `analyse`, `variant_of`, `write_passages`, `write_roles`,
`release_calculations`, `claim_of`, `read_claim`, `show`.
Standard library only; every value is a Fraction or an integer.
"""

import argparse
import hashlib
import importlib.util
import json
import os
import re
import sys
import time
from collections import Counter
from dataclasses import dataclass, field
from fractions import Fraction

__all__ = [
    "Problem", "Variant", "Unusable", "parse_problems", "analyse", "variant_of",
    "write_passages", "write_roles", "number_tokens", "format_like", "main",
    "release_calculations", "claim_of", "read_claim", "show",
]

NUMBER = re.compile(r"\d+(?:,\d{3})*(?!\d)(?:\.\d+)?")
CALCULATION = re.compile(r"<<([^=<>]*)=([^<>]*)>>")
EXPR_TOKEN = re.compile(r"\s*(?:(\d+(?:\.\d+)?|\.\d+)|([-+*/()]))")
ORDINAL = re.compile(r"(?:st|nd|rd|th)\b")
ANSWER = re.compile(r"-?(?:\d+(?:,\d{3})*(?!\d)(?:\.\d+)?|\.\d+)")


# ---------------------------------------------------------------- passages


@dataclass(frozen=True)
class Problem:
    question: str
    solution: tuple
    answer: str  # the text after `#### `

    def passage(self):
        return "\n".join([self.question, *self.solution, "#### " + self.answer])


def parse_problems(text):
    """Split a passage file into problems. Raises ValueError on a malformed problem."""
    problems = []
    for n, chunk in enumerate(re.split(r"\n\s*\n", text.strip())):
        lines = chunk.split("\n")
        if len(lines) < 2 or not lines[-1].startswith("#### "):
            raise ValueError(f"problem {n}: a question line and a last line `#### answer` are required")
        problems.append(Problem(lines[0], tuple(lines[1:-1]), lines[-1][5:].strip()))
    return problems


# ---------------------------------------------------------------- numbers


def decimals_of(value):
    """Decimal places of a terminating value, None when its decimal expansion does not end."""
    d = value.denominator
    twos = fives = 0
    while d % 2 == 0:
        d //= 2
        twos += 1
    while d % 5 == 0:
        d //= 5
        fives += 1
    return max(twos, fives) if d == 1 else None


def places_in(text):
    return len(text.split(".")[1]) if "." in text else 0


def format_value(value, decimals, grouped):
    sign = "-" if value < 0 else ""
    scaled = abs(value) * 10 ** decimals
    if scaled.denominator != 1:
        raise ValueError("value does not end within the places")
    digits = str(scaled.numerator).rjust(decimals + 1, "0")
    whole, frac = digits[: len(digits) - decimals], digits[len(digits) - decimals:]
    if grouped:
        whole = f"{int(whole):,}"
    return sign + whole + ("." + frac if decimals else "")


def _bare(text, like):
    """A value below one is written `.5` when its model is."""
    return text.replace("0.", ".", 1) if like.lstrip("-").startswith(".") and text.startswith("0.") else text


def format_like(value, like):
    """Write `value` as the token `like` is written: its places (more if the value needs them)
    and its comma grouping."""
    need = decimals_of(value)
    if need is None:
        raise ValueError("value does not end")
    return _bare(format_value(value, max(need, places_in(like)), "," in like), like)


def to_value(text):
    return Fraction(text.replace(",", ""))


def replaceable(line, match):
    """A number token that is a role: not glued to a letter before it, not an ordinal, not a clock
    or ratio form."""
    s, e = match.span()
    if s > 0 and line[s - 1].isalpha():
        return False
    if ORDINAL.match(line, e):
        return False
    if e + 1 < len(line) and line[e] == ":" and line[e + 1].isdigit():
        return False
    if s >= 2 and line[s - 1] == ":" and line[s - 2].isdigit():
        return False
    return True


def number_tokens(line, start=0, end=None):
    """(start, end, text) of each replaceable number token of `line[start:end]`."""
    end = len(line) if end is None else end
    return [(m.start(), m.end(), m.group()) for m in NUMBER.finditer(line, start, end)
            if replaceable(line, m)]


# ---------------------------------------------------------------- the keyed stream


class Stream:
    """SHA-256 in counter mode over the key; uniform integers by rejection."""

    def __init__(self, seed, problem, variant):
        self.key = f"gsm8k_variants:{seed}:{problem}:{variant}".encode()
        self.counter = 0
        self.buffer = b""

    def _take(self, n):
        while len(self.buffer) < n:
            self.buffer += hashlib.sha256(self.key + self.counter.to_bytes(8, "big")).digest()
            self.counter += 1
        out, self.buffer = self.buffer[:n], self.buffer[n:]
        return out

    def below(self, n):
        size = (n.bit_length() + 7) // 8
        limit = 256 ** size - 256 ** size % n
        while True:
            x = int.from_bytes(self._take(size), "big")
            if x < limit:
                return x % n


# ---------------------------------------------------------------- calculations


class Unusable(Exception):
    """A problem that has no variant at all (a structural reason, not a refused draw)."""

    def __init__(self, reason, ambiguous=0):
        super().__init__(reason)
        self.reason = reason
        self.ambiguous = ambiguous


def parse_expression(expr):
    """(leaves, ast): leaves are (start, end, text, value); the ast refers to leaves by index."""
    tokens, pos = [], 0
    while pos < len(expr):
        if not expr[pos:].strip():
            break
        m = EXPR_TOKEN.match(expr, pos)
        if m is None:
            raise ValueError("expression")
        tokens.append(("n", m.group(1), m.start(1), m.end(1)) if m.group(1) is not None
                      else ("o", m.group(2), m.start(2), m.end(2)))
        pos = m.end()
    leaves, at = [], 0

    def peek():
        return tokens[at] if at < len(tokens) else None

    def sum_():
        nonlocal at
        node = product()
        while peek() and peek()[0] == "o" and peek()[1] in "+-" :
            op = tokens[at][1]
            at += 1
            node = ("bin", op, node, product())
        return node

    def product():
        nonlocal at
        node = factor()
        while peek() and peek()[0] == "o" and peek()[1] in "*/":
            op = tokens[at][1]
            at += 1
            node = ("bin", op, node, factor())
        return node

    def factor():
        nonlocal at
        t = peek()
        if t is None:
            raise ValueError("expression")
        at += 1
        if t[0] == "n":
            leaves.append((t[2], t[3], t[1], Fraction(t[1])))
            return ("n", len(leaves) - 1)
        if t[1] == "-":
            return ("neg", factor())
        if t[1] == "+":
            return factor()
        if t[1] == "(":
            node = sum_()
            close = peek()
            if close is None or close[1] != ")":
                raise ValueError("expression")
            at += 1
            return node
        raise ValueError("expression")

    ast = sum_()
    if at != len(tokens):
        raise ValueError("expression")
    return leaves, ast


def evaluate(node, values):
    kind = node[0]
    if kind == "n":
        return values[node[1]]
    if kind == "neg":
        return -evaluate(node[1], values)
    a, b = evaluate(node[2], values), evaluate(node[3], values)
    op = node[1]
    if op == "+":
        return a + b
    if op == "-":
        return a - b
    if op == "*":
        return a * b
    if b == 0:
        raise ZeroDivisionError
    return a / b


@dataclass
class Calc:
    index: int
    line: int
    start: int
    end: int
    expr: str
    leaves: list
    ast: tuple
    result_text: str
    result: Fraction
    exact: bool
    roles: list = field(default_factory=list)  # per leaf: ("q", k) | ("c", j) | ("const", None)


@dataclass
class QTok:
    start: int
    end: int
    text: str
    value: Fraction
    role: int


@dataclass
class Analysis:
    problem: Problem
    q_tokens: list
    q_roles: list  # the first token of each role
    calcs: list
    lines: list  # per solution line: ("t", text) | ("n", text, value, role|None) | ("c", j)
    answer_role: tuple
    ambiguous: int
    consts: frozenset  # constant operands and the results of calculations no question number reaches
    originals: frozenset  # original values of every source
    fixed: frozenset  # calculations no question number reaches: their result never changes


def analyse(problem):
    """Read a problem's roles: question numbers, calculations with their operand roles, the prose
    tokens that are sources, and the answer's source. Raises Unusable."""
    q_tokens, q_map, q_roles = [], {}, []
    for s, e, text in number_tokens(problem.question):
        value = to_value(text)
        if value not in q_map:
            q_map[value] = len(q_map)
        tok = QTok(s, e, text, value, q_map[value])
        if len(q_roles) == tok.role:
            q_roles.append(tok)
        q_tokens.append(tok)
    if not q_tokens:
        raise Unusable("no_numbers")

    calcs, raw_lines = [], []
    for li, line in enumerate(problem.solution):
        pieces, cursor = [], 0
        for m in CALCULATION.finditer(line):
            pieces.append(("prose", cursor, m.start()))
            result_text = m.group(2).strip()
            if not ANSWER.fullmatch(result_text):
                raise Unusable("result")
            try:
                leaves, ast = parse_expression(m.group(1))
            except ValueError:
                raise Unusable("expression") from None
            result = to_value(result_text)
            try:
                exact = evaluate(ast, [leaf[3] for leaf in leaves]) == result
            except ZeroDivisionError:
                raise Unusable("expression") from None
            calcs.append(Calc(len(calcs), li, m.start(), m.end(), m.group(1), leaves, ast,
                              result_text, result, exact))
            pieces.append(("calc", len(calcs) - 1))
            cursor = m.end()
        pieces.append(("prose", cursor, len(line)))
        if "<<" in CALCULATION.sub("", line) or ">>" in CALCULATION.sub("", line):
            raise Unusable("markup")
        raw_lines.append(pieces)
    if not calcs:
        raise Unusable("no_calcs")

    ambiguous = 0
    for j, calc in enumerate(calcs):
        for leaf in calc.leaves:
            v = leaf[3]
            earlier = [i for i in range(j) if calcs[i].result == v]
            k = q_map.get(v)
            if len(earlier) + (k is not None) > 1:
                ambiguous += 1
            if earlier:
                calc.roles.append(("c", max(earlier)))
            elif k is not None:
                calc.roles.append(("q", k))
            else:
                calc.roles.append(("const", None))

    answer_text = problem.answer
    if not ANSWER.fullmatch(answer_text):
        raise Unusable("answer", ambiguous)
    answer = to_value(answer_text)
    with_result = [i for i, c in enumerate(calcs) if c.result == answer]
    if with_result:
        answer_role = ("c", max(with_result))
    elif answer in q_map:
        answer_role = ("q", q_map[answer])
    else:
        raise Unusable("answer", ambiguous)

    by_line = {}
    for j, c in enumerate(calcs):
        by_line.setdefault(c.line, []).append(j)

    def prose_role(li, p, v):
        here = [calcs[j] for j in by_line.get(li, [])]
        following = sorted((c for c in here if c.start >= p), key=lambda c: c.start)
        preceding = sorted((c for c in here if c.end <= p), key=lambda c: -c.end)
        for c in following + preceding:
            for role, leaf in zip(c.roles, c.leaves):
                if leaf[3] == v and role[0] != "const":
                    return role
        before = [j for j, c in enumerate(calcs)
                  if c.result == v and (c.line, c.end) <= (li, p)]
        if before:
            return ("c", max(before))
        if v in q_map:
            return ("q", q_map[v])
        after = [j for j, c in enumerate(calcs) if c.result == v and (c.line, c.start) > (li, p)]
        if after:
            return ("c", min(after))
        return None

    lines = []
    for li, pieces in enumerate(raw_lines):
        line, out = problem.solution[li], []
        for piece in pieces:
            if piece[0] == "calc":
                out.append(("c", piece[1]))
                continue
            cursor = piece[1]
            for s, e, text in number_tokens(line, piece[1], piece[2]):
                if s > cursor:
                    out.append(("t", line[cursor:s]))
                value = to_value(text)
                out.append(("n", text, value, prose_role(li, s, value)))
                cursor = e
            if piece[2] > cursor:
                out.append(("t", line[cursor:piece[2]]))
        lines.append(out)

    fixed = set()
    for j, calc in enumerate(calcs):
        if all(r[0] == "const" or (r[0] == "c" and r[1] in fixed) for r in calc.roles):
            fixed.add(j)
    consts = frozenset([leaf[3] for c in calcs for role, leaf in zip(c.roles, c.leaves)
                        if role[0] == "const"] + [calcs[j].result for j in fixed])
    originals = frozenset([t.value for t in q_roles] + [c.result for c in calcs])
    return Analysis(problem, q_tokens, q_roles, calcs, lines, answer_role, ambiguous, consts,
                    originals, frozenset(fixed))


# ---------------------------------------------------------------- drawing and rendering


def draw_text(token, stream):
    """A number of the token's digit count, places and grouping."""
    whole = token.text.split(".")[0].replace(",", "")
    frac = token.text.split(".")[1] if "." in token.text else ""
    digits = []
    for i in range(len(whole)):
        low = 1 if (i == 0 and whole[0] != "0") else 0
        digits.append(str(low + stream.below(10 - low)))
    text = "".join(digits)
    if "," in token.text:
        text = f"{int(text):,}"
    if frac:
        out = []
        for i in range(len(frac)):
            low = 1 if (i == len(frac) - 1 and frac[-1] != "0") else 0
            out.append(str(low + stream.below(10 - low)))
        text += "." + "".join(out)
    return text


def _value(role, new_q, new_c):
    return new_q[role[1]] if role[0] == "q" else new_c[role[1]]


def render(a, new_q, new_c, q_texts):
    """The variant's question, solution lines and answer for the given new values."""
    question, cursor = [], 0
    for tok in a.q_tokens:
        question.append(a.problem.question[cursor:tok.start])
        question.append(q_texts[tok.role] if tok is a.q_roles[tok.role]
                        else format_like(new_q[tok.role], tok.text))
        cursor = tok.end
    question.append(a.problem.question[cursor:])

    solution = []
    for pieces in a.lines:
        parts = []
        for piece in pieces:
            if piece[0] == "t":
                parts.append(piece[1])
            elif piece[0] == "n":
                parts.append(piece[1] if piece[3] is None
                             else format_like(_value(piece[3], new_q, new_c), piece[1]))
            else:
                parts.append(_markup(a.calcs[piece[1]], new_q, new_c))
        solution.append("".join(parts))
    answer = format_like(_value(a.answer_role, new_q, new_c), a.problem.answer)
    return "".join(question), tuple(solution), answer


def _leaf_text(role, leaf, new_q, new_c):
    return leaf[2] if role[0] == "const" else format_like(_value(role, new_q, new_c), leaf[2])


def _markup(calc, new_q, new_c):
    expr, cursor = [], 0
    for role, leaf in zip(calc.roles, calc.leaves):
        expr.append(calc.expr[cursor:leaf[0]])
        expr.append(_leaf_text(role, leaf, new_q, new_c))
        cursor = leaf[1]
    expr.append(calc.expr[cursor:])
    return f"<<{''.join(expr)}={format_like(new_c[calc.index], calc.result_text)}>>"


def _verify(solution, answer, new_q, new_c, a):
    seen = []
    for line in solution:
        for m in CALCULATION.finditer(line):
            leaves, ast = parse_expression(m.group(1))
            value = evaluate(ast, [leaf[3] for leaf in leaves])
            assert value == to_value(m.group(2).strip()), "rendered calculation disagrees with itself"
            seen.append(value)
    assert seen == new_c, "rendered calculations disagree with the new results"
    assert to_value(answer) == _value(a.answer_role, new_q, new_c), "answer disagrees"


def attempt(a, stream, avoid):
    """One draw. Returns (None, reason) when refused, else (new_q, new_c, q_texts)."""
    q_texts = [draw_text(t, stream) for t in a.q_roles]
    new_q = [to_value(x) for x in q_texts]
    for t, n in zip(a.q_roles, new_q):
        if n == 0 and t.value != 0:
            return None, "zero"
        if n == t.value:
            return None, "q_same"
    if len(set(new_q)) != len(new_q):
        return None, "q_equal"
    if any(n in a.originals for n in new_q):
        return None, "q_original"
    if any(n in a.consts for n in new_q):
        return None, "q_const"
    if tuple(new_q) in avoid:
        return None, "repeat"

    new_c = []
    for calc in a.calcs:
        values = [leaf[3] if role[0] == "const" else _value(role, new_q, new_c)
                  for role, leaf in zip(calc.roles, calc.leaves)]
        try:
            n = evaluate(calc.ast, values)
        except ZeroDivisionError:
            return None, "div0"
        r = calc.result
        if r.denominator == 1 and n.denominator != 1:
            return None, "fractional"
        if n < 0 <= r:
            return None, "negative"
        if n == 0 and r != 0:
            return None, "zero"
        need = decimals_of(n)
        if need is None or need > decimals_of(r):
            return None, "places"
        new_c.append(n)

    owner = {}
    for orig, new in [(t.value, n) for t, n in zip(a.q_roles, new_q)] + \
                     [(c.result, n) for c, n in zip(a.calcs, new_c) if c.index not in a.fixed]:
        if new == orig and orig != 0:
            return None, "c_same"
        if new in a.consts:
            return None, "c_const"
        if owner.setdefault(new, orig) != orig:
            return None, "c_collide"
    return (new_q, new_c, q_texts), None


@dataclass
class Variant:
    problem: int
    variant: int
    question: str
    solution: tuple
    answer: str
    key: tuple  # the new question values, to keep variants of one problem apart
    record: dict

    def passage(self):
        return "\n".join([self.question, *self.solution, "#### " + self.answer])


def _record(a, i, v, seed, refused, new_q, new_c, q_texts, solution, answer):
    def fmt(x, like):
        return format_like(x, like)

    calcs = []
    for j, c in enumerate(a.calcs):
        operands = []
        for role, leaf in zip(c.roles, c.leaves):
            name = "const" if role[0] == "const" else f"{role[0]}:{role[1]}"
            operands.append({"role": name, "orig": leaf[2],
                             "new": _leaf_text(role, leaf, new_q, new_c)})
        calcs.append({"calc": j, "operands": operands, "orig_result": c.result_text,
                      "new_result": fmt(new_c[j], c.result_text), "orig_exact": c.exact})
    role = a.answer_role
    return {
        "problem": i, "variant": v, "seed": seed, "refused_draws": refused,
        "ambiguous_operands": a.ambiguous,
        "roles": [{"role": k, "orig": t.text, "new": q_texts[k]} for k, t in enumerate(a.q_roles)],
        "calcs": calcs,
        "answer": {"role": f"{role[0]}:{role[1]}", "orig": a.problem.answer, "new": answer},
    }


def variant_of(problem, problem_index, variant_index, seed, tries=64, avoid=(), analysis=None):
    """One variant of `problem`, or None. Returns (variant_or_None, receipt) where the receipt is
    {"draws", "refused", "reasons": Counter} (or {"unusable": reason} with nothing drawn).
    `avoid` holds the keys of earlier variants of the same problem."""
    try:
        a = analysis or analyse(problem)
    except Unusable as u:
        return None, {"draws": 0, "refused": 0, "reasons": Counter(), "unusable": u.reason,
                      "ambiguous": u.ambiguous}
    stream = Stream(seed, problem_index, variant_index)
    reasons = Counter()
    for draw in range(tries):
        got, reason = attempt(a, stream, avoid)
        if reason:
            reasons[reason] += 1
            continue
        new_q, new_c, q_texts = got
        question, solution, answer = render(a, new_q, new_c, q_texts)
        _verify(solution, answer, new_q, new_c, a)
        record = _record(a, problem_index, variant_index, seed, draw, new_q, new_c, q_texts,
                         solution, answer)
        variant = Variant(problem_index, variant_index, question, solution, answer,
                          tuple(new_q), record)
        return variant, {"draws": draw + 1, "refused": draw, "reasons": reasons,
                         "ambiguous": a.ambiguous}
    return None, {"draws": tries, "refused": tries, "reasons": reasons, "ambiguous": a.ambiguous}


# ---------------------------------------------------------------- files


def write_passages(path, variants):
    """The variants' passages separated by one blank line."""
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n\n".join(v.passage() for v in variants) + ("\n" if variants else ""))


def write_roles(path, variants):
    """The sidecar: one JSON line of roles per variant."""
    with open(path, "w", encoding="utf-8") as f:
        for v in variants:
            f.write(json.dumps(v.record, sort_keys=True) + "\n")


# ---------------------------------------------------------------- the reading of the claim


_WRITTEN_RULES = None


def _written_rules():
    """`tools/gsm8k/written_rules.py`, loaded by its path (`-I` puts no directory on sys.path)."""
    global _WRITTEN_RULES
    if _WRITTEN_RULES is None:
        path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "gsm8k", "written_rules.py")
        spec = importlib.util.spec_from_file_location("gsm8k_written_rules", path)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        _WRITTEN_RULES = module
    return _WRITTEN_RULES


def release_calculations(release):
    """The operands (Fractions) of each calculation of a release (bytes), in order: the release is
    its bytes up to the first blank line, a calculation a `<<expression=c>>` whose expression is
    numerals, `.`, `+ - * /` and parentheses and whose `c` is a number, an operand a numeral."""
    rules = _written_rules()
    text = release.split(b"\n\n")[0].decode("utf-8", "replace")
    out = []
    for expression, c in rules.CALC.findall(text):
        if rules.value(expression) is None or rules.number(c) is None:
            continue
        out.append([Fraction(t) for t in re.findall(r"\d*\.\d+|\d+", expression)])
    return out


def claim_of(original, variant, record):
    """(taken, of) of one variant: `original` and `variant` are the calculations' operands of the
    two releases (release_calculations), `record` the variant's line of the sidecar."""
    new = {to_value(r["orig"]): to_value(r["new"]) for r in record["roles"]}
    taken = total = 0
    for i, operands in enumerate(original):
        later = variant[i] if i < len(variant) else None
        for operand in operands:
            if operand in new:
                total += 1
                taken += later is not None and new[operand] in later
    return taken, total


def _read_releases(directory, count):
    rules = _written_rules()
    rows = rules.read_tsv(os.path.join(directory, "FREE.tsv"), 2)
    if [int(r[0]) for r in rows] != list(range(count)):
        raise SystemExit(f"{directory}/FREE.tsv does not hold one release a passage, in order")
    return [rules.unescape(r[1]) for r in rows]


def read_claim(originals, variants, roles, orig_dir, var_dir):
    """Read the claim. Returns (problems, per, originals, variants, original releases, variant
    releases): `problems` the distinct originals with a variant, `per` one dict a variant in the
    sidecar's order (problem, variant, taken, of, the two calculation counts, its row n). Stops
    (SystemExit) when the sidecar does not describe the files."""
    with open(originals, encoding="utf-8") as f:
        held = parse_problems(f.read())
    with open(variants, encoding="utf-8") as f:
        made = parse_problems(f.read())
    with open(roles, encoding="utf-8") as f:
        records = [json.loads(line) for line in f if line.strip()]
    if len(records) != len(made):
        raise SystemExit("the sidecar does not hold one line a variant")
    originals_out = _read_releases(orig_dir, len(held))
    variants_out = _read_releases(var_dir, len(made))
    per = []
    for n, (record, passage) in enumerate(zip(records, made)):
        p = record["problem"]
        if not 0 <= p < len(held):
            raise SystemExit(f"variant {n}: the sidecar names a problem the originals do not hold")
        new = {to_value(r["orig"]): to_value(r["new"]) for r in record["roles"]}
        old_tokens = number_tokens(held[p].question)
        new_tokens = number_tokens(passage.question)
        if len(old_tokens) != len(new_tokens) or any(
                new.get(to_value(a[2])) != to_value(b[2]) for a, b in zip(old_tokens, new_tokens)):
            raise SystemExit(f"variant {n}: its question does not read as the sidecar's roles")
        if passage.answer != record["answer"]["new"]:
            raise SystemExit(f"variant {n}: its answer is not the sidecar's")
        before = release_calculations(originals_out[p])
        after = release_calculations(variants_out[n])
        taken, total = claim_of(before, after, record)
        per.append({"problem": p, "variant": record["variant"], "taken": taken, "of": total,
                    "calculations_original": len(before), "calculations_variant": len(after),
                    "n": n})
    return len({row["problem"] for row in per}), per, held, made, originals_out, variants_out


def show(originals, variants, roles, orig_dir, var_dir, out_file):
    """Write three held problems with their two variants' releases, verbatim, to `out_file` (under
    a `.local` directory). Returns the indices written."""
    if ".local" not in os.path.abspath(out_file).split(os.sep)[:-1]:
        raise SystemExit("the report holds private text: write it under a .local directory")
    _, per, held, made, before, after = read_claim(originals, variants, roles, orig_dir, var_dir)
    by_problem = {}
    for row in per:
        by_problem.setdefault(row["problem"], []).append(row)
    chosen = [p for p in sorted(by_problem)
              if len(by_problem[p]) == 2 and by_problem[p][0]["of"] > 0][:3]
    out = []
    for p in chosen:
        out.append(f"=== problem {p} ===\n--- original question\n".encode())
        out.append(held[p].question.encode("utf-8") + b"\n--- original release\n" + before[p] + b"\n")
        for row in by_problem[p]:
            n, v = row["n"], row["variant"]
            out.append(f"--- variant {v} question\n".encode())
            out.append(made[n].question.encode("utf-8") + f"\n--- variant {v} release\n".encode()
                       + after[n] + b"\n")
    with open(out_file, "wb") as f:
        f.write(b"".join(out))
    return chosen


def claim_main(argv):
    if len(argv) != 5:
        raise SystemExit("usage: claim ORIGINALS VARIANTS ROLES ORIG_DIR VAR_DIR")
    problems, per, *_ = read_claim(*argv)
    taken = sum(r["taken"] for r in per)
    total = sum(r["of"] for r in per)
    first = {}
    for r in per:
        first.setdefault(r["problem"], r["calculations_original"])
    share = taken * 1_000_000 // total if total else 0
    print(f"VARIANTS_CLAIM taken={taken} of={total} share_millionths={share} problems={problems} "
          f"calculations_original={sum(first.values())} "
          f"calculations_variant={sum(r['calculations_variant'] for r in per)}")
    for r in per:
        print(f"VARIANTS_CLAIM_PROBLEM index={r['problem']} variant={r['variant']} "
              f"taken={r['taken']} of={r['of']}")
    return 0


def show_main(argv):
    if len(argv) != 6:
        raise SystemExit("usage: show ORIGINALS VARIANTS ROLES ORIG_DIR VAR_DIR OUT_FILE")
    chosen = show(*argv)
    print(f"VARIANTS_SHOW shown={len(chosen)} indices={','.join(map(str, chosen))}")
    return 0


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if argv and argv[0] == "claim":
        return claim_main(argv[1:])
    if argv and argv[0] == "show":
        return show_main(argv[1:])
    ap = argparse.ArgumentParser(description="Variants of GSM8K problems with new numbers.")
    ap.add_argument("input")
    ap.add_argument("output")
    ap.add_argument("--variants", type=int, default=2)
    ap.add_argument("--seed", type=int, required=True)
    ap.add_argument("--tries", type=int, default=64)
    args = ap.parse_args(argv)

    start = time.perf_counter_ns()
    with open(args.input, encoding="utf-8") as f:
        problems = parse_problems(f.read())
    written, refused, no_variant, ambiguous = [], 0, 0, 0
    detail = Counter()
    for i, problem in enumerate(problems):
        try:
            a = analyse(problem)
        except Unusable as u:
            ambiguous += u.ambiguous
            no_variant += args.variants
            detail["unusable_" + u.reason] += args.variants
            continue
        ambiguous += a.ambiguous
        avoid = set()
        for v in range(args.variants):
            variant, receipt = variant_of(problem, i, v, args.seed, args.tries, avoid, a)
            refused += receipt["refused"]
            for reason, n in receipt["reasons"].items():
                detail["refused_" + reason] += n
            if variant is None:
                no_variant += 1
                detail["exhausted"] += 1
            else:
                avoid.add(variant.key)
                written.append(variant)
    write_passages(args.output, written)
    write_roles(args.output + ".roles", written)
    elapsed = (time.perf_counter_ns() - start) // 1_000_000
    print(f"VARIANTS problems={len(problems)} written={len(written)} refused_draws={refused} "
          f"no_variant={no_variant} ambiguous_operands={ambiguous} elapsed_ms={elapsed}")
    print("DETAIL " + " ".join(f"{k}={n}" for k, n in sorted(detail.items())), file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
