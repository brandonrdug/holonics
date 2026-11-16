#!/usr/bin/env python3
"""The word problems' slice of a store (Brandon, November 16 17:06Z: TinyGSM beside the arithmetic world, so the number exchanges stand in
words). The boundary codec of `TinyGSM/TinyGSM` (MIT; 11.8 million GSM-style problems, each with a short Python solution): a problem is
its question in words, then its solution's statements (the function's body without its docstring and its `return`), then the world's
answer, `answer = VALUE`.

The answer is evaluated here, at the boundary, and never by running the solution: the solution's text is parsed (`ast`) and only a straight
line of assignments of arithmetic is interpreted (numbers, names already assigned, `+ - * / // %`, a power of a small exponent, a sign, and
`result = …`/`return …`), on rationals, so a decimal in the text is its exact rational. A problem whose solution holds anything else (a
call, a loop, a branch, an import), or whose answer is not an integer, is left out and counted. No downloaded code is executed.

Overlap with GSM8K is left out: a problem whose question shares any eight-word shingle (lower case, words of letters and digits) with any
GSM8K question in GSM8K_JSONL (one JSON object a line with a `question`) is counted and dropped, so GSM8K stays a yardstick.

Usage: words_passage.py OUT PARQUET_DIR GSM8K_JSONL TEXT_OCTETS [--held-text HELD]

Writes corpus_passage.py's files for the slice `words` (`DOCS_words.*`, `IDS_words.txt`): the problems in the dataset's order (its
parquet files by name, rows in order) until the text reaches TEXT_OCTETS. With HELD (GSM8K problems as text, one problem a paragraph:
its question, a line feed and its answer as GSM8K writes it, problems apart by a blank line), writes `HELD_words.*` from them, each problem
one document, and leaves out of training every problem sharing a shingle with one of them.
Prints the slice's `STORE.tsv` rows with their SHA-256 and the counts left out.
"""
import argparse
import ast
import hashlib
import json
import os
import re
import sys
import warnings
from fractions import Fraction

import pyarrow.parquet as pq

SLICE = "words"
INDEX_HEAD = "document\ttitle_octets\ttext_octets\topens\tcloses\n"
SHINGLE = 8
POWER_BOUND = 12
MAGNITUDE_BOUND = 10**30


class Refused(Exception):
    pass


def value(node, names):
    if isinstance(node, ast.Constant) and isinstance(node.value, (int, float)) and not isinstance(node.value, bool):
        return Fraction(repr(node.value)) if isinstance(node.value, float) else Fraction(node.value)
    if isinstance(node, ast.Name):
        if node.id not in names:
            raise Refused("an unassigned name")
        return names[node.id]
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.USub, ast.UAdd)):
        v = value(node.operand, names)
        return -v if isinstance(node.op, ast.USub) else v
    if isinstance(node, ast.BinOp):
        a, b = value(node.left, names), value(node.right, names)
        op = node.op
        if isinstance(op, ast.Add):
            out = a + b
        elif isinstance(op, ast.Sub):
            out = a - b
        elif isinstance(op, ast.Mult):
            out = a * b
        elif isinstance(op, (ast.Div, ast.FloorDiv, ast.Mod)):
            if b == 0:
                raise Refused("a division by zero")
            out = a / b if isinstance(op, ast.Div) else Fraction(a // b) if isinstance(op, ast.FloorDiv) else a % b
        elif isinstance(op, ast.Pow):
            if b.denominator != 1 or abs(b) > POWER_BOUND:
                raise Refused("a power past its bound")
            out = a ** int(b)
        else:
            raise Refused("an operation outside arithmetic")
        if abs(out) > MAGNITUDE_BOUND:
            raise Refused("a magnitude past its bound")
        return out
    raise Refused("an expression outside arithmetic")


def solved(code):
    """The solution's body without its docstring and return, and the world's answer; Refused where it is not straight arithmetic."""
    tree = ast.parse(code)
    funcs = [n for n in tree.body if isinstance(n, ast.FunctionDef)]
    if len(funcs) != 1 or len(tree.body) != 1:
        raise Refused("not one function")
    body = funcs[0].body
    names, kept, answer = {}, [], None
    lines = code.split("\n")
    for st in body:
        if isinstance(st, ast.Expr) and isinstance(st.value, ast.Constant) and isinstance(st.value.value, str):
            continue
        if isinstance(st, ast.Assign) and len(st.targets) == 1 and isinstance(st.targets[0], ast.Name):
            names[st.targets[0].id] = value(st.value, names)
            kept.append("\n".join(l.strip() for l in lines[st.lineno - 1:st.end_lineno]))
            continue
        if isinstance(st, ast.Return) and st.value is not None:
            answer = value(st.value, names)
            continue
        raise Refused("a statement outside a straight line of assignments")
    if answer is None:
        raise Refused("no return")
    if answer.denominator != 1:
        raise Refused("an answer that is not an integer")
    return "\n".join(kept), int(answer)


def shingles(text):
    words = re.findall(r"[a-z0-9]+", text.lower())
    return {" ".join(words[i:i + SHINGLE]) for i in range(len(words) - SHINGLE + 1)}


def write_role(out, stem, documents):
    h = hashlib.sha256()
    octets = n = 0
    ids_name = "HELD_IDS" if stem == "HELD" else "IDS"
    with open(os.path.join(out, f"{stem}_{SLICE}.bin"), "xb") as b, open(os.path.join(out, f"{stem}_{SLICE}.tsv"), "x") as t, open(os.path.join(out, f"{ids_name}_{SLICE}.txt"), "x") as ids:
        t.write(INDEX_HEAD)
        for ident, text in documents:
            data = text.encode()
            b.write(data)
            h.update(data)
            t.write(f"{n}\t0\t{len(data)}\t1\t1\n")
            ids.write(f"{ident}\n")
            octets += len(data)
            n += 1
    return n, octets, h.hexdigest()


def main():
    warnings.simplefilter("ignore", SyntaxWarning)
    p = argparse.ArgumentParser()
    p.add_argument("out")
    p.add_argument("parquet_dir")
    p.add_argument("gsm8k_jsonl")
    p.add_argument("text_octets", type=int)
    p.add_argument("--held-text")
    a = p.parse_args()
    seen = set()
    for line in open(a.gsm8k_jsonl):
        seen |= shingles(json.loads(line)["question"])
    held_problems = []
    if a.held_text:
        held_problems = [h.strip() for h in open(a.held_text).read().split("\n\n") if h.strip()]
        for h in held_problems:
            seen |= shingles(h.split("\n", 1)[0])
    counts = {"read": 0, "overlap": 0, "refused": 0, "kept": 0}
    reasons = {}
    total = [0]

    def documents():
        for fn in sorted(os.listdir(a.parquet_dir)):
            if not fn.endswith(".parquet"):
                continue
            pf = pq.ParquetFile(os.path.join(a.parquet_dir, fn))
            for g in range(pf.metadata.num_row_groups):
                for row in pf.read_row_group(g).to_pylist():
                    if total[0] >= a.text_octets:
                        return
                    counts["read"] += 1
                    q = row["question"].strip()
                    if shingles(q) & seen:
                        counts["overlap"] += 1
                        continue
                    try:
                        steps, answer = solved(row["code"])
                    except (Refused, SyntaxError, ValueError, ZeroDivisionError, OverflowError, RecursionError) as e:
                        counts["refused"] += 1
                        reasons[str(e)[:40]] = reasons.get(str(e)[:40], 0) + 1
                        continue
                    text = f"{q}\n{steps}\nanswer = {answer}\n"
                    counts["kept"] += 1
                    total[0] += len(text.encode())
                    yield (f"tinygsm:{fn}:{counts['read'] - 1}", text)

    os.makedirs(a.out, exist_ok=True)
    docs, octets, sha = write_role(a.out, "DOCS", documents())
    for role in ("train", "prefix"):
        print(f"{role}\t{SLICE}\t-\t0\t{docs}\t{docs}\t{octets}\t{octets}\t{sha}")
    if held_problems:
        held = [(f"gsm8k-held:{n}", f"{h}\n") for n, h in enumerate(held_problems)]
        hn, ho, hs = write_role(a.out, "HELD", held)
        print(f"held\t{SLICE}\t-\t0\t{hn}\t{hn}\t{ho}\t{ho}\t{hs}")
    top = sorted(reasons.items(), key=lambda kv: -kv[1])[:6]
    print(f"WORDS_PASSAGE read={counts['read']} kept={counts['kept']} overlap={counts['overlap']} refused={counts['refused']} octets={octets} refusals={top}", file=sys.stderr)


if __name__ == "__main__":
    main()
