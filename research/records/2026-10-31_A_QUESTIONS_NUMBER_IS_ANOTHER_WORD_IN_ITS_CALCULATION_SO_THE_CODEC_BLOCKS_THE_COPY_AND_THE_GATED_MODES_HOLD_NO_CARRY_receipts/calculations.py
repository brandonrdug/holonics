"""GSM8K's own arithmetic evidence: its training calculations counted (record §4).

    python3 -I calculations.py TRAIN_JSONL

Counts every `<<expression=value>>` of the public training split: distinct expressions, how many
are written once, the binary whole-number calculations by operation, and the results' whole-part
digits. An exterior count: nothing here enters the machine.
"""
import collections, json, re, sys

rows = [json.loads(l) for l in open(sys.argv[1], encoding="utf-8")]
calc = re.compile(r"<<([^=>]*)=([^>]*)>>")
total, exprs, ops, digits = 0, collections.Counter(), collections.Counter(), collections.Counter()
for r in rows:
    for m in calc.finditer(r["answer"]):
        total += 1
        e = m.group(1).replace(" ", "")
        exprs[e] += 1
        b = re.fullmatch(r"(\d+)([-+*/])(\d+)", e)
        if b:
            ops[b.group(2)] += 1
        digits[len(m.group(2).split(".")[0])] += 1
print(f"CALCULATIONS problems={len(rows)} calculations={total} distinct={len(exprs)} "
      f"written_once={sum(1 for v in exprs.values() if v == 1)} binary={sum(ops.values())} "
      f"sums={ops['+']} differences={ops['-']} products={ops['*']} quotients={ops['/']} "
      f"result_digits={dict(sorted(digits.items()))}")
