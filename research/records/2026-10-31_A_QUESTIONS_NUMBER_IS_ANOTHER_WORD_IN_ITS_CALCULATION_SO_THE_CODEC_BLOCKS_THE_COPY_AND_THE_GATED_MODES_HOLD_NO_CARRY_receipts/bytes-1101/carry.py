"""Exterior receipt reads beside written_rules.py (record 2026-10-31, a question's number…, §6, acceptance 4).

    python3 -I carry.py ROOT HELD TRAIN DIR [DIR ...]

For each DIR (holding MARKS.tsv as card_written.py convert writes it) one CARRY line: the never-met
calculations at the equals by operation (two whole or decimal numerals `a op b`), and on the never-met
sums of two whole numerals whose units carry (a mod 10 + b mod 10 >= 10): how many are right, and of the
wrong ones written as a whole number of at least two digits, how many write the exact tens digit, how
many write the tens digit without the carry ((a div 10 + b div 10) mod 10), and how many neither.
Nothing here enters the machine or selects a release.
"""
import re, sys
from collections import Counter
sys.path.insert(0, sys.argv[1] + "/tools/gsm8k")
import written_rules as w

held, train = (open(p, "rb").read() for p in sys.argv[2:4])
problems = w.problems_of(held)
train_text = train.decode("utf-8", "replace")
for d in sys.argv[4:]:
    marks = w.read_tsv(f"{d}/MARKS.tsv", 4)
    seen, by_op, each = w.mark_reads(problems, marks, train_text)
    ops = Counter()
    carry = Counter()
    for kind, good, heard, e, v, wv, finished in each:
        if kind != "never":
            continue
        m = re.fullmatch(r"(\d*\.?\d+)([+\-*/])(\d*\.?\d+)", e.replace(" ", ""))
        if m:
            ops[m.group(2), "n"] += 1
            ops[m.group(2), "right"] += good
        s = re.fullmatch(r"(\d+)\+(\d+)", e.replace(" ", ""))
        if not s:
            continue
        a, b = int(s.group(1)), int(s.group(2))
        if a % 10 + b % 10 < 10:
            continue
        carry["n"] += 1
        if good:
            carry["right"] += 1
            continue
        if wv is None or wv.denominator != 1 or wv < 10:
            carry["wrong_other"] += 1
            continue
        tens = int(wv) // 10 % 10
        if tens == int(v) // 10 % 10:
            carry["tens_right"] += 1
        elif tens == (a // 10 + b // 10) % 10:
            carry["tens_without_carry"] += 1
        else:
            carry["tens_neither"] += 1
    opline = " ".join(f"{op}={ops[op, 'right']}/{ops[op, 'n']}" for op in "+-*/")
    print(f"CARRY dir={d} never_met={seen['never'][1]}/{seen['never'][0]} never_by_op {opline} carrying_sums={carry['n']} right={carry['right']} "
          f"wrong_tens_right={carry['tens_right']} wrong_tens_without_carry={carry['tens_without_carry']} wrong_tens_neither={carry['tens_neither']} wrong_not_whole={carry['wrong_other']}")
