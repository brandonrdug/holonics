"""Exterior reading of GSM8K's training answers: where can the question still inform an answer
byte once the byte's neighbours are resolved?

This reads the data only. It is not machinery, not a learner input and not an acceptance; no
generation is read or graded. It answers one question about the field's "context" read (an
answer site t open where (t - |q|) % 4 == r, every other site resolved): which open bytes are
restated elsewhere in the answer with that byte resolved (the answer itself carries them), which
are restated only in the question (the question is their only restating source), and which are
restated nowhere (language or arithmetic). Beside it, the joint left-to-right reading: the bytes
of each run's first occurrence in the answer, split by whether the run occurs in the question.

A run is a maximal [A-Za-z0-9]+ string; everything else (spaces, punctuation, operators, the
annotation marks) is glue. Usage: python3 -I screen.py TRAIN_JSONL
"""

import json
import re
import sys
from collections import Counter

RUN = re.compile(rb"[A-Za-z0-9]+")
CONTEXT = 4


def main(path):
    rows = [json.loads(line) for line in open(path, encoding="utf-8")]
    tot = Counter()
    per_problem_qonly_zero = 0
    for row in rows:
        q = row["question"].encode("utf-8")
        a = row["answer"].encode("utf-8")
        q_runs = {m.group() for m in RUN.finditer(q)}
        a_runs = [(m.start(), m.end(), m.group()) for m in RUN.finditer(a)]
        where = {}
        occ = {}
        for s, e, w in a_runs:
            occ.setdefault(w, []).append(s)
            for i in range(s, e):
                where[i] = (i - s, w, s)
        n = len(a)
        tot["answer_bytes"] += n
        qonly_here = 0
        for r in range(CONTEXT):
            for i in range(r, n, CONTEXT):
                tot["open"] += 1
                if i not in where:
                    tot["glue"] += 1
                    continue
                off, w, s = where[i]
                kind = "digit" if w.isdigit() else "word"
                restated = any(s2 != s and (s2 + off) % CONTEXT != r for s2 in occ[w])
                if restated:
                    tot["restated"] += 1
                    tot["restated_" + kind] += 1
                elif w in q_runs:
                    tot["qonly"] += 1
                    tot["qonly_" + kind] += 1
                    qonly_here += 1
                else:
                    tot["new"] += 1
                    tot["new_" + kind] += 1
        if qonly_here == 0:
            per_problem_qonly_zero += 1
        seen = set()
        in_runs = 0
        for s, e, w in a_runs:
            in_runs += e - s
            kind = "digit" if w.isdigit() else "word"
            if w in seen:
                tot["joint_repeat"] += e - s
            elif w in q_runs:
                tot["joint_first_in_q"] += e - s
                tot["joint_first_in_q_" + kind] += e - s
            else:
                tot["joint_first_new"] += e - s
                tot["joint_first_new_" + kind] += e - s
            seen.add(w)
        tot["joint_glue"] += n - in_runs

    o = tot["open"]
    b = tot["answer_bytes"]
    print(f"problems {len(rows)}  answer bytes {b}  open bytes over the four parts {o}")
    print("context read (each open byte with its neighbours resolved):")
    for k in ["glue", "restated", "restated_digit", "restated_word", "qonly", "qonly_digit",
              "qonly_word", "new", "new_digit", "new_word"]:
        print(f"  {k:16s} {tot[k]:8d}  {tot[k] / o:7.4f}")
    print(f"  problems where no open byte is restated only in the question: {per_problem_qonly_zero}")
    print("joint left-to-right reading (each answer byte once):")
    for k in ["joint_glue", "joint_repeat", "joint_first_in_q", "joint_first_in_q_digit",
              "joint_first_in_q_word", "joint_first_new", "joint_first_new_digit",
              "joint_first_new_word"]:
        print(f"  {k:24s} {tot[k]:8d}  {tot[k] / b:7.4f}")


if __name__ == "__main__":
    main(sys.argv[1])
