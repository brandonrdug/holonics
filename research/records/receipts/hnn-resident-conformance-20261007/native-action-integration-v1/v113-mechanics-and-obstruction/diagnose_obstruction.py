#!/usr/bin/env python3
"""Exact saved-output reading only. Does not execute or synthesize an HNN passage."""
import hashlib
import json
import re
from fractions import Fraction as F
from pathlib import Path
p = Path(__file__).with_name("ACTUAL_OUTPUT.txt")
raw = p.read_bytes()
line = next(x for x in raw.decode().splitlines() if x.startswith(
    "NATIVE PROSPECTIVE RELATION; role=native prepared encounter 0;"))
def rats(s):
    return [F(int(n), int(d)) for n,d in re.findall(
        r"Ratio \{ numer: (-?\d+), denom: (\d+) \}",s)]
def rank(rows):
    a = [r[:] for r in rows]
    k = 0
    for j in range(len(a[0])):
        i = next((i for i in range(k,len(a)) if a[i][j]),None)
        if i is None: continue
        a[k],a[i] = a[i],a[k]
        d = a[k][j]; a[k] = [x/d for x in a[k]]
        for i in range(len(a)):
            if i == k: continue
            d = a[i][j]; a[i] = [x-d*y for x,y in zip(a[i],a[k])]
        k += 1
    return k
m = re.search(r"complete_response=ExactRatMatrix \{ rows: (\d+), columns: (\d+), entries: (.*?) \}; residual=(.*?); full_control_fibre=(.*?); unique_control=",line)
n,k = int(m[1]),int(m[2]); values = rats(m[3])
A = [values[i*k:(i+1)*k] for i in range(n)]
r = rats(m[4]); fibre = m[5]
assert fibre.startswith("Obstructed")
lam = rats(fibre.split("pairing:")[0]); pairing = rats(fibre.split("pairing:")[1])[0]
left = [sum(lam[i]*A[i][j] for i in range(n)) for j in range(k)]
actual = sum(x*y for x,y in zip(lam,r))
assert all(x == 0 for x in left) and actual == pairing and actual != 0
assert rank(A) == 2 and rank([row+[x] for row,x in zip(A,r)]) == 3
result = {"claim":"Exact saved-output diagnosis; no new native passage/test/training",
    "source":"ab860c504750f4b626eb488c3f86044ab9bc442e",
    "actual_output_sha256":hashlib.sha256(raw).hexdigest(),
    "source_actuator_B_shape":[8,2], "response_shape":[n,k],
    "L":[[str(x) for x in row] for row in A], "residual":[str(x) for x in r],
    "rank_L":rank(A), "rank_augmented":rank([row+[x] for row,x in zip(A,r)]),
    "control_kernel_dimension":k-rank(A), "annihilator":[str(x) for x in lam],
    "lambda_L":[str(x) for x in left], "lambda_residual":str(actual),
    "decision":"No control in the entire declared Q^2 source-E domain realizes the original quiet 4-coordinate carrier. Keep obstruction/Hold.",
    "not_established":["learned relation is the causal deficiency","larger grain/limit repairs reachability","a finite retained-alternative/probe partition exists"],
    "physical_result":{"encounters":0,"World_commit":0,"native_tick":4,"reset_or_action":False}}
print(json.dumps(result,indent=2))
