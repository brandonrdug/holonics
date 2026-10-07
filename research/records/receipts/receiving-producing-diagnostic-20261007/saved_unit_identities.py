"""Coefficient/unit identities from the existing saved phase-two normal law, no model calls."""
from pathlib import Path
from fractions import Fraction as F
import re
import json

ROOT = Path(__file__).resolve().parent.parent
text = (ROOT / "pair-v60-failure-20261007/v60/HNN_PHASE_CONTROL_FULL_OUTPUT.txt").read_text()
line = next(s for s in text.splitlines() if s.startswith("nonzero-phase current consumer producing="))
at = line.index("{", line.index("receiving: Some(NormalLaw"))
depth = 0
for end in range(at, len(line)):
    depth += line[end] == "{"
    depth -= line[end] == "}"
    if depth == 0:
        break
law = line[at:end+1]


def values(part):
    return [F(int(n), int(d)) for n, d in
            re.findall(r"Ratio \{ numer: (-?\d+), denom: (\d+) \}", part)]


def matrix(flat):
    assert len(flat) == 64
    return [flat[i*8:(i+1)*8] for i in range(8)]


def multiply(A, B):
    return [[sum(A[i][k]*B[k][j] for k in range(8)) for j in range(8)] for i in range(8)]


def scaled(A, c):
    return [[x*c for x in row] for row in A]


R = matrix(values(law[:law.index("gram:")]))
H = matrix(values(law[law.index("gram:"):law.index("chart:")]))
exponent = int(re.search(r"chart: SolvedChart \{ exponent: (\d+)", law)[1])
scale = int(re.search(r"chart: SolvedChart \{ exponent: \d+, scale: (\d+)", law)[1])
block = re.search(r"support: \[([^\]]+)\], block: \[([^\]]+)\]", law)
assert list(map(int, block[1].split(","))) == list(range(8))
X = matrix([F(int(x), 2**exponent) for x in block[2].split(",")])
c, s = F(2), F(2**scale)
R_star, H_star, X_star = scaled(R, 1/c), scaled(H, c*c), scaled(X, 1/(c*c))
assert scaled(R_star, c) == R  # coefficient identity: R_star (c f) = R f for every f
assert multiply(X_star, H_star) == multiply(X, H)
trace = sum(H[i][i]-s for i in range(8))
scaled_trace = sum(H_star[i][i]-c*c*s for i in range(8))
assert scaled_trace/(c*c*s) == trace/s
residual = multiply(X, H)
delta = max(sum(abs((F(1) if i == j else F())-residual[i][j]) for j in range(8)) for i in range(8))
certificate = values(law[law.index("certificate:"):law.index("map_carry:")])[0]
assert delta == certificate
print(json.dumps({
    "scope": "saved v60 phase2 normal-law coefficient identities; no phase0/algorithm inference",
    "native_Word_deposit_or_model_calls": 0,
    "coordinate_unit_c": str(c), "current_prior": str(s), "reexpressed_prior": str(c*c*s),
    "R_star_times_c_equals_R": True, "left_chart_residual_invariant": True,
    "sample_trace_over_prior_invariant": str(trace/s), "chart_residual_exact": str(delta),
    "carrier_units": {"map": "u_R/c", "map_remainder": "r_R/c",
                      "Gram": "c^2 u_H", "Gram_remainder": "c^2 r_H",
                      "solved_chart": "u_X/c^2", "released_residuals": "same scaling as their carrier"},
    "limitations": "No observed feature invented; per-teaching features remain unlogged. Exact coefficient identities hold for every f. Native lattice/floor/certified-step equivariance is not asserted; no transformed model is constructed or run."
}, indent=2))
