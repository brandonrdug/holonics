"""Exact arithmetic on committed v60 receipts; never imports or calls the machine."""
from fractions import Fraction as F
from pathlib import Path
import json
import re

HERE = Path(__file__).resolve().parent


def balanced(text, at, left="[", right="]"):
    depth = 0
    for end in range(at, len(text)):
        depth += text[end] == left
        depth -= text[end] == right
        if depth == 0:
            return text[at:end + 1]
    raise ValueError("unclosed saved Debug block")


def ratios(text):
    return [F(int(n), int(d)) for n, d in
            re.findall(r"Ratio \{ numer: (-?\d+), denom: (\d+) \}", text)]


def logits(line, marker):
    at = line.index("logits: [", line.index(marker)) + len("logits: ")
    return ratios(balanced(line, at))


def mean(rows):
    return [sum(row[j] for row in rows) / len(rows) for j in range(len(rows[0]))]


def centered(rows):
    m = mean(rows)
    return [[x - y for x, y in zip(row, m)] for row in rows]


def rank(row):
    return sorted(range(len(row) // 2), key=lambda c: row[2 * c], reverse=True)


def enclosure(value, grain):
    value *= grain
    return [str(F(value.__floor__(), grain)), str(F(value.__ceil__(), grain))]


def factor(n):
    powers = []
    p = 2
    while p * p <= n:
        k = 0
        while n % p == 0:
            k += 1
            n //= p
        if k:
            powers.append([p, k])
        p = 3 if p == 2 else p + 2
    if n > 1:
        powers.append([n, 1])
    return powers


def main():
    full = (HERE / "v60/HNN_FULL_ACTUAL_OUTPUT.txt").read_text()
    control_lines = [s for s in full.splitlines()
                     if s.startswith("pair fixed-carry material controls;")]
    assert len(control_lines) == 4
    before = [logits(s, "no_pair=") for s in control_lines]
    after = [logits(s, "learned=") for s in control_lines]
    actual = [logits(s, "actual_continuing=") for s in control_lines]
    delta = [[b-a for a, b in zip(x, y)] for x, y in zip(before, after)]
    c_before, c_delta = centered(before), centered(delta)
    c_r_max = max(abs(x) for row in c_before for x in row[::2])
    c_pair_max = max(abs(x) for row in c_delta for x in row[::2])
    expected = json.loads((HERE / "V60_RECEIVING_AND_PAIR_DECOMPOSITION.v1.json").read_text())
    assert before == [[F(x) for x in r] for r in expected["pre_pair_common_carry_logits"]]
    assert after == [[F(x) for x in r] for r in expected["post_pair_common_carry_logits"]]
    assert c_delta == [[F(x) for x in r] for r in expected["centered_pair_delta"]]
    baseline = (HERE.parent / "pair-coordinate-consumer-20261007/v56/HNN_FULL_ACTUAL_OUTPUT.txt").read_text()
    old = [logits(s, "learned=") for s in baseline.splitlines()
           if s.startswith("exact fixed-carry controls;")]
    assert len(old) == 4 and centered(old) == c_before
    assert rank(before[0]) == rank(after[0])
    truths = [1, 2, 3, 0]
    margins = []
    for i, target in enumerate(truths):
        def margin(row):
            return row[2*target] - max(x for c, x in enumerate(row[::2]) if c != target)
        row = {name: margin(values[i]) for name, values in
               (("no_pair", before), ("learned_common", after), ("continuing", actual))}
        for name, value in row.items():
            assert value == F(expected["margins"][i][name + "_margin"])
            assert value < F(1, 16)
        margins.append({name: enclosure(x, 4096) for name, x in row.items()})

    phase = (HERE / "v60/HNN_PHASE_CONTROL_FULL_OUTPUT.txt").read_text()
    line = next(s for s in phase.splitlines() if s.startswith("nonzero-phase current consumer producing="))
    at = line.index("{", line.index("receiving: Some(NormalLaw"))
    law = balanced(line, at, "{", "}")
    gram_at = law.index("[", law.index("gram:"))
    flat = ratios(balanced(law, gram_at))
    assert len(flat) == 64
    scale = int(re.search(r"chart: SolvedChart \{ exponent: \d+, scale: (\d+)", law)[1])
    assert scale == 3 and "ReceivingMap(0): Lattice { exponent: 8 }" in line
    sample_trace = sum(flat[i*8+i] - 2**scale for i in range(8))
    sample_trace_upper = sample_trace + F(8, 256)
    assert sample_trace == F(35, 128) and sample_trace_upper == F(39, 128)
    located = re.search(r"located: Some\(LocatedPrior \{ from: (\d+), a0: Ratio \{ numer: (-?\d+), denom: (\d+) \}, a1: Ratio \{ numer: (-?\d+), denom: (\d+) \}, s: Ratio \{ numer: (-?\d+), denom: (\d+) \}", law)
    founding, n0, d0, n1, d1, ns, ds = map(int, located.groups())
    a0, a1, S = F(n0, d0), F(n1, d1), F(ns, ds)
    # ln 2 = 2 sum_j 1/((2j+1) 3^(2j+1)); the positive tail is bounded geometrically.
    N = 8
    lower = 2*sum((F(1, (2*j+1)*3**(2*j+1)) for j in range(N)), F())
    upper = lower + F(2, (2*N+1)*3**(2*N+1))*F(9, 8)
    assert founding == 0 and S > 0
    assert max(a0 + (a1+S)*x for x in (lower, upper)) < 0

    paths = {
        "v56": HERE.parent / "pair-coordinate-consumer-20261007/v56/VALIDATION.json",
        "v58": HERE.parent / "pair-phase-control-20261007/v58/VALIDATION.json",
        "v60": HERE / "v60/VALIDATION.json",
    }
    cost = {}
    for version, path in paths.items():
        stages = json.loads(path.read_text())["stages"].values()
        stages = list(stages)
        cost[version] = {"jobs": len(stages), "CPU_ns": sum(s["aggregate_CPU_ns"] for s in stages),
                         "wall_ns": sum(s.get("wall_ns", s.get("whole_wall_ns", 0)) for s in stages)}
    total = {k: sum(s[k] for s in cost.values()) for k in ("jobs", "CPU_ns", "wall_ns")}
    assert total == {"jobs": 25, "CPU_ns": 267945955000, "wall_ns": 198753675763}
    print(json.dumps({"saved_output_checks": "pass", "native_calls": 0,
          "R_centered_max_real": str(c_r_max), "pair_centered_max_real": str(c_pair_max),
          "R_to_pair_centered_ratio": str(c_r_max / c_pair_max),
          "pre_pair_rankings": list(map(rank, before)), "post_pair_rankings": list(map(rank, after)),
          "continuing_rankings": list(map(rank, actual)), "margins_at_grain4096": margins,
          "centered_R_equal_v56_v60": True,
          "phase2_prior": str(F(2**scale)), "phase2_sample_trace_upper": str(sample_trace_upper),
          "phase2_trace_upper_over_prior": str(sample_trace_upper / 2**scale),
          "phase2_retained_V_plus_a": "strictly negative",
          "cost_by_continuation": cost, "cost_total": total,
          "cost_CPU_prime_powers": factor(total["CPU_ns"]),
          "cost_wall_prime_powers": factor(total["wall_ns"])}, indent=2))


if __name__ == "__main__":
    main()
