"""Fold receipt.sh's output into the four-draw range and mean per lap (record 2026-10-31 §6)."""
import re, sys
from collections import defaultdict
lines = open(sys.argv[1]).read().splitlines()
passes = {}
lap, draws = None, defaultdict(lambda: defaultdict(list))
flux = {}
for l in lines:
    m = re.match(r"TOWER_PASS pass=(\d+) train_bits_a_byte=([\d.]+) dev_bits_a_byte=([\d.]+) dev_regions Q=([\d.]+) P=([\d.]+) N=([\d.]+) M=([\d.]+).*elapsed_ms=(\d+)", l)
    if m:
        passes[int(m.group(1)) + 1] = m.groups()[1:]
    m = re.match(r"== lap (\d+)", l)
    if m:
        lap = int(m.group(1))
    m = re.match(r"FLUX .* = ([\d.-]+) bits", l)
    if m:
        flux[lap] = float(m.group(1))
    d = draws[lap]
    m = re.match(r"WRITTEN dir=\S+ problems=\d+ a_on_problem=(\d+) b_free_calculations=(\d+) b_free_right=(\d+) c_first_calculations=(\d+) c_from_question=(\d+) b_equals=(\d+)/\d+ met=(\d+)/(\d+) never_met=(\d+)/(\d+)", l)
    if m:
        for k, v in zip(["on_problem", "free_calcs", "free_right", "first_calcs", "first_from_question", "equals", "met", "met_n", "never", "never_n"], m.groups()):
            d[k].append(int(v))
    m = re.match(r"CARRY dir=\S+ never_met=\S+ never_by_op \+=(\d+)/(\d+) -=(\d+)/(\d+) \*=(\d+)/(\d+) /=(\d+)/(\d+) carrying_sums=(\d+) right=(\d+) wrong_tens_right=(\d+) wrong_tens_without_carry=(\d+) wrong_tens_neither=(\d+) wrong_not_whole=(\d+)", l)
    if m:
        g = list(map(int, m.groups()))
        for k, v in zip(["never+", "never+n", "never-", "never-n", "never*", "never*n", "never/", "never/n", "carry_n", "carry_right", "carry_tens_right", "carry_tens_without", "carry_tens_neither", "carry_not_whole"], g):
            d[k].append(v)
    m = re.match(r"\S+ WRITTEN_COUPLING chart=(\w+) problems=\d+ held=\d+ written=(\d+) lambda=(\d+) friction=(\d+) plateaus=\d+ longest=(\d+) question_own=(\d+) question_next=(\d+)", l)
    if m:
        c, written, lam, fr, longest, own, nxt = m.group(1), *map(int, m.groups()[1:])
        d[f"{c}_lambda"].append(lam); d[f"{c}_friction"].append(fr); d[f"{c}_written"].append(written)
        d[f"{c}_question_contact"].append(own - nxt); d[f"{c}_own"].append(own); d[f"{c}_next"].append(nxt)
def rm(v):
    return f"{min(v)}–{max(v)} ({sum(v)/len(v):.2f})" if v else "-"
for lap in sorted(k for k in draws if k):
    d = draws[lap]
    p = passes.get(lap)
    print(f"== lap {lap}" + (f": training {p[0]} held-out {p[1]} (Q {p[2]} P {p[3]} N {p[4]} M {p[5]}) elapsed {int(p[6])/1000:.1f} s" if p else "") + (f"; flux {flux.get(lap)}" if lap in flux else ""))
    for k in ["on_problem", "free_calcs", "free_right", "first_calcs", "first_from_question", "equals", "met", "never", "never+", "never-", "never*", "never/", "carry_n", "carry_right", "carry_tens_right", "carry_tens_without", "carry_tens_neither", "carry_not_whole",
              "bytes_lambda", "bytes_friction", "bytes_question_contact", "numerals_lambda", "numerals_friction", "numerals_question_contact", "numerals_own", "numerals_next"]:
        extra = ""
        if k in ("met", "never") and d.get(k + "_n"):
            extra = f" of {d[k + '_n'][0]}"
        if k.startswith("never") and len(k) == 6 and d.get(k + "n"):
            extra = f" of {d[k + 'n'][0]}"
        print(f"  {k}: {rm(d.get(k, []))}{extra}")
