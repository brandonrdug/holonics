# Digit and mantissa distributions of the passage's single-operation integer products, read as the
# faces a multiplier acts on: the trailing face (units on Z/10 = Z/2 x Z/5, the unit ring <3> = Z/4)
# and the leading face (Benford). usage: python3 -I digits.py PASSAGE OUT_JSON
import json, re, sys, math, collections
passage = open(sys.argv[1], "rb").read()
op_re = re.compile(rb"^(\d+)\*(\d+)$")
U = {1, 3, 7, 9}
DLOG = {1: 0, 3: 1, 9: 2, 7: 3}                       # 3^k mod 10
operand_units, result_units, result_lead = collections.Counter(), collections.Counter(), collections.Counter()
kind = collections.Counter(); unit_pairs = 0; dlog_ok = 0; nine = []; nine_ok = 0
for m in re.finditer(rb"<<([^=>]*)=([^>]*)>>", passage):
    o = op_re.match(m.group(1)); r = m.group(2)
    if not o or not re.fullmatch(rb"\d+", r) or int(r) == 0: continue
    x, y, z = int(o.group(1)), int(o.group(2)), int(r)
    ux, uy, uz = x % 10, y % 10, z % 10
    operand_units[ux] += 1; operand_units[uy] += 1; result_units[uz] += 1; result_lead[int(str(z)[0])] += 1
    kind["both units of Z/10" if ux in U and uy in U else ("a zero (units 0)" if 0 in (ux, uy) else "zero divisor, no zero")] += 1
    if ux in U and uy in U:
        unit_pairs += 1; dlog_ok += (DLOG[ux] + DLOG[uy]) % 4 == DLOG[uz]
    for a, b in ((x, y), (y, x)):
        if a == 9:
            nine.append((b, z)); nine_ok += z % 10 == (10 - b % 10) % 10
n = sum(result_units.values())
benford = {d: math.log10(1 + 1 / d) for d in range(1, 10)}
out = {"products": n, "operand units": dict(sorted(operand_units.items())), "result units": dict(sorted(result_units.items())),
       "result leading digit": dict(sorted(result_lead.items())), "benford share": benford, "kinds": dict(kind),
       "unit pairs": unit_pairs, "unit pairs whose discrete logs add": dlog_ok,
       "products by 9": len(nine), "products by 9 ending in 10 minus the other's units": nine_ok, "examples by 9": nine[:8]}
json.dump(out, open(sys.argv[2], "w"), indent=1)
print("products", n); print("kinds", dict(kind))
print("operand units", dict(sorted(operand_units.items())))
print("result units ", dict(sorted(result_units.items())))
print("result lead  ", dict(sorted(result_lead.items())), " benford", {d: round(benford[d] * n) for d in benford})
print("unit pairs", unit_pairs, "discrete logs add", dlog_ok, "| products by 9", len(nine), "ending 10-x", nine_ok, nine[:8])
