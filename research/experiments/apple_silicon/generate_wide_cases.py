import json, random
from math import gcd

rng = random.Random(0x5EED_2026)
MASK = (1 << 32) - 1

def limbs(x):
    return [(x >> (32*i)) & MASK for i in range(4)]

pairs = []
for i in range(100):
    if i < 40:
        a = rng.randrange(1, 1 << 95)
        b = rng.randrange(1, 1 << 31)
    elif i < 70:
        base = rng.randrange(1, 1 << 40)
        q = rng.randrange(1, 1 << 80)
        a, b = base * q, base
    else:
        a = rng.randrange(1, 1 << 127)
        b = rng.randrange(1, 1 << 32)
    pairs.append((a, b))

# Preserve the original wide cases, and exercise the complete 32-/64-bit chart
# boundaries used by the exact Metal carrier specializations.
for a in (0, 1, 2, 32767, 32768, (1 << 32)-1, 1 << 32, (1 << 64)-1):
    for b in (1, 2, 32768, (1 << 32)-1, (1 << 32)+1, (1 << 64)-1):
        pairs.append((a, b))
for _ in range(100):
    pairs.append((rng.randrange(1 << 32), rng.randrange(1, 1 << 32)))

cases = []
for a, b in pairs:
    product = a * b
    flags = 1 if product >= (1 << 127) else 0
    cases.append({
        "a": limbs(a), "b": limbs(b), "flags": flags,
        "product": limbs(product) if not flags else [0, 0, 0, 0],
        "gcd": limbs(gcd(a, b)), "quotient": limbs(a // b),
    })
with open("research/experiments/apple_silicon/wide_cases.json", "w") as f:
    json.dump(cases, f, separators=(",", ":"))
print(f"generated {len(cases)} deterministic cases")
