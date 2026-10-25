# The carriage's ceiling table, a diagnostic held table (authored; read as a ceiling, never as a
# founding): a newline rests the ring, a digit holds it at 15/16, and '+' and '=' turn it by the
# seam digit's tenth of a turn at 15/16; '*' and '-' hold it. Pairs as (seam class, arriving class).
import math, sys
U = 1 << 30
m = U * 15 // 16
digits = range(48, 58)
out = []
for prev in list(range(256)) + [256]:
    for cur in [10, 42, 43, 45, 61] + list(digits):
        if cur == 10:
            mv = (0, 0)
        elif cur in (43, 61) and prev in digits:
            a = 2 * math.pi * (prev - 48) / 10
            mv = (round(m * math.cos(a)), round(m * math.sin(a)))
        else:
            mv = (m, 0)
        out.append(f"{prev} {cur} {mv[0]} {mv[1]} 0 0")
open(sys.argv[1], 'w').write("\n".join(out) + "\n")
