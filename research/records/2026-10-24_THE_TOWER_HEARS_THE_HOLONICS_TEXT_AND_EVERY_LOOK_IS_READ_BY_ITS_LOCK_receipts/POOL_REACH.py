"""Whether the digits' ring is an attractor of the blind founding, and whether the landmark's breadth
is what makes the line marks lead.

POOL_SEEDS.py: from the unit and from the classes' coupling modes 1, 2 and 4 the blind founding,
read after `=` on a sum's line, closes on forms whose pool sits on the lines' marks (newline, the
operations, `=`) with shares 0.40 to 0.57, and reads 44 to 51 of 495 held out at B. From mode 3
(the digits' ring, chi_1 and chi_9 at 0.44 each) it stays on the digits (0.988), turns towards
chi_1 (0.70) and reads 116, at the smallest share (0.27). Two readings of why:
- "long": from mode 3, eight rounds instead of three. If the pool keeps turning to chi_1 and the
  units reach the 393 the handed chi_1 pool reached, the digits' ring is a basin of the alternation
  whose share the louder line marks exceed.
- "U": the landmark after `=` marks about four cells a line, and the result's units are news at one
  of them (the cell before c0 is coded); the line's end is news at the others. Read at the sums' U
  cells alone (the landmark marking where the result's units are coded, not their value), from the
  unit, mode 2 and mode 3, three rounds each. If the unit start then founds the digits' ring, the
  breadth of the landmark, not the pool law, made the line marks lead.
Each step prints as BLIND_POOL.py.
Projection (largest measured: loading 31 s, K a few seconds, a start of three rounds and its close
82 s): "long" about 31 + 8 x 27 + 27 = 280 s, deadline 480 s; "U" about 31 + 3 x 82 = 280 s,
deadline 480 s; peak under 5 GiB each. Argument 1 "long" or "U", then POOL_SEED.py, BLIND_POOL.py,
BLIND_GATE.py, OP_GATE.py, RING_REGIONS.py and FOUND_RING.py."""
import sys
which = sys.argv[1]
ps = open(sys.argv[2]).read()
sys.argv = [sys.argv[0]] + sys.argv[3:]
exec(ps[:ps.index("bv = np.zeros(256, dtype=complex); bv[classes] = U[:, 0] + 1j * U[:, 1]")])

def start_of(i):
    e = np.zeros(256, dtype=complex)
    if i is None:
        e[classes] = 1
    else:
        e[classes] = U[:, i]
    return e

def found(name, bv, read, rounds, every):
    print(f"from {name}: {pool_report(bv)}", flush=True)
    gv = np.ones(N)
    for rnd in range(rounds):
        P = a_cols(bv, gv)
        lead, th = found_k(*read_rows(P, read)); del P
        a = th[:128] + 1j * th[128:]
        P = b_cols(a, gv)
        lead, wv = found_k(*read_rows(P, read)); del P
        bv = np.zeros(256, dtype=complex); bv[classes] = wv[0::2] + 1j * wv[1::2]
        if every:
            step(f"from {name}, round {rnd}, the pool", a, bv, gv, lead)
        P = g_cols(a, bv)
        lead, gw = found_k(*read_rows(P, read)); del P
        gv = XG @ gw
    P = a_cols(bv, gv)
    lead, th = found_k(*read_rows(P, read)); del P
    a = th[:128] + 1j * th[128:]
    step(f"from {name}, closing", a, bv, gv, lead)

if which == "long":
    found("K's mode 3, eight rounds, read after = on a sum's line", start_of(2), after_sum, 8, True)
else:
    for name, i in [("the unit", None), ("K's mode 2", 1), ("K's mode 3", 2)]:
        found(f"{name}, read at the sums' U cells", start_of(i), read_u, 3, False)
print(f"done in {time.time() - t0:.1f} s")
