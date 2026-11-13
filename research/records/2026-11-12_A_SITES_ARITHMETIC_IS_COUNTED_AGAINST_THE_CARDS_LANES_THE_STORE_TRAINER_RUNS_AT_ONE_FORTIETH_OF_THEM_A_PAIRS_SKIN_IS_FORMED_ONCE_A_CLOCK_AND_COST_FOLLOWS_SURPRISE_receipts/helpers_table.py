"""P55 A5, a ruler: the two return entries' time by helper, as counted warp issues times the helper's yardstick, by entry and clock, with the
remainder and each helper's share of the entry's time (the profiled controls' mean in the hold), and G126 (a) to (e) scored. Numbers only.

Inputs in the run directory: count.log (FIELD_TALLY, FIELD_HELPER), tc9.log and tc10.log (the controls' FIELD_PROFILE_HEAD), tparts.log (the parts'
copies), tb4.log (the rows at four blocks). A helper's issues are its call sites' warp issues; products not counted at a site are its block's issues
times the source's count of them a block (the census), named in each line."""
import sys
from collections import defaultdict

Q = sys.argv[1]
SECTIONS = 100
RK = dict(ROW=0, PAIR=2, CROWD=4, DIVISOR=6, DIVBY=8, LOCKDIV64=10, LOCKDIV128=12, LOCK_FALLBACK=14, MULFITS_FAST=16, MULFITS_SLOW=18, ADDWIDE=20, W_WIDE=22, PROBE=24, CROWD_ENTRY=26, CROWD_X=28, LOCKMODE=30)
PK = dict(ROW=0, PAIR=2, PAIR_SIGNED=4, PAIR_MODE=6, CROWD=8, CROWD_SIGNED=10, TURNDIV64=12, TURNDIV128=14, VALDIV64=16, VALDIV128=18, MULFITS_FAST=20, MULFITS_SLOW=22, ADDWIDE=24, W_WIDE=26, BRDIV64=28, BRDIV128=30)


def kv(line):
    return dict(w.split("=", 1) for w in line.split()[1:] if "=" in w)


tally = defaultdict(int)  # (entry, head, row, kind) -> calls over the run
unit = {}  # yardstick kind -> ns a warp issue
for line in open(f"{Q}/count.log"):
    if line.startswith("FIELD_TALLY "):
        d = kv(line)
        tally[(d["entry"], int(d["head"]), d["row"], int(d["kind"]))] += int(d["calls"])
    elif line.startswith("FIELD_HELPER ") and "kind=" in line:
        d = kv(line)
        unit[int(d["kind"])] = float(d["ns_a_warp_issue"])


def prof(name):
    out = {}
    for line in open(f"{Q}/{name}.log"):
        if line.startswith("FIELD_PROFILE_HEAD "):
            d = kv(line)
            out[(d["entry"], int(d["head"]))] = (d["kind"], int(d["us"]))
    return out


c9, c10, parts, b4 = prof("tc9"), prof("tc10"), prof("tparts"), prof("tb4")
kinds = {h: k for (e, h), (k, _) in c9.items()}


def ms(p, entry, h):
    return p[(entry, h)][1] / 1000 / SECTIONS if (entry, h) in p else 0.0


def control(entry, h):
    return (ms(c9, entry, h) + ms(c10, entry, h)) / 2


def w(entry, h, kind, row=None):
    rows = [row] if row else ["definite", "open"]
    return sum(tally[(entry, h, r, kind + 1)] for r in rows) / SECTIONS


def lanes(entry, h, kind, row=None):
    rows = [row] if row else ["definite", "open"]
    return sum(tally[(entry, h, r, kind)] for r in rows) / SECTIONS


def t(issues, k):
    return issues * unit[k] / 1e6  # ms a section


print("# P55 A5: the two return entries' time by helper (ms a profiled section; counts a section over the pass's sections 2,001 to 2,100).")
print("UNITS " + " ".join(f"k{k}={unit[k]:.4f}" for k in sorted(unit)) + " (ns a warp issue, each helper's yardstick at its entry's launch shape)")
heads = sorted(kinds)
for h in heads:
    for row in ("definite", "open"):
        r, p = (lambda k: lanes("rows", h, RK[k], row)), (lambda k: lanes("pace", h, PK[k], row))
        print(f"COUNTS head={h} kind={kinds[h]} row={row} rows={r('ROW'):.0f} pairs={r('PAIR'):.0f} crowds={r('CROWD'):.0f} crowd_entries={r('CROWD_ENTRY'):.0f} lock_modes={r('LOCKMODE'):.0f}"
              f" lock_fallbacks={r('LOCK_FALLBACK'):.0f} w_wide={r('W_WIDE'):.0f} lockdiv64={r('LOCKDIV64'):.0f} lockdiv128={r('LOCKDIV128'):.0f} divisor_of={r('DIVISOR'):.0f}"
              f" div_by={r('DIVBY'):.0f} mul_fits_fast={r('MULFITS_FAST'):.0f} mul_fits_slow={r('MULFITS_SLOW'):.0f} add_wide={r('ADDWIDE'):.0f}"
              f" | pace rows={p('ROW'):.0f} pairs={p('PAIR'):.0f} signed_pairs={p('PAIR_SIGNED'):.0f} pair_modes={p('PAIR_MODE'):.0f} crowds={p('CROWD'):.0f}"
              f" signed_crowds={p('CROWD_SIGNED'):.0f} turndiv64={p('TURNDIV64'):.0f} turndiv128={p('TURNDIV128'):.0f} valdiv64={p('VALDIV64'):.0f} valdiv128={p('VALDIV128'):.0f}"
              f" brdiv64={p('BRDIV64'):.0f} brdiv128={p('BRDIV128'):.0f} mul_fits_fast={p('MULFITS_FAST'):.0f} mul_fits_slow={p('MULFITS_SLOW'):.0f} add_wide={p('ADDWIDE'):.0f} w_wide={p('W_WIDE'):.0f}")
sums = defaultdict(float)
for h in heads:
    paced = kinds[h] == "paced"
    E = control("field_contact_rows", h)
    sums[("rows", "E", paced)] += E
    W = lambda k: w("rows", h, RK[k])
    helpers = [
        ("div128_crowd_lock", t(W("LOCKDIV64") + W("LOCKDIV128"), 0 if paced else 1), f"issues={W('LOCKDIV128'):.0f}+{W('LOCKDIV64'):.0f}(64)"),
        ("divisor_of", t(W("DIVISOR"), 16) / 2 + t(W("DIVISOR"), 17) / 2, f"issues={W('DIVISOR'):.0f}"),
        ("div_nearest_by", t(W("DIVBY"), 2) / 2 + t(W("DIVBY"), 3) / 2, f"issues={W('DIVBY'):.0f}"),
        ("mul_fits", t(W("MULFITS_FAST") + W("MULFITS_SLOW"), 4), f"issues={W('MULFITS_FAST'):.0f}+{W('MULFITS_SLOW'):.0f}(full)"),
        ("add_wide", t(W("ADDWIDE"), 5), f"issues={W('ADDWIDE'):.0f}"),
        ("products_128", t(5 * W("PAIR") + 2 * W("CROWD_X") + 5 * W("CROWD") + 6 * W("W_WIDE") + 4 * W("LOCK_FALLBACK"), 14), "issues=5 pair+2 crowd_x+5 crowd+6 w_wide+4 fallback"),
        ("products_64", t(32 * W("PAIR") + 2 * W("PROBE") + 8 * W("CROWD_ENTRY") + 6 * W("LOCKMODE"), 13), "issues=32 pair+2 probe+8 crowd_entry+6 lock_mode"),
    ]
    rest = E - sum(x for _, x, _ in helpers)
    for name, x, note in helpers:
        sums[("rows", name, paced)] += x
        print(f"TABLE entry=field_contact_rows head={h} kind={kinds[h]} helper={name} ms={x:.3f} share={x / E:.3f} {note}")
    print(f"TABLE entry=field_contact_rows head={h} kind={kinds[h]} helper=remainder ms={rest:.3f} share={rest / E:.3f} entry_ms={E:.3f}")
    if not paced:
        continue
    E = control("field_pace_skin_back", h)
    sums[("pace", "E", True)] += E
    V = lambda k: w("pace", h, PK[k])
    skins = V("PAIR_MODE") + 8 * V("CROWD_SIGNED")
    helpers = [
        ("div128_bracket", t(V("BRDIV128"), 11), f"issues={V('BRDIV128'):.0f} (64: {V('BRDIV64'):.0f})"),
        ("div_value", t(V("VALDIV64") + V("VALDIV128"), 12), f"issues={V('VALDIV128'):.0f}(128)+{V('VALDIV64'):.0f}(64)"),
        ("skin_back_with_turn", t(skins, 9), f"issues={skins:.0f} (turn's division 64: {V('TURNDIV64'):.0f}, 128: {V('TURNDIV128'):.0f})"),
        ("mul_fits_outside_skin_back", t(V("MULFITS_FAST") + V("MULFITS_SLOW") - 2 * skins, 7) / 2 + t(V("MULFITS_FAST") + V("MULFITS_SLOW") - 2 * skins, 8) / 2, f"issues={V('MULFITS_FAST') + V('MULFITS_SLOW') - 2 * skins:.0f} (full {V('MULFITS_SLOW'):.0f} of all)"),
        ("add_wide", t(V("ADDWIDE"), 5), f"issues={V('ADDWIDE'):.0f}"),
        ("products_128", t(skins + 6 * V("W_WIDE"), 14), "issues=pair_modes+8 signed_crowds+6 w_wide"),
        ("products_64", t(7 * V("PAIR_MODE") + 48 * V("CROWD_SIGNED"), 13), "issues=7 pair_mode+48 signed_crowd"),
    ]
    rest = E - sum(x for _, x, _ in helpers)
    for name, x, note in helpers:
        sums[("pace", name, True)] += x
        print(f"TABLE entry=field_pace_skin_back head={h} kind=paced helper={name} ms={x:.3f} share={x / E:.3f} {note}")
    print(f"TABLE entry=field_pace_skin_back head={h} kind=paced helper=remainder ms={rest:.3f} share={rest / E:.3f} entry_ms={E:.3f}")
    allfits = t(V("MULFITS_FAST") + V("MULFITS_SLOW"), 7) / 2 + t(V("MULFITS_FAST") + V("MULFITS_SLOW"), 8) / 2
    sums[("pace", "mul_fits_all", True)] += allfits
# the entries over the four clocks
Er = sum(control("field_contact_rows", h) for h in heads)
Ep = sum(control("field_pace_skin_back", h) for h in heads if kinds[h] == "paced")
rp = sum(ms(parts, "field_yard_rows_pairs", h) for h in heads)
rc = sum(ms(parts, "field_yard_rows_crowds", h) for h in heads)
pp = sum(ms(parts, "field_yard_pace_pairs", h) for h in heads)
pc = sum(ms(parts, "field_yard_pace_crowds", h) for h in heads)
r4 = sum(ms(b4, "field_contact_rows", h) for h in heads)
c9r, c10r = sum(ms(c9, "field_contact_rows", h) for h in heads), sum(ms(c10, "field_contact_rows", h) for h in heads)
c9p, c10p = sum(ms(c9, "field_pace_skin_back", h) for h in heads), sum(ms(c10, "field_pace_skin_back", h) for h in heads)
print(f"ENTRY rows control1={c9r:.2f} control2={c10r:.2f} spread={abs(c9r - c10r):.2f} pairs_only={rp:.2f} ({rp / Er:.3f}) crowds_only={rc:.2f} ({rc / Er:.3f}) four_blocks={r4:.2f} ({r4 / Er:.3f})")
print(f"ENTRY pace control1={c9p:.2f} control2={c10p:.2f} spread={abs(c9p - c10p):.2f} pairs_only={pp:.2f} ({pp / Ep:.3f}) crowds_only={pc:.2f} ({pc / Ep:.3f})")
for h in heads:
    line = f"PARTS head={h} kind={kinds[h]} rows={control('field_contact_rows', h):.2f} rows_pairs={ms(parts, 'field_yard_rows_pairs', h):.2f} rows_crowds={ms(parts, 'field_yard_rows_crowds', h):.2f} rows_b4={ms(b4, 'field_contact_rows', h):.2f}"
    if kinds[h] == "paced":
        line += f" pace={control('field_pace_skin_back', h):.2f} pace_pairs={ms(parts, 'field_yard_pace_pairs', h):.2f} pace_crowds={ms(parts, 'field_yard_pace_crowds', h):.2f}"
    print(line)
Erp = sums[("rows", "E", True)]
div_rows = sums[("rows", "div128_crowd_lock", True)]
div_rows_all = div_rows + sums[("rows", "divisor_of", True)]
div_pace = sums[("pace", "div128_bracket", True)] + sums[("pace", "div_value", True)]
print(f"G126 a rows_without_crowds={rp / Er:.3f} guess=0.50 band=0.30..0.70")
print(f"G126 b pace_without_crowds={pp / Ep:.3f} guess=0.55 band=0.35..0.75")
print(f"G126 c rows_paced_division_128={div_rows / Erp:.3f} (with divisor_of's own division {div_rows_all / Erp:.3f}) guess=0.12 band=0.04..0.25; pace_divisions={div_pace / Ep:.3f} guess=0.30 band=0.12..0.50")
print(f"G126 d pace_checked_products={sums[('pace', 'mul_fits_all', True)] / Ep:.3f} (outside skin_back_dev {sums[('pace', 'mul_fits_outside_skin_back', True)] / Ep:.3f}) guess=0.20 band=0.08..0.35")
print(f"G126 e rows_four_blocks={r4 / Er:.3f} guess=1.00 band=0.90..1.12")
for entry, E in (("rows", Er), ("pace", Ep)):
    names = sorted({k[1] for k in sums if k[0] == entry and k[1] not in ("E", "mul_fits_all")})
    for name in names:
        x = sums[(entry, name, True)] + sums[(entry, name, False)]
        print(f"SHARE entry={entry} helper={name} ms={x:.3f} share_of_entry={x / E:.3f} rebuilt_by_rule={'yes' if x / E >= 0.08 else 'no'}")
