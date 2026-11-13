"""P57 item 1 (G131), a ruler on the host: the schedule of one store-trainer section from a launch trace, the entries' lowering, a 100-section
profile and the source survey; the families beside the count's products and octets. Numbers only.

usage: python3 schedule.py TRACE_LOG PROFILE_LOG SURVEY_TSV ENGINE_COUNT_TXT STEP5_RECEIPT
TRACE_LOG: a train-store log with FIELD_TRACE, FIELD_TRACE_REGIONS and FIELD_ENTRY lines (the section read is run 1, the trace's second);
PROFILE_LOG: a 100-section profiled log (FIELD_PROFILE entry lines) of main's kernels; SURVEY_TSV: the kernels' source survey (entry, launch
lines, grid, unit, reads, writes, cross_region, notes); ENGINE_COUNT_TXT: engine_count.py's table; STEP5_RECEIPT: p55_step5.txt (its fourteen
PROFILE entries).
"""
import re
import sys
from collections import OrderedDict, defaultdict

SMS = 80
LANE_STEPS = 2.611e13
STEPS_A_PRODUCT = 6
OCTETS_A_SECOND = 7.36e11
RUN = 1
FAMILIES = [
    ("contact", r"field_(contact_|exposure|pace_skin_back|spread|sums|classes)"),
    ("moments and clocks", r"field_(moment_|pace_|paces|pframes|skin_addresses)"),
    ("site maps", r"field_(affine|outer|transposed)"),
    ("blank clocks", r"field_blank_"),
    ("faces", r"field_(face|tied_|encoding|exponential|open)"),
    ("carry circles", r"field_pair"),
    ("site kernels, small", r"field_"),
]
COUNT_OF = {
    "contact": ["contact, forward", "contact, return", "crowds"],
    "moments and clocks": ["moments"],
    "site maps": ["site maps, forward", "site maps, return"],
    "blank clocks": ["blank clocks"],
    "faces": ["face and its return"],
    "carry circles": [],
    "site kernels, small": ["site kernels, small"],
}


def family(entry):
    return next(name for name, pattern in FAMILIES if re.match(pattern, entry))


def kv(line):
    return dict(w.split("=", 1) for w in line.split()[1:] if "=" in w)


trace_log, profile_log, survey_tsv, count_txt, step5 = sys.argv[1:6]
launches, attrs, regions = [], {}, {}
for line in open(trace_log):
    if line.startswith("FIELD_TRACE "):
        k = kv(line)
        if int(k["run"]) == RUN:
            g = [int(x) for x in k["grid"].split(",")]
            launches.append(dict(seq=int(k["seq"]), after=k["phase"], entry=k["entry"], blocks=g[0] * g[1] * g[2], grid=k["grid"], block=int(k["block"]),
                                 shared=int(k["shared"]), ns=int(k["ns"]), head=k["head"]))
    elif line.startswith("FIELD_ENTRY "):
        k = kv(line)
        attrs[(k["entry"], int(k["block"]), int(k["shared"]))] = {a: int(k[a]) for a in ("registers", "static_shared", "local", "max_threads", "blocks_a_multiprocessor")}
    elif line.startswith("FIELD_TRACE_REGIONS "):
        k = kv(line)
        regions[int(k["run"])] = k
prof = OrderedDict()
for line in open(profile_log):
    m = re.match(r"FIELD_PROFILE entry=(\w+) launches=(\d+) ms=(\d+) us_a_launch=(\d+) grid_threads=(\d+)", line)
    if m:
        prof[m.group(1)] = dict(launches=int(m.group(2)) / 100, ms=int(m.group(3)) / 100, threads=int(m.group(5)))
survey = {}
try:
    rows = [l.rstrip("\n").split("\t") for l in open(survey_tsv)]
    head = rows[0]
    for r in rows[1:]:
        if r and r[0].startswith("field_"):
            survey[r[0]] = dict(zip(head, r + [""] * (len(head) - len(r))))
except FileNotFoundError:
    pass
printed = [m.group(1) for m in (re.match(r"PROFILE entry=(\w+)", l) for l in open(step5)) if m]
counted = {}
for line in open(count_txt):
    cells = [c.strip() for c in line.split("|")]
    if len(cells) == 6 and cells[0] != "family":
        counted[cells[0]] = (float(cells[4]), float(cells[5]))

out = []
p = out.append
reg = regions.get(RUN, {})
p("# P57 item 1 (G131): the schedule of one store-trainer section, launch by launch, from a launch trace of claude/engine-schedule (step 6's")
p("# realization with a trace reading; kernels as main's but the faces' gather), sections 2,001 to 2,003 from run 2's STATE.1900, the second traced;")
p("# the entries' ms a section from the 100-section profiled control of P58's hold (main's kernels with the P56 readings). Numbers only.")
p(f"SECTION run={RUN} regions={reg.get('regions')} sites={reg.get('sites')} largest_region={reg.get('largest')} median_region={reg.get('median')} smallest_region={reg.get('smallest')} launches={len(launches)}")
p(f"CARD multiprocessors={SMS} lane_steps_a_second={LANE_STEPS:.4g} steps_a_product={STEPS_A_PRODUCT} octets_a_second={OCTETS_A_SECOND:.4g}")
p("## every launch in order: seq, after the phase mark, entry, grid (blocks), block, dynamic shared, registers, blocks a multiprocessor, resident warps a")
p("## multiprocessor, the grid's warps over the card's resident warps (fill, capped at 1), traced us, head")
total_ns = sum(l["ns"] for l in launches)
unfilled_ns = 0
for l in launches:
    a = attrs.get((l["entry"], l["block"], l["shared"]), {})
    warps = -(-l["block"] // 32)
    resident = a.get("blocks_a_multiprocessor", 0) * warps
    fill = min(1.0, l["blocks"] * warps / (SMS * resident)) if resident else 0.0
    l["fill"], l["resident"], l["registers"] = fill, resident, a.get("registers", 0)
    if l["blocks"] * warps < 0.5 * SMS * resident:
        unfilled_ns += l["ns"]
    p(f"L {l['seq']} after={l['after']} {l['entry']} grid={l['grid']} block={l['block']} shared={l['shared']} registers={a.get('registers')} blocks_a_sm={a.get('blocks_a_multiprocessor')}"
      f" resident_warps_a_sm={resident} fill={fill:.3f} us={l['ns'] / 1000:.1f} head={l['head']}")
p(f"TRACE section_kernel_us={total_ns / 1000:.1f} launches={len(launches)}")
p("## by entry: launches a section (trace), ms a section (100-section profile), fill range, the entry's lowering, family, unit, and the source survey's columns")
by = defaultdict(list)
for l in launches:
    by[l["entry"]].append(l)
for entry, ls in sorted(by.items(), key=lambda e: -prof.get(e[0], {}).get("ms", 0)):
    pr = prof.get(entry, {})
    s = survey.get(entry, {})
    fills = [l["fill"] for l in ls]
    p(f"E {entry} family={family(entry)} launches_traced={len(ls)} launches_a_section={pr.get('launches', 0):.0f} ms_a_section={pr.get('ms', 0):.2f}"
      f" us_a_launch={1000 * pr.get('ms', 0) / max(pr.get('launches', 1), 1):.1f} registers={ls[0]['registers']} fill_min={min(fills):.3f} fill_max={max(fills):.3f}"
      f" printed_in_step5={'yes' if entry in printed else 'no'} cross_region={s.get('cross_region', '?').split(' ')[0]}")
    if s:
        for col in ("grid", "unit", "reads", "writes", "cross_region", "notes"):
            if s.get(col):
                p(f"  {col}: {s[col]}")
kernels = sum(v["ms"] for v in prof.values())
p("## G131")
rest = {e: v for e, v in prof.items() if e not in printed}
rest_ms = sum(v["ms"] for v in rest.values())
rest_launches = sum(v["launches"] for v in rest.values())
p(f"G131 kernels_ms_a_section={kernels:.1f} printed_entries={len(printed)} printed_ms={kernels - rest_ms:.1f} rest_entries={len(rest)} rest_ms={rest_ms:.1f}")
p(f"G131 part=a rest_entries={len(rest)} (guess 45, 30..70) rest_launches_a_section={rest_launches:.0f} (guess 330, 250..400) ms_a_launch={rest_ms / max(rest_launches, 1):.3f} (guess 0.24, 0.19..0.31)")
paced = sum(v["ms"] for e, v in rest.items() if family(e) == "moments and clocks")
p(f"G131 part=b moments_and_clocks_in_rest_ms={paced:.2f} share={paced / rest_ms:.3f} (guess 0.45, 0.30..0.60)")
p(f"G131 part=c unfilled_launches_traced_us={unfilled_ns / 1000:.1f} share_of_traced_kernels={unfilled_ns / total_ns:.3f} (guess 0.30, 0.15..0.45)")
# the same on the 100-section profile, each entry's launches taken at its traced launches' fill
unf = 0.0
for entry, ls in by.items():
    pr = prof.get(entry)
    if not pr:
        continue
    traced = sum(l["ns"] for l in ls)
    under = sum(l["ns"] for l in ls if l["blocks"] * -(-l["block"] // 32) < 0.5 * SMS * l["resident"])
    unf += pr["ms"] * (under / traced if traced else 0.0)
p(f"G131 part=c_profile unfilled_ms_a_section={unf:.1f} share_of_kernels={unf / kernels:.3f} (each entry's profiled time split by its traced launches' fill)")
# (d): the couplings across regions in the training path, read at source. The contact entry's carrier width (field_contact_l5 to l20) is chosen
# on the host from the exposure's spread, the batch's one maximum (bits[1], fetched between the two each tick). The entries whose unit is an
# entry of the constitution summed over tiles of sites that cross regions carry the deposits' sums over the batch. field_exposure's own
# width is read off the material. Every other entry's unit is a site, a row, a region or a cell of one, and the survey reads no value of
# another region in it.
WIDTH = r"field_contact_l\d+$"
DEPOSIT_SUMS = {"field_outer_x32", "field_outer_x64", "field_blank_bias_enc", "field_blank_lift_read", "field_tied_back_e", "field_encoding"}
ONCE_A_RUN = {"field_exponential"}
if survey:
    width = sum(v["ms"] for e, v in prof.items() if re.match(WIDTH, e))
    sums = sum(v["ms"] for e, v in prof.items() if e in DEPOSIT_SUMS)
    once = sum(v["ms"] for e, v in prof.items() if e in ONCE_A_RUN)
    crossed = sum(v["ms"] for e, v in prof.items() if not survey.get(e, {}).get("cross_region", "no").lower().startswith("no"))
    unknown = sum(v["ms"] for e, v in prof.items() if e not in survey)
    local = kernels - width - sums - once - crossed - unknown
    p(f"G131 part=d region_local_ms={local:.1f} share={local / kernels:.3f} (guess 0.85, 0.70..0.95); coupled: the carrier width {width:.1f} ms"
      f" ({width / kernels:.3f}), the deposits' sums over tiles of the batch {sums:.1f} ({sums / kernels:.3f}), once a run {once:.2f},"
      f" a cross-region read {crossed:.1f}, not surveyed {unknown:.1f}")
def held(read, lo, hi):
    return "HELD" if lo <= read <= hi else ("MISSED below" if read < lo else "MISSED above")


p(f"G131_SCORE a entries {len(rest)}: {held(len(rest), 30, 70)}; launches {rest_launches:.0f}: {held(rest_launches, 250, 400)}; ms a launch {rest_ms / max(rest_launches, 1):.3f}: {held(rest_ms / max(rest_launches, 1), 0.19, 0.31)}")
p(f"G131_SCORE b {paced / rest_ms:.3f}: {held(paced / rest_ms, 0.30, 0.60)}")
p(f"G131_SCORE c {unfilled_ns / total_ns:.3f} (the profile's {unf / kernels:.3f}): {held(unfilled_ns / total_ns, 0.15, 0.45)}")
if survey:
    p(f"G131_SCORE d {local / kernels:.3f}: {held(local / kernels, 0.70, 0.95)}")
c_share = unfilled_ns / total_ns
rule_c = "the fusion first" if c_share >= 0.25 else ("the contact's layout alone first (a pair's record in walk order, its forward entries one launch, its return's one), the small launches stay" if c_share < 0.15 else "the layout first, the fusion second")
p(f"G131_RULE (c) at {c_share:.3f}: {rule_c}; (d) at {local / kernels:.3f}: {'the couplings are derived as joins at named crossings first' if survey and local / kernels < 0.70 else 'no join is derived before the order'}")
# What the reading holds past its score: the launches whose unit is a region (a block or a thread a region, or a region and a head, mode
# or circle) run for as long as the batch's largest region, whatever their fill.
if survey:
    per_region = [e for e in prof if re.search(r"\bregion\b", survey.get(e, {}).get("unit", "").split(";")[0]) and not re.search(r"\bsite\b", survey.get(e, {}).get("unit", "").split(";")[0])]
    pr_ms = sum(prof[e]["ms"] for e in per_region)
    p(f"G131 region_units entries={len(per_region)} ms_a_section={pr_ms:.1f} share={pr_ms / kernels:.3f} largest_over_median_region={int(reg.get('largest', 0)) / max(int(reg.get('median', 1)), 1):.2f}"
      f" ({', '.join(sorted(per_region))})")
p("## families: ms a section, launches, the count's products and octets a section, the floors at the card's lanes and its octets a second")
fam = defaultdict(lambda: [0.0, 0.0])
for e, v in prof.items():
    fam[family(e)][0] += v["ms"]
    fam[family(e)][1] += v["launches"]
p("family | ms a section | launches a section | products a section | arithmetic floor ms | products a second achieved | octets a section | octets floor ms"
  " | octets a second achieved | over the card's | ms over the larger floor")
for name, _ in FAMILIES:
    ms, n = fam[name]
    products = sum(counted.get(k, (0, 0))[0] for k in COUNT_OF[name])
    octets = sum(counted.get(k, (0, 0))[1] for k in COUNT_OF[name])
    af = 1e3 * products * STEPS_A_PRODUCT / LANE_STEPS
    of = 1e3 * octets / OCTETS_A_SECOND
    floor = max(af, of)
    rate = 1e3 * products / ms if ms else 0.0
    orate = 1e3 * octets / ms if ms else 0.0
    p(f"{name} | {ms:.1f} | {n:.0f} | {products:.4g} | {af:.2f} | {rate:.3g} | {octets:.4g} | {of:.2f} | {orate:.3g} | {orate / OCTETS_A_SECOND:.3f}"
      f" | {ms / floor if floor else float('nan'):.1f}")
tp = sum(v[0] for v in counted.values())
to = sum(v[1] for v in counted.values())
p(f"all | {kernels:.1f} | {sum(v['launches'] for v in prof.values()):.0f} | {tp:.4g} | {1e3 * tp * STEPS_A_PRODUCT / LANE_STEPS:.2f} | {1e3 * tp / kernels:.3g} | {to:.4g}"
  f" | {1e3 * to / OCTETS_A_SECOND:.2f} | {1e3 * to / kernels:.3g} | {1e3 * to / kernels / OCTETS_A_SECOND:.3f} | {kernels / max(1e3 * tp * STEPS_A_PRODUCT / LANE_STEPS, 1e3 * to / OCTETS_A_SECOND):.1f}")
p("FAMILY_NOTE the products and octets a section are engine_count.py's count on run 2 (40,741 sites a section, the traced one 41,462); no per-launch")
p("  octet counter is open on this card (the driver keeps profiling counters to its administrators and no Nsight Compute is installed), so the")
p("  octets stand by family from the count, and a launch row carries its grid, fill and traced time.")
print("\n".join(out))
