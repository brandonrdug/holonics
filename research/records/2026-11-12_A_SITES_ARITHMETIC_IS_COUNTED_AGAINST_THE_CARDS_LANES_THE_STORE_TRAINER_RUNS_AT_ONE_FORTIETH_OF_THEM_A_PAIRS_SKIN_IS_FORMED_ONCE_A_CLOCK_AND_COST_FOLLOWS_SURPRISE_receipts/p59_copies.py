"""P59 item 2, a ruler on the host: the contact's copies against their entries, one mechanism a copy. Numbers only.

Per copy: its SASS counts (cuobjdump of ptxas's sm_89 cubin from the ruler build's PTX), its registers, stack and spills (ptxas -v), its launches
and ms a profiled section (by head where the entry is launched a head at a time), the entry's ms in the two profiled controls of the same hold,
the controls' spread, and the copy's ratio over the mean of the two controls; its checked products that took their long path and the status
bits it raised; for the copies that must give their entry's words, the words compared and those that differ.

usage: python3 p59_copies.py RUN_DIR
"""
import re
import sys
from collections import defaultdict

Q = sys.argv[1]
SECTIONS = 100
ENTRIES = {
    "exposure": "field_exposure",
    "contact_l5": "field_contact_l5",
    "contact_l6": "field_contact_l6",
    "contact_rows": "field_contact_rows",
    "contact_columns": "field_contact_columns",
    "pace_skin_back": "field_pace_skin_back",
}
MECHANISMS = {"n": "the entry as it stands", "r": "source rows resident", "w": "a pair's words in walk order", "a": "the reductions as plain stores",
              "c": "the columns from a record in column order"}
COUNTED = ["LDG", "STG", "ATOMG", "RED", "LDS", "STS", "LDL", "STL", "IMAD", "IMAD_WIDE"]


def sass_counts(path):
    counts, name = {}, None
    op = re.compile(r"^\s+/\*[0-9a-f]{4,}\*/\s+(?:@!?U?P[T0-9]+\s+)?([A-Z][A-Z0-9_.]*)")
    for line in open(path):
        m = re.search(r"Function : (\S+)", line)
        if m:
            name = m.group(1)
            counts[name] = defaultdict(int)
            continue
        m = op.match(line)
        if m and name:
            o = m.group(1)
            c = counts[name]
            c["instructions"] += 1
            base = o.split(".")[0]
            if o.startswith("IMAD.WIDE"):
                c["IMAD_WIDE"] += 1
            elif o.startswith("IMAD.HI"):
                c["IMAD_HI"] += 1
            elif base == "IMAD":
                c["IMAD"] += 1
            elif base in COUNTED:
                c[base] += 1
    return counts


def resources(path):
    out, name = {}, None
    for line in open(path):
        m = re.search(r"Function properties for (\S+)", line)
        if m:
            name = m.group(1)
            out.setdefault(name, {})
            continue
        m = re.search(r"(\d+) bytes stack frame, (\d+) bytes spill stores, (\d+) bytes spill loads", line)
        if m and name:
            out[name].update(stack=int(m.group(1)), spill_stores=int(m.group(2)), spill_loads=int(m.group(3)))
            continue
        m = re.search(r"Compiling entry function '(\S+)'", line)
        if m:
            name = m.group(1)
            out.setdefault(name, {})
            continue
        m = re.search(r"Used (\d+) registers", line)
        if m and name:
            out[name]["registers"] = int(m.group(1))
    return out


def profile(path):
    entry, head, copy, check = {}, defaultdict(dict), {}, {}
    for line in open(path):
        m = re.match(r"FIELD_PROFILE entry=(\w+) launches=(\d+) ms=(\d+) us_a_launch=(\d+)", line)
        if m:
            entry[m.group(1)] = (int(m.group(2)), int(m.group(4)) * int(m.group(2)) / 1000.0)
        m = re.match(r"FIELD_PROFILE_HEAD entry=(\w+) head=(\d+) kind=(\w+) launches=(\d+) us=(\d+)", line)
        if m:
            head[m.group(1)][int(m.group(2))] = (m.group(3), int(m.group(4)), int(m.group(5)) / 1000.0)
        m = re.match(r"FIELD_PROFILE_COPY entry=(\w+) launches=(\d+) long_paths=(\d+) status_bits=(\d+)", line)
        if m:
            copy[m.group(1)] = (int(m.group(2)), int(m.group(3)), int(m.group(4)))
        m = re.match(r"FIELD_PROFILE_COPY_CHECK entry=(\w+) words_compared=(\d+) words_differing=(\d+)", line)
        if m:
            check[m.group(1)] = (int(m.group(2)), int(m.group(3)))
    return entry, head, copy, check


sass = sass_counts(f"{Q}/field_copies.sass")
res = resources(f"{Q}/ptxas.log")
c1, h1, _, _ = profile(f"{Q}/hc1.log")
cp, hp, copies, checks = profile(f"{Q}/hcopies.log")
c2, h2, _, _ = profile(f"{Q}/hc2.log")
P = []
p = P.append
p("# P59 item 2, 2026-11-13 UTC: the contact's copies, one mechanism a copy, each launched immediately before its entry on the entry's words, its")
p("# outputs in scratch arrays that start as the entry's (claude/contact-copies; tools/contact_copies.py generates them from field.cu's entries).")
p("# One hold: a profiled control, the copies' run, a profiled control; the store trainer's sections 2,001 to 2,100 from run 2's STATE.1900.")
p("# ms are a profiled section's (a run's total over its 100 sections). SASS from ptxas for sm_89 on the ruler build's PTX. Numbers only.")
p("## the builds")
for b in ("bin_copies", "bin_control"):
    p(open(f"{Q}/{b}/BUILD").read().strip())
p("## the entries in the controls (ms a profiled section, both controls) and their lowering")
for key, e in ENTRIES.items():
    r, s = res.get(e, {}), sass.get(e, {})
    a, b = c1.get(e, (0, 0.0)), c2.get(e, (0, 0.0))
    p(f"ENTRY entry={e} launches={a[0]}/{b[0]} control1_ms={a[1] / SECTIONS:.3f} control2_ms={b[1] / SECTIONS:.3f} spread={abs(a[1] - b[1]) / max(a[1] + b[1], 1e-9) * 2:.3f}"
      f" registers={r.get('registers')} stack={r.get('stack')} spill_stores={r.get('spill_stores')} spill_loads={r.get('spill_loads')} "
      + " ".join(f"{k}={s.get(k, 0)}" for k in ["instructions"] + COUNTED))
p("## the copies")
for key, e in ENTRIES.items():
    for mech in MECHANISMS:
        name = f"field_copy_{mech}_{key}"
        if name not in copies and name not in cp:
            continue
        r, s = res.get(name, {}), sass.get(name, {})
        launches, ms = cp.get(name, (0, 0.0))
        a, b = c1.get(e, (0, 0.0))[1], c2.get(e, (0, 0.0))[1]
        mean = (a + b) / 2
        lp, bits = copies.get(name, (0, 0, 0))[1:]
        null = cp.get(f"field_copy_n_{key}", (0, 0.0))[1]
        p(f"COPY copy={name} entry={e} mechanism={mech} ({MECHANISMS[mech]}) launches={launches} copy_ms={ms / SECTIONS:.3f} control1_ms={a / SECTIONS:.3f} control2_ms={b / SECTIONS:.3f}"
          f" controls_spread={abs(a - b) / max(mean, 1e-9):.3f} ratio={ms / mean if mean else float('nan'):.3f} over_null_copy={ms / null if null else float('nan'):.3f} long_paths={lp} status_bits={bits}")
        p(f"  LOWERING registers={r.get('registers')} stack={r.get('stack')} spill_stores={r.get('spill_stores')} spill_loads={r.get('spill_loads')} "
          + " ".join(f"{k}={s.get(k, 0)}" for k in ["instructions"] + COUNTED))
        if name in hp:
            for h in sorted(hp[name]):
                kind, hl, hms = hp[name][h]
                ca = h1.get(e, {}).get(h, (kind, 0, 0.0))[2]
                cb = h2.get(e, {}).get(h, (kind, 0, 0.0))[2]
                hm = (ca + cb) / 2
                hn = hp.get(f"field_copy_n_{key}", {}).get(h, (kind, 0, 0.0))[2]
                p(f"  HEAD head={h} kind={kind} launches={hl} copy_ms={hms / SECTIONS:.3f} control1_ms={ca / SECTIONS:.3f} control2_ms={cb / SECTIONS:.3f} ratio={hms / hm if hm else float('nan'):.3f} over_null_copy={hms / hn if hn else float('nan'):.3f}")
        if name in checks:
            words, differ = checks[name]
            p(f"  CHECK the entry's words: compared={words} differing={differ}")
for name in ("field_copy_c_columns_count", "field_copy_c_columns_record", "field_copy_w_walk"):
    if name in cp:
        p(f"PREPARATION entry={name} launches={cp[name][0]} ms={cp[name][1] / SECTIONS:.3f} status_bits={copies.get(name, (0, 0, 0))[2]} (outside every copy's time)")
for line in open(f"{Q}/p59-hold.out"):
    if line.startswith(("MEASURE", "STATE_SHA", "GATE_REPRO", "# hold", "# hc", "# hcop")):
        p("HOLD " + line.strip().lstrip("# "))
k1, k2 = sum(v[1] for v in c1.values()), sum(v[1] for v in c2.values())
p(f"KERNELS control1_ms={k1 / SECTIONS:.1f} control2_ms={k2 / SECTIONS:.1f}")
print("\n".join(P))
