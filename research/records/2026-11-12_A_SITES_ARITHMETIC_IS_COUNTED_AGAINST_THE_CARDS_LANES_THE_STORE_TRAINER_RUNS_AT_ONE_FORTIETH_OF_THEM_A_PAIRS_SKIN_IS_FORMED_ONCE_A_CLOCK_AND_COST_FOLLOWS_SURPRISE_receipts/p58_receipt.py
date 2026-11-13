"""P58 step 6's receipt from its run logs (the counted read, the step's run at 8ffb8ecb5, the head's run at f2518976f). Numbers only.
Argument: the run directory."""
import re
import sys

Q = sys.argv[1]
SECTIONS = 100


def read(name):
    with open(f"{Q}/{name}") as f:
        return [line.rstrip("\n") for line in f]


def kv(line):
    return dict(w.split("=", 1) for w in line.split()[1:] if "=" in w)


def grab(lines, prefix):
    return [l for l in lines if l.startswith(prefix)]


def per(ms):
    return float(ms) / SECTIONS


count, tpc, tps, out, outb = read("count.log"), read("tpc6.log"), read("tps6.log"), read("p58-step6.out"), read("p58-step6b.out")
P = []
p = P.append
p("# P58 step 6 of the engine, 2026-11-13 UTC (claude/engine-host 8ffb8ecb5, head f2518976f, from main 4d0870d1c): the pool serves a plain take")
p("# from a longer kept buffer, eleven takes spared their zeroing, the training path's faces gathered at their classes, the deposit's host parts")
p("# read. Sections 2,001 to 2,100 of the store trainer's pass from run 2's STATE.1900 (sha256 cda6ac8a1129f147) unless a line says otherwise.")
p("# Milliseconds are a section's (a read's total over its 100 sections), profiled reads synchronize the card around every launch, copy and take.")
p("# Numbers only.")
p("## the builds")
for b in ("bin6", "bin6b", "bin_main6", "bin_readc"):
    p(read(f"{b}/BUILD")[0])
p("count read: claude/engine-host b43dba8bd (main 4d0870d1c with the P56 readings and step 6's spared e) with the pool's counters and the coarse deposit marks")

p("## item 1: the counted read of the pool (FIELD_PROFILE, 100 sections, its own hold)")
p(" ".join(l for l in grab(count, "MEASURE")))
names = {2434: "dz (the face covector's block, i128)", 3025: "sk (the clock's skins, i128)"}
for l in grab(count, "FIELD_PROFILE_POOL"):
    k = kv(l)
    line = int(k["line"])
    if line in names:
        miss = int(k["misses"])
        freed = int(k["freed_octets"])
        p(f"COUNT_POOL take={names[line]} class_octets={k['class_octets']} hits={k['hits']} misses={miss} frees={k['frees']} freed_octets={freed}"
          f" freed_octets_a_miss={freed // max(miss, 1)}")
tot = {"hits": 0, "misses": 0, "frees": 0, "freed_octets": 0}
for l in grab(count, "FIELD_PROFILE_POOL"):
    k = kv(l)
    for key in tot:
        tot[key] += int(k[key])
p("COUNT_POOL all_takes " + " ".join(f"{a}={b}" for a, b in tot.items()))
for l in grab(count, "FIELD_PROFILE_SITE kind=take"):
    k = kv(l)
    if int(k["line"]) in names:
        p(f"COUNT_TAKE take={names[int(k['line'])].split()[0]} calls={k['calls']} ms_a_section={per(k['ms']):.3f}")
p("COUNT_READING: the two takes alternate within each batch and are never live together; each miss frees the other's kept buffer (the freed octets")
p("  a miss equal the other's class), the live set, the other's kept buffer and the new one passing the budget, and the other's buffer more than twice")
p("  the class the pool serves from. Both are taken in every section, so freeing what the last section did not take first, or holding a section's")
p("  set, leaves the budget unable to hold both beside the live set. Chosen: a plain take that the budget would pay for with a free is served by the")
p("  least kept buffer of its type at least its class (live plus kept unchanged, under the budget); a zeroed take keeps the twice-class bound.")
p("## item 1 in the step's profiled read (tps6) against the profiled control (tpc6, main's crates with the P56 readings)")
steps = {2496: "dz", 3101: "sk", 2360: "picked"}
for l in grab(tps, "FIELD_PROFILE_POOL"):
    k = kv(l)
    if int(k["line"]) in steps:
        p(f"STEP_POOL take={steps[int(k['line'])]} class_octets={k['class_octets']} hits={k['hits']} misses={k['misses']} frees={k['frees']} served_longer={k['served_longer']}")
tot = {"hits": 0, "misses": 0, "frees": 0, "freed_octets": 0, "served_longer": 0}
for l in grab(tps, "FIELD_PROFILE_POOL"):
    k = kv(l)
    for key in tot:
        tot[key] += int(k[key])
p("STEP_POOL all_takes " + " ".join(f"{a}={b}" for a, b in tot.items()))
ctl_takes = {3002: "sk", 2411: "dz"}
step_takes = {3101: "sk", 2496: "dz"}
two = {"control": 0.0, "step": 0.0}
for side, lines, m in (("control", tpc, ctl_takes), ("step", tps, step_takes)):
    for l in grab(lines, "FIELD_PROFILE_SITE kind=take"):
        k = kv(l)
        if int(k["line"]) in m:
            two[side] += per(k["ms"])
            p(f"TAKE side={side} take={m[int(k['line'])]} calls={k['calls']} ms_a_section={per(k['ms']):.3f}")
p(f"TAKES_TWO control_ms_a_section={two['control']:.3f} step_ms_a_section={two['step']:.3f}")
for side, lines in (("control", tpc), ("step", tps)):
    k = kv(grab(lines, "FIELD_PROFILE_SPLIT")[0])
    p(f"SPLIT side={side} kernels_ms_a_section={per(k['kernels_ms']):.2f} copies={k['copies']} copies_ms_a_section={per(k['copies_ms']):.2f}"
      f" takes={k['allocations']} takes_ms_a_section={per(k['allocations_ms']):.2f}")

p("## item 2: the spared zeroings, each with its proof (the source's own comment at the take states it)")
spared = [
    ("e (the pairs' scores and shares)", 1499, 1557, "field_contact exposure writes the score at every support entry of each computed row and head; the contact, the rows, the pace and the rulers read only those entries; the columns read e at the pairs whose ds they read, which the rows write only at support entries; the dense readers (echo trips, held rows, row currents, a landmark's kept rows) run only under logits or kept rows, which zero it"),
    ("the face's scale", 2199, 2264, "field_chart writes every lane's scale of an open site; its one reader, field_ratio_adjoint in the reverse, reads it at open sites alone"),
    ("the face's totals", 2202, 2267, "field_face writes an open site's total; field_face_covector, the host's faces at the batch's end and a port's places read it at open sites alone"),
    ("the face's lift", 2206, 2272, "field_affine (no add) writes every output of an open site; field_tied_face and field_tied_back_e read it at open sites alone"),
    ("the blank's dr", 2431, 2520, "field_transposed (no accumulation) writes every column of a site the clock read (blank_read); its one reader, field_ratio_adjoint on the same sites, reads it only there"),
    ("the blank's back", 2433, 2522, "field_ratio_adjoint with no base writes every word: zero at a skipped site, every lane's coordinates at an open one, before field_blank_dx reads it"),
    ("the blank clock's read", 2448, 2544, "field_chart writes it at blank_read sites; field_affine and field_ratio_adjoint read it there, field_blank_lift_read only where dy is nonzero (written zero elsewhere by field_blank_dy); zeroed while the clocks are read at named sites"),
    ("the blank clock's scale", 2449, 2545, "field_chart writes every lane's scale at blank_read sites; field_ratio_adjoint (blank_back) reads it there alone; zeroed while the clocks are read at named sites"),
    ("the blank clock's lift", 2456, 2552, "field_affine writes it at blank_read sites; field_tied_face reads it there, field_blank_bias_enc only where dz is nonzero (written zero elsewhere by field_blank_dz); zeroed while the clocks are read at named sites"),
    ("the blank clock's totals", 2465, 2561, "field_face writes them at blank_read sites; field_blank_rates and field_blank_dz read them there, field_pace_c_back where blank_read[t]; zeroed while the clocks are read at named sites, whose reading fetches a silent site's face the clock may not have read"),
    ("dkappa at each tick's clock", 2901, 2999, "field_pace_kappa_back writes every (paced head, site) word, each region from its last site to its first, before field_pace_c_back and field_blank_dz read it"),
    ("dkappa at the pass's clock", 2929, 3028, "field_pace_kappa_back writes every word before field_pace_c_back reads it"),
]
zc = {int(kv(l)["line"]): kv(l) for l in grab(tpc, "FIELD_PROFILE_ZEROED")}
zs = {int(kv(l)["line"]): kv(l) for l in grab(tps, "FIELD_PROFILE_ZEROED")}
sum_spared = 0.0
for name, cl, sl, proof in spared:
    c = zc.get(cl)
    ms = per(c["ms"]) if c else 0.0
    sum_spared += ms
    octets = int(c["octets"]) // SECTIONS if c else 0
    p(f"SPARED take={name} control_line={cl} step_line={sl} control_zeroing_ms_a_section={ms:.3f} control_zeroed_octets_a_section={octets} step_zeroed={'yes' if sl in zs else 'no'}")
    p(f"  PROOF {proof}")
ctl_total = sum(per(v["ms"]) for v in zc.values())
stp_total = sum(per(v["ms"]) for v in zs.values())
p(f"ZEROINGS control_ms_a_section={ctl_total:.3f} control_takes={len(zc)} step_ms_a_section={stp_total:.3f} step_takes={len(zs)} spared_ms_a_section={ctl_total - stp_total:.3f}"
  f" the_spared_takes_own_control_ms={sum_spared:.3f}")
p(f"ZEROED_OCTETS control_a_section={sum(int(v['octets']) for v in zc.values()) // SECTIONS} step_a_section={sum(int(v['octets']) for v in zs.values()) // SECTIONS}")

p("## item 3: the faces at the pass's end")
p("TRAINING_PATH_READS: the learner's comparison (compared) reads each open site's mass at its class and its total before a port; with no held step")
p("  and no port it asks for those alone (read_and_return_at_class); field_face_at_class gathers m_c on the card; the fetch is 8 octets a site of")
p("  m_c and 16 of the total, where the whole faces are 8 octets a site and class (alphabet 244) beside the totals. Whole faces stay for read_faces,")
p("  the held reads, the logits, the kept rows and every port.")
for side, lines, m in (("control", tpc, {2287: "masses_whole", 2288: "totals"}), ("step", tps, {2363: "picked_m_c", 2364: "totals"})):
    for l in grab(lines, "FIELD_PROFILE_SITE kind=copy"):
        k = kv(l)
        if int(k["line"]) in m:
            p(f"FETCH side={side} words={m[int(k['line'])]} calls={k['calls']} ms_a_section={per(k['ms']):.3f}")
for side, lines in (("control", tpc), ("step", tps)):
    for l in grab(lines, "FIELD_PHASE name=batch_drop_and_collect"):
        k = kv(l)
        p(f"COLLECT side={side} phase=batch_drop_and_collect ms_a_section={per(k['ms']):.2f} card_ms_a_section={per(k['card_ms']):.2f} host_ms_a_section={per(k['host_ms']):.2f}")

p("## item 4: the deposit on the host (a reading; the step's profiled read, fine marks), ms a section")
k = kv(grab(tps, "STORE_DEPOSIT_PARTS")[0])
host_parts = {a[:-3]: per(b) for a, b in k.items() if a.endswith("_ms")}
for a, b in host_parts.items():
    p(f"DEPOSIT part={a} ms_a_section={b:.3f}")
dep = sum(b for a, b in host_parts.items() if a != "read_and_return")
p(f"DEPOSIT host_total_ms_a_section={dep:.3f} (every part but the realization's read and return)")
arith = sum(host_parts[a] for a in ("external_step", "moments", "step", "covector_grains", "stepped", "entry_rates"))
prices = sum(host_parts[a] for a in ("transfer_price", "external_price", "step_price", "parts_price"))
copies = sum(host_parts[a] for a in ("covector_clone", "reading_parts"))
p(f"DEPOSIT_CLASSES entries_arithmetic_ms={arith:.3f} (the rates, the external step and the step, the covector's grains, the moments, the stepped constitution with its clone)"
  f" prices_ms={prices:.3f} (four first-order prices) compared_and_code_ms={host_parts['compared_and_code']:.3f} (over the open sites) bare_copies_ms={copies:.3f} (the covector's clone, the parts' fill)")
p("DEPOSIT_LAYOUT_PASSES the constitution's 117,478 entries: 10 passes that compute (transfer price, external step, external price, grains, moments, step,")
p("  step price, parts fill, parts price, stepped update) and 6 whole-layout copies or allocations a section: the covector's clone 1,879,648 octets,")
p("  the entries' rates 469,912, the external step 1,879,648, the step 1,879,648, the parts 117,478, the stepped constitution's material 469,912")
p("  (6,696,246 octets a section in all)")
k = kv(grab(tps, "STORE_HOST")[0])
p(f"TRAINER side=step mean_of_states_ms_a_section={per(k['mean_ms']):.3f} cut_ms_a_section={per(k['cut_ms']):.3f} saves_ms_a_section={per(k['saves_ms']):.3f}")
for l in grab(tps, "FIELD_PHASE name=material_upload") + grab(tps, "FIELD_PHASE name=covector_fetch"):
    k = kv(l)
    p(f"REALIZATION side=step phase={k['name']} ms_a_section={per(k['ms']):.3f} card_ms_a_section={per(k['card_ms']):.3f} host_ms_a_section={per(k['host_ms']):.3f}")
k = kv(grab(count, "STORE_DEPOSIT_PARTS")[0])
p("COUNT_DEPOSIT (coarse marks, before item 3) " + " ".join(f"{a}={per(b):.3f}" for a, b in k.items() if a.endswith("_ms")))

p("## gates at 8ffb8ecb5 (gate 1, then the GPU suite alone on the card)")
for l in out:
    if re.match(r"^(GATE_EXIT|SUITE_BUILD_EXIT|SUITE_EXIT|SUITE_TESTS_OK|MEASURE lap=step6_)|^gate guard-lints|^test result", l):
        p(l)
p("GATE1_NOTE guard-lints failed at 8ffb8ecb5 on three float prints in store_train's readings (P56's and this step's); f2518976f prints them in integers")
p("## gates at the head f2518976f")
for l in outb:
    if re.match(r"^(GATE_EXIT|SUITE_BUILD_EXIT|SUITE_EXIT|SUITE_TESTS_OK|MEASURE lap=step6b_)|^gate (check|guard|reproduction)|FAILED|^test result", l):
        p(l)
p("## the reproduction (run 1's STATE.101, 600 sections; projection 257 s, stop 327,600 ms, outer 390 s)")
for l in read("repro6.log"):
    if l.startswith("MEASURE"):
        p("repro6 " + l)
for l in out:
    if l.startswith(("GATE_REPRO", "GATE_SAVE", "GATE_BYTES")):
        p("8ffb8ecb5 " + l)
for l in read("repro6b.log"):
    if l.startswith("MEASURE"):
        p("repro6b " + l)
for l in outb:
    if l.startswith(("GATE_REPRO", "GATE_SAVE", "GATE_BYTES")):
        p("f2518976f " + l)
p("## the hold: control, step 6, control, profiled control, profiled step (each 100 sections; projections 43 s and 50 s, stops 54,600 and 72,618 ms)")
for n in ("tc61", "ts6", "tc62", "tpc6", "tps6"):
    for l in read(f"{n}.log"):
        if l.startswith("MEASURE"):
            p(l)
for l in out:
    if l.startswith(("TIMING", "STATE_SHA")) or l.startswith("# timing"):
        p(l.replace("# ", "HOLD "))
p("## the head's profiled read (f2518976f, integer prints), its deposit parts and states")
for l in read("tps6b.log"):
    if l.startswith(("STORE_DEPOSIT_PARTS", "MEASURE")):
        p("tps6b " + l)
for l in outb:
    if l.startswith("STATE_SHA"):
        p(l)
p("## G134, fixed before the read, scored")
collect = {}
for side, lines in (("control", tpc), ("step", tps)):
    collect[side] = per(kv(grab(lines, "FIELD_PHASE name=batch_drop_and_collect")[0])["ms"])
ratio = float(kv(next(l for l in out if l.startswith("TIMING controls_spread_ms")))["step_over_controls"])


def score(name, guess, lo, hi, read, unit=""):
    inside = lo <= read <= hi
    p(f"G134 part={name} guess={guess}{unit} range={lo}..{hi}{unit} read={read:.3f}{unit} {'inside' if inside else ('under' if read < lo else 'over')}")


score("a_two_takes", 1.0, 0.1, 2.0, two["step"], "_ms")
p(f"  from control {two['control']:.3f} ms (the guess's premise 10.9)")
score("b_spared_zeroings", 4.5, 3.4, 6.0, ctl_total - stp_total, "_ms")
p(f"  of control {ctl_total:.3f} ms (the premise 6.6)")
score("c_faces_fetch_and_collection", 2.0, 0.5, 4.0, collect["step"], "_ms")
p(f"  from control {collect['control']:.3f} ms (the premise 12.4)")
score("d_deposit_arithmetic", 2.0, 0.3, 3.0, arith, "_ms")
p(f"  of the deposit's host total {dep:.3f} ms; with the prices and the code {arith + prices + host_parts['compared_and_code']:.3f}")
score("d_whole_layout_copies_share", 0.60, 0.35, 0.85, copies / dep)
p("  the allocations inside the external step's and the step's passes are counted in those passes (their pages are first written there)")
score("e_unprofiled_step_over_controls", 0.935, 0.90, 0.96, ratio)
p(f"G134_RULES (d) as guessed (copies 0.60 of it): {'met' if 0.35 <= copies / dep <= 0.85 else 'not met'}, the bare copies read {copies / dep:.3f} of the deposit;"
  f" (d) arithmetic over 6 ms: {'met' if arith > 6 else 'not met'} at the entries' arithmetic alone ({arith:.3f} ms, at the rule's line),"
  f" {arith + prices + host_parts['compared_and_code']:.3f} with the prices and the code; (e) over 0.96: {'met' if ratio > 0.96 else 'not met'} ({ratio:.3f}).")
print("\n".join(P))
