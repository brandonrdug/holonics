"""P50 step 0a, a ruler: the profile by head of one profiled read (field_pass's FIELD_PROFILE_HEAD and FIELD_PROFILE_PAIRS lines).

For each entry launched a head at a time: launches, ms and the pairs the head's forward contact met, by head and kind; the paced heads'
share of each entry's time; and G116 (d), the two paced heads' share of field_contact_rows' time. Numbers only."""
import sys
from collections import defaultdict

log = sys.argv[1]
sections = int(sys.argv[2]) if len(sys.argv) > 2 else 100
heads, pairs, entries = {}, {}, defaultdict(dict)
for line in open(log):
    if not line.startswith(("FIELD_PROFILE_HEAD ", "FIELD_PROFILE_PAIRS ")):
        continue
    kv = dict(w.split("=", 1) for w in line.split()[1:])
    h = int(kv["head"])
    heads[h] = kv["kind"]
    if line.startswith("FIELD_PROFILE_PAIRS "):
        pairs[h] = int(kv["pairs"])
    else:
        entries[kv["entry"]][h] = (int(kv["launches"]), int(kv["us"]))
total_pairs = sum(pairs.values())
print(f"sections={sections} heads={len(heads)} kinds={','.join(f'{h}:{heads[h]}' for h in sorted(heads))}")
for h in sorted(pairs):
    print(f"pairs head={h} kind={heads[h]} pairs={pairs[h]} a_section={pairs[h] / sections:.0f} share={pairs[h] / max(total_pairs, 1):.3f}")
for e in sorted(entries, key=lambda e: -sum(v[1] for v in entries[e].values())):
    per = entries[e]
    tot = sum(v[1] for v in per.values())
    paced = sum(v[1] for h, v in per.items() if heads.get(h) == "paced")
    for h in sorted(per):
        launches, us = per[h]
        print(f"{e:24s} head={h} kind={heads[h]:5s} launches={launches:5d} ms={us / 1000:9.1f} ms_a_section={us / 1000 / sections:7.2f} pairs={pairs.get(h, 0)} ns_a_pair={us * 1000 / max(pairs.get(h, 1), 1):.3f}")
    print(f"{e:24s} all ms={tot / 1000:9.1f} ms_a_section={tot / 1000 / sections:7.2f} paced_share={paced / max(tot, 1):.3f}")
rows = entries.get("field_contact_rows", {})
tot = sum(v[1] for v in rows.values())
paced = sum(v[1] for h, v in rows.items() if heads.get(h) == "paced")
share = paced / max(tot, 1)
print(f"G116_d paced_share_of_field_contact_rows={share:.3f} fixed=0.78 range=0.70..0.86 {'IN' if 0.70 <= share <= 0.86 else 'OUT'} stop_rule_under_0.65={'STOP' if share < 0.65 else 'held'}")
