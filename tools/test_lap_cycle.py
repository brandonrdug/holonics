#!/usr/bin/env -S python3 -I
"""Controls of lap_cycle.py on logs written here (no run's log is read).

  train     a train-store log is read by its STORE_PASS line, never by a section's own ms;
  held      a held read's rows are summed over its slices, and its time is its CAVITY_DONE line's;
  host      a log that opened no card is listed and left out of the card's time;
  cycle     the card's time is the card logs' sum, the training's share and the reads' time over it follow;
  open      a log with no closing line reads `-`, is named, and adds nothing to the sums.
"""
import os
import sys
import tempfile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lap_cycle as lc

passed = 0


def check(cond, what):
    global passed
    if not cond:
        sys.exit(f"FAILED {what}")
    passed += 1


TRAIN = """FIELD_COMMAND train-store UNITS 00 STORE 11
FIELD_CARD_OPEN card=drawn free=1 total=2 batch_budget=1
STORE_SECTION n=0 regions=4 sites=9 regions_ms=3 deposit_ms=742 ms=751
STORE_SECTION n=1 regions=4 sites=9 regions_ms=2 deposit_ms=643 ms=650
STORE_PASS role=prefix sections=2 stretches_read=7 ended=false ms=2000
"""
HELD = """FIELD_COMMAND read-cavity UNITS 00 STORE 11
FIELD_CARD_OPEN card=drawn free=1 total=2 batch_budget=1
CAVITY_LAW role=held places=20 ms=295
CAVITY_FRONTIER slice=code places=20 batches=2 ms=300
CAVITY_KNOWN slice=code places=20 batches=2 ms=120
CAVITY_STRAND slice=code places=20 batches=1 ms=2
CAVITY_SLICE slice=code stretches=1 places=20 host_c0_ms=0 card_cK_ms=800 card_batches=2 host_opening_ms=3 whole_masks=1 whole_places=4 whole_ms=8 copy_places=4 later_places=16 host_copy_ms=400 elapsed_ms=1633
CAVITY_FRONTIER slice=web places=20 batches=2 ms=310
CAVITY_SLICE slice=web stretches=1 places=20 host_c0_ms=0 card_cK_ms=700 card_batches=2 host_opening_ms=2 whole_masks=1 whole_places=4 whole_ms=7 copy_places=0 later_places=20 host_copy_ms=0 elapsed_ms=1019
CAVITY_DONE ms=3000
"""
HOST = """FIELD_COMMAND write-next UNITS 00 KEYS 22
NEXT_WRITE_DONE rows=4 run=8 window=- ms=900
"""
OPEN = """FIELD_COMMAND read-loudness UNITS 00 STORE 11
FIELD_CARD_OPEN card=drawn free=1 total=2 batch_budget=1
LOUDNESS_SLICE slice=code places=20 card_ms=600
"""

with tempfile.TemporaryDirectory() as d:
    paths = {}
    for name, text in (("train.log", TRAIN), ("held.log", HELD), ("host.log", HOST), ("open.log", OPEN)):
        paths[name] = os.path.join(d, name)
        with open(paths[name], "w") as f:
            f.write(text)
    train, held, host, unread = (lc.read(paths[n]) for n in ("train.log", "held.log", "host.log", "open.log"))

    check(train["word"] == "train-store" and train["card"] and train["ms"] == 2000, "train: the pass's own line")
    check(train["rows"] == {}, "train: no rows")

    check(held["ms"] == 3000 and held["card"], "held: the read's own line")
    check(held["rows"] == {"P": 1500, "W": 15, "F": 610, "K": 120, "S": 2, "copies": 400, "opening": 5}, "held: rows summed by slice")

    check(host["word"] == "write-next" and not host["card"] and host["ms"] == 900, "host: listed")

    c = lc.cycle([train, held, host, unread])
    check(c["card_ms"] == 5000 and c["train_ms"] == 2000 and c["reads_ms"] == 3000, "cycle: the card's sums")
    check(c["host_ms"] == 900, "cycle: the host's time apart")
    check(c["incomplete"] == ["open.log"], "open: named")

    out = lc.lines([train, held, host, unread])
    check(out[0] == "LAP_CYCLE log=train.log word=train-store surface=card ms=2000", "lines: a training log")
    check(out[1].endswith("rows: P=1500 W=15 F=610 K=120 S=2 copies=400 opening=5"), "lines: a held read's rows")
    check("surface=host ms=900" in out[2], "lines: a host log")
    check("word=read-loudness surface=card ms=-" in out[3], "lines: an open log")
    check("train_share=0.400 reads_over_train=1.50" in out[4] and "card_minutes=0.1" in out[4], "lines: the cycle")
    check(out[5] == "LAP_CYCLE_INCOMPLETE open.log", "lines: the open log named")

    only = lc.lines([host])
    check("train_share=- reads_over_train=-" in only[1], "lines: no card log divides nothing")

print(f"lap_cycle controls: {passed} passed")
