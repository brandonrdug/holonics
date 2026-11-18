#!/usr/bin/env -S python3 -I
"""Controls of lap_check.py (host text only; no script is run and no state is read).

The ruler's null is held to planted omissions: a lap script that names every read of the procedure prints nothing, and the
same script with one read taken out prints that read's rule and no other. A script that trains nothing prints nothing.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lap_check  # noqa: E402

WHOLE = r'''#!/bin/bash
# The level's arm (G-1118-16): lap L14 beside the line's own P14, read at its lap mean and written on both panels.
set -u
LOCK=$ROOT/.local/gpu.lock
train() { # train NAME SOURCE SECTIONS DEADLINE
  ( flock -w 14400 9 || exit 75
    card timeout $4 $BIN train complete-language train-store $U0 $S prefix $K $C2 $H $3 1000 2400000 $D/arm_$1 $2 \
      > $D/arm_$1.log 2>&1 ) 9>$LOCK
}
cav() { card timeout 1800 $BIN train complete-language read-cavity $U0 $S $K $C 20000 $2 $D/out_$1 known > $D/cav_$1.log; }
loud() { card timeout 1800 $BIN train complete-language read-loudness $U0 $S $K $C $2 $D/loud_$1 > $D/loud_$1.log; }
panels() { $BIN host complete-language write-next $U0 $K $C $N/panel.tsv 64 $D/n_$1 $2 48; }
train L14 $D/OPEN.L14 3000 1272
mean_s=$(ls $D/arm_L14/MEAN.* | tail -n 1)
cav mean_L14 $mean_s; loud mean_L14 $mean_s; panels L14_mean $mean_s
'''

# Each planted omission: (what is taken out, what replaces it, the one rule the ruler must then print).
PLANTED = [
    ("(G-1118-16)", "", 1),
    ("card timeout $4 $BIN train", "card $BIN train", 4),
    ("flock -w 14400 9 || exit 75", "true", 4),
    ("train complete-language read-cavity", "train complete-language read-held", 5),
    ("MEAN.*", "STATE.*", 5),
    ("write-next", "write-nothing", 6),
    ("read-loudness", "read-nothing", 7),
]

READS_ONLY = r'''#!/bin/bash
# A read of a saved state: nothing trains here.
card timeout 1800 $BIN train complete-language read-cavity $U0 $S $K $C 20000 $ST $D/out known
'''

# Words that are no guess and no read: a dataset's name and commands that stand only in a comment. A hash sign inside quotes
# opens no comment, so the training command after it is still read.
DECOYS = r'''#!/bin/bash
# GSM8K sections on the GPU. read-loudness is not called below; write-next, read-cavity MEAN, flock gpu.lock and timeout neither.
echo "lap # one" && $BIN train complete-language train-store $U0 $S
'''


def main():
    assert lap_check.notes(WHOLE) == [], lap_check.notes(WHOLE)
    for old, new, rule in PLANTED:
        assert old in WHOLE, old
        got = [r for r, _ in lap_check.notes(WHOLE.replace(old, new))]
        assert got == [rule], (old, got)
    assert lap_check.notes(READS_ONLY) == []
    decoys = sorted(r for r, _ in lap_check.notes(DECOYS))
    assert decoys == [1, 4, 4, 5, 6, 7], decoys
    print(f"lap check: the whole script prints nothing, {len(PLANTED)} planted omissions are each found alone, the decoys are not read")


if __name__ == "__main__":
    main()
