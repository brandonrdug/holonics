#!/bin/bash
# The takeover (§16.44): blank60 (the operand form) stops after its segment 2 (its control at 90 card-minutes); once the
# exact return's parity has passed, the old law reads blank60 seg1's last state tick by tick (the unified-theory thread's
# reading (2) on STATE.8), the exact return's cost is read (150 s of train-field from blank60's opening state at 2^-12),
# and exact63's chain launches. Detached.
set -u
ROOT=/home/b/Workspaces/holonics; W=$ROOT/.local/wt/qgchgu-sampler; R=$W/.local/run; O=$R/2026-11-05-exact63; P=$R/2026-11-04-blank60
G=$ROOT/.local/wt/section-edge/.local/run/gsm8k; K=$ROOT/.local/wt/field-card/.local/run/KEYS8; BIN=$O/field_pass
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
timeout 3600 bash -c "until grep -q '^SEGMENT 2 done' $P/launch.out; do sleep 5; done" || { echo "TAKEOVER blank60 reached no boundary"; exit 1; }
kill -TERM -$(cat $P/launch.pid) 2>/dev/null; pkill -TERM -f "$P/field_pass" 2>/dev/null; sleep 3
echo "# blank60 stopped $(date -u +%H:%M:%S)"
timeout 3600 bash -c "until grep -q 'PARITY exit' $R/2026-11-05-exact62/parity.out; do sleep 5; done"
grep -E 'FIELD_PARITY_DONE' $R/2026-11-05-exact62/parity.out
grep -q 'learners_unequal=0 releases=1 releases_unequal=0' $R/2026-11-05-exact62/parity.out && ! grep -q 'learner_equal=false\|near_equal=false\|rows_equal=false\|currents_equal=false\|shares_equal=false' $R/2026-11-05-exact62/parity.out || { echo "TAKEOVER parity failed"; exit 1; }
bash $R/2026-11-05-accept61/trio.sh oldat8 $R/2026-11-05-accept61/field_pass_old $P/seg1/STATE.8
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "TAKEOVER LOCK_BUSY"; exit 75; }
FROM=$R/2026-11-04-main52/seg3/STATE.10
T="$G/UNITS0 $(sha $G/UNITS0) $G/TRAIN.txt $(sha $G/TRAIN.txt) $G/HELD128.txt $(sha $G/HELD128.txt) $K $(sha $K)"
rm -rf $O/dev
FIELD_GROWTH_HELD=1 FIELD_STEP_TRANSFER=1 FIELD_RATE_BITS=12 $M dev timeout 240 $BIN train complete-language train-field $T 32 4 8 2 32 4 16 60 8 300000 300000 150000 $O/dev $FROM $(sha $FROM) > $O/dev.log 2>&1
exec 9>&-
grep -E '^FIELD_SECTION' $O/dev.log | sed -E 's/.* ms=([0-9]+)$/\1/' | awk '{n++; s+=$1; if ($1>m) m=$1} END {printf "dev sections %d mean_ms %.0f max_ms %d lap_projection_s %.0f\n", n, s/n, m, 413*s/n/1000}'
grep -E '^MEASURE|rror|panic' $O/dev.log
echo "# exact63 launch $(date -u +%H:%M:%S)"
setsid nohup bash $O/launch.sh > $O/launch.out 2>&1 < /dev/null & echo $! > $O/launch.pid
echo "TAKEOVER exit $(date -u +%H:%M:%S)"
