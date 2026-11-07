#!/bin/bash
# lap 5 (theory, November 7, 05:33: "If held exact code falls by more than twice its paired standard error, LAP 5 follows on the same law at once"), lap 4's law (theory, November 7, 04:05 and 05:20: route (b), its negative one exact kernel step from the truth; GO inside the hour
# after a minute's development read): one lap of contrast-field on the card from lap 4's STATE.0, the
# line's training passage (24,685 problems, 1,543 sections of 16); each state one Metropolis-Hastings block step from the
# truth (answer places 11 apart, keyed offset), the deposit (1/T) min(1, A)[dG/dtheta(truth) - dG/dtheta(proposal)]; the
# exact conditional at 64 held places before and after. devk (60 s, 153 sections): acceptance 0.959 (sd 0.104), 0.318 s a
# section -> 8.2 min a lap, 9.5 min at the mean plus two standard errors; with the two exact reads (11 s each) the deadline
# is 600 s (STOP_MS; the lap stops after the section past it, writing STATE.stopped, reported incomplete); outer timeout
# 700 s. Card: RTX 4080 SUPER under .local/gpu.lock, peak store about 8.1 GB; host part one process, 8 threads, about 0.4 GB.
set -u
export RAYON_NUM_THREADS=8
ROOT=/home/b/Workspaces/holonics; R=$ROOT/.local/wt/qgchgu-sampler/.local/run; O=$R/2026-11-07-lap4; BIN=$O/field_pass; A=$R/2026-11-07-energy131
P=$ROOT/.local/data/python-codes-25k/passage; F84=$R/2026-11-05-code84; U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
CODEC=$F84/dev/CODEC; U="$U0 $(sha $U0)"; S=$O/lap/STATE.0
exec 9>$ROOT/.local/gpu.lock; flock -w 600 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
echo "# lock taken $(date -u +%H:%M:%S), binary $(sha $BIN | cut -c1-16)"
D=$O/lap5; rm -rf $D
$M lap timeout 700 $BIN train complete-language contrast-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/TRAIN.txt $(sha $P/TRAIN.txt) $P/HELD128.txt $(sha $P/HELD128.txt) 16 1 64 600000 600000 $D > $D.log 2>&1
grep -E '^FIELD_(KERNEL_ACCEPT|STOPPED|CARD|EXACT_READ)|^MEASURE|rror|panic' $D.log | cut -c1-300
[ -f $D/EXACT.tsv ] && python3 -I $O/exact.py $D/EXACT.tsv
[ -f $D/STATE.0 ] && echo "STATE.0 $(sha $D/STATE.0)"
echo "MAIN exit $(date -u +%H:%M:%S)"
