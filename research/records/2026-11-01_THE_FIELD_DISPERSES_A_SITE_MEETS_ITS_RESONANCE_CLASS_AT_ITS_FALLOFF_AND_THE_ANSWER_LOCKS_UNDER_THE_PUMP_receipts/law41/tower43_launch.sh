#!/bin/bash
# run41's tower arm, completed (the tower record's acceptance, §4). run41's tower arm stopped at 01:51 UTC after its lap 3
# (STATE.3 written, ms 1,085,095 at its withheld read) when the session that held it ended and took its process group with it;
# this launch is detached (setsid) so it outlives any session. The arm continues from that state under the same binary and law
# (FIELD_GROWTH_HELD=1, no FIELD_SCALE_FIRST: the state is already a tower; its lap count keys the walk, so the laps go on at 4).
# Same wall time as the field alone: the uninterrupted arm's lap 4 would begin at about 1,099 s, the continuation's lap 0 at
# about 27 s (its opening reads), so STOP_MS = 2,700,000 − 1,072,000 = 1,628,000, which lets laps 4–8 begin, as the
# uninterrupted arm would have (9 laps in all against the field alone's 12; its lap 9 would begin past its bound).
# Projection: laps 246–250 s, 270 s with their reads; 5 laps and the opening 1,380 s; bound 320 s; outer timeout 1,688 s. Then
# the write (three refinement passes on 6 held problems; the field alone's 365 s; STOP_MS 450,000, outer 470 s), then the
# expansion and volume reading across the training's states (expand42's list, run41_tower read at this arm's last state;
# each read's outer timeout 300 s; projected under 10 minutes). The whole under 50 minutes.
# RTX 4080 SUPER under .local/gpu.lock, 24 host threads.
set -u
ROOT=$ROOT; W=$ROOT/.local/wt/qgchgu-sampler; G=$ROOT/.local/wt/section-edge/.local/run/gsm8k
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; R=$W/.local/run; O=$R/2026-11-04-tower43; BIN=$R/2026-11-04-run41/field_pass
XBIN=$R/2026-11-04-expand42/field_pass; FROM=$R/2026-11-04-run41/tower/STATE.3
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
exec 9>$ROOT/.local/gpu.lock
flock -w 3600 9 || { echo "TOWER_RUN LOCK_BUSY"; exit 75; }
echo "# binary sha $(sha $BIN) from $(sha $FROM) started $(date -u +%H:%M:%S)"
T="$G/UNITS0 $(sha $G/UNITS0) $G/TRAIN.txt $(sha $G/TRAIN.txt) $G/HELD128.txt $(sha $G/HELD128.txt) $K $(sha $K)"
U="$G/UNITS0 $(sha $G/UNITS0)"
rm -rf $O/tower
env FIELD_GROWTH_HELD=1 $M tower timeout 1688 $BIN train complete-language train-field $T 32 4 8 2 32 4 16 60 8 320000 320000 1628000 $O/tower $FROM $(sha $FROM) > $O/tower.log 2>&1
grep -E '^FIELD_(SCALE|JOINT_NATS|LAPS_HELD|STOPPED)|^MEASURE|rror|panic' $O/tower.log | cut -c1-240
S=$(ls -t $O/tower/STATE.* 2>/dev/null | head -1)
cp $R/2026-11-04-run41/tower/CODEC $O/tower/CODEC 2>/dev/null
if [ -n "$S" ]; then
  $M tower_write timeout 470 $BIN train complete-language sample-field $S $(sha $S) $O/tower/CODEC $(sha $O/tower/CODEC) $U $G/HELD128.txt $(sha $G/HELD128.txt) 6 1229 3 450000 $O/tower_write > $O/tower_write.log 2>&1
  grep -E '^FIELD_SAMPLE |^MEASURE' $O/tower_write.log
  python3 -I $R/2026-11-03-refine36/words.py $G/TRAIN.txt $O/tower_write/SAMPLE.tsv
else
  echo "tower no state"
fi
echo "TOWER_RUN arm done $(date -u +%H:%M:%S)"
read_state() { # NAME STATE CODEC
  [ -f "$2" ] || { echo "$1 absent"; return; }
  echo "== $1"
  timeout 300 $XBIN train complete-language expansion-field "$2" $(sha "$2") "$3" $(sha "$3") $U $G/HELD128.txt $(sha $G/HELD128.txt) 8 2>&1 | grep -E '^FIELD_EXPANSION|rror|panic'
}
read_state run35_lap0 $R/2026-11-03-run35/train/STATE.0 $R/2026-11-03-run35/train/CODEC
read_state run35_lap4 $R/2026-11-03-run35/train/STATE.4 $R/2026-11-03-run35/train/CODEC
read_state run35_lap20 $R/2026-11-03-run35/train/STATE.20 $R/2026-11-03-run35/train/CODEC
read_state run36_lap9 $R/2026-11-03-run36/train/STATE.9 $R/2026-11-03-run36/train/CODEC
read_state run36_lap19 $R/2026-11-03-run36/train/STATE.19 $R/2026-11-03-run36/train/CODEC
read_state run37_lap17 $R/2026-11-03-run37/train/STATE.17 $R/2026-11-03-run37/train/CODEC
read_state run38_lap13 $R/2026-11-03-run38/train/STATE.13 $R/2026-11-03-run38/train/CODEC
read_state run41_alone $R/2026-11-04-run41/alone/STATE.11 $R/2026-11-04-run41/alone/CODEC
read_state run43_tower "${S:-none}" $O/tower/CODEC
echo "TOWER_RUN exit $(date -u +%H:%M:%S)"
