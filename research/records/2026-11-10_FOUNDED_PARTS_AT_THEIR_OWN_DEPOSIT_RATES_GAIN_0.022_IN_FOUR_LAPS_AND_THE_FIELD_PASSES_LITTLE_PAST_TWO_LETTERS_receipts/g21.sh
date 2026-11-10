#!/bin/bash
# g21.sh STATE TAG [parts]: the significant digits of the field's numbers (theory's G21, November 10 21:34): STATE copied five times with every
# stored material number x != 0 rounded to nearest to its leading s significant binary digits at its own scale (round_state.py: sign
# kept, zero stays zero), s = 8, 4, 2, 1 and the unrounded copy (the parity check), the saved state untouched; the held joint
# (FIELD_JOINT_NATS own, as a lap reads it at lap -1: no bare clock, long114's other laws) read on each copy with the v14 line's reads binary
# (field_pass.joint, BUILD.joint, joint-field: read only). With `parts`, four more copies at s = 4 with only the faces' families, the contacts',
# the lanes' or the heads' rounded. Each read is a card stage of its own (flock -w 14400 on .local/gpu.lock). Output under $N/g21/TAG/.
# Printed: own nats a place per copy and its change from the unrounded copy; theory's guess +0.0005, +0.006, +0.06, +0.5 for s = 8, 4, 2, 1
# (s = 4 under 0.01: the digits past the fourth are baggage; 0.03 or more: they carry law). Projection: a measured held read, 2.4 s wall on ct8 (nine of them took 22 s); 10 s a read, deadline 12.5 s.
set -u
ROOT=${HOLONICS_ROOT}; W=$ROOT/.local/wt/qgchgu-sampler; P=$ROOT/.local/data/python-codes-25k/passage
K=$ROOT/.local/wt/field-card/.local/run/KEYS8; R=$W/.local/run; N=$R/2026-11-10-contacts; BIN=$N/field_pass.joint; F84=$R/2026-11-05-code84
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
U="$U0 $(sha $U0)"; CODEC=$F84/dev/CODEC
[ $# -ge 2 ] || { echo "g21.sh STATE TAG [parts]"; exit 2; }
S=$1; TAG=$2; WITH=${3:-}; O=$N/g21/$TAG
[ -x $BIN ] || { echo "MAIN no binary at $BIN"; exit 1; }
mkdir -p $O
PROJ=10; DEAD=$(( PROJ * 5 / 4 ))
echo "# BUILD $(cat $N/BUILD.joint) binary $(sha $BIN) state $(sha $S): $(sed -n 2p $S | cut -c1-60); a read projected $PROJ s, deadline $DEAD s"
export FIELD_PATH_FAR_KEYED=1 FIELD_PATH_OPENING=1 FIELD_PATH_WRITER=1 FIELD_ROOM_CUT=1 FIELD_STEP_HELD=1
unset FIELD_CLOCK_BARE
copies="33:all 8:all 4:all 2:all 1:all"
[ "$WITH" = parts ] && copies="$copies 4:faces 4:contacts 4:lane 4:heads"
for c in $copies; do
  s=${c%%:*}; sub=${c##*:}
  case $sub in all) name=s$s;; *) name=s${s}_$sub;; esac
  [ -e $N/STOP.g21 ] && { echo "MAIN STOP.g21 read: stops before $name"; exit 0; }
  [ -e $O/$name.state ] || python3 -I $N/round_state.py $S $s $O/$name.state $sub > $O/$name.round.log || { echo "MAIN rounding $name failed"; exit 1; }
  rm -rf $O/$name.joint
  ( flock -w 14400 9 || { echo "MAIN LOCK_BUSY at $name"; exit 75; }
    $M g21_${TAG}_$name timeout $DEAD $BIN train complete-language joint-field $O/$name.state $(sha $O/$name.state) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) $K $(sha $K) $O/$name.joint > $O/$name.log 2>&1
  ) 9>$ROOT/.local/gpu.lock
  echo "G21 $name $(head -1 $O/$name.round.log | sed -E 's/ROUND //') $(grep -E '^FIELD_JOINT_NATS' $O/$name.log | sed -E 's/.*own_nats_a_place=([0-9.]+) foil_nats_a_place=([0-9.]+).*/own=\1 foil=\2/') $(grep -E '^MEASURE' $O/$name.log | sed -E 's/.*wall_s=([0-9.]+).*/wall_s=\1/')"
done
for c in $copies; do s=${c%%:*}; sub=${c##*:}; case $sub in all) name=s$s;; *) name=s${s}_$sub;; esac; echo "$name $(grep -E '^FIELD_JOINT_NATS' $O/$name.log | sed -E 's/.*own_nats_a_place=([0-9.]+) foil.*/\1/')"; done > $O/summary.txt
awk -v tag=$TAG '
{ own[$1]=$2 }
END { u=own["s33"]; printf "G21 %s unrounded own %s\n", tag, u;
  split("8 4 2 1", ss, " "); split("0.0005 0.006 0.06 0.5", gs, " ");
  for (i=1;i<=4;i++) { k="s" ss[i]; printf "G21 %s s=%s own %s change %+.4f (theory guess +%s)\n", tag, ss[i], own[k], own[k]-u, gs[i] }
  split("faces contacts lane heads", ps, " ");
  for (i=1;i<=4;i++) { k="s4_" ps[i]; if (k in own) printf "G21 %s s=4 only %s own %s change %+.4f\n", tag, ps[i], own[k], own[k]-u } }' $O/summary.txt
echo "MAIN g21 exit $(date -u +%H:%M:%S)"
