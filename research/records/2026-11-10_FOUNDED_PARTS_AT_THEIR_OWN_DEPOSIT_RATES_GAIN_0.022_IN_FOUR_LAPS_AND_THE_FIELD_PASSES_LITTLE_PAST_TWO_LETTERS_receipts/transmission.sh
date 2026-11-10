#!/bin/bash
# transmission.sh STATE TAG: the field's transmission by joint (theory's reading, November 10 20:34; transmission-field, the commit in
# BUILD.transmission) of STATE on held 0-31: at an answer place the reference's exactly d nearest letters written, the rest of the answer
# the void letter, the question given, the code -ln f_t(x_t) in nats; left (d = 0..4) and both sides (d = 1..4), batched in periodic
# patterns over every shift of the period so each answer place is a target once per (mode, d); targets without their d letters are
# counted out. A reading only: STATE's bytes are unchanged; a trailing parts line (the rate arm's states) is read past. A short card stage
# of its own (flock -w 14400 on .local/gpu.lock, taken for this stage alone), so it fits between laps; output under $N/transmission/TAG.*.
# Printed: FIELD_TRANSMISSION per mode and d, then beside theory's row (the text's count table on held 0-31: left 3.481 2.710 1.898 1.423
# 1.224, both 1.564 0.569 0.419 0.397) the field's gain over its d = 0 read per d against the text's gain over its d = 0 (G12, fixed: full
# gain at d = 1 and 2, under half the text's at d = 3), and the same for both sides against the text's.
# Projection: a measured read of ct5 (BUILD.transmission): 3.9 s of the reads on the card (9 lines, 8,760 places each), 4.2 s wall, 0.28 GB resident; with the lock wait outside it,
# 20 s for the stage (the load and the hashes), deadline 1.25 x = 25 s. RTX 4080 SUPER.
set -u
ROOT=${HOLONICS_ROOT}; W=$ROOT/.local/wt/qgchgu-sampler; P=$ROOT/.local/data/python-codes-25k/passage
R=$W/.local/run; N=$R/2026-11-10-contacts; BIN=$N/field_pass.transmission; F84=$R/2026-11-05-code84
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
U="$U0 $(sha $U0)"; CODEC=$F84/dev/CODEC
[ $# -eq 2 ] || { echo "transmission.sh STATE TAG"; exit 2; }
S=$1; TAG=$2; O=$N/transmission
[ -x $BIN ] || { echo "MAIN no binary at $BIN"; exit 1; }
mkdir -p $O
PROJ=20; DEAD=$(( PROJ * 5 / 4 ))
echo "# BUILD $(cat $N/BUILD.transmission) binary $(sha $BIN) state $(sha $S): $(sed -n 2p $S | cut -c1-60); $(grep -a '^parts ' $S | head -1 | cut -c1-60); projected $PROJ s, deadline $DEAD s"
export FIELD_PATH_FAR_KEYED=1 FIELD_PATH_OPENING=1 FIELD_PATH_WRITER=1 FIELD_ROOM_CUT=1 FIELD_STEP_HELD=1 FIELD_CLOCK_BARE=1
( flock -w 14400 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
  echo "# lock taken $(date -u +%H:%M:%S)"
  $M transmission_$TAG timeout $DEAD $BIN train complete-language transmission-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) 32 > $O/$TAG.log 2>&1
) 9>$ROOT/.local/gpu.lock
grep -E '^FIELD_TRANSMISSION|^MEASURE|rror|panic|refused' $O/$TAG.log | cut -c1-200
awk -v tag=$TAG '
/^FIELD_TRANSMISSION mode=/ { split($2,m,"="); split($3,d,"="); split($6,c,"="); code[m[2] "," d[2]]=c[2] }
END {
  split("3.481 2.710 1.898 1.423 1.224", tl, " "); split("1.564 0.569 0.419 0.397", tb, " ");
  printf "TRANSMISSION %s left d=0..4 field", tag; for (i=0;i<=4;i++) printf " %.3f", code["left," i]; printf "\n";
  printf "TRANSMISSION %s left d=0..4 text ", tag; for (i=1;i<=5;i++) printf " %s", tl[i]; printf "\n";
  printf "TRANSMISSION %s left (d-1 minus d) d=1..4 field", tag; for (i=1;i<=4;i++) printf " %.3f", code["left," (i-1)] - code["left," i]; printf "\n";
  printf "TRANSMISSION %s left (d-1 minus d) d=1..4 text 0.71 0.73 0.51 0.23\n", tag;
  printf "TRANSMISSION %s left gain_field/gain_text d=1..4", tag;
  for (i=1;i<=4;i++) { g=code["left,0"]-code["left," i]; t=tl[1]-tl[i+1]; printf " %.2f", (t>0 ? g/t : 0) } printf "\n";
  printf "TRANSMISSION %s both d=1..4 field", tag; for (i=1;i<=4;i++) printf " %.3f", code["both," i]; printf "\n";
  printf "TRANSMISSION %s both d=1..4 text ", tag; for (i=1;i<=4;i++) printf " %s", tb[i]; printf "\n";
  printf "TRANSMISSION %s both gain_field/gain_text over left d=0, d=1..4", tag;
  for (i=1;i<=4;i++) { g=code["left,0"]-code["both," i]; t=tl[1]-tb[i]; printf " %.2f", (t>0 ? g/t : 0) } printf "\n";
}' $O/$TAG.log
echo "MAIN transmission exit $(date -u +%H:%M:%S)"
