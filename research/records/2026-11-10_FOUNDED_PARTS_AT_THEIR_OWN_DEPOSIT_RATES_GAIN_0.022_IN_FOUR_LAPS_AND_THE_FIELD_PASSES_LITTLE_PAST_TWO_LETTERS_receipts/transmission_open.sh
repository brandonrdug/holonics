#!/bin/bash
# transmission_open.sh STATE TAG [MODE]: the field's transmission by joint, like for like (theory's reading, November 10 21:03): the rest of
# the answer OPEN (unknown, no void written), only the d window letters written, the question given, the void past the answer's end as the
# keyed and locked reads give it; the code -ln f_t(x_t) at t in nats on held 0-31. Rows: left d = 0..4, both sides d = 1..4, the uneven splits
# (3L,1R), (1L,3R), (2L,1R), (1L,2R). MODE (default open-0) is transmission-field's: open-0 one target a region (exact: no other target's
# window is known there), open-S the targets of one shift of period S share a region (batched; other windows are then known there too). A reading
# only: STATE's bytes are unchanged. A short card stage of its own (flock -w 14400 on .local/gpu.lock). Output under $N/transmission/open_TAG.*.
# Printed to three decimals beside the text's rows (left 3.481 2.710 1.898 1.423 1.224; both 1.564 0.569 0.419 0.397; splits 0.690 0.714 0.923
# 0.938) and, for the left-only rows, `d-1 minus d` (what a grip of d-1 held letters passes on) beside the text's 0.71 0.73 0.51 0.23.
# Projection: a measured full read of ct8 (open-0, 114k regions of one target each): 185 s wall, 0.38 GB resident; 190 s, deadline 238 s (open-64 would read in about a fifth of it and changes the codes by up to 0.06, open-12 by up to 0.32).
set -u
ROOT=${HOLONICS_ROOT}; W=$ROOT/.local/wt/qgchgu-sampler; P=$ROOT/.local/data/python-codes-25k/passage
R=$W/.local/run; N=$R/2026-11-10-contacts; BIN=$N/field_pass.transmission; F84=$R/2026-11-05-code84
U0=$ROOT/.local/wt/section-edge/.local/run/gsm8k/UNITS0
M="python3 -I $ROOT/.local/wt/field-card/.local/run/dispersing/measure.py"
sha() { sha256sum "$1" | cut -c1-64; }
U="$U0 $(sha $U0)"; CODEC=$F84/dev/CODEC
[ $# -ge 2 ] || { echo "transmission_open.sh STATE TAG [MODE]"; exit 2; }
S=$1; TAG=$2; MODE=${3:-open-0}; O=$N/transmission
[ -x $BIN ] || { echo "MAIN no binary at $BIN"; exit 1; }
mkdir -p $O
PROJ=190; DEAD=$(( PROJ * 5 / 4 ))
echo "# BUILD $(cat $N/BUILD.transmission) binary $(sha $BIN) state $(sha $S): $(sed -n 2p $S | cut -c1-60); $(grep -a '^parts ' $S | head -1 | cut -c1-60); mode $MODE; projected $PROJ s, deadline $DEAD s"
export FIELD_PATH_FAR_KEYED=1 FIELD_PATH_OPENING=1 FIELD_PATH_WRITER=1 FIELD_ROOM_CUT=1 FIELD_STEP_HELD=1 FIELD_CLOCK_BARE=1
( flock -w 14400 9 || { echo "MAIN LOCK_BUSY"; exit 75; }
  echo "# lock taken $(date -u +%H:%M:%S)"
  $M transmission_open_$TAG timeout $DEAD $BIN train complete-language transmission-field $S $(sha $S) $CODEC $(sha $CODEC) $U $P/HELD128.txt $(sha $P/HELD128.txt) 32 $MODE > $O/open_$TAG.log 2>&1
) 9>$ROOT/.local/gpu.lock
grep -E '^MEASURE|rror|panic|refused' $O/open_$TAG.log | cut -c1-200
awk -v tag=$TAG '
/^FIELD_TRANSMISSION mode=/ { for (i=2;i<=NF;i++) { split($i,kv,"="); v[kv[1]]=kv[2] } key=v["mode"] "," v["l"] "," v["r"]; code[key]=v["code_nats_a_place"]; places[key]=v["places"]; outc[key]=v["out"]; regions[key]=v["regions"] }
END {
  split("3.481 2.710 1.898 1.423 1.224", tl, " "); split("1.564 0.569 0.419 0.397", tb, " "); split("0.690 0.714 0.923 0.938", ts, " ");
  printf "OPEN %s left d=0..4 field", tag; for (i=0;i<=4;i++) printf " %.3f", code["open-left," i ",0"]; printf "\n";
  printf "OPEN %s left d=0..4 text ", tag; for (i=1;i<=5;i++) printf " %s", tl[i]; printf "\n";
  printf "OPEN %s left (d-1 minus d) d=1..4 field", tag; for (i=1;i<=4;i++) printf " %.3f", code["open-left," (i-1) ",0"] - code["open-left," i ",0"]; printf "\n";
  printf "OPEN %s left (d-1 minus d) d=1..4 text  0.71 0.73 0.51 0.23\n", tag;
  printf "OPEN %s both d=1..4 field", tag; for (i=1;i<=4;i++) printf " %.3f", code["open-both," i "," i]; printf "\n";
  printf "OPEN %s both d=1..4 text ", tag; for (i=1;i<=4;i++) printf " %s", tb[i]; printf "\n";
  printf "OPEN %s splits (3L,1R) (1L,3R) (2L,1R) (1L,2R) field %.3f %.3f %.3f %.3f\n", tag, code["open-split,3,1"], code["open-split,1,3"], code["open-split,2,1"], code["open-split,1,2"];
  printf "OPEN %s splits text  %s %s %s %s\n", tag, ts[1], ts[2], ts[3], ts[4];
  printf "OPEN %s places a row (left d=0) %s, regions %s\n", tag, places["open-left,0,0"], regions["open-left,0,0"];
}' $O/open_$TAG.log
echo "MAIN transmission_open exit $(date -u +%H:%M:%S)"
