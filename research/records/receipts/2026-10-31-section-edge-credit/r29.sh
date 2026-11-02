#!/usr/bin/env bash
# Record §29, acceptance 51: from C′'s founding, the every-level credit for one lap then the motive
# for one lap, back to back in one lock beside the game, binary BIN. Each lap's deadline is fixed
# before launch from its own 64-section development read (m29): the lap's 726 sections at the read's
# time a section (its first window's refusals make it the upper rate), a tenth more, and 30 s for the
# held-out read and close. Then, under the same lock: each lap's writing (six prompts, 1,024 classes,
# agree 1; deadline 60 s each, six prompts took 8 to 9 s) and the motive learner's held-out read
# with and without D↓ (deadline 120 s; a held-out read takes some 4 s on the card).
set -u
P=$ROOT/.local/wt/race/.local/race/passage
W=$ROOT/.local/wt/section-edge
R=$W/.local/run
BIN=${BIN:?the race binary}
E=$R/race/r29; mkdir -p $E
dl() { local ms; ms=$(grep -E 'TOWER_SECTION.*section=64 ' $R/race/m29/dev-$1/lap0.log | grep -oE 'elapsed_ms=[0-9]+' | cut -d= -f2); echo $(( (ms * 726 / 64) * 11 / 10 / 1000 + 30 )); }
exec 9>$ROOT/.local/gpu.lock
flock -w 1800 9 || { echo "LOCK_BUSY"; exit 75; }
# The race runs only on the card's equality with the host (m29: the suite and the race
# declaration's parity) and on both development reads.
# The card suite is the tower's (`--test tower_pass`, as every receipt before it); the library's
# port tests fail beside it on a state's bit count (30,197 against 30,195), outside the tower.
cd $W
python3 -I $R/measure.py tower-suite timeout 300 cargo test -p holonics-cuda --test tower_pass -- --include-ignored --test-threads=1 > $E/tower-suite.log 2>&1
echo "TOWER_SUITE rc=$? $(grep -E 'test result|MEASURE' $E/tower-suite.log | tr '\n' ' ')"
grep -q 'test result: ok' $E/tower-suite.log && grep -E 'PARITY rc=0' $R/race/m29.log | grep -q 'gradient_unequal=0 learners_unequal=0' || { echo "STOP the card is not the host's: $(grep -E 'PARITY' $R/race/m29.log)"; exit 1; }
DL_EVERY=$(dl every); DL_MOTIVE=$(dl motive)
[ "$DL_EVERY" -gt 30 ] && [ "$DL_MOTIVE" -gt 30 ] || { echo "STOP no development read"; exit 1; }
echo "BIN=$(sha256sum $BIN | cut -c1-64) HEAD=$(git -C $W rev-parse --short HEAD) deadlines every=${DL_EVERY}s motive=${DL_MOTIVE}s at=$(date -u +%FT%TZ)"
unset TOWER_REFUSAL_TICKS TOWER_REFUSAL_PARTS TOWER_HOLD TOWER_MEETING TOWER_LAP_SECTIONS TOWER_PROFILE TOWER_REFUSAL_CLOSURE
nvidia-smi --query-gpu=memory.used --format=csv,noheader,nounits -lms 500 > $E/vram.log &
VRAM=$!
lap() { local name=$1 route=$2 deadline=$3; local O=$E/$name; mkdir -p $O
  echo "NVIDIA_SMI before $name: $(nvidia-smi --query-gpu=utilization.gpu,clocks.sm,clocks.mem,temperature.gpu,power.draw,pstate,memory.used --format=csv,noheader) at=$(date -u +%FT%TZ)"
  systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
    python3 -I $R/measure.py $name timeout $deadline $BIN train complete-language $route 257 \
    $P/TRAIN.classes 3f64e8a5a02a549c046cd28c2e38309004e755d8c384e1bdd641ba249398e283 \
    $P/DEV.classes c0648e23af0aaf1d101d31fa84450493a9ea45b063dad33e276185b6fe85f0d6 \
    $P/DEV.roles 99716b831415bb4637fd66f4e0591837dfb2198bc472aa86dcc7b0e1535c616d \
    $P/KEYS2 d4a65962a1eb6f7e60332c049c630f5d3eca815a55d3c3256b9ec82efef48132 \
    64 128 256 6 320 128 1 7 $O/lap0 > $O/lap0.log 2>&1
  echo "RUN_END $name deadline_s=$deadline rc=$? $(grep -E 'TOWER_PASS |TOWER_CARD|MEASURE' $O/lap0.log | tr '\n' ' ')"; }
lap every train-two-ladder-stacked-news-heading-credited-every-level-tower-classes $DL_EVERY
lap motive train-two-ladder-stacked-news-heading-credited-every-level-motive-tower-classes $DL_MOTIVE
for name in every motive; do
  S=$E/$name/lap0/STATE.0
  [ -f $S ] || continue
  systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
    python3 -I $R/measure.py release-$name timeout 60 $BIN release complete-language release-tower-classes \
    $S $(sha256sum $S | cut -c1-64) $P/PROMPTS.classes b45cf44ee3a5dd6b84e4b76c23cbab77e1816b1a903b4e7d394c445f9b6b7e3b \
    $P/RELEASE_KEYS 9e358671eb6968c1f4b624611b41de7fed4ede5fc1af9532a8d9db36f3c9b739 1024 1 $E/$name/release > $E/$name/release.log 2>&1
  echo "RELEASE_END $name rc=$? $(grep -E 'CLASSES_RELEASE_DONE|MEASURE' $E/$name/release.log | tr '\n' ' ')"
done
S=$E/motive/lap0/STATE.0
if [ -f $S ]; then
  systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
    python3 -I $R/measure.py held-cut timeout 120 $BIN read complete-language read-tower-held-classes \
    $S $(sha256sum $S | cut -c1-64) $P/DEV.classes c0648e23af0aaf1d101d31fa84450493a9ea45b063dad33e276185b6fe85f0d6 \
    $P/DEV.roles 99716b831415bb4637fd66f4e0591837dfb2198bc472aa86dcc7b0e1535c616d 320 128 > $E/held-cut.log 2>&1
  echo "HELD_CUT rc=$? $(grep -E 'TOWER_HELD|MEASURE' $E/held-cut.log | tr '\n' ' ')"
fi
kill $VRAM; echo "VRAM_PEAK_MIB=$(sort -n $E/vram.log | tail -1)"
