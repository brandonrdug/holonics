#!/usr/bin/env bash
# Reading 5's checks of the card realization after the tiled contact (the exponential's resident face, the carriers'
# widths from the frame, keys and values read a tile a block): parityA7, parityB7 (stop at the first unequal or
# refused), the profile at A (one section and one release batch, every launch timed alone), then timeA7, timeB7.
# The same declarations and deadlines as reading 4's checks.
set -u
W=$ROOT/.local/wt/field-card
ok() { grep -q 'FIELD_PARITY_DONE' $W/.local/run/$1.log && ! grep -E 'FIELD_PARITY_DONE' $W/.local/run/$1.log | grep -qE '_unequal=[1-9]'; }
bash $W/.local/run/fp.sh parityA7 420 parity parity-field 32 4 8 2 32 2 16 8 8 1 4 4
ok parityA7 || { echo "STOP parityA7 $(grep -m1 -E 'unequal=[1-9]|rror|refused' $W/.local/run/parityA7.log)"; exit 1; }
bash $W/.local/run/fp.sh parityB7 540 parity parity-field 32 4 8 2 32 2 16 4 8 2 2 4
ok parityB7 || { echo "STOP parityB7 $(grep -m1 -E 'unequal=[1-9]|rror|refused' $W/.local/run/parityB7.log)"; exit 1; }
FIELD_PROFILE=1 bash $W/.local/run/fp.sh prof7-section 300 time time-field 32 4 8 2 32 2 16 1 8 0 16
FIELD_PROFILE=1 bash $W/.local/run/fp.sh prof7-release 300 time time-field 32 4 8 2 32 2 16 1 8 4 16
bash $W/.local/run/fp.sh timeA7 120 time time-field 32 4 8 2 32 2 16 16 8 4 16
bash $W/.local/run/fp.sh timeB7 120 time time-field 64 8 8 2 64 2 16 16 8 4 16
