#!/usr/bin/env bash
# Reading 7's checks of the card realization after the strand contacts (§17: the opening adds each site's neighbours'
# rows within its region, and each encoding's covector is its own partition of the sites by row): parityA8, parityB8
# (stop at the first unequal or refused), then timeA8, timeB8 for the reading's projections. Reading 5's declarations
# and deadlines.
set -u
W=$ROOT/.local/wt/field-card
ok() { grep -q 'FIELD_PARITY_DONE' $W/.local/run/$1.log && ! grep -E 'FIELD_PARITY_DONE' $W/.local/run/$1.log | grep -qE '_unequal=[1-9]'; }
bash $W/.local/run/fp.sh parityA8 420 parity parity-field 32 4 8 2 32 2 16 8 8 1 4 4
ok parityA8 || { echo "STOP parityA8 $(grep -m1 -E 'unequal=[1-9]|rror|refused' $W/.local/run/parityA8.log)"; exit 1; }
bash $W/.local/run/fp.sh parityB8 540 parity parity-field 32 4 8 2 32 2 16 4 8 2 2 4
ok parityB8 || { echo "STOP parityB8 $(grep -m1 -E 'unequal=[1-9]|rror|refused' $W/.local/run/parityB8.log)"; exit 1; }
bash $W/.local/run/fp.sh timeA8 120 time time-field 32 4 8 2 32 2 16 16 8 4 16
bash $W/.local/run/fp.sh timeB8 120 time time-field 64 8 8 2 64 2 16 16 8 4 16
