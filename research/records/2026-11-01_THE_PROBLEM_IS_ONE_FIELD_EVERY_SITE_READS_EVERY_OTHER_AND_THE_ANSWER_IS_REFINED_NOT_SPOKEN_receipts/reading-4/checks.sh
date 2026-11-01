#!/usr/bin/env bash
# Reading 4's checks of the rewritten card realization: parityA6, parityB6 (stop at the first unequal or refused),
# the profile of card-profile/prof.sh on the rewrite (one section and one release batch at A, every launch timed
# alone), then timeA6, timeB6. The same declarations and deadlines as reading 3's (chain4.sh) and the profile's.
set -u
W=$ROOT/.local/wt/field-card
ok() { grep -q 'FIELD_PARITY_DONE' $W/.local/run/$1.log && ! grep -E 'FIELD_PARITY_DONE' $W/.local/run/$1.log | grep -qE '_unequal=[1-9]'; }
bash $W/.local/run/fp.sh parityA6 420 parity parity-field 32 4 8 2 32 2 16 8 8 1 4 4
ok parityA6 || { echo "STOP parityA6 $(grep -m1 -E 'unequal=[1-9]|rror|refused' $W/.local/run/parityA6.log)"; exit 1; }
bash $W/.local/run/fp.sh parityB6 540 parity parity-field 32 4 8 2 32 2 16 4 8 2 2 4
ok parityB6 || { echo "STOP parityB6 $(grep -m1 -E 'unequal=[1-9]|rror|refused' $W/.local/run/parityB6.log)"; exit 1; }
FIELD_PROFILE=1 bash $W/.local/run/fp.sh prof6-section 300 time time-field 32 4 8 2 32 2 16 1 8 0 16
FIELD_PROFILE=1 bash $W/.local/run/fp.sh prof6-release 300 time time-field 32 4 8 2 32 2 16 1 8 4 16
bash $W/.local/run/fp.sh timeA6 120 time time-field 32 4 8 2 32 2 16 16 8 4 16
bash $W/.local/run/fp.sh timeB6 120 time time-field 64 8 8 2 64 2 16 16 8 4 16
