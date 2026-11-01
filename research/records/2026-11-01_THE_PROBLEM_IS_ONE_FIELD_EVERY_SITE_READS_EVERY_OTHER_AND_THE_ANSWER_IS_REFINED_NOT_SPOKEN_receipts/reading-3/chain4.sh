#!/usr/bin/env bash
# Reading 3's checks: parityA4, parityB4 (stop at the first unequal or refused), then timeA4, timeB4.
set -u
W=$ROOT/.local/wt/field-card
ok() { grep -q 'FIELD_PARITY_DONE' $W/.local/run/$1.log && ! grep -E 'FIELD_PARITY_DONE' $W/.local/run/$1.log | grep -qE '_unequal=[1-9]'; }
bash $W/.local/run/fp.sh parityA4 420 parity parity-field 32 4 8 2 32 2 16 8 8 1 4 4
ok parityA4 || { echo "STOP parityA4 $(grep -m1 -E 'unequal=[1-9]|rror|refused' $W/.local/run/parityA4.log)"; exit 1; }
bash $W/.local/run/fp.sh parityB4 540 parity parity-field 32 4 8 2 32 2 16 4 8 2 2 4
ok parityB4 || { echo "STOP parityB4 $(grep -m1 -E 'unequal=[1-9]|rror|refused' $W/.local/run/parityB4.log)"; exit 1; }
bash $W/.local/run/fp.sh timeA4 120 time time-field 32 4 8 2 32 2 16 16 8 4 16
bash $W/.local/run/fp.sh timeB4 120 time time-field 64 8 8 2 64 2 16 16 8 4 16
