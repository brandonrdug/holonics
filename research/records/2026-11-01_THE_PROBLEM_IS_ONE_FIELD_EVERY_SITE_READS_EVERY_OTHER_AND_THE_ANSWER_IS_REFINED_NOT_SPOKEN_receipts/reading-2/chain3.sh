#!/usr/bin/env bash
# Reading 2's checks: parityA3, parityB3 (stop at the first unequal or refused), then timeA3, timeB3.
set -u
W=$ROOT/.local/wt/field-card
ok() { grep -q 'FIELD_PARITY_DONE' $W/.local/run/$1.log && ! grep -E 'FIELD_PARITY_DONE' $W/.local/run/$1.log | grep -qE '_unequal=[1-9]'; }
bash $W/.local/run/fp.sh parityA3 420 parity parity-field 32 4 8 2 32 2 16 8 8 1 4 4
ok parityA3 || { echo "STOP parityA3 $(grep -m1 -E 'unequal=[1-9]|rror|refused' $W/.local/run/parityA3.log)"; exit 1; }
bash $W/.local/run/fp.sh parityB3 540 parity parity-field 32 4 8 2 32 2 16 4 8 2 2 4
ok parityB3 || { echo "STOP parityB3 $(grep -m1 -E 'unequal=[1-9]|rror|refused' $W/.local/run/parityB3.log)"; exit 1; }
bash $W/.local/run/fp.sh timeA3 120 time time-field 32 4 8 2 32 2 16 8 8 4 16
bash $W/.local/run/fp.sh timeB3 120 time time-field 64 8 8 2 64 2 16 8 8 4 16
