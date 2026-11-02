#!/usr/bin/env bash
# The card's own work at A (32 4 8 2 32 2): one training section of length 1,408 (time-field's first) and the same
# with one release batch (4 held problems, 16 sweeps), each profiled (FIELD_PROFILE: every launch, transfer and
# allocation timed alone) and plain; nvidia-smi sampled every 200 ms. Deadline 300 s each.
set -u
W=$ROOT/.local/wt/field-card
FIELD_PROFILE=1 bash $W/.local/run/fp.sh prof-section 300 time time-field 32 4 8 2 32 2 16 1 8 0 16
FIELD_PROFILE=1 bash $W/.local/run/fp.sh prof-release 300 time time-field 32 4 8 2 32 2 16 1 8 4 16
bash $W/.local/run/fp.sh plain-section 300 time time-field 32 4 8 2 32 2 16 1 8 0 16
bash $W/.local/run/fp.sh plain-release 300 time time-field 32 4 8 2 32 2 16 1 8 4 16
