#!/bin/bash
# The formal thread's reads S1 and S2 (fixed 04:04Z, relayed): the circles' scan with its residue carried, on L71 (a host ruler; no card).
set -u
L=$REPO/.local/wt/lead; F=$L/.local/run/front/arm_L71
cd $L
export DEPOSIT_STATE=$F/STATE.3000 CARRIER_UNITS=$REPO/.local/wt/section-edge/.local/run/gsm8k/UNITS0 CARRIER_CODEC=$F/CODEC CARRIER_SITES=240 CARRIER_TEXT=$L/docs/THE_ENGINE.md
t0=$(date +%s); echo "CARRY start $(date -u +%H:%M:%S) host_threads=24 (beside the line's lap on the card)"
timeout 900 nice -n 10 cargo test --release -p holonics-engine the_circles_scan_with_its_residue_carried -- --ignored --nocapture 2>&1 | grep -E "SCAN_CARRY|test result|panicked|error"
echo "CARRY elapsed $(( $(date +%s) - t0 )) s"
