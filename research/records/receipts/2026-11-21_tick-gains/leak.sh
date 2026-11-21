#!/bin/bash
set -u
L=$REPO/.local/wt/lead; F=$L/.local/run/front/arm_L71
cd $L
export DEPOSIT_STATE=$F/STATE.3000 CARRIER_UNITS=$REPO/.local/wt/section-edge/.local/run/gsm8k/UNITS0 CARRIER_CODEC=$F/CODEC CARRIER_SITES=240 CARRIER_TEXT=$L/docs/THE_ENGINE.md PROBE_SITES=120,122,200,201 PROBE_OUT=$L/.local/run/nu/leak
t0=$(date +%s); echo "LEAK start $(date -u +%H:%M:%S) host_threads=24"
timeout 1200 cargo test --release -p holonics-engine a_leaks_first_deposit_against_the_ticks_gains -- --ignored --nocapture 2>&1 | grep -E "LEAK_|test result|panicked|error"
echo "LEAK elapsed $(( $(date +%s) - t0 )) s"
