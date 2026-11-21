#!/bin/bash
# The leak's founding record's reads B1 to B5 and F3 (its GUESS.txt, fixed 02:22:29Z by the formal thread): a host ruler, no state, no card.
set -u
L=$REPO/.local/wt/lead; F=$L/.local/run/front/arm_L71
cd $L
export DEPOSIT_STATE=$F/STATE.3000 CARRIER_UNITS=$REPO/.local/wt/section-edge/.local/run/gsm8k/UNITS0 CARRIER_CODEC=$F/CODEC CARRIER_SITES=240 CARRIER_TEXT=$L/docs/THE_ENGINE.md LEAK_TICKS=8 LEAK_DELTAS=1/0 LEAK_HOLD=1 LEAK_LAW_DELTAS=821000,835000,862000,857000,891000,889000,876000
t0=$(date +%s); echo "LEAK8LAW start $(date -u +%H:%M:%S) host_threads=24"
timeout 1800 cargo test --release -p holonics-engine a_lane_leaks_reads_at_set_strengths -- --ignored --nocapture 2>&1 | grep -E "LEAK_|test result|panicked|error"
echo "LEAK8LAW elapsed $(( $(date +%s) - t0 )) s"
