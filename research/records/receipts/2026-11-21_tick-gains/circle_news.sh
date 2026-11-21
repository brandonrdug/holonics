#!/bin/bash
# The formal thread's read S4 (fixed 04:04Z, relayed): the circles' successive news on L71 at its own ticks (a host ruler; no state, no card).
set -u
L=$REPO/.local/wt/lead; F=$L/.local/run/front/arm_L71
cd $L
export DEPOSIT_STATE=$F/STATE.3000 CARRIER_UNITS=$REPO/.local/wt/section-edge/.local/run/gsm8k/UNITS0 CARRIER_CODEC=$F/CODEC CARRIER_SITES=240 CARRIER_TEXT=$L/docs/THE_ENGINE.md
t0=$(date +%s); echo "NEWS start $(date -u +%H:%M:%S) host_threads=24 (beside the line's lap L75 on the card)"
timeout 900 nice -n 10 cargo test --release -p holonics-engine the_circles_successive_news -- --ignored --nocapture 2>&1 | grep -E "CIRCLE_NEWS|test result|panicked|error"
echo "NEWS elapsed $(( $(date +%s) - t0 )) s"
