#!/bin/bash
# The formal thread's gate law G reads G1, G2 (fixed 04:15Z, relayed): the circles. news at lighter gates, on L71 (a host ruler; no card).
set -u
L=$REPO/.local/wt/lead; F=$L/.local/run/front/arm_L71
cd $L
export DEPOSIT_STATE=$F/STATE.3000 CARRIER_UNITS=$REPO/.local/wt/section-edge/.local/run/gsm8k/UNITS0 CARRIER_CODEC=$F/CODEC CARRIER_SITES=240 CARRIER_TEXT=$L/docs/THE_ENGINE.md NEWS_SHIFTS=0,1,2,3,4,5
t0=$(date +%s); echo "LIGHTER start $(date -u +%H:%M:%S) host_threads=24 (beside the line's lap on the card)"
timeout 900 nice -n 10 cargo test --release -p holonics-engine the_circles_news_at_lighter_gates -- --ignored --nocapture 2>&1 | grep -E "GATE_LIGHTER|test result|panicked|error"
echo "LIGHTER elapsed $(( $(date +%s) - t0 )) s"
