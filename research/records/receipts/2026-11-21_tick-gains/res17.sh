#!/bin/bash
# The trained tick's residual by tick, L71's end state, ticks raised to 17, 240 sites of docs/THE_ENGINE.md (a host ruler; no state).
# Projection: build 3 min, run under 10 min; timeout 1500 s.
set -u
L=$REPO/.local/wt/lead; F=$L/.local/run/front/arm_L71
cd $L
export DEPOSIT_STATE=$F/STATE.3000 CARRIER_UNITS=$REPO/.local/wt/section-edge/.local/run/gsm8k/UNITS0 CARRIER_CODEC=$F/CODEC CARRIER_SITES=240 CARRIER_TEXT=$L/docs/THE_ENGINE.md CARRIER_TICKS=17
t0=$(date +%s)
timeout 1500 cargo test --release -p holonics-engine the_trained_ticks_residual_by_tick -- --ignored --nocapture 2>&1 | grep -E "TICK_RESID|test result|panicked|error" 
echo "RES17 elapsed $(( $(date +%s) - t0 )) s"
