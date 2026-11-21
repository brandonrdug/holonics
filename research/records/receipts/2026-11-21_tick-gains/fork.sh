#!/bin/bash
set -u
L=$REPO/.local/wt/lead; F=$L/.local/run/front/arm_L71
cd $L
export DEPOSIT_STATE=$F/STATE.3000 CARRIER_UNITS=$REPO/.local/wt/section-edge/.local/run/gsm8k/UNITS0 CARRIER_CODEC=$F/CODEC FORK_FILLERS=$L/.local/run/nu/fork/fillers.txt PROBE_OUT=$L/.local/run/nu/fork
t0=$(date +%s); echo "FORK start $(date -u +%H:%M:%S) host_threads=24"
timeout 1200 cargo test --release -p holonics-engine the_forks_closing_orders_on_the_carry_circles -- --ignored --nocapture 2>&1 | grep -E "FORK |test result|panicked|error"
echo "FORK elapsed $(( $(date +%s) - t0 )) s"
