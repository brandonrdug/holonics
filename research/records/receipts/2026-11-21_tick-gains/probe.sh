#!/bin/bash
# The tick's gains by finite differences on L71's end state (a host ruler; no state, no card). Args: TICKS SITES OUTDIR TIMEOUT_S
set -u
L=$REPO/.local/wt/lead; F=$L/.local/run/front/arm_L71
cd $L
export DEPOSIT_STATE=$F/STATE.3000 CARRIER_UNITS=$REPO/.local/wt/section-edge/.local/run/gsm8k/UNITS0 CARRIER_CODEC=$F/CODEC CARRIER_SITES=240 CARRIER_TEXT=$L/docs/THE_ENGINE.md PROBE_TICKS=$1 PROBE_SITES=$2 PROBE_OUT=$3
mkdir -p $3
t0=$(date +%s); echo "PROBE start $(date -u +%H:%M:%S) ticks=$1 sites=$2 host_threads=24"
timeout $4 cargo test --release -p holonics-engine the_ticks_gains_by_finite_differences -- --ignored --nocapture 2>&1 | grep -E "TICK_PROBE|test result|panicked|error"
echo "PROBE elapsed $(( $(date +%s) - t0 )) s"
