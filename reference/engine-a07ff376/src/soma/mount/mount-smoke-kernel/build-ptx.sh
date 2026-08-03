#!/usr/bin/env bash
# Build the PTX payload for the CUDA mount smoke. Deterministic, offline, explicit.
# Emits mount_smoke_kernel.ptx next to this script (the artifact include_bytes!'d by mount-smoke),
# then validates it assembles for the RTX 4080 SUPER (sm_89) with ptxas.
#
# Run manually from this directory. NOT wired into the workspace build — the workspace
# compiles without the nvptx target present because the .ptx artifact is committed alongside,
# exactly as kernel/soma.spv is the Vulkan boundary artifact.
set -euo pipefail
cd "$(dirname "$0")"

PTXAS="${PTXAS:-/opt/cuda/bin/ptxas}"
TARGET="nvptx64-nvidia-cuda"
# sm_89 = Ada (RTX 4080 SUPER); +ptx78 pairs with CUDA 13.2's ptxas.
export RUSTFLAGS="-C target-cpu=sm_89 -C target-feature=+ptx78"

cargo build --release --target "$TARGET" -Z build-std=core

BUILT="target/${TARGET}/release/mount_smoke_kernel.ptx"
cp -f "$BUILT" mount_smoke_kernel.ptx

echo "=== PTX header ==="
head -6 mount_smoke_kernel.ptx
echo "=== ptxas -arch=sm_89 validation ==="
"$PTXAS" -arch=sm_89 mount_smoke_kernel.ptx -o /dev/null && echo "PTXAS: EXACT (assembles clean)"
