#!/usr/bin/env bash
# Build the PTX payload for CONFIGURATION FOLD ⊕ M5 FOUNDED ⊕ §XXXII-b CHART ⊕ §XXVIII-b SCOPE
# ⊕ the CUDA-only §XXXII-c REGISTER entry ⊕ contemporary live-current, resident text,
# returned-contact, material-shadow, morphological-conduct, and recurrent-law mouths.
# Deterministic, offline, explicit. Emits the artifact
# next to this script
# (the artifact include_bytes!'d by mount-link-gate / mount-founded-gate / mount-chart-gate /
# mount-scope-gate / mount-register-gate), then validates it assembles for the RTX 4080 SUPER
# (sm_89) with ptxas.
#
# Run manually from this directory. NOT wired into the workspace build — the workspace compiles
# without the nvptx target present because the .ptx artifact is committed alongside, exactly as
# kernel/soma.spv is the Vulkan boundary artifact and mount_smoke_kernel.ptx is the smoke boundary.
#
# `body` reaches a native u64 divide on some paths, so build-std carries compiler_builtins as well
# as core (the smoke kernel needed only core). Both lower to PTX; ptxas is the final judge.
set -euo pipefail
cd "$(dirname "$0")"

PTXAS="${PTXAS:-/opt/cuda/bin/ptxas}"
TARGET="nvptx64-nvidia-cuda"
# sm_89 = Ada (RTX 4080 SUPER); +ptx78 pairs with CUDA 13.2's ptxas.
export RUSTFLAGS="-C target-cpu=sm_89 -C target-feature=+ptx78"

cargo build --release --target "$TARGET" -Z build-std=core,compiler_builtins

BUILT="target/${TARGET}/release/soma_kernel_cuda.ptx"
cp -f "$BUILT" soma_kernel_cuda.ptx

echo "=== PTX header ==="
head -6 soma_kernel_cuda.ptx
echo "=== entries present ==="
for e in link_grain link_sum link_finish link_founded_grain link_register_grain link_register_sum link_register_finish link_founded_sum chart_mark chart_register_mark chart_count chart_recast register_own_recast register_own_recast_finish register_carrier_rebase scope_felt scope_founded scope_register scope_register_surface regional_contacts lineage_event lineage_event_population material_shadow_read text_incidence_select text_section_restrict returned_contact_group returned_contact_sparse_group morphological_suffix_condition morphological_prefix_condition morphological_conduct_group recurrent_law_found recurrent_law_evaluate recurrent_law_fold; do
  if grep -q ".entry $e" soma_kernel_cuda.ptx; then echo "  .entry $e: present"; else echo "  .entry $e: MISSING"; exit 1; fi
done
echo "=== ptxas -arch=sm_89 validation ==="
"$PTXAS" -arch=sm_89 soma_kernel_cuda.ptx -o /dev/null && echo "PTXAS: VALID (assembles clean)"
