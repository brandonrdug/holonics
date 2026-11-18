#!/usr/bin/env bash
# Gate 1 on a machine with no card (a cloud container): `tools/gate.sh` run against a stand-in for the driver library.
#
# Gate 1 runs nothing on the card: it checks the workspace, lints and tests the engine on the host, runs athena's host tests and the
# tools' controls, and reads the text against the tree. Its one tie to a card is the link of athena's test binary against `libcuda`,
# which a container does not hold. This script builds a stand-in from the driver calls `crates/engine-cuda/src/ffi.rs` declares, every
# call answering CUDA_ERROR_NOT_INITIALIZED (3), puts it on the linker's and the loader's path and runs `tools/gate.sh`. It prints the
# compiler it ran, which the repository does not pin.
#
# What it reads and what it does not. With no `nvcc` the card crate's build script compiles no kernel (its image is empty, and it says
# so), so a change under `kernels/` is not read here, and no test that opens a card can run. A change that leaves every crate's
# compiled tokens as they were (comments, guides, records, tools) is gated by it. For any other change it is a read before the PC's
# gate 1, never in its place, because the PC's compiler and its `nvcc` are the ones the line's binaries are built with (CLAUDE.md,
# Method, a line's lap, rule 4). Gates 2 to 4 are the PC's.
#
# Reason (November 18): the retirement of #995 was written in a cloud container and its gate 1 waited on the PC behind the line's laps,
# while every part of gate 1 but that one link ran in the container that wrote it.
#
#   bash tools/gate_nocard.sh        from the repository root; exit status is gate 1's
set -u -o pipefail
if command -v nvidia-smi >/dev/null 2>&1 && nvidia-smi >/dev/null 2>&1; then
  echo "gate_nocard: a card answers here; run bash tools/gate.sh" >&2
  exit 2
fi
root=$(cd "$(dirname "$0")/.." && pwd)
out="${CARGO_TARGET_DIR:-$root/target}/nocard"
mkdir -p "$out"
names=$(grep -oE 'pub fn cu[A-Za-z0-9_]+' "$root/crates/engine-cuda/src/ffi.rs" | awk '{print $3}' | sort -u)
if [ -z "$names" ]; then
  echo "gate_nocard: no driver call read from crates/engine-cuda/src/ffi.rs" >&2
  exit 2
fi
{
  echo "/* A stand-in for the driver library on a machine with no card: every call answers CUDA_ERROR_NOT_INITIALIZED (3). */"
  for n in $names; do echo "int $n() { return 3; }"; done
} > "$out/stub.c"
cc -shared -fPIC -o "$out/libcuda.so" "$out/stub.c" || exit 2
# Every call the crate declares stands in the stand-in, or the link would fail later with a line that names the linker.
for n in $names; do
  nm -D --defined-only "$out/libcuda.so" | grep -q " T $n\$" || { echo "gate_nocard: the stand-in lacks $n" >&2; exit 2; }
done
printf 'gate_nocard: %s driver calls stood in; %s; %s\n' "$(echo "$names" | wc -l)" "$(rustc --version)" "$(cargo clippy --version 2>/dev/null)"
cd "$root" || exit 2
LIBRARY_PATH="$out${LIBRARY_PATH:+:$LIBRARY_PATH}" LD_LIBRARY_PATH="$out${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}" bash tools/gate.sh
status=$?
printf 'gate_nocard: gate 1 %s with no card and no kernel read\n' "$([ $status -eq 0 ] && echo passed || echo FAILED)"
exit $status
