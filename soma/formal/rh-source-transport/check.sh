#!/usr/bin/env bash
set -euo pipefail

formal_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
laboratory_root="$(cd "${formal_dir}/../../../.." && pwd)"
shared_mathlib="${laboratory_root}/experiments/byte-lm/sidecar/lean_proj"

if [[ -f "${shared_mathlib}/lake-manifest.json" ]] &&
   [[ -f "${shared_mathlib}/.lake/packages/mathlib/Mathlib.lean" ]]; then
  (
    cd "${shared_mathlib}"
    lake env lean \
      "${formal_dir}/SomaRHSourceTransport/FiniteTransport.lean"
    lake env lean \
      "${formal_dir}/SomaRHSourceTransport/QuotientFamily.lean"
  )
else
  (
    cd "${formal_dir}"
    lake update
    lake exe cache get
    lake build
  )
fi
