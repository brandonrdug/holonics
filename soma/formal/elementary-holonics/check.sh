#!/usr/bin/env bash
set -euo pipefail

formal_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
laboratory_root="$(cd "${formal_dir}/../../../.." && pwd)"
shared_mathlib="${laboratory_root}/experiments/byte-lm/sidecar/lean_proj"

files=(
  "${formal_dir}/ElementaryHolonics/Foundation/Receiver.lean"
  "${formal_dir}/ElementaryHolonics/Foundation/Presentation.lean"
  "${formal_dir}/ElementaryHolonics/Algorithm/Transition.lean"
  "${formal_dir}/ElementaryHolonics/Algorithm/Rebase.lean"
  "${formal_dir}/ElementaryHolonics/Geometry/Telescoping.lean"
  "${formal_dir}/ElementaryHolonics/Geometry/CrossRatio.lean"
  "${formal_dir}/ElementaryHolonics/RH/Statement.lean"
  "${formal_dir}/ElementaryHolonics/RH/Route.lean"
  "${formal_dir}/ElementaryHolonics.lean"
)

if [[ -f "${shared_mathlib}/lake-manifest.json" ]] &&
   [[ -f "${shared_mathlib}/.lake/packages/mathlib/Mathlib.lean" ]]; then
  (
    cd "${shared_mathlib}"
    build_dir="$(mktemp -d)"
    trap 'rm -rf "${build_dir}"' EXIT
    mathlib_path="$(lake env printenv LEAN_PATH)"
    for source_file in "${files[@]}"; do
      module_path="${source_file#"${formal_dir}/"}"
      output_file="${build_dir}/${module_path%.lean}.olean"
      mkdir -p "$(dirname "${output_file}")"
      LEAN_PATH="${build_dir}:${mathlib_path}" \
        lake env lean -R "${formal_dir}" -o "${output_file}" "${source_file}"
    done
  )
else
  (
    cd "${formal_dir}"
    lake update
    lake exe cache get
    lake build
  )
fi
