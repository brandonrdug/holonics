#!/usr/bin/env bash
set -euo pipefail

notebook_root="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repository_root="$(cd "${notebook_root}/../.." && pwd)"

mkdir -p "${notebook_root}/build"

typst compile \
  "${notebook_root}/book/main.typ" \
  "${notebook_root}/build/notebook.pdf"

typst compile \
  "${notebook_root}/book/solutions.typ" \
  "${notebook_root}/build/notebook-solutions.pdf"

typst compile \
  --pages 1 \
  "${notebook_root}/book/main.typ" \
  "${notebook_root}/build/notebook.png"

typst compile \
  "${notebook_root}/attempts/sheet.typ" \
  "${notebook_root}/build/attempt-sheet.pdf"

(
  cd "${repository_root}/formal/elementary-holonics"
  lake env lean "${notebook_root}/lean/U001Trace.lean"
)

printf 'Notebook rendered and Lean unit checked.\n'
