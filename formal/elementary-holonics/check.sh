#!/usr/bin/env bash
# Use this project's pinned dependencies through the repository's supervised formal entry point.
# Verification never updates dependency versions or borrows a predecessor project's artifacts.
set -euo pipefail
formal_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec bash "${formal_dir}/../../tools/lean_check.sh" "$@"
