#!/usr/bin/env bash
# THE ONE COMMAND — emit kernel/soma.spv (the pinned nightly is picked up by rust-toolchain.toml).
set -e
cd "$(dirname "$0")/builder"
cargo run --release
