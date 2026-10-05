# The control read at 9078f103 (the same evaluate on lane B's founded keys state), run once from a
# detached worktree of that commit with its own target.
set -u
cd "$(git rev-parse --show-toplevel)"  # a detached worktree at 9078f103
export CARGO_TARGET_DIR=$PWD/target
s=$(date +%s%3N); timeout 900 cargo build --release -q -p holonics --example hnn_prediction -j 12; echo "build exit $? wall $(( $(date +%s%3N) - s )) ms"
keys=research/records/2026-10-05_LOCATED_KEYS_receipts
RAYON_NUM_THREADS=12 timeout 120 $CARGO_TARGET_DIR/release/examples/hnn_prediction executed evaluate order2 2026093042 8 .local/main_sections.txt keys-founded=$keys/state_keys_founded.txt 2>&1 | head -5
echo "run exit ${PIPESTATUS[0]}"
