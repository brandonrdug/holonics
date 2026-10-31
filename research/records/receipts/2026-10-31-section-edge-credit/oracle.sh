#!/usr/bin/env bash
# Record §22, acceptance 40: the frozen read with the credit's return beside it, on the heading's
# saved learners (a38c1c63f's law, laps 0, 1, 2), on the card under its lock.
set -u
W=${W:?the worktree}; S=${S:?the heading run's saved learners STATE.0..2}; P=${P:?the race passage}
for lap in 0 1 2; do
  sha=$(sha256sum $S/STATE.$lap | cut -c1-64)
  flock -w 60 ${LOCK:?the card lock} python3 -I $W/.local/run/measure.py lap$lap timeout 300 \
    $W/target/release/examples/opening_return $S/STATE.$lap $sha $P/TRAIN.classes \
    3f64e8a5a02a549c046cd28c2e38309004e755d8c384e1bdd641ba249398e283 320 128 16 16 1,2,4
done
