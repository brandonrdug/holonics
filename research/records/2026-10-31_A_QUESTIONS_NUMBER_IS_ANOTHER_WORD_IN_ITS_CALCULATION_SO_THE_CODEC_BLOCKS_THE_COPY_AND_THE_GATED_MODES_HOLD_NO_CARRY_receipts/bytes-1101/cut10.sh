#!/usr/bin/env bash
# Stop R2's trainer once lap 10 is read (its STATE.9 and TOWER_PASS pass=9 written), so brun.sh reads the lap-10
# receipt now; the run continues from STATE.9 in ten-lap segments (Brandon, November 1: results within 15 minutes).
E=$ROOT/.local/wt/section-edge/.local/run/race/bytes-1101
until grep -q '^TOWER_PASS pass=9 ' $E/r2.log 2>/dev/null; do sleep 5; done
pkill -f "^[^ ]*tower_pass[^ ]* train complete-language .* $E/r2\$" && echo "CUT r2 after lap 10 at=$(date -u +%FT%TZ)"
