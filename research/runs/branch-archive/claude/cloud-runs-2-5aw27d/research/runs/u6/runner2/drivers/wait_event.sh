#!/usr/bin/env bash
# Exits when the queue log or any chain/listing gains a line (one event), printing what changed.
cd /home/user/holonics
snap() { cat out/queue2.log out/q2k/chain.txt out/q4/chain.txt out/q5/listing.txt 2>/dev/null | wc -l; ls out/q7 2>/dev/null | wc -l; }
a=$(snap)
while [ "$(snap)" = "$a" ]; do sleep 20; done
tail -3 out/queue2.log; for f in out/q2k/chain.txt out/q4/chain.txt out/q5/listing.txt; do [ -f $f ] && { echo "== $f"; tail -6 $f | cut -c1-400; }; done
exit 0
