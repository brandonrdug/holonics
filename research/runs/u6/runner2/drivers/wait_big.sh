#!/usr/bin/env bash
# Exits on a queue-log change, a chain's terminal line, or every 4th move line of the Q2 control chain.
cd /home/user/holonics
q=$(wc -l < out/queue2.log); m=$(grep -c '^move' out/q2k/chain.txt)
while true; do
  [ "$(wc -l < out/queue2.log)" != "$q" ] && break
  n=$(grep -c '^move' out/q2k/chain.txt); [ $n -ge $((m+4)) ] && break
  grep -qE 'not accepted|did not close|RESTORE|^final state' out/q2k/chain.txt && [ ! -f out/q2k/.seen_final ] && { touch out/q2k/.seen_final; break; }
  sleep 20
done
tail -3 out/queue2.log; exit 0
