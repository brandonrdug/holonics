#!/usr/bin/env bash
# Samples the peak resident set (VmHWM, kB) of every running hnn_prediction every 5 s; one line per new maximum.
f=$1; max=0
while true; do
  for p in $(pgrep -f 'release/examples/hnn_prediction'); do
    v=$(awk '/VmHWM/{print $2}' /proc/$p/status 2>/dev/null)
    [ -n "$v" ] && [ "$v" -gt "$max" ] && { max=$v; echo "$(date -u +%FT%TZ) pid $p VmHWM $v kB $(tr '\0' ' ' </proc/$p/cmdline | cut -c1-160)" >> $f; }
  done
  sleep 5
done
