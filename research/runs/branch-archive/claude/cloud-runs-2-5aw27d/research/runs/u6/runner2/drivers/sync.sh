#!/usr/bin/env bash
# Copies this runner's receipts into the branch and pushes them.
set -e
cd /home/user/holonics
d=research/runs/u6/runner2; mkdir -p $d
for x in q2k q12 throw q7; do [ -d out/$x ] && { rm -rf $d/$x; cp -r out/$x $d/$x; rm -f $d/$x/sampler.pid $d/$x/.seen_final; }; done
cp out/NOTES.md out/queue2.log out/queue2d.sh out/peak_rss.sh $d/ 2>/dev/null || true
git add $d
git -c user.email=brandonrdug@users.noreply.github.com -c user.name=brandonrdug commit -q -m "runs: the second cloud runner's receipts (${1:-progress})

Refs #63

Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01XwZxmaCK6rqcJNfz1aPkft" || echo nothing new
for i in 1 2 3 4; do git push -q -u origin claude/cloud-runs-2-5aw27d && break; sleep $((2**i)); done
git log -1 --format='%h %ae'
