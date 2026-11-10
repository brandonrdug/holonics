#!/bin/bash
# carry13e's lap end as its own declared read (theory, November 9 13:29): the run stopped at 259 (FIELD_STOPPED, 10,090 s), so the
# held read of STATE.stopped runs here, at 9580985d4 (carry13e's 6e94ca86c has no held-under), as held-under of the state under itself
# with classes held: the plain enumerated read at the 512 held places. Build about 90 s, read about 104 s; deadline 600 s.
set -u
export PATH=$HOME/.cargo/bin:/usr/local/cuda/bin:$PATH LIBRARY_PATH=/usr/lib64-nvidia:/usr/local/cuda/lib64/stubs LD_LIBRARY_PATH=/usr/lib64-nvidia CARGO_BUILD_JOBS=12 RAYON_NUM_THREADS=4
C=/content; cd $C/holonics && git fetch -q origin claude/project-thread-nclk1x && git checkout -q -f 9580985d4 && echo "# source $(git log -1 --format=%h)"
S0=$(date +%s); cargo build --release -p holonics-cuda --example field_pass 2>&1 | grep -E '^error|Finished'; echo "# build $(( $(date +%s) - S0 )) s"
BIN=$C/holonics/target/release/examples/field_pass; sha() { sha256sum "$1" | cut -c1-64; }
S=$C/carry_d/STATE.stopped; out=$C/held259; rm -rf $out; S1=$(date +%s)
timeout 600 $BIN train complete-language held-under $S $(sha $S) $S $(sha $S) $C/CODEC $(sha $C/CODEC) $C/UNITS0 $(sha $C/UNITS0) $C/HELD128.txt $(sha $C/HELD128.txt) 512 $out classes > $out.log 2>&1
echo "held259 rc $? $(( $(date +%s) - S1 )) s"; grep -E '^FIELD_HELD_UNDER|error|panic|refused' $out.log | cut -c1-300
echo "MAIN exit $(date -u +%H:%M:%S)"
