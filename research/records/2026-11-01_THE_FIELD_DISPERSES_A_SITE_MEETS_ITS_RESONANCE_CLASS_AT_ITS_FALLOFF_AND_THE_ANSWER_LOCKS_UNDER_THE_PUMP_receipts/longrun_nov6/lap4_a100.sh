#!/bin/bash
# lap 4 replayed on the Colab A100 (the same binary's source at 5c7db3137, built for the VM's device), from the same tempered
# founding and data, to read whether a whole lap's state comes out bit for bit the local card's, and its time.
set -u
export PATH=$HOME/.cargo/bin:/usr/local/cuda/bin:$PATH LIBRARY_PATH=/usr/lib64-nvidia:/usr/local/cuda/lib64/stubs LD_LIBRARY_PATH=/usr/lib64-nvidia RAYON_NUM_THREADS=8 CARGO_BUILD_JOBS=12
cd /content/holonics && git fetch -q origin claude/project-thread-nclk1x && git checkout -q 5c7db3137 && git log -1 --format='%h' 
S=$(date +%s); cargo build --release -p holonics-cuda --example field_pass 2>&1 | grep -E '^error|Finished'; echo "build $(( $(date +%s) - S )) s"
sha() { sha256sum "$1" | cut -c1-64; }
C=/content; BIN=/content/holonics/target/release/examples/field_pass; D=$C/lap4; rm -rf $D
nvidia-smi --query-gpu=name --format=csv,noheader
S=$(date +%s)
timeout 700 $BIN train complete-language contrast-field $C/TEMPERED.STATE $(sha $C/TEMPERED.STATE) $C/CODEC $(sha $C/CODEC) $C/UNITS0 $(sha $C/UNITS0) $C/TRAIN.txt $(sha $C/TRAIN.txt) $C/HELD128.txt $(sha $C/HELD128.txt) 16 1 64 600000 600000 $D > $D.log 2>&1
echo "lap rc $? wall $(( $(date +%s) - S )) s"
grep -E '^FIELD_(KERNEL_ACCEPT|STOPPED|CARD |EXACT_READ)|rror|panic' $D.log | cut -c1-260
[ -f $D/STATE.0 ] && echo "STATE.0 $(sha $D/STATE.0)"
python3 /content/exact.py $D/EXACT.tsv
