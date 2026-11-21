#!/bin/bash
# Compile one variant of the kernels (sed expressions as arguments) with line info and read ptxas's registers and spills,
# and the source lines of every local-memory instruction in the chosen kernels.
set -u
name=$1; shift
K=$REPO/.local/wt/lead/crates/engine-cuda/kernels
S=$SCRATCH
D=$S/$name; rm -rf $D; mkdir -p $D/kernels; cp $K/* $D/kernels/
for e in "$@"; do sed -i "$e" $D/kernels/field.cu; done
export PATH=/opt/cuda/bin:$PATH
cd $D
t0=$(date +%s)
nvcc --ptx -O3 --std=c++20 -lineinfo --gpu-architecture=compute_89 kernels/field.cu -o field.ptx 2> nvcc.err || { echo "$name NVCC_FAIL"; tail -5 nvcc.err; exit 1; }
ptxas -arch=sm_89 -O3 -v -lineinfo field.ptx -o field.cubin > ptxas.txt 2>&1
t1=$(date +%s)
python3 $S/scripts/census.py ptxas.txt > census.txt
echo "$name done in $((t1-t0)) s"; cat census.txt
