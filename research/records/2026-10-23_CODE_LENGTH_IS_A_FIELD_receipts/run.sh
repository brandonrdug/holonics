#!/bin/bash
# Code length as a field: the whole passage in context, each region alone, and the primes' signs.
# Projection: 4.72 us/cell is the largest measured (whole partition, two runs together); four lanes together
# are unmeasured, so the upper end is declared at 2x, 9.4 us/cell. Deadline = upper end per run:
#   whole 14,112,672 cells: 67-133 s; Q 6,324,000: 30-60 s; P 5,983,920: 28-57 s; N 732,116: 4-7 s;
#   M 1,072,636: 5-11 s; mu, lam 4,194,304 each: 20-40 s. Memory: about 1.1 GB for the whole, less for the rest.
cd "$(dirname "$0")/run"
t() { local name=$1 dl=$2; shift 2; local s=$(date +%s.%N); timeout $dl "$@" > $name.txt 2>&1; local x=$?; echo "exit $x wall $(echo "$(date +%s.%N) - $s" | bc) s deadline $dl s" >> $name.txt; }
F=../field
( t whole 133 $F 24 12 13 64 ../../full/train_all.txt whole.f32 ) &
( t Q 60 $F 24 12 13 64 Q.bin Q.f32; t N 7 $F 24 12 13 64 N.bin N.f32 ) &
( t P 57 $F 24 12 13 64 P.bin P.f32; t M 11 $F 24 12 13 64 M.bin M.f32 ) &
( FIELD_CELLS=1 FIELD_PH=1 FIELD_PROBS=mu1.p t mu1 40 $F 24 12 13 64 mu.bin mu1.f32
  FIELD_CELLS=1 FIELD_PH=1 FIELD_PROBS=lam1.p t lam1 40 $F 24 12 13 64 lam.bin lam1.f32
  FIELD_CELLS=1 FIELD_PH=4 FIELD_PROBS=mu4.p t mu4 40 $F 24 12 13 64 mu.bin mu4.f32 ) &
wait
for f in whole Q N P M mu1 lam1 mu4; do echo "== $f"; head -1 $f.txt; tail -1 $f.txt; done
