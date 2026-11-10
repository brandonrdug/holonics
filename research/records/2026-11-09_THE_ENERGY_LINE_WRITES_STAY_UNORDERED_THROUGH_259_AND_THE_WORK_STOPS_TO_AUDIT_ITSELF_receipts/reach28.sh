#!/bin/bash
# The base-class |dphi| split on the main line (theory, November 9 14:17): reach_base.py over class_carry/word_carry 239f and 249
# (reach26's reads), truth letters from the held under-read's ENUMERATED (lap -1). A reading only, host Python, one thread.
# Projection: four passes over KEYS (10.6 M rows each) at about 0.5 M rows/s plus two CLASSES passes, about 3 min; deadline 900 s.
set -u
C=/content; S1=$(date +%s)
timeout 900 python3 $C/reach_base.py $C/class_carry.239f/CLASSES.tsv $C/word_carry.239f $C/class_carry.249/CLASSES.tsv $C/word_carry.249 \
  $C/under_carry.239f_carry.249_classes/ENUMERATED.tsv -1 $C/reach28.tsv
echo "reach rc $? $(( $(date +%s) - S1 )) s"
echo "MAIN exit $(date -u +%H:%M:%S)"
