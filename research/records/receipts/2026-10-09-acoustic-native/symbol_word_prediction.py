"""Predicts, with the first rung's exact replica, how the first rung's frame family reads the symbol
word of ring t = 1 on F1 (the native dynamic section's output, 7-cycle (class, advance):
1:+1 2:+1 3:+1 0:+1 1:+1 2:-2 0:+1), three cycles read, rings up to 6 and up to 9.

It runs no repository code. It is a PREDICTION, written before the native probe test runs.
Usage: python3 -I symbol_word_prediction.py <path to the first rung's replica.py>
"""
import importlib.util
import sys

spec = importlib.util.spec_from_file_location("rung1", sys.argv[1])
rung1 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(rung1)

CYCLE = [(1, 1), (2, 1), (3, 1), (0, 1), (1, 1), (2, -2), (0, 1)]
for bound in (6, 9):
    rung1.scan("ring t=1 symbol word", CYCLE * 3, bound)
