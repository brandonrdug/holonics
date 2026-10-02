"""closes.py <checkpoint lower> <end upper>: the window's close, end.upper < checkpoint.lower - σ, with
σ = 64 decisions · 1/16 · ln 2 at an upper rational end of ln 2 (ReleaseExcursion::grain)."""
import sys
from fractions import Fraction as F
LN2_UPPER = F(6931471805599454, 10**16)  # ln 2 = 0.69314718055994530941..., this end lies above it
SIGMA = 64 * F(1, 16) * LN2_UPPER
lo, end = F(sys.argv[1]), F(sys.argv[2])
print('closes' if end < lo - SIGMA else 'open')
