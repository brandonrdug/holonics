# The register's own content given the nearer letters: the letter at -d coded from the d-1 letters nearer to the place.
# By the shift this is the right-only table of depth d-1 (a letter coded from the letters after it). HELD128, Witten-Bell chain.
import numpy as np, time, sys
exec(open('yard.py').read().split("xT,sT=load")[0])
z=np.load('train.npz'); xT=z['x'].astype(np.int64); sT=z['seg']; xH,sH=load('HELD128.txt')
right=[tuple(range(1,k+1)) for k in range(1,7)]
run('RIGHT ONLY, fit TRAIN, read HELD128',right,xT,sT,xH,sH)
