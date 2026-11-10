import numpy as np, time, sys
exec(open('yard.py').read().split("xT,sT=load")[0])
z=np.load('train.npz'); xT=z['x'].astype(np.int64); sT=z['seg']; xH,sH=load('HELD128.txt')
both=[(-1,1),(-2,-1,1,2),(-3,-2,-1,1,2,3),(-4,-3,-2,-1,1,2,3,4)]
run('BOTH SIDES, fit TRAIN, read HELD128',both,xT,sT,xH,sH)
run('BOTH SIDES, fit TRAIN, read HELD 0-31',both,xT,sT,xH,sH,sel=sH<32)
left=[tuple(range(-k,0)) for k in range(1,5)]
run('LEFT ONLY, fit TRAIN, read HELD 0-31',left,xT,sT,xH,sH,sel=sH<32)
