import numpy as np, time
t0=time.time()
exec(open('yard.py').read().split("xT,sT=load")[0])
z=np.load('train.npz'); xT=z['x'].astype(np.int64); sT=z['seg']
xH,sH=load('HELD128.txt')
left=[(-1,),(-2,-1),(-3,-2,-1),(-4,-3,-2,-1)]
run('LEFT ONLY, fit TRAIN, read HELD128',left,xT,sT,xH,sH)
run('LEFT ONLY, fit TRAIN, read HELD 0-31',left,xT,sT,xH,sH,sel=sH<32)
print('%.1fs'%(time.time()-t0))
