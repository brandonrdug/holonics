# Ruler: shared directions of two travels above a row-shuffled null, drawn on spans of known rank (numbers only).
import numpy as np
rng=np.random.default_rng(14)
def k_sig(d1,d2,perms=8):
    s=np.linalg.svd(d1.T@d2, compute_uv=False)
    null=max(np.linalg.svd(d1.T@d2[rng.permutation(d2.shape[0])], compute_uv=False)[0] for _ in range(perms))
    return int((s>null).sum())
for rows in (245,128,64):
    cols=32
    res=[]
    for r,noise in ((32,0.0),(24,0.5),(16,0.5),(8,0.5),(8,1.0),(0,1.0)):
        ks=[]
        for _ in range(20):
            if r>0:
                basis=np.linalg.qr(rng.standard_normal((cols,r)))[0]
                shared=rng.standard_normal((rows,r))@basis.T
            else:
                shared=np.zeros((rows,cols))
            d1=shared+noise*rng.standard_normal((rows,cols)); d2=shared+noise*rng.standard_normal((rows,cols))
            ks.append(k_sig(d1,d2))
        res.append((r,noise,round(float(np.mean(ks)),1)))
    print("rows",rows,"(shared rank, noise, k_sig):",res)
