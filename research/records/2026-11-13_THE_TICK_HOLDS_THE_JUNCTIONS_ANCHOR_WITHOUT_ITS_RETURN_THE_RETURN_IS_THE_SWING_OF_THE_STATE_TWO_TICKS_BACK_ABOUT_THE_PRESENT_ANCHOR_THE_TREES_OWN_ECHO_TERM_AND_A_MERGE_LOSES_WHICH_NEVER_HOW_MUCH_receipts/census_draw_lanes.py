# A ruler drawn on spans of known kind for the census's k (15/16 of the cross singular values' sum), at the lanes' shapes.
import numpy as np, sys
rng=np.random.default_rng(14)
def k_of(d1,d2):
    s=np.linalg.svd(d1.T@d2, compute_uv=False); c=np.cumsum(s)/s.sum()
    return int(np.searchsorted(c, 15/16)+1)
for rows in (245,128,64):
    for cols in (32,):
        full=[k_of(rng.standard_normal((rows,cols)), rng.standard_normal((rows,cols))) for _ in range(40)]
        shared=[]
        for r in (8,16,24):
            ks=[]
            for _ in range(40):
                basis=np.linalg.qr(rng.standard_normal((cols,r)))[0]
                d1=rng.standard_normal((rows,r))@basis.T + 0.3*rng.standard_normal((rows,cols))
                d2=rng.standard_normal((rows,r))@basis.T + 0.3*rng.standard_normal((rows,cols))
                ks.append(k_of(d1,d2))
            shared.append((r, np.mean(ks)))
        print(f"rows={rows} cols={cols} full_rank_independent k={np.mean(full):.1f}  confined(r, k)={[(r, round(k,1)) for r,k in shared]}")
