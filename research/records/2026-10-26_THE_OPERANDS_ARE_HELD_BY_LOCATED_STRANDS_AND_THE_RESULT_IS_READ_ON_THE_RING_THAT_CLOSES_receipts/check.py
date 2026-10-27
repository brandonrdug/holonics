from fractions import Fraction as F
W=6
bad_write=bad_size=checked=0
nines=0
for S in range(1,10**W-1):
    s=str(S); L=len(s); q=10**L-1
    if S==q:
        nines+=1; continue
    # size: largest width w (1..W) whose face S/(10^w-1) mod 1 >= 1/10
    sz=max(w for w in range(1,W+1) if F(S % (10**w-1),10**w-1) >= F(1,10))
    if sz!=L: bad_size+=1
    # writing into ring L from H=-S
    H=(-S)%q
    for k,ch in enumerate(s):
        nxt=int(F((-H)%q,q)*10)   # tenth of conj(H)'s face 0
        if nxt!=int(ch): bad_write+=1; break
        H=(10*H+int(ch))%q
    else:
        if H!=0: bad_write+=1
    checked+=1
print("checked",checked,"bad_size",bad_size,"bad_write",bad_write,"all_nines_skipped",nines)
