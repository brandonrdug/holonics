import sys, math
from collections import defaultdict
data = b"".join(open(p,'rb').read() for p in sys.argv[1:])
d = [x for b in data for x in (b>>6,(b>>4)&3,(b>>2)&3,b&3)]
n = len(d); cut = int(n*0.8)//4*4
train, test = d[:cut], d[cut:]
def held_out(key):
    # KT-smoothed counts on train, code length on test (bits per digit)
    c = defaultdict(lambda:[0,0,0,0])
    for i,x in enumerate(train): c[key(train,i)][x]+=1
    bits=0.0
    for i,x in enumerate(test):
        k=c[key(test,i,cut)]; bits -= math.log2((k[x]+0.5)/(sum(k)+2))
    return bits/len(test)
def pos(m): return lambda s,i,off=0:(i+off)%m
def ctx(k,m=None):
    def f(s,i,off=0):
        p=tuple(s[max(0,i-k):i])
        return (p,(i+off)%m) if m else p
    return f
print("bytes",len(data),"digits",n)
for name,key in [("marginal",pos(1)),("pos mod 2",pos(2)),("pos mod 3",pos(3)),("pos mod 5",pos(5)),
                 ("pos mod 30 (rings 5,2,3)",pos(30)),("pos mod 4 (byte frame)",pos(4)),("pos mod 60",pos(60)),
                 ("prev 1",ctx(1)),("prev 1 + mod 4",ctx(1,4)),("prev 3",ctx(3)),("prev 3 + mod 4",ctx(3,4)),
                 ("prev 6",ctx(6)),("prev 6 + mod 4",ctx(6,4))]:
    print(f"{name:28s} {held_out(key):.3f} bits/digit")
