import sys, math
def lines(p, ks):
    out={}
    with open(p) as f:
        for i,l in enumerate(f,1):
            if i in ks: out[i]=[int(v) for v in l.split()]
            if i>max(ks): break
    return out
A,B,C=[lines(p,{3,6,7}) for p in sys.argv[1:4]]
for k,name in [(3,'fine'),(6,'level'),(7,'glue')]:
    d1=[b-a for a,b in zip(A[k],B[k])]; d2=[c-b for b,c in zip(B[k],C[k])]
    dot=sum(x*y for x,y in zip(d1,d2)); n1=math.sqrt(sum(x*x for x in d1)); n2=math.sqrt(sum(x*x for x in d2))
    print(name,'cos(successive displacements)',round(dot/(n1*n2),3),'|d1|',round(n1),'|d2|',round(n2))
