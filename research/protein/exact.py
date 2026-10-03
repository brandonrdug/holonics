"""Outward exact interval faces; ordinary Python integers and fractions only.

SPDX-License-Identifier: MIT OR Apache-2.0
"""
from fractions import Fraction as F

def need(value, message):
    if not value:
        raise ValueError(message)

Z=F(0);G=2**80
def rebase(a):return F(a[0].numerator*G//a[0].denominator,G),F(-((-a[1].numerator*G)//a[1].denominator),G)
def val(x):return rebase((F(x),F(x)))
def add(a,b):return rebase((a[0]+b[0],a[1]+b[1]))
def sub(a,b):return rebase((a[0]-b[1],a[1]-b[0]))
def mul(a,b):
 xs=[x*y for x in a for y in b];return rebase((min(xs),max(xs)))
def scale(a,k):return rebase((a[0]*k,a[1]*k) if k>=0 else (a[1]*k,a[0]*k))
def square(a):return rebase((Z if a[0]<=Z<=a[1] else min(x*x for x in a),max(x*x for x in a)))
def div(a,b):
 need(b[0]>Z,'independent positiveCayleydenominator');xs=[x/y for x in a for y in b];return rebase((min(xs),max(xs)))
def dot(a,b):
 x=val(0)
 for u,v in zip(a,b):x=add(x,mul(u,v))
 return x
def norm(a):
 x=val(0)
 for v in a:x=add(x,square(v))
 return x
def minus(a,b):return [sub(x,y) for x,y in zip(a,b)]
def cross(a,b):return [sub(mul(a[1],b[2]),mul(a[2],b[1])),sub(mul(a[2],b[0]),mul(a[0],b[2])),sub(mul(a[0],b[1]),mul(a[1],b[0]))]
from functools import lru_cache
@lru_cache(maxsize=4096)
def rotation(d,chart,t):
 Q=norm(d);t2=square(t);zero=val(0);skew=((zero,scale(d[2],-1),d[1]),(d[2],zero,scale(d[0],-1)),(scale(d[1],-1),d[0],zero));D=add(val(1),mul(Q,t2)) if chart=='F' else add(t2,Q);rows=[]
 for i in range(3):
  beta=sub(square(d[i]),add(square(d[(i+1)%3]),square(d[(i+2)%3])));row=[]
  for j in range(3):
   if i==j:top=add(val(1),mul(t2,beta)) if chart=='F' else add(t2,beta)
   else:top=add(scale(mul(mul(t2,d[i]),d[j]),2) if chart=='F' else scale(mul(d[i],d[j]),2),scale(mul(t,skew[i][j]),2))
   row.append(div(top,D))
  rows.append(tuple(row))
 return tuple(rows)
def rotate(x,o,d,chart,t):
 z=minus(x,o);R=rotation(tuple(d),chart,tuple(t));return [add(oi,dot(row,z)) for oi,row in zip(o,R)]
