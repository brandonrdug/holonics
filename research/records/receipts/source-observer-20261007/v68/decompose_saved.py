from pathlib import Path
exec(Path(__file__).with_name('parse_saved.py').read_text().split('for i,pb in enumerate(probes):print')[0])
N=8
I=[[F(i==j) for j in range(N)] for i in range(N)]
def mul(a,b):return [[sum((x*y for x,y in zip(row,col)),F(0)) for col in zip(*b)] for row in a]
def inverse(a):
 a=[list(r)+list(I[i]) for i,r in enumerate(a)]
 for i in range(N):
  p=next(j for j in range(i,N) if a[j][i]);a[i],a[p]=a[p],a[i];v=a[i][i];a[i]=[x/v for x in a[i]]
  for j in range(N):
   if i!=j:
    v=a[j][i];a[j]=[x-v*y for x,y in zip(a[j],a[i])]
 return [r[N:] for r in a]
mask=(1<<64)-1
def splitmix(z):
 z=(z+0x9E3779B97F4A7C15)&mask;z=((z^(z>>30))*0xBF58476D1CE4E5B9)&mask;z=((z^(z>>27))*0x94D049BB133111EB)&mask;return z^(z>>31)
def sign(i,j):
 z=splitmix(0)
 for x in (0,i,j):z=splitmix(z^x)
 return F(1 if z&1 else -1,2)
E=[[sign(i,j) for j in range(4)] for i in range(N)]
nu=F(699051,2097152)
def rotate(v,k):
 out=[F(0)]*N
 for n in range(4):out[2*((n+k)%4):2*((n+k)%4)+2]=v[2*n:2*n+2]
 return out
for ksgn in [1,-1]:
 K=[[F(-1,4) if i==j else F(0) for j in range(N)] for i in range(N)]
 for i in range(N):K[i][(i+1)%N]+=ksgn;K[(i+1)%N][i]-=ksgn
 A=[[I[i][j]-K[i][j]/2 for j in range(N)] for i in range(N)]
 inv=inverse(A);L=[[2*inv[i][j]-I[i][j] for j in range(N)] for i in range(N)]
 H=[[F(19,54)*L[i][j]-F(392,2187)*I[i][j] for j in range(N)] for i in range(N)]
 if all(apply(H,pb['source'])==pb['features'][2] for pb in probes):break
else:raise ValueError('actual H2 not recovered')
print('actual H2 match; skew sign',ksgn)
for orientation in [1,-1]:
 for i,pb in enumerate(probes):
  cells=[[0,3,None,0],[1,0,None,1],[2,1,None,2],[3,2,None,3]][i]
  terms=[[nu*x for x in rotate([row[c] for row in E],-orientation*(j+1))] for j,c in enumerate(cells) if c is not None]
  if [sum(x,F(0)) for x in zip(*terms)]!=pb['source']:break
 else:break
else:raise ValueError('source station decomposition mismatch')
print('actual source match; rotor orientation',orientation,'nu',nu,'nu−1/3',nu-F(1,3))
pb=probes[1];cells=[1,0,None,1];terms=[]
for j,c in enumerate(cells):
 if c is None:continue
 st=[nu*x for x in rotate([row[c] for row in E],-orientation*(j+1))]; f=apply(H,st); y=apply(obs[-1]['after']['map'],f)
 terms.append({'station':j,'class':c,'source_clock_integer':j+1,'phase':(j+1)%4,'winding':(j+1)//4,'E_column':[row[c] for row in E],'transported_normalized_source':st,'H2_feature':f,'complex_score':y,'target2_minus_final_rival1':y[4]-y[2]})
assert [sum(x,F(0)) for x in zip(*(t['complex_score'] for t in terms))]==pb['scores']
# Real score includes both input quadratures. This split is diagnostic in the declared chart.
f=pb['features'][2]; map_=obs[-1]['after']['map']; parity=[]
for start in [0,1]:parity.append([sum((r[k]*f[k] for k in range(start,8,2)),F(0)) for r in map_])
assert [a+b for a,b in zip(*parity)]==pb['scores']
# Recover Chi and validate the full88-coordinate identity from the stationary saved source laws.
def add(a,b):return [[x+y for x,y in zip(ra,rb)] for ra,rb in zip(a,b)]
def scale(a,v):return [[x*v for x in r] for r in a]
L2=mul(L,L);L3=mul(L2,L)
M=add(add(scale(L3,-27),scale(L2,-19)),add(scale(L,23),scale(I,23)))
Bs=[add(add(scale(L3,54),scale(L2,38)),scale(L,-46)),add(add(scale(L2,-54),scale(L,-38)),scale(I,-30)),add(scale(L,54),scale(I,76)),scale(I,-54),scale(I,-16),scale(I,16)]
mi=inverse(M);chis=[scale(mul(mi,b),-1) for b in Bs]
# Full opening state components: s0,s1,s2,a01from,a01to,a12from,a12to,u01,w01,u12,w12.
O=[];Afull=[]
for k in range(88):
 x=[[F(int(8*g+n==k)) for n in range(8)] for g in range(11)];anchors=[]
 for step in range(4):
  s=x[:3];a=x[3:7];u=[x[7],x[9]];w=[x[8],x[10]]
  v=[[sum(z,F(0))*weight for z in zip(*parts)] for parts,weight in [([s[0],a[0]],F(1,2)),([s[1],a[1],a[2]],F(1,3)),([s[2],a[3]],F(1,2))]]
  anchors.append(v)
  sn=[apply(L,[2*t-q for t,q in zip(vr,sr)]) for vr,sr in zip(v,s)]
  na=[];ns=[]
  for i,(g,h) in enumerate([(0,1),(1,2)]):
   og=[2*t-q for t,q in zip(v[g],a[2*i])];oh=[2*t-q for t,q in zip(v[h],a[2*i+1])]
   z=[F(8,27)*(ag-ah+2*ww-uu/4) for ag,ah,ww,uu in zip(og,oh,w[i],u[i])]
   na.extend([[ag-zz for ag,zz in zip(og,z)],[ah+zz for ah,zz in zip(oh,z)]])
   ns.extend([[uu+zz for uu,zz in zip(u[i],z)],[2*zz-ww for zz,ww in zip(z,w[i])]])
  x=sn+na+ns
 maps=[anchors[a][b] for a,b in [(0,0),(1,0),(2,0),(3,0),(1,1),(2,1)]]
 rec=[sum(col,F(0)) for col in zip(*(apply(ch,v) for ch,v in zip(chis,maps)))];assert rec==[F(n==k) for n in range(8)]
 O.append(maps)
# Actual anchor vectors were not printed. Reconstruct SOURCE-ONLY contributions, not fabricate actual carried anchors.
source_anchors=[[sum((O[k][i][n]*pb['source'][k] for k in range(8)),F(0)) for n in range(8)] for i in range(6)]
anchor_scores=[apply(map_,apply(H,apply(ch,v))) for ch,v in zip(chis,source_anchors)]
assert [sum(col,F(0)) for col in zip(*anchor_scores)]==pb['scores']
out={'saved_input_sha256':result['source_output_sha256'],'saved_operand_arithmetic_not_model_execution':True,'probe_index':1,'identity_labels':'symbol0=class0, symbol1=class1, symbol2=class2, symbol3=class3; no words/natural semantics','nu':nu,'nu_minus_exact_1_over_3':nu-F(1,3),'E':E,'L':L,'H2':H,'source_decomposition':terms,'score_from_even_feature_coordinates':parity[0],'score_from_odd_feature_coordinates':parity[1],'source_only_anchor_complex_scores':anchor_scores,'chi':chis,'full88_identity_recovered':True,'actual_individual_carried_anchor_vectors_saved':False,'all_retained_interior_coefficients_in_final_observer_score':'exactly0 by chiO=[I|0]; carry itself retained, not reset','actual_four_deposit_complex_score_increments':pb['per_deposit_scores'],'actual_four_deposit_target2_minus_final_rival1':pb['per_deposit_target_minus_final_rival'],'exact_final_complex_score':pb['scores'],'final_margin':pb['scores'][4]-pb['scores'][2]}
(output_dir/'DECOMPOSITION.v1.json').write_text(json.dumps(serial(out),indent=2)+'\n')
print('station margins',[str(t['target2_minus_final_rival1']) for t in terms])
print('quadrature real scores even',serial(parity[0][::2]),'odd',serial(parity[1][::2]))
print('anchor margin source-only',[str(t[4]-t[2]) for t in anchor_scores])
