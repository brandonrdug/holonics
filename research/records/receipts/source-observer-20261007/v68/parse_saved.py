from pathlib import Path
from fractions import Fraction as F
import re,json,hashlib
R=re.compile(r"Ratio \{ numer: (-?\d+), denom: (\d+) \}")
def bracket(s,key,left='[',right=']'):
 p=s.index(key)+len(key); p=s.index(left,p); depth=0
 for q in range(p,len(s)):
  if s[q]==left:depth+=1
  if s[q]==right:
   depth-=1
   if depth==0:return s[p:q+1]
 raise ValueError(key)
def rats(s):return [F(int(a),int(b)) for a,b in R.findall(s)]
def vec(s,key):return rats(bracket(s,key))
def law(s,key):
 t=bracket(s,key,'{','}'); entries=vec(t,'entries: '); assert len(entries)==64
 return {'map':[entries[i:i+8] for i in range(0,64,8)],'gram':vec(t,'gram: '),'located':t[t.index('located: '):]}
def apply(m,v):return [sum((x*y for x,y in zip(row,v)),F(0)) for row in m]
def sub(a,b):return [x-y for x,y in zip(a,b)]
def serial(x):
 if isinstance(x,F):return str(x)
 if isinstance(x,dict):return {k:serial(v) for k,v in x.items()}
 if isinstance(x,(list,tuple)):return [serial(v) for v in x]
 return x
import sys
if len(sys.argv)!=2: raise SystemExit("Usage: parse_saved.py OUTPUT_DIRECTORY (saved arithmetic only)")
output_dir=Path(sys.argv[1]); output_dir.mkdir(parents=True,exist_ok=True)
p=Path(__file__).with_name("HNN_ACTUAL_FULL_OUTPUT.txt")
assert hashlib.sha256(p.read_bytes()).hexdigest()=="f21c867ab0cd0d6adcb2e0939b977dc0f3e99f8ed485f70b3691b418626309a8"
text=p.read_text(); teaches=[]; probes=[]; obs=[]; controls=[]
for l in text.splitlines():
 if 'observer blind;' in l:
  o=l[l.index('actual_observation='):]; source=vec(o,'source: '); z=vec(o,'features: ');features=[z[i:i+8] for i in range(0,32,8)];assert len(z)==32
  x={'input':re.search(r'input=(\[.*?\]);',l)[1],'source':source,'features':features,'anchors':o[o.index('anchors: '):o.index('source: ')],'response_component_ratios':[list(dict.fromkeys(a/b for a,b in zip(f,source) if b)) for f in features]}
  (teaches if 'teaching=true' in l else probes).append(x)
 if 'observer observed R operands;' in l:
  before=law(l,'before_law=');after=law(l,'after_law=');sample=l[l.index('samples='):l.index('; class_metric')]
  feature=vec(sample,'feature: ');covector=vec(sample,'covector: ')
  apbefore=vec(l,'applied_same_feature_before=');apafter=vec(l,'; after=')
  assert apply(before['map'],feature)==apbefore;assert apply(after['map'],feature)==apafter
  obs.append({'before':before,'after':after,'feature':feature,'covector':covector,'map_delta':[sub(a,b) for a,b in zip(after['map'],before['map'])],'applied_class_descent':re.search(r'applied_class_descent=([^;]+)',l)[1],'applied_phase_descent':re.search(r'applied_phase_descent=([^;]+)',l)[1],'prior_terms':l[l.index('actual_predeposit_prior_terms='):l.index('; before_law=')],'publication':l[l.index('publication='):l.index('; applied_same_feature_before=')]})
 if 'observer fixed-carry controls' in l:
  a=vec(l[l.index('; learned='):],'logits: ');b=vec(l[l.index('; actual_continuing='):],'logits: ');assert a==b;controls.append(a)
for i,o in enumerate(obs):
 if i:assert o['before']['map']==obs[i-1]['after']['map']
for i,pb in enumerate(probes):
 f=pb['features'][2]; y=apply(obs[-1]['after']['map'],f);assert y==controls[i]
 increments=[apply(o['map_delta'],f) for o in obs];assert [sum(a,F(0)) for a in zip(*increments)]==y
 target=[1,2,3,0][i]; rival=max((c for c in range(4) if c!=target),key=lambda c:y[2*c]);pb.update({'scores':y,'per_deposit_scores':increments,'target':target,'final_best_rival':rival,'per_deposit_target_minus_final_rival':[a[2*target]-a[2*rival] for a in increments]})
result={'source_output_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'saved_arithmetic_only':True,'teachers':teaches,'probes':probes,'observations':obs,'assertions':'actual maps apply to same features exactly; maps telescope over four deposits; common=continuing all complex components'}
(output_dir/'parsed.v1.json').write_text(json.dumps(serial(result),indent=2)+'\n')
for i,pb in enumerate(probes):print('probe',i,'source',serial(pb['source']),'H ratios',serial(pb['response_component_ratios']),'perdeposit margin',serial(pb['per_deposit_target_minus_final_rival']))
for i,o in enumerate(obs):print('deposit',i,'priorbefore',o['before']['located'],'priorafter',o['after']['located'],'terms',o['prior_terms'],'class/phase',o['applied_class_descent'],o['applied_phase_descent'])
