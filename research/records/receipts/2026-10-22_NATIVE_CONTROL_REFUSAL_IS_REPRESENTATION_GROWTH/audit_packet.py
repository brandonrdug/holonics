"""Pure saved-packet arithmetic. No native/model calls, no source mutation."""
from pathlib import Path
from fractions import Fraction as Q
import re,json,hashlib
root=Path(__file__).parent
log=root/'code-02-native/log.txt';text=log.read_text()
line=next(l for l in text.splitlines() if l.startswith('FINAL_INGRESS_SECOND_REFUSAL'))
quoted=re.findall(r'evidence: ("(?:[^"\\]|\\.)*")',line)
evidence=[json.loads(s) for s in quoted]
geometry=next(s for s in evidence if s.startswith('kind=authentic_source_geometry'))
material=next(s for s in evidence if s.startswith('kind=original_material_contraction'))
(root/'SOURCE_GEOMETRY_PACKET.txt').write_text(geometry+'\n')
(root/'MATERIAL_CONTEXT_PACKET.txt').write_text(material+'\n')
def rs(s):return [Q(int(n),int(d)) for n,d in re.findall(r'Ratio \{ numer: (-?\d+), denom: (\d+) \}',s)]
def array(s,key):
 a=s.index('[',s.index(key)+len(key));level=0
 for b in range(a,len(s)):
  if s[b]=='[':level+=1
  elif s[b]==']':
   level-=1
   if level==0:return s[a:b+1]
 raise ValueError('incomplete '+key)
def rat(q):return {'numerator':str(q.numerator),'denominator':str(q.denominator),'numerator_bits':abs(q.numerator).bit_length(),'denominator_bits':q.denominator.bit_length(),'approx':float(q)}
u=rs(array(material,' control='));fv=rs(array(material,' feature='));mv=rs(array(material,' M='))
assert len(u)==4 and len(fv)==180 and len(mv)==720
f=[fv[j:j+2] for j in range(0,len(fv),2)]
M=[[mv[(i*90+j)*2:(i*90+j)*2+2] for j in range(90)] for i in range(4)]
actual=[]
for row in M:
 real=sum((a*c-b*d for (a,b),(c,d) in zip(row,f)),Q(0));imag=sum((a*d+b*c for (a,b),(c,d) in zip(row,f)),Q(0));assert imag==0;actual.append(real)
assert actual==u
assert all(z[1]==0 for row in M for z in row) and all(z[1]==0 for z in f)
shape=re.search(r'B=ExactRatMatrix \{ rows: (\d+), columns: (\d+)',geometry);rows,cols=map(int,shape.groups())
b=rs(array(geometry,' B='));old=rs(array(geometry,' old='));assert (rows,cols,len(b),len(old))==(10,4,40,10)
metric=rs(geometry.split(' metric=',1)[1])[0];assert metric==Q(1,2)
added=[sum((b[i*4+j]*u[j] for j in range(4)),Q(0)) for i in range(10)]
new=[a+c for a,c in zip(old,added)]
before=metric*sum((q*q for q in old),Q(0));after=metric*sum((q*q for q in new),Q(0));cross=2*metric*sum((a*c for a,c in zip(old,added)),Q(0));quadratic=metric*sum((q*q for q in added),Q(0));work=after-before
assert work==cross+quadratic
assert abs(work)<65536
ubits=[[abs(q.numerator).bit_length(),q.denominator.bit_length()] for q in u]
assert max(n for n,d in ubits)==1803 and max(d for n,d in ubits)==1803
r={'kind':'exact saved refusal packet audit; no new native calls','source':json.loads((root/'PRE_DISPATCH_PINS.json').read_text())['source'],'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),'operative_error':'QuadraticControlBound','source_cells':12,'material_commit':7,'source_ring':0,'opened_at_tick':36,'lift':[12,2,1],'phase_part':0,'original_material_observations':int(re.search(r'M_observations=(\d+)',material)[1]),'lag_identity_text':material.split(' lag=',1)[1].split(' scalar_open_context=',1)[0],'material_schema':material.split('schema=',1)[1].split()[0],'material_packet_sha256':hashlib.sha256((root/'MATERIAL_CONTEXT_PACKET.txt').read_bytes()).hexdigest(),'source_packet_sha256':hashlib.sha256((root/'SOURCE_GEOMETRY_PACKET.txt').read_bytes()).hexdigest(),'dimensions':{'M':[4,90],'feature':90,'context':6,'p_c_a':[4,4,12],'control':4,'B':[rows,cols],'old_source_opening':len(old),'added':len(added),'receiving_fresh_carried':[6,6],'R_maps_each':[8,6],'R_gram_each':[6,6],'R_news_each':[8,6]},'limits':{'control_and_added_coordinate_bits':1024,'physical_abs_work':65536,'native_integer_bits':65536,'native_aggregate_bits':1048576},'all_material_feature_imaginary_parts_exact_zero':True,'independent_M_times_f_equals_actual_control':True,'controls':[rat(q) for q in u],'control_max_abs':rat(max(map(abs,u))),'all_controls_exceed_1024_bit_representation':all(max(n,d)>1024 for n,d in ubits),'source_control_packet_numerator_denominator_max':[1803,1803],'metric':rat(metric),'B':[[rat(b[i*4+j]) for j in range(4)] for i in range(rows)],'old_source_opening':[rat(q) for q in old],'added_from_actual_Bu':[rat(q) for q in added],'all_added_nonzero_coordinates_exceed_1024_bit_representation':all(q==0 or max(abs(q.numerator).bit_length(),q.denominator.bit_length())>1024 for q in added),'work_diagnostic':{'label':'counterfactual algebra on actual operands, not an admitted/applied source move','before':rat(before),'after':rat(after),'cross':rat(cross),'quadratic':rat(quadratic),'total':rat(work),'cross_plus_quadratic_equals_after_minus_before':True,'within_physical_cap':True,'not_native_work_admitted':True},'classification':'Representation growth, not physical magnitude: exact authentic controls require1803bits; work algebra remains below unchanged65536 cap. Merely widening the control precheck is insufficient because downstream added coordinates also exceed1024. No move was applied.','no_native_calls_in_audit':True,'rollback_to_actual_source11_verified_by_runtime':True}
(root/'EXACT_CONTROL_AUDIT.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({'M_observations':r['original_material_observations'],'controls':[{'bits':[q['numerator_bits'],q['denominator_bits']],'approx':q['approx']} for q in r['controls']],'max_abs_control':r['control_max_abs']['approx'],'metric':float(metric),'work':float(work),'cross':float(cross),'quadratic':float(quadratic),'work_bits':[abs(work.numerator).bit_length(),work.denominator.bit_length()],'added_bits':[[abs(q.numerator).bit_length(),q.denominator.bit_length()] for q in added],'classification':r['classification']},indent=2))
