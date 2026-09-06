"""Exact declared-point current/source enclosures on the retained positive branch."""
import json
from pathlib import Path
import sympy as sp

BASE=Path(__file__).parent
source=json.loads((BASE/'lamb_current_receipt.json').read_text())
parent=json.loads((BASE.parent/'mfr3_viscous_strain_source/source_order3_receipt.json').read_text())
rho,sigma=sp.symbols('rho sigma',real=True)
def read(s): return sp.sympify(s,locals={'rho':rho,'sigma':sigma})
P=sp.Poly(read(parent['pressure_hessian']['target_polynomial']),rho)
lo,hi=map(sp.Rational,next(v for v,m in parent['strain_current']['all_real_root_intervals'] if sp.Rational(v[0])>0))
assert lo>0 and hi>lo and P.eval(lo)*P.eval(hi)<0
phase={name:[read(v) for v in values] for name,values in source['phase_receiver'].items() if name!='point'}
for i in range(3):
 assert sp.expand(phase['Ct'][i]+phase['advection'][i]+phase['minus_laplacian'][i]
  -phase['stretching'][i]-phase['minus_pressure_cross'][i]-phase['derivative_cross'][i])==0
out={}
for name,values in phase.items():
 out[name]=[]
 for value in values:
  f=sp.Poly(value.subs(sigma,0),rho).rem(P)
  assert f.degree()<=1
  a,b=sorted([f.eval(lo),f.eval(hi)])
  out[name].append({'affine_remainder':str(f.as_expr()),'exact':[str(a),str(b)],
                   'grid_1e3':[str(sp.floor(a*1000)/1000),str(sp.ceiling(b*1000)/1000)]})
assert all(sp.Rational(out['Ct'][i]['exact'][1])<0 for i in (0,1))
assert all(sp.Rational(out['stretching'][i]['exact'][0])>0 for i in (0,1))
coefficient=list(map(read,source['resolved_cutoff']['generated_velocity_current_after_Leray_coefficient']))
g=sp.Rational(35,768)*(2+5*(rho+sigma))
assert [sp.expand(v) for v in coefficient]==[-sp.expand(g),sp.expand(g),0]
assert sp.Rational(35,768)>0 and 2+5*lo>0
print(json.dumps({'scope':'Initial phase point (pi/2,0,0), sigma=0 and the accepted positive pressure-matching root; no positive-time bound',
 'root_interval':[str(lo),str(hi)],'oriented_source_enclosures':out,
 'generated_velocity_mode':[-2,-2,-1],'generated_coefficient_factor':str(g),
 'generated_selected_mode_zero_fibre':'rho+sigma=-2/5',
 'generated_mode_nonzero_on_accepted_branch':True,
 'checks':{'exact_full_parameter_point_balance':True,'initial_first_two_current_rates_negative':True,
           'stretching_first_two_components_positive':True,'exact_generated_factor_and_branch_nonzero':True},
 'exit_status':0},indent=2))
