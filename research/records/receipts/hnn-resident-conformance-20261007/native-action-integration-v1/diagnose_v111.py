"""Read only saved native Rust Debug output. No native HNN execution or estimated arithmetic."""
import hashlib
import json
import re
from fractions import Fraction as Q
from pathlib import Path

ROOT = Path('/home/b/Workspaces/holonics')
SOURCE = ROOT / 'research/records/receipts/2026-10-06-lean-rust-native-queue/continuation-v111/ACTUAL_OUTPUT.txt'
OUT = Path(__file__).with_name('FACTOR_DIAGNOSIS.v111.json')

def balanced(text, start):
    first = text.index('{', start)
    level = 0
    for k in range(first, len(text)):
        level += (text[k] == '{') - (text[k] == '}')
        if level == 0:
            return text[start:k+1], k+1
    raise ValueError('unclosed native structure')

def structs(text, name):
    pos = 0
    while True:
        start = text.find(name + ' {', pos)
        if start < 0:
            return
        found, pos = balanced(text, start)
        yield found

def ratio(text, name):
    match = re.search(re.escape(name) + r': Ratio \{ numer: (-?\d+), denom: (\d+) \}', text)
    if not match:
        raise ValueError(name)
    return Q(int(match[1]), int(match[2]))

def ratios(text):
    return [Q(int(a), int(b)) for a,b in re.findall(r'Ratio \{ numer: (-?\d+), denom: (\d+) \}', text)]

def printed(value):
    match = re.search(r'\((-?\d+) rem (\d+) over (\d+)\)$', value)
    if not match:
        return Q(int(value))
    whole, rest, divisor = map(int, match.groups())
    assert 0 <= rest < divisor
    return Q(whole*divisor+rest, divisor)

def vec(parts, name):
    return [printed(x) for x in json.loads(parts[name])]

def pow2(e):
    return Q(2**e) if e >= 0 else Q(1,2**(-e))

def dyadic(value):
    value = abs(value)
    if not value:
        return {'zero': True}
    exponent = value.numerator.bit_length()-value.denominator.bit_length()
    if value < pow2(exponent):
        exponent -= 1
    assert pow2(exponent) <= value < pow2(exponent+1)
    return {'abs_lower_inclusive_power_two': exponent, 'abs_upper_exclusive_power_two': exponent+1}

def exact(value):
    return {'numerator': str(value.numerator), 'denominator': str(value.denominator), **dyadic(value)}

lines = SOURCE.read_text().splitlines()
unit = Q(1,64)
previous = {(family,index):Q(0) for family in range(3) for index in range(4)}
previous_scale = {family:Q(1) for family in range(3)}
previous_scale_remainder = {family:Q(0) for family in range(3)}
result = {
    'source_commit':'14418468094aa9f19efe77a8166919280b68be95',
    'actual_output_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
    'scope':'Exact exterior analysis of the saved native receipt. No compiler, HNN run, changed observation, proposed policy or new material.',
    'factor_lattice_unit':exact(unit),
    'coordinate_contract':'one contact; families C/K/D in order; row-major 2 by 2 factors; 12 full-state variation columns',
    'publications':[],
}
for credit_line,publication_line in ((50,51),(63,64),(76,77)):
    credit_parts = dict(x.split('=',1) for x in lines[credit_line-1].split('; ')[1:])
    pub_parts = dict(x.split('=',1) for x in lines[publication_line-1].split('; ')[1:])
    within,carried,total = (vec(credit_parts,x) for x in ('within_word','carried','total'))
    assert len(total)==12 and all(w+c==t for w,c,t in zip(within,carried,total))
    coords=re.findall(r'ContactCoordinate \{ contact: (\d+), family: (\d+), row: (\d+), column: (\d+) \}',credit_parts['coordinates'])
    assert [(int(a),int(f),int(r),int(c)) for a,f,r,c in coords]==[(0,f,r,c) for f in range(3) for r in range(2) for c in range(2)]
    pub = pub_parts['admitted_publication']
    remainder = {(int(f),int(i)):Q(int(n),int(d)) for f,i,n,d in re.findall(r'\(Channel\(0\), Factor\((\d)\), (\d), Ratio \{ numer: (-?\d+), denom: (\d+) \}\)',pub)}
    scale_remainder = {int(f):Q(int(n),int(d)) for f,n,d in re.findall(r'\(Channel\(0\), FactorScale\((\d)\), 0, Ratio \{ numer: (-?\d+), denom: (\d+) \}\)',pub)}
    assert len(remainder)==12
    metrics=list(structs(credit_parts['reached_metric'],'ReachedContactMetric'))
    steps=list(structs(pub,'StepReading'))
    loaded=next(structs(pub,'LoadedSpanReading'))
    gamma=ratios(loaded[loaded.index('gamma:'):loaded.index('receiving_projection:')])
    gain_parts=[ratio(loaded,'receiving_projection'), ratios(loaded[loaded.index('contact_injection:'):loaded.index('contact_coordinates:')])[0], ratio(loaded,'station_sum')]
    joint=next(structs(pub,'JointReading'))
    material=list(structs(pub_parts['canonical_held_continuation'],'ContactMaterialMove'))
    assert len(material)==3
    all_material_ratios=[q for m in material for q in ratios(m)]
    assert all(q==0 for q in all_material_ratios)
    entry={'credit_line':credit_line,'publication_line':publication_line,'role':credit_parts['role'],
           'all_twelve_reached_nonzero':all(total),
           'all_twelve_delayed_nonzero':all(carried),
           'each_within_plus_carried_equals_total':True,
           'zero_actual_factor_linear_quadratic_form_movements':True,
           'deposition_work':exact(ratio(pub_parts['canonical_held_continuation'],'deposition_work')),
           'loaded_gamma':list(map(exact,gamma)),
           'loaded_gain_parts':list(map(exact,gain_parts)),
           'joint_curvature':exact(ratio(joint,'curvature')),
           'joint_decrease':exact(ratio(joint,'decrease')),
           'joint_holds':ratio(joint,'curvature')<=ratio(joint,'decrease'),
           'no_released_covectors': 'released: []' in pub,
           'families':[]}
    actual=[]
    for family,(metric,step) in enumerate(zip(metrics,steps)):
        assert f'family: Factor({family})' in metric and f'family: Factor({family})' in step
        eta=ratio(step,'step')
        energy=ratio(metric,'within_word_energy')+ratio(metric,'opening_column_power')
        deltas=[remainder[(family,i)]-previous[(family,i)] for i in range(4)]
        scales=[-eta*total[family*4+i]/deltas[i] for i in range(4)]
        assert len(set(scales))==1 and scales[0]>0
        scale=scales[0]
        assert energy+previous_scale_remainder[family]==scale-previous_scale[family]+scale_remainder[family]
        moving=(energy+previous_scale_remainder[family])/unit+Q(1,2)
        quotient=moving.numerator//moving.denominator
        assert scale-previous_scale[family]==quotient*unit
        alignment,curvature,covector=(ratio(step,x) for x in ('alignment','curvature','covector'))
        gain,moves,bound=(ratio(step,x) for x in ('gain','moves','bound'))
        assert Q(1,2)*gain*moves==curvature
        assert gain==gain_parts[0]*gain_parts[1]*gain_parts[2]*ratio(step,'readout')
        assert eta*curvature<=alignment and eta*covector<=1
        coords_summary=[]
        for i in range(4):
            t=total[4*family+i]
            d=deltas[i]
            after=remainder[(family,i)]
            assert d==-eta*t/scale
            assert -unit/2<=after<unit/2
            coords_summary.append({'row':i//2,'column':i%2,'within_word':exact(within[4*family+i]),'carried':exact(carried[4*family+i]),'total':exact(t),'proposed_delta':exact(d),'applied_delta':exact(Q(0)),'retained_remainder_before':exact(previous[(family,i)]),'retained_remainder_after':exact(after),'accounting_closes':True})
        actual.append((eta,alignment,bound))
        entry['families'].append({'family':('C','K','D')[family],
            'step':exact(eta),'prepared_scale_inferred_four_matching_coordinates':exact(scale),
            'scale_before':exact(previous_scale[family]),
            'scale_applied_delta':exact(scale-previous_scale[family]),
            'scale_remainder_before':exact(previous_scale_remainder[family]),
            'scale_remainder_after':exact(scale_remainder[family]),
            'energy_plus_old_remainder_equals_scale_delta_plus_new_remainder':True,
            'actual_reached_energy':exact(energy),
            'alignment':exact(alignment),'curvature':exact(curvature),'covector':exact(covector),
            'gain':exact(gain),'moves':exact(moves),'bound':exact(bound),
            'own_curvature_admits_double_at_printed_ray':2*eta*curvature<=alignment,
            'covector_admits_double':2*eta*covector<=1,
            'coordinates':coords_summary,
            'max_abs_remainder_after':exact(max(abs(remainder[(family,i)]) for i in range(4)))})
    total_bound=sum(eta*bound for eta,alignment,bound in actual)
    decrease=sum(eta*alignment for eta,alignment,bound in actual)
    assert Q(1,2)*total_bound**2==ratio(joint,'curvature')
    assert decrease==ratio(joint,'decrease')
    for f,(eta,alignment,bound) in enumerate(actual):
        entry['families'][f]['joint_admits_double_one_family_at_fixed_printed_bounds']=Q(1,2)*(total_bound+eta*bound)**2<=decrease+eta*alignment
    previous=remainder
    previous_scale={f:Q(int(entry['families'][f]['prepared_scale_inferred_four_matching_coordinates']['numerator']),int(entry['families'][f]['prepared_scale_inferred_four_matching_coordinates']['denominator'])) for f in range(3)}
    previous_scale_remainder=scale_remainder
    result['publications'].append(entry)
OUT.write_text(json.dumps(result,indent=2)+'\n')
print(OUT)
print('Saved receipt accounting: 36 nonzero reached coordinates, 36 exact proposed/remainder closures, all factor/form movements zero.')
for p in result['publications']:
    print(p['role'],'gamma',p['loaded_gamma'][0]['abs_lower_inclusive_power_two'])
    for f in p['families']:
        print(f['family'],'eta',f['step'],'scale',f['prepared_scale_inferred_four_matching_coordinates']['numerator']+'/'+f['prepared_scale_inferred_four_matching_coordinates']['denominator'], 'max|remainder|',f['max_abs_remainder_after']['abs_lower_inclusive_power_two'],'double_own',f['own_curvature_admits_double_at_printed_ray'],'double_joint',f['joint_admits_double_one_family_at_fixed_printed_bounds'])
