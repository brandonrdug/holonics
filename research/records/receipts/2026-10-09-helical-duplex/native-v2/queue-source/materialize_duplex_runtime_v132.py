"""Source-bound direct native selectors with fixed development/measured acceptance reads."""
from pathlib import Path
import hashlib, json, math, sys

R=Path(__file__).resolve().parent;ROOT=R.parents[2];L=R/'helical-duplex-20261009-v132'
def read(p):return json.loads(Path(p).read_text())
def save(p,v):
    with Path(p).open('x') as f:json.dump(v,f,indent=2);f.write('\n')
def pin(p):
    p=Path(p);h=hashlib.sha256()
    with p.open('rb') as f:
        while b:=f.read(2**20):h.update(b)
    return {'sha256':h.hexdigest(),'bytes':p.stat().st_size}
ad=read(L/'SOURCE_NATIVE_INPUTS.json');build='helical-duplex-build-20261009-v132'
assert read(R/(build+'.acceptance.json'))['passed'] and read(R/(build+'.release.json'))['quiescence_confirmed']
artifact=L/'COMPILED_LIB.json'
if not artifact.exists():
    rows=[]
    for line in (R/(build+'.stdout')).read_text().splitlines():
        try:j=json.loads(line)
        except ValueError:continue
        if j.get('reason')=='compiler-artifact' and j.get('executable') and j['target']['name']=='holonics' and j.get('manifest_path','').startswith(ad['source_root']):rows.append(j)
    assert len(rows)==1 and not rows[0]['fresh'];exe=Path(rows[0]['executable'])
    save(artifact,{'row':rows[0],'executable_pin':pin(exe),'source_admission':pin(L/'SOURCE_NATIVE_INPUTS.json')})
else:exe=Path(read(artifact)['row']['executable']);assert pin(exe)==read(artifact)['executable_pin']
mode=sys.argv[1];prefix='compression::keys::duplex::tests::'
if mode in ('index','binding','development'):
    name={'index':'a_malformed_partner_contact_is_refused_before_any_index_arithmetic','binding':'a_changed_transport_on_the_same_helix_is_refused_its_founded_quotient','development':'the_family_diameter_is_the_maximum_over_its_coordinates_and_the_supports_are_exact'}[mode]
    names=[prefix+name];assert names[0] in ad['test_selectors'];selection=['--exact',names[0]]
    projection=17000000000;cpu_us=17000000;upper=16000000000
    basis={'fixed_existing_bounded_development_unit_ns':17000000000,'purpose':'Actual contract/representative workload measurement, not a whole namespace projection','development_cold_foundings':mode=='development','representative_scope':'Three charts; founding, supported decoding, complete <=8-member enumeration and pairwise diameter checks'}
else:
    assert mode=='acceptance'
    measured=[]
    for unit in ['index','binding','development']:
        label='helical-duplex-runtime-'+unit+'-20261009-v132'
        assert read(R/(label+'.acceptance.json'))['passed'] and read(R/(label+'.release.json'))['quiescence_confirmed']
        measured.append(read(R/(label+'.final.json'))['wall_ns'])
    upper=max(measured);names=sorted(ad['test_selectors']);selection=[prefix];projection=len(names)*upper
    assert projection<=245000000000,'Measured namespace projection exceeds the existing workload policy; do not launch'
    cpu_us=min(245000000,math.ceil(projection/1000))
    basis={'largest_measured_native_unit_wall_ns':upper,'all_prior_development_values_ns':measured,'declared_units':len(names),'projection_equation':'21 * max(all three measured development unit wall times)','single_process_reuses_founded_receivers_and_actual_runs':True,'early_stop_each_unit':True,'fixed_after_launch':True,'no_limit_raise_after_failed_read':True}
label='helical-duplex-runtime-'+mode+'-20261009-v132'
descriptor=L/(mode+'.RUNTIME_REQUEST.json')
d={'native_argv':[str(exe),*selection,'--nocapture','--test-threads=1'],'expected_names':names,'per_unit_upper_ns':upper,'native_stdout':str(L/(mode+'.native.stdout')),'native_stderr':str(L/(mode+'.native.stderr')),'result':str(L/(mode+'.RUNTIME_RESULT.json')),'source_commit':ad['source_commit']};save(descriptor,d)
c=read(R/'integration-c6-targeted-01-20261008-v120.config.json')
inputs=[Path(ad['source_root'])/p for p in ad['source_inputs']]+[Path(__file__),R/'stream_duplex_runtime_v132.py',descriptor,L/'SOURCE_NATIVE_INPUTS.json',L/'SOURCE_ADMISSION.json',artifact,exe]+[R/(build+'.'+ext) for ext in ['config.json','acceptance.json','release.json','output_seal.json','stdout']]+[Path('/usr/bin/env'),Path('/usr/bin/timeout'),Path('/usr/bin/python3.14')]+[R/n for n in ['final_stage_memory_v120.py','leased_stage_memory_v120.py','bounded_stage_memory_v120.py']]
inputs=list(dict.fromkeys(inputs));child_seconds=max(1,(projection-1000000000)//1000000000)
c.update(label=label,scope_unit='holonics-prune-admission-'+label,cwd=ad['source_root'],scope='Exact corrected native duplex '+mode+' source-bound read; no other native namespace',stage_kind='native_runtime',inputs=list(map(str,inputs)),expected_inputs={str(p.resolve()):pin(p) for p in inputs},input_directories=[],outputs=[d['result'],d['native_stdout'],d['native_stderr']],argv=['/usr/bin/timeout','--signal=TERM','--kill-after=1s',str(child_seconds)+'s','/usr/bin/env','-i','PATH=/usr/bin','HOME=/home/b','LANG=C','LC_ALL=C','RAYON_NUM_THREADS=1','/usr/bin/python3.14','-B',str(R/'stream_duplex_runtime_v132.py'),str(descriptor)],projection_ns=projection,aggregate_cpu_limit_us=cpu_us,aggregate_cpu_stop_margin_us=min(1000000,cpu_us//10),group_memory_max_bytes=2**33,address_space_max_bytes=-1,minimum_MemAvailable_KiB=12*2**20,thread_budget=1,explicit_user_8GiB_authorization=True,explicit_user_workload_duration_authorization=True,expected_test_count=len(names),expected_test_names_from_source=names,source_commit=ad['source_commit'],allocation_basis=basis)
save(R/(label+'.config.json'),c);print(json.dumps({'label':label,'units':len(names),'projection_ns':projection,'per_unit_ns':upper}))
