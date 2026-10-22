"""One bounded fresh campaign of clean native stages; no retry after an uncertain event.

The unchanged native stage owns ingestion/material/checkpoints. This exterior owns
only pins, fixed time/resource guards, exact parent chain and one final output pool.
"""
from pathlib import Path
import datetime,fcntl,hashlib,importlib.util,json,os,sys,time

NS=10**9

def sha(p):
    with Path(p).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def utc():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def durable(p,x):
    p=Path(p)
    with p.open('x') as f:json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
    fd=os.open(p.parent,os.O_DIRECTORY);os.fsync(fd);os.close(fd)
def load_module(name,path):
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def collect_pins(x):
    found={}
    def visit(v):
        if isinstance(v,dict):
            if isinstance(v.get('path'),str) and isinstance(v.get('sha256'),str):
                p,h=v['path'],v['sha256'];assert p not in found or found[p]==h,'conflicting pin';found[p]=h
            for value in v.values():visit(value)
        elif isinstance(v,list):
            for value in v:visit(value)
    visit(x);return [{'path':p,'sha256':h} for p,h in sorted(found.items())]

def validate(p):
    assert p['execution_authorized'] is True
    assert p['campaign_cap_ns']==13300*NS and p['max_native_stages']==8
    assert p['hard_training_guard_ns']==1500*NS and p['cooperative_stop_ns']==1400*NS
    assert p['automatic_retry'] is False and p['automatic_resume_after_hard_kill'] is False
    assert (p['records'],p['bytes'],p['cells'],p['horizon'])==(136,73580,294320,524288)
    assert p['output_cells_per_arm']==512 and len(p['output_arms'])==8 and p['output_shared_cap_ns']==500*NS
    assert p['sample_command']=='sample-prepared-retained-full-question-v1'
    assert [s['stage'] for s in p['stage_slots']]==list(range(1,9))
    assert sum(s['total_cap_ns'] for s in p['stage_slots'])==p['campaign_cap_ns']
    for i,s in enumerate(p['stage_slots']):
        assert s['training_hard_ns']==1500*NS and s['cooperative_native_ns']==1400*NS
        assert s['receipts_ns']==90*NS and s['cleanup_ns']==10*NS
        assert s['output_cap_ns']==(500*NS if i==7 else 0)
        assert s['total_cap_ns']==(2100*NS if i==7 else 1600*NS)
    return True

def clean_stage(r,t,previous,number,p):
    assert t['exit']==0 and t['stop'] is None and not t['owned_cleanup_remaining'] and t['final_integrity']
    assert not t['GPU_postflight'],'GPU cleanup before continuation'
    c=int(r['accepted']);n=int(r['published']);k=int(r['pending'])
    assert c==n+k==int(r['next_unread']) and 0<=k<10 and n%10==0
    assert int(r['accepted_at_start'])==previous and c>previous and c<=p['cells']
    assert int(r['global_epochs'])*10==n and r['stage_id']==f"{p['campaign_id']}-s{number:02}"
    assert r['source_sha256']==p['train']['sha256'] and r['native_source_identity']==p['source']
    assert r['execution_binary_sha256']==p['cuda_binary']['sha256'] and r['backend']=='cuda-observed-epoch-device0'
    assert r['cold_exact']=='true' and r['flush']=='false' and sha(r['checkpoint'])==r['checkpoint_sha256']
    assert (r['training_complete']=='true')==(c==p['cells'] and k==0)
    return c

def output_plan(p,checkpoint,cap):
    return {'workers':4,'cells':512,'deadline_ns':cap,'aggregate_host_bytes':8*1024**3,'aggregate_cpus':4,
            'binary':p['host_binary'],'checkpoint':checkpoint,'keys':p['keys'],
            'controller_sha256':p['output_pool']['sha256'],'sample_command':p['sample_command'],'arms':p['output_arms']}

def checkpoint_shape(path,expected,horizon):
    data=Path(path).read_bytes();assert data==Path(path).read_bytes()
    magic,lengths,body=data.split(b'\n',2);h,n,c,p,v=map(int,lengths.split())
    assert magic==b'solenoidal-alpha-family-local-subquantum20-v1' and h==horizon
    assert len(body)==n+c+p+v and min(n,c,p,v)>0
    crib=body[n:n+c].decode().splitlines();opening,published,count=map(int,crib[1].split())
    pending=body[n+c:n+c+p].decode().split()
    assert pending[:5]==['observed-stream-pending-v4','retained-fibre-v1','family-local-retained-return-v1','bounded-subquantum20-v1','local-receiving-held-map-v1']
    commit,frontier,k=map(int,pending[5:8]);assert frontier==published and 0<=k<10
    assert len(pending[8:])==k and count==published-opening and len(crib)==count+3
    assert published+k==expected and sha(path)==hashlib.sha256(data).hexdigest()
    return {'accepted':expected,'published':published,'pending':k,'checkpoint':{'path':str(path),'sha256':sha(path)}}

def choose_output(root,latest,horizon):
    candidates=[]
    for folder in Path(root).glob('stage-*/native'):
        if not (folder/'STAGE_GUARD_TERMINAL.json').exists():continue
        for meta in folder.glob('snapshot-*.json'):
            r=json.loads(meta.read_text())
            if r['pending']==0:
                path=meta.with_suffix('.state');assert sha(path)==r['sha256']
                checked=checkpoint_shape(path,int(r['accepted']),horizon)
                assert checked['published']==r['published'] and checked['pending']==0
                candidates.append(checked)
    if latest['pending']==0:
        checked=checkpoint_shape(latest['checkpoint']['path'],latest['accepted'],horizon)
        assert checked['pending']==0;candidates.append(checked)
    return max(candidates,key=lambda x:x['accepted']) if candidates else None

def epoch_summary(folder,published_start,published_end):
    counts={'Applied(ReceivingOnly)':0,'HeldReceiving':0,'Neutral':0};records=0;last=published_start
    path=folder/'epochs.jsonl'
    for raw in path.open('rb'):
        assert raw.endswith(b'\n'),'incomplete native epoch record'
        r=json.loads(raw);records+=1
        assert r['source_cells']==last+10 and r['epoch']==r['source_cells']//10 and r['consumed']==10
        assert r['closed_section'] is True and r['receiving_law']=='retained-fibre-v1'
        assert r['outcome'] in ('ReceivingOnly','HeldReceiving','Neutral')
        last=r['source_cells'];label='Applied(ReceivingOnly)' if r['outcome']=='ReceivingOnly' else r['outcome'];counts[label]+=1
    assert last==published_end
    return {'complete_records':records,'counts':counts,'last_complete_source_cells':last,'source_sha256':sha(path),'held_is_not_map_motion':True}

def inner(plan_path,digest,root,start,global_end):
    root=Path(root);p=json.loads(Path(plan_path).read_text());validate(p);assert sha(plan_path)==digest
    pins=collect_pins(p)+[{'path':str(plan_path),'sha256':digest}]
    assert all(sha(x['path'])==x['sha256'] for x in pins)
    identities={x['path']:(Path(x['path']).stat().st_size,Path(x['path']).stat().st_mtime_ns) for x in pins}
    check=lambda:all(Path(path).exists() and (Path(path).stat().st_size,Path(path).stat().st_mtime_ns)==v for path,v in identities.items())
    d=load_module('campaign_supervisor',p['supervisor']['path']);s=load_module('campaign_preparer',p['stage_preparer']['path'])
    previous=0;previous_published=0;parent=None;stages=[];selected=None;failure=None;eval_receipt=None
    def event(kind,**fields):
        x={'UTC':utc(),'kind':kind,'campaign_elapsed_ns':time.monotonic_ns()-start,**fields}
        with (root/'events.jsonl').open('a') as f:f.write(json.dumps(x)+'\n');f.flush();os.fsync(f.fileno())
        print(json.dumps(x),flush=True)
        tmp=root/'OWNER_CONTINUATION_CHECKPOINT.tmp';tmp.write_text(json.dumps(x,indent=2)+'\n')
        with tmp.open('rb') as f:os.fsync(f.fileno())
        os.replace(tmp,root/'OWNER_CONTINUATION_CHECKPOINT.json')
    try:
        for number in range(1,9):
            opened=time.monotonic_ns();slot=p['stage_slots'][number-1]
            assert opened+slot['total_cap_ns']<=global_end,'insufficient cumulative reserved stage budget'
            folder=root/f'stage-{number:02}';folder.mkdir();native=folder/'native';control=folder/'STAGE.tsv'
            argv=s.prepare(p,number,control,native,parent)
            deadline=opened+1500*NS
            durable(folder/'START.json',{'UTC':utc(),'stage':number,'accepted_start':previous,'argv':argv,'hard_deadline_monotonic_ns':deadline,'hard_deadline_UTC':(datetime.datetime.now(datetime.timezone.utc)+datetime.timedelta(seconds=max(0,(deadline-time.monotonic_ns())/NS))).isoformat(),'stage_deadline_monotonic_ns':opened+slot['total_cap_ns'],'global_deadline_monotonic_ns':global_end})
            event('STAGE_START',stage=number,accepted_start=previous,hard_deadline_monotonic_ns=deadline,hard_deadline_UTC=json.loads((folder/'START.json').read_text())['hard_deadline_UTC'],native_output=str(native))
            sup=d.Supervisor(folder,check)
            t=sup.run(argv,deadline,'training',{'CUDA_PATH':'/opt/cuda','NVCC':'/opt/cuda/bin/nvcc','RAYON_NUM_THREADS':'4'},gpu=True)
            assert time.monotonic_ns()<opened+1600*NS,'stage report/cleanup cap'
            r=s.table(native/'STAGE_COMPLETE.tsv','complete-language-stage-complete-v1')
            accepted=clean_stage(r,t,previous,number,p)
            assert all(sha(x['path'])==x['sha256'] for x in pins),'full poststage integrity'
            durable(native/'STAGE_GUARD_TERMINAL.json',t)
            row={'stage':number,'accepted':accepted,'published':int(r['published']),'pending':int(r['pending']),'checkpoint':{'path':r['checkpoint'],'sha256':r['checkpoint_sha256']},'native_elapsed_ns':int(r['elapsed_ns']),'guard_elapsed_ns':t['elapsed_ns'],'stage_receipt_sha256':sha(native/'STAGE_COMPLETE.tsv'),'training_complete':r['training_complete']=='true','outcomes':epoch_summary(native,previous_published,int(r['published']))}
            durable(folder/'TRANSITION.json',row);stages.append(row);parent=native;previous=accepted;previous_published=int(r['published'])
            selected=row
            event('STAGE_DURABLE',**row)
            if row['training_complete']:break
        assert selected is not None
        # Select only by greatest durable zero-pending offset, never by output/score.
        output_selected=choose_output(root,selected,p['horizon'])
        assert output_selected is not None,'no durable zero-pending output checkpoint; latest partial preserved'
        durable(root/'OUTPUT_CHECKPOINT_SELECTION.json',{'rule':'greatest durable verified zero-pending accepted frontier','selected':output_selected,'latest_durable_separately_preserved':selected})
        out_open=time.monotonic_ns();cap=min(500*NS,global_end-out_open-100*NS)
        assert cap>0,'no final output allocation'
        ep=output_plan(p,output_selected['checkpoint'],cap);epp=root/'FINAL_OUTPUT_PLAN.json';durable(epp,ep)
        event('FINAL_OUTPUT_START',checkpoint=output_selected['checkpoint'],accepted=output_selected['accepted'],published=output_selected['published'],pending=0,output_deadline_monotonic_ns=out_open+cap)
        sup=d.Supervisor(root,check)
        eval_receipt=sup.run(['python3',p['output_pool']['path'],str(epp),sha(epp),str(root/'outputs')],out_open+cap,'evaluation',{'RAYON_NUM_THREADS':'1'},gpu=False)
        assert time.monotonic_ns()<out_open+600*NS
        event('FINAL_OUTPUT_TERMINAL',exit=eval_receipt['exit'],stop=eval_receipt['stop'])
    except BaseException as exc:
        failure=f'{type(exc).__name__}:{exc}';event('CAMPAIGN_STOP',cause=failure)
    finally:
        integrity=all(sha(x['path'])==x['sha256'] for x in pins)
        terminal={'UTC':utc(),'campaign_elapsed_ns':time.monotonic_ns()-start,'cap_ns':p['campaign_cap_ns'],'stages':stages,'latest_durable':selected,'failure':failure,'training_complete':bool(selected and selected['training_complete']),'evaluation':None if eval_receipt is None else {k:eval_receipt[k] for k in ['exit','stop','elapsed_ns','owned_cleanup_remaining','final_integrity']},'final_integrity':integrity,'automatic_retry':False}
        durable(root/'CAMPAIGN_TERMINAL.json',terminal)
        print(json.dumps(terminal),flush=True)
    return 0 if failure is None and eval_receipt and eval_receipt['exit']==0 and not eval_receipt['stop'] and integrity else 1

def launch(plan_path,digest,root):
    p=json.loads(Path(plan_path).read_text());validate(p);assert sha(plan_path)==digest
    root=Path(root);root.mkdir()
    assert all(Path(a['prompt']['path']).stat().st_size==a['bytes']<=512 for a in p['output_arms']),'complete question length/pin'
    assert Path(p['keys']['path']).stat().st_size==4096
    pins=collect_pins(p)+[{'path':str(plan_path),'sha256':digest}]
    assert all(sha(x['path'])==x['sha256'] for x in pins)
    lock=open(p['gpu_lock'],'a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    d=load_module('outer_supervisor',p['supervisor']['path']);assert not d.gpu_status(),'foreign GPU compute before campaign'
    # Exact binary identities, not aggregate display utilization, define competing work.
    competing=[]
    for proc in Path('/proc').glob('[0-9]*'):
        try:
            argv=proc.joinpath('cmdline').read_bytes().split(b'\0')
            if argv and argv[0].decode(errors='replace') in [p['cuda_binary']['path'],p['host_binary']['path']]:competing.append(int(proc.name))
        except OSError:pass
    assert not competing,f'duplicate native process {competing}'
    start=time.monotonic_ns();end=start+p['campaign_cap_ns']
    durable(root/'LAUNCH_ONCE.json',{'UTC':utc(),'PID':os.getpid(),'plan_sha256':digest,'start_monotonic_ns':start,'deadline_monotonic_ns':end,'deadline_UTC':(datetime.datetime.now(datetime.timezone.utc)+datetime.timedelta(seconds=p['campaign_cap_ns']/NS)).isoformat(),'fresh_once':True,'no_competing_native':True,'GPU_preflight':[],'authority':p['authority']})
    meta={x['path']:(Path(x['path']).stat().st_size,Path(x['path']).stat().st_mtime_ns) for x in pins}
    check=lambda:all(Path(path).exists() and (Path(path).stat().st_size,Path(path).stat().st_mtime_ns)==v for path,v in meta.items())
    sup=d.Supervisor(root,check)
    r=sup.run(['python3',str(Path(__file__).resolve()),'inner',str(plan_path),digest,str(root),str(start),str(end)],end,'campaign',{'RAYON_NUM_THREADS':'4'},gpu=True)
    assert all(sha(x['path'])==x['sha256'] for x in pins)
    durable(root/'FINAL_CLEANUP.json',{'UTC':utc(),'owned_remaining':r['owned_cleanup_remaining'],'GPU':r['GPU_postflight'],'final_integrity':r['final_integrity'],'elapsed_ns':time.monotonic_ns()-start,'cap_ns':p['campaign_cap_ns']})
    return 0 if r['exit']==0 and not r['stop'] and not r['owned_cleanup_remaining'] else 1

if __name__=='__main__':
    if sys.argv[1]=='inner':sys.exit(inner(sys.argv[2],sys.argv[3],sys.argv[4],int(sys.argv[5]),int(sys.argv[6])))
    assert sys.argv[1]=='launch' and len(sys.argv)==5
    sys.exit(launch(sys.argv[2],sys.argv[3],sys.argv[4]))
