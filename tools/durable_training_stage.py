"""Prepare one pinned native stage command. Never launches a model or retries a stage.

The campaign envelope is external and explicit. Native code authenticates/cold-loads
its parent and pending frontier before ingress; this owner binds source order and
emits the exact argument vector for an independently guarded local executor.
"""
from pathlib import Path
import hashlib,json,sys

COMMAND='stage-adaptive-family-local-arrival-held-v1'
HEADER='complete-language-stage-v1'

def sha(path):
    with Path(path).open('rb')as f:return hashlib.file_digest(f,'sha256').hexdigest()
def checked(pin):
    assert sha(pin['path'])==pin['sha256'],'pinned input identity';return Path(pin['path'])
def table(path,head):
    text=Path(path).read_text();lines=text.splitlines();assert text.endswith('\n') and lines[0]==head
    out={}
    for l in lines[1:]:
        k,v=l.split('\t');assert k and v and k not in out;out[k]=v
    return out

def validate_source(plan):
    data=checked(plan['train']).read_bytes();meta=json.loads(checked(plan['source_order_manifest']).read_text())
    assert len(data)==plan['bytes']==73580 and plan['cells']==4*len(data)==294320
    assert plan['records']==136 and plan['passes']==1 and plan['horizon']==524288
    at=0;ids=[]
    for row in meta['records']:
        n=row['framed_bytes'];b=data[at:at+n];assert len(b)==n and b.endswith(b'\n') and hashlib.sha256(b).hexdigest()==row['framed_sha256']
        assert row['role']=='originaltrain';ids.append(row['row']);at+=n
    assert at==len(data) and ids==plan['record_ids'] and len(ids)==136
    prefix=checked(plan['legacy21_source_prefix']).read_bytes();assert len(prefix)==11435 and data.startswith(prefix)
    assert plan['source_framing']=='complete-Q-LF-A-LF-v1'
    return data

def prepare(plan,number,control_path,output_path,parent_folder=None):
    assert 1<=number<=8 and plan['campaign_cap_ns']==13_300_000_000_000
    assert isinstance(plan['execution_authorized'],bool) # preparation alone never launches, under either authority state
    assert plan['cooperative_stop_ns']==1_400_000_000_000 and plan['hard_training_guard_ns']==1_500_000_000_000
    assert plan['automatic_retry'] is False and plan['automatic_resume_after_hard_kill'] is False
    validate_source(plan);binary=checked(plan['cuda_binary']);cuts=checked(plan['diagnostic_cuts']);checked(plan['source_custody'])
    expected_id=lambda n:f"{plan['campaign_id']}-s{n:02}"
    cp='-';cph='-';receipt='-';rh='-';previous='-';previous_sha='-';accepted=0
    if number==1:assert parent_folder is None,'new campaign starts once, not from abandoned a25 tail'
    else:
        assert parent_folder is not None
        folder=Path(parent_folder);rp=folder/'STAGE_COMPLETE.tsv';r=table(rp,'complete-language-stage-complete-v1')
        terminal=json.loads((folder/'STAGE_GUARD_TERMINAL.json').read_text())
        assert terminal['exit']==0 and terminal['stop'] is None and not terminal['owned_cleanup_remaining'],'hard-killed/failed stage stops campaign, no replay'
        assert r['stage_id']==expected_id(number-1) and r['training_complete']=='false'
        assert r['source_sha256']==plan['train']['sha256'] and r['execution_binary_sha256']==plan['cuda_binary']['sha256']
        assert r['native_source_identity']==plan['source'] and r['backend']=='cuda-observed-epoch-device0' and r['source_framing']==plan['source_framing']
        cp=r['checkpoint'];cph=r['checkpoint_sha256'];assert sha(cp)==cph
        accepted=int(r['accepted']);published=int(r['published']);pending=int(r['pending']);assert accepted==published+pending==int(r['next_unread'])
        assert int(r['global_epochs'])*10==published and 0<=pending<10 and accepted>int(r['accepted_at_start'])
        receipt=str(rp);rh=sha(rp);previous=plan['train']['path'];previous_sha=plan['train']['sha256']
    assert not Path(output_path).exists(),'native output directory must be new'
    snapshots=[n for n in plan['snapshot_offsets'] if n>=accepted]
    values={'stage_id':expected_id(number),'mode':'fresh'if number==1 else'resume','global_accepted':str(accepted),'next_unread':str(accepted),
        'parent_checkpoint':cp,'parent_checkpoint_sha256':cph,'parent_receipt':receipt,'parent_receipt_sha256':rh,
        'previous_source':previous,'previous_source_sha256':previous_sha,'source_sha256':plan['train']['sha256'],'source_bytes':str(plan['bytes']),
        'stop_accepted':'-','cooperative_stop_ns':str(plan['cooperative_stop_ns']),'hard_training_guard_ns':str(plan['hard_training_guard_ns']),
        'snapshot_offsets':','.join(map(str,snapshots))or'-','native_source_identity':plan['source'],'execution_binary_sha256':plan['cuda_binary']['sha256'],
        'source_framing':plan['source_framing'],'source_order_manifest':plan['source_order_manifest']['path'],'source_order_manifest_sha256':plan['source_order_manifest']['sha256']}
    text=HEADER+'\n'+''.join(f'{k}\t{v}\n'for k,v in values.items());path=Path(control_path)
    with path.open('x')as f:f.write(text)
    return [str(binary),'complete-language',COMMAND,'cuda-observed-epoch-device0',plan['train']['path'],plan['train']['sha256'],str(cuts),plan['diagnostic_cuts']['sha256'],str(plan['horizon']),str(plan['cells']),str(plan['cells']//10),str(output_path),str(path),sha(path)]

if __name__=='__main__':
    assert len(sys.argv) in (5,6),'PLAN STAGE CONTROL_PATH NEW_NATIVE_OUTPUT [CLEAN_PARENT_FOLDER]'
    p=json.loads(Path(sys.argv[1]).read_text());argv=prepare(p,int(sys.argv[2]),sys.argv[3],sys.argv[4],sys.argv[5]if len(sys.argv)==6 else None)
    print(json.dumps({'prepared_only':True,'model_launched':False,'argv':argv,'independent_hard_guard_required_ns':p['hard_training_guard_ns']}))
