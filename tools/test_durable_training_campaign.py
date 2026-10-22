"""Synthetic controller controls only: no native model or dataset execution."""
from pathlib import Path
import copy,hashlib,json,os,tempfile,time,types,unittest
from unittest.mock import patch
import durable_training_campaign as c
import durable_training_stage as stage

def base_plan():
    pin={'path':'not-executed','sha256':'0'*64}
    arms=[{'id':name,'policy':'native','prompt':dict(pin),'bytes':size,'cold':False} for name,size in zip(['native-2348','context-zero-2348','native-6469','context-zero-6469','dev-3001','dev-3023','dev-3028','dev-3050'],[43,43,52,52,302,197,248,141])]
    return {'execution_authorized':True,'campaign_id':'fake-controller','source':'fake-source','campaign_cap_ns':13300*c.NS,'max_native_stages':8,'hard_training_guard_ns':1500*c.NS,'cooperative_stop_ns':1400*c.NS,'automatic_retry':False,'automatic_resume_after_hard_kill':False,'records':136,'bytes':73580,'cells':294320,'horizon':524288,'output_cells_per_arm':512,'output_shared_cap_ns':500*c.NS,'output_arms':arms,'sample_command':'sample-prepared-retained-full-question-v1','train':dict(pin),'keys':dict(pin),'host_binary':dict(pin),'cuda_binary':dict(pin),'stage_preparer':dict(pin),'output_pool':dict(pin),'stage_slots':[{'stage':i,'training_hard_ns':1500*c.NS,'cooperative_native_ns':1400*c.NS,'receipts_ns':90*c.NS,'cleanup_ns':10*c.NS,'output_cap_ns':500*c.NS if i==8 else 0,'total_cap_ns':2100*c.NS if i==8 else 1600*c.NS} for i in range(1,9)]}

def fixture(root):
    p=base_plan();p['execution_authorized']=True;p['sample_command']='sample-prepared-retained-full-question-v1'
    data=root/'fake-pin';data.write_bytes(b'controller-control-only');pin={'path':str(data),'sha256':c.sha(data)}
    def replace(x):
        if isinstance(x,dict):
            if 'path' in x and 'sha256' in x:x.update(pin)
            else:
                for v in x.values():replace(v)
        elif isinstance(x,list):
            for v in x:replace(v)
    replace(p);p['supervisor']=pin;p['authority']=pin;p['output_pool']=pin
    return p

def checkpoint(path,accepted,pending):
    published=accepted-pending;native=b'fake-native-not-admitted';crib=f'observed-unplaced-crib-v1\n{published} {published} 0\n-\n'.encode()
    pend=('observed-stream-pending-v4 retained-fibre-v1 family-local-retained-return-v1 bounded-subquantum20-v1 local-receiving-held-map-v1 1 '+str(published)+' '+str(pending)+(' 0'*pending)+'\n').encode();prov=b'fake controller only\n'
    body=native+crib+pend+prov
    path.write_bytes(b'solenoidal-alpha-family-local-subquantum20-v1\n'+f'524288 {len(native)} {len(crib)} {len(pend)} {len(prov)}\n'.encode()+body)

class Campaign(unittest.TestCase):
    def test_actual_fixed_guard_stops_fake_child_and_cleans_owned_group(self):
        module=c.load_module('real_controller_guard',os.environ['HOLONICS_CAMPAIGN_SUPERVISOR'])
        with tempfile.TemporaryDirectory() as tmp:
            supervisor=module.Supervisor(Path(tmp),lambda:True)
            r=supervisor.run(['python3','-c','import time;time.sleep(2)'],time.monotonic_ns()+150000000,'fake-deadline',{},gpu=False)
            self.assertEqual(r['stop'],'hard_phase_elapsed_deadline');self.assertFalse(r['owned_cleanup_remaining'])
            self.assertLess(r['elapsed_ns'],1000000000)
    def test_fixed_caps_and_explicit_command(self):
        p=base_plan();p.update(execution_authorized=True,sample_command='sample-prepared-retained-full-question-v1')
        self.assertTrue(c.validate(p))
        for key,value in [('campaign_cap_ns',13301*c.NS),('automatic_retry',True),('cooperative_stop_ns',1499*c.NS)]:
            changed=copy.deepcopy(p);changed[key]=value
            with self.assertRaises(AssertionError):c.validate(changed)
        op=c.output_plan(p,{'path':'fixed','sha256':'a'*64},500*c.NS)
        self.assertEqual(len(op['arms']),8);self.assertEqual(op['sample_command'],p['sample_command'])
        self.assertEqual([a['bytes'] for a in op['arms'][-4:]],[302,197,248,141])
    def test_actual_pending_shape_and_zero_selection(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);folder=root/'stage-01/native';folder.mkdir(parents=True)
            c.durable(folder/'STAGE_GUARD_TERMINAL.json',{'exit':0})
            cp=folder/'stage.state';checkpoint(cp,13,3)
            latest={'accepted':13,'published':10,'pending':3,'checkpoint':{'path':str(cp),'sha256':c.sha(cp)}}
            snap=folder/'snapshot-000010.state';checkpoint(snap,10,0)
            c.durable(snap.with_suffix('.json'),{'accepted':10,'published':10,'pending':0,'sha256':c.sha(snap)})
            before=cp.read_bytes();chosen=c.choose_output(root,latest,524288)
            self.assertEqual(chosen['accepted'],10);self.assertEqual(cp.read_bytes(),before)
            cp.write_bytes(before+b'corrupt')
            with self.assertRaises(AssertionError):c.checkpoint_shape(cp,13,524288)
    def run_fake(self,fail=None):
        with tempfile.TemporaryDirectory() as tmp:
            temp=Path(tmp);p=fixture(temp);plan=temp/'plan.json';c.durable(plan,p);root=temp/'run';root.mkdir()
            depths=[35003,70006,105009,140002,175005,210008,245001,280004];calls=[];prior=0
            def prepare(p,n,control,native,parent):
                nonlocal prior
                if n==1:self.assertIsNone(parent)
                else:
                    r=stage.table(parent/'STAGE_COMPLETE.tsv','complete-language-stage-complete-v1')
                    self.assertEqual(int(r['accepted']),depths[n-2]);self.assertTrue((parent/'STAGE_GUARD_TERMINAL.json').exists())
                control.write_text('fake only\n');return ['fake-native',str(n),str(native)]
            class Supervisor:
                def __init__(self,folder,check):self.folder=folder;self.check=check
                def run(self,argv,deadline,name,env,gpu=False):
                    nonlocal prior
                    calls.append((name,argv,deadline,gpu))
                    terminal={'exit':1 if name=='training' and int(argv[1])==fail else 0,'stop':None,'owned_cleanup_remaining':[],'GPU_postflight':[],'final_integrity':self.check(),'elapsed_ns':1}
                    if name=='training':
                        n=int(argv[1]);native=Path(argv[2]);native.mkdir();end=depths[n-1];published=end//10*10
                        cp=native/'stage.state';checkpoint(cp,end,end-published)
                        fields={'stage_id':f"{p['campaign_id']}-s{n:02}",'accepted':str(end),'published':str(published),'pending':str(end-published),'next_unread':str(end),'accepted_at_start':str(prior),'global_epochs':str(published//10),'source_sha256':p['train']['sha256'],'native_source_identity':p['source'],'execution_binary_sha256':p['cuda_binary']['sha256'],'backend':'cuda-observed-epoch-device0','cold_exact':'true','flush':'false','checkpoint':str(cp),'checkpoint_sha256':c.sha(cp),'training_complete':'false','elapsed_ns':'1'}
                        (native/'STAGE_COMPLETE.tsv').write_text('complete-language-stage-complete-v1\n'+''.join(k+'\t'+v+'\n'for k,v in fields.items()))
                        snap=native/f'snapshot-{published:06}.state';checkpoint(snap,published,0)
                        c.durable(snap.with_suffix('.json'),{'accepted':published,'published':published,'pending':0,'sha256':c.sha(snap)})
                        prior=end
                    return terminal
            mods={'campaign_supervisor':types.SimpleNamespace(Supervisor=Supervisor),'campaign_preparer':types.SimpleNamespace(prepare=prepare,table=stage.table)}
            start=time.monotonic_ns()
            with patch.object(c,'load_module',side_effect=lambda name,path:mods[name]),patch.object(c,'epoch_summary',return_value={'fake':True}):
                exit=c.inner(plan,c.sha(plan),root,start,start+13300*c.NS)
            terminal=json.loads((root/'CAMPAIGN_TERMINAL.json').read_text())
            if fail:
                self.assertEqual(exit,1);self.assertEqual(len(calls),fail);self.assertEqual(len(terminal['stages']),fail-1)
                self.assertFalse((root/'FINAL_OUTPUT_PLAN.json').exists())
            else:
                self.assertEqual(exit,0);self.assertEqual(len(calls),9)
                self.assertEqual(terminal['latest_durable']['accepted'],280004)
                selected=json.loads((root/'OUTPUT_CHECKPOINT_SELECTION.json').read_text());self.assertEqual(selected['selected']['accepted'],280000)
                self.assertEqual([a['id'] for a in json.loads((root/'FINAL_OUTPUT_PLAN.json').read_text())['arms']],[a['id'] for a in p['output_arms']])
                self.assertFalse(terminal['training_complete'])
    def test_eight_clean_transitions_no_pending_replay_one_output(self):self.run_fake()
    def test_failed_stage_stops_without_retry_or_outputs(self):self.run_fake(fail=3)

if __name__=='__main__':unittest.main()
