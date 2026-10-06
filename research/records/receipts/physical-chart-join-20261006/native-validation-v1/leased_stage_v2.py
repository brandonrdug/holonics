"""In-group lifecycle; verify the external common-lease owner, which survives group OOM."""
from pathlib import Path
import hashlib,json,os,runpy,signal,sys,time
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parent
LEASE=Path('/home/b/Workspaces/holonics/.local/codex-lean-run.lock')
config_path=Path(sys.argv[1]).resolve();config=json.loads(config_path.read_text());label=config['label']
def save(name,v):
 with (ROOT/name).open('x') as f:json.dump(v,f,indent=2);f.write('\n')
def ident(p):
 p=Path(p);h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(2**20):h.update(b)
 return {'sha256':h.hexdigest(),'bytes':p.stat().st_size}
def stop(ex):
 if ex.get('quiesce'):
  ex['quiesce']();ex['child_reaped']=('child' in ex);return
 p=ex.get('child')
 if p is None or ex.get('child_reaped'):return
 try:
  ticks=Path('/proc/'+str(p.pid)+'/stat').read_text().rpartition(')')[2].split()[19]
  if ticks!=ex['child_start_ticks'] or os.getpgid(p.pid)!=p.pid:raise RuntimeError('own child identity changed')
  os.killpg(p.pid,signal.SIGKILL)
 except (FileNotFoundError,ProcessLookupError):pass
 p.wait();ex['child_reaped']=True
def interrupt(s,f):raise KeyboardInterrupt(str(s))
for s in [signal.SIGINT,signal.SIGTERM,signal.SIGHUP]:signal.signal(s,interrupt)
threads=int(config.get('thread_budget',1))
assert threads==(8 if config.get('stage_kind')=='native_build' else 1)
allowed=sorted(os.sched_getaffinity(0));assert len(allowed)>=threads
os.sched_setaffinity(0,set(allowed[:threads]))
owner=json.loads(sys.argv[2]);ex={};outcome={};owner_verified=False
try:
 mask=signal.pthread_sigmask(signal.SIG_BLOCK,{signal.SIGINT,signal.SIGTERM,signal.SIGHUP})
 try:
  resolved=LEASE.resolve(strict=True);st=resolved.stat();pid=int(owner['controller_PID'])
  assert (st.st_dev,st.st_ino)==(owner['device'],owner['inode']), 'external lease object changed'
  ticks=Path('/proc/'+str(pid)+'/stat').read_text().rpartition(')')[2].split()[19]
  assert ticks==owner['start_ticks'], 'external lease owner identity changed'
  fdpath=Path('/proc/'+str(pid)+'/fd/'+str(owner['fd']));opened=fdpath.stat()
  assert (opened.st_dev,opened.st_ino)==(st.st_dev,st.st_ino), 'external owner FD mismatch'
  flags=int(next(x.split()[1] for x in Path('/proc/'+str(pid)+'/fdinfo/'+str(owner['fd'])).read_text().splitlines() if x.startswith('flags:')),8)
  assert flags & os.O_ACCMODE == os.O_RDONLY, 'external lease FD is not read-only'
  locks=[x.split() for x in Path('/proc/locks').read_text().splitlines()]
  assert any(x[1:4]==['FLOCK','ADVISORY','WRITE'] and x[4]==str(pid) and x[5].endswith(':'+str(st.st_ino)) for x in locks), 'external lease lock not visible'
  row={**owner,'status':'held_by_external_owner','in_group_controller_PID':os.getpid(),'verified_before_native_child':True}
  owner_verified=True;save(label+'.lease-identity.json',row)
 finally:signal.pthread_sigmask(signal.SIG_SETMASK,mask)
 sys.argv=[str(ROOT/'bounded_stage_v1.py'),str(config_path)]
 runpy.run_path(str(ROOT/'bounded_stage_v1.py'),init_globals={'EXECUTION':ex},run_name='__main__')
 seal=json.loads((ROOT/(label+'.output_seal.json')).read_text())
 if not(seal['within_projection'] and seal['inputs_unchanged'] and seal['all_outputs_present']):raise RuntimeError('bounded real stage failed')
 if config.get('acceptance_flags'):
  output=json.loads(Path(config['outputs'][0]).read_text())
  if not all(output.get(k) is v for k,v in config['acceptance_flags'].items()):raise RuntimeError('declared scientific conformance failed')
 outcome={'provisional_passed':True,'final_acceptance_requires_external_CPU_read':True,'label':label,'wall_ns':seal['wall_ns'],'peak_child_RSS_KiB':seal['peak_child_RSS_KiB'],'group_memory_peak_bytes':seal['group_memory_peak_bytes'],'original_coordinates_modified':False}
except BaseException as error:
 stop(ex);outcome={'provisional_passed':False,'final_acceptance_requires_external_CPU_read':True,'label':label,'error_type':type(error).__name__,'error':str(error),'child_launched':'child' in ex,'child_reaped':ex.get('child_reaped',False)};save(label+'.failure.json',outcome)
finally:
 if owner_verified:
  stop(ex);line=next(x[3:].lstrip('/') for x in Path('/proc/self/cgroup').read_text().splitlines() if x.startswith('0::'));cg=Path('/sys/fs/cgroup')/line
  others=[int(x) for x in (cg/'cgroup.procs').read_text().split() if int(x)!=os.getpid()]
  if others:raise RuntimeError('owned stage not quiescent')
  cpu_us=int(dict(line.split() for line in (cg/'cpu.stat').read_text().splitlines())['usage_usec'])
  if cpu_us>int(config['aggregate_cpu_limit_us']):outcome.update(provisional_passed=False,aggregate_cpu_final_guard='ceiling exceeded')
  outcome.update(aggregate_cpu_final_us=cpu_us,aggregate_cpu_limit_us=int(config['aggregate_cpu_limit_us']),CPU_kernel_hard_total_limit=False)
  files=[ROOT/(label+x) for x in ['.lease-identity.json','.memory-gate.json','.child-identity.json','.system-floor.json','.quiescence.json','.input_seal.json','.output_seal.json','.failure.json','.stdout','.stderr']]+[Path(x) for x in config['outputs']]
  publication={'lease_still_held':True,'own_group_other_PIDs':others,'outcome':outcome,'outputs':{str(f):ident(f) for f in files if f.exists()}}
  save(label+'.publication.json',publication)
  save(label+'.stage-quiescence.json',{'external_owner_still_holds_lease':True,'child_reaped':ex.get('child_reaped',False),'own_group_other_PIDs':others,'monotonic_ns':time.monotonic_ns()})
  print(json.dumps(outcome))
if not outcome.get('provisional_passed'):raise SystemExit(125)
