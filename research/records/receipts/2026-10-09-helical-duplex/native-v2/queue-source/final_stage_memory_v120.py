"""Owned oneshot completion event, then final aggregate CPU acceptance; no polling."""
from pathlib import Path
import fcntl, hashlib, json, os, re, signal, subprocess, sys, time
ROOT=Path(__file__).resolve().parent
cfgpath=Path(sys.argv[1]).resolve();cfg=json.loads(cfgpath.read_text())
unit=cfg['scope_unit']+'.service';label=cfg['label']
assert re.fullmatch(r'holonics-prune-admission-[a-z0-9-]+',cfg['scope_unit'])
assert re.fullmatch(r'[a-z0-9-]+',label)
# The recovered native-build allocation is separate from the one-CPU runtime policy.
# Native builds keep the same aggregate accounting and final acceptance; no child-only reading.
native_build=cfg.get('stage_kind')=='native_build'
wall_policy=65_000_000_000 if native_build else (245_000_000_000 if cfg.get('explicit_user_workload_duration_authorization') else 60_000_000_000)
cpu_policy=128_000_000 if native_build else (245_000_000 if cfg.get('explicit_user_workload_duration_authorization') else 17_000_000)
assert int(cfg.get('thread_budget',1))==(8 if native_build else 1)
cap_ns=int(cfg['projection_ns']);assert 0<cap_ns<=wall_policy
cpu_limit=int(cfg['aggregate_cpu_limit_us']);assert 0<cpu_limit<=cpu_policy
group_bytes=int(cfg['group_memory_max_bytes']);assert 2**28<=group_bytes<=2**33
assert group_bytes<=2**32 or cfg.get('explicit_user_8GiB_authorization')==True
fault=cfg.get('synthetic_cleanup_fault')
assert not fault or (not cfg.get('scientific_job') and fault in ('show','stop','interrupt'))
def ident(p):
 p=Path(p);h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(2**20):h.update(b)
 return {'sha256':h.hexdigest(),'bytes':p.stat().st_size}
def save(p,v):
 with p.open('x') as f:json.dump(v,f,indent=2);f.write('\n')
def show():
 r=subprocess.run(['systemctl','--user','show',unit,'--no-pager',
  '-p','LoadState','-p','ActiveState','-p','SubState','-p','Result',
  '-p','ExecMainStatus','-p','ControlGroup','-p','CPUUsageNSec',
  '-p','MemoryPeak','-p','TasksCurrent','-p','Description','-p','InvocationID'],
  capture_output=True,text=True,timeout=2)
 return dict(x.split('=',1) for x in r.stdout.splitlines() if '=' in x)
before=show();assert before.get('LoadState')=='not-found',('unit already exists; left untouched',before)
LEASE=Path('/home/b/Workspaces/holonics/.local/codex-lean-run.lock')
def interrupt(s,f):raise KeyboardInterrupt(str(s))
for s in (signal.SIGINT,signal.SIGTERM,signal.SIGHUP):signal.signal(s,interrupt)
signal.pthread_sigmask(signal.SIG_BLOCK,{signal.SIGUSR1})
mask=signal.pthread_sigmask(signal.SIG_BLOCK,{signal.SIGINT,signal.SIGTERM,signal.SIGHUP})
fd=None
try:
 assert LEASE.is_absolute() and LEASE.is_file(), 'exact existing common lease absent'
 fd=os.open(str(LEASE),os.O_RDONLY|os.O_CLOEXEC);opened=os.fstat(fd);resolved=LEASE.resolve(strict=True);st=resolved.stat()
 assert (opened.st_dev,opened.st_ino)==(st.st_dev,st.st_ino), 'lease FD/path mismatch'
 owner={'requested_absolute_path':str(LEASE),'resolved_absolute_path':str(resolved),
  'opened_fd_path':os.readlink('/proc/self/fd/'+str(fd)),'device':opened.st_dev,'inode':opened.st_ino,
  'opened_readonly':True,'single_nonblocking_acquisition':True,'controller_PID':os.getpid(),
  'start_ticks':Path('/proc/self/stat').read_text().rpartition(')')[2].split()[19],'fd':fd}
 try:fcntl.flock(fd,fcntl.LOCK_EX|fcntl.LOCK_NB)
 except BlockingIOError:
  owner.update(acquired=False,status='deferred_lock_busy');save(ROOT/(label+'.external-lease.json'),owner)
  save(ROOT/(label+'.final.json'),{'passed':False,'deferred_lock_busy':True,'label':label,'scientific_job':False,'unit_launched':False})
  os.close(fd);fd=None;print(json.dumps({'label':label,'deferred_lock_busy':True}));raise SystemExit(0)
 st=LEASE.stat();assert (opened.st_dev,opened.st_ino)==(st.st_dev,st.st_ino), 'lease object changed'
 owner.update(acquired=True,status='held_by_external_owner');save(ROOT/(label+'.external-lease.json'),owner)
except BaseException:
 if fd is not None:os.close(fd);fd=None
 signal.pthread_sigmask(signal.SIG_SETMASK,mask)
 raise
description='Owned holonics admission '+label+' '+os.urandom(16).hex()
argv=['systemd-run','--user','--quiet','--unit='+unit,'--description='+description,
 '--service-type=oneshot','--remain-after-exit',
 '-p','MemoryMax='+str(group_bytes),'-p','MemorySwapMax=0',
 '-p','TimeoutStartSec='+str(cap_ns//1000)+'us','-p','TimeoutStopSec=1s',
 '-p','KillMode=control-group','-p','SendSIGKILL=yes',
 '/usr/bin/python3',str(ROOT/'leased_stage_memory_v120.py'),str(cfgpath),json.dumps(owner)]
start=time.monotonic_ns();run=None;error=None;properties={};result={};cleanup={};accepted={}
try:
 # Keep catchable signals blocked while the lease is owned, closing cleanup-entry races.
 # Cancellation is recorded at completion of the fixed bounded unit, before acceptance.
 try:run=subprocess.run(argv,capture_output=True,text=True,timeout=cap_ns/1_000_000_000)
 except subprocess.TimeoutExpired:error='outer fixed wall projection exceeded'
 properties=show()
 if properties.get('Description')!=description:raise RuntimeError('owned unit identity not confirmed; no stop of unrelated unit')
 if error:
  subprocess.run(['systemctl','--user','stop',unit],capture_output=True,text=True,timeout=2)
  properties=show()
 wall=time.monotonic_ns()-start
 publication=ROOT/(label+'.publication.json');lease=ROOT/(label+'.lease-identity.json')
 provisional=json.loads(publication.read_text()) if publication.exists() else {}
 lease_row=json.loads(lease.read_text()) if lease.exists() else {}
 raw_cpu=properties.get('CPUUsageNSec','')
 cpu_ns=int(raw_cpu) if raw_cpu.isdigit() else None
 quiescent=properties.get('ControlGroup')=='' and properties.get('TasksCurrent')=='[not set]'
 completed=properties.get('SubState') in ('exited','dead','failed')
 passed=bool(run and run.returncode==0 and not error and completed and quiescent
  and properties.get('Result')=='success' and properties.get('ExecMainStatus')=='0'
  and wall<=cap_ns and cpu_ns is not None and cpu_ns<=cpu_limit*1000
  and provisional.get('outcome',{}).get('provisional_passed'))
 files=[p for p in ROOT.glob(label+'.*') if p.is_file()]
 result={'passed':passed,'label':label,'scientific_job':bool(cfg.get('scientific_job',False)),
  'deferred_lock_busy':lease_row.get('status')=='deferred_lock_busy',
  'final_CPU_ns':cpu_ns,'CPU_reading_grain_ns':1000,'aggregate_CPU_limit_us':cpu_limit,
  'final_CPU_source':'systemd retained oneshot CPUUsageNSec after all group processes exit',
  'CPU_kernel_hard_total_limit':False,'sampled_stop_margin_us':cfg['aggregate_cpu_stop_margin_us'],
  'aggregate_CPU_within_limit':cpu_ns is not None and cpu_ns<=cpu_limit*1000,
  'no_overshoot_accepted':not passed or (cpu_ns is not None and cpu_ns<=cpu_limit*1000),
  'wall_ns':wall,'projection_ns':cap_ns,'wall_source':'external monotonic_ns through final property read',
  'quiescent':quiescent,'completion_event':'oneshot start job completed; no polling',
  'unit_properties':properties,'outer_error':error,'unit_start_exit':run.returncode if run else None,
  'unit_start_stdout':run.stdout if run else '', 'unit_start_stderr':run.stderr if run else '',
  'config':ident(cfgpath),'receipt_pins':{str(p):ident(p) for p in files},
  'launcher_outside_native_group':True,'lease_owner_outside_capped_group':True,
  'lease_held_through_final_CPU_read_and_publication':True}
 save(ROOT/(label+'.final.json'),{**result,'passed':False,'stage_passed_before_cleanup':result['passed'],'requires_cleanup_acceptance':True})
except BaseException as e:
 if not result:
  result={'passed':False,'label':label,'error_type':type(e).__name__,'error':str(e),'scientific_job':False,'lease_still_held':True}
  save(ROOT/(label+'.final.json'),result)
finally:
 # Catchable cleanup signals cannot close the lease owner. Unknown cleanup retains it.
 signal.pthread_sigmask(signal.SIG_BLOCK,{signal.SIGINT,signal.SIGTERM,signal.SIGHUP})
 injected=False;retained=0
 while True:
  try:
   if fault=='show' and not injected:injected=True;raise subprocess.TimeoutExpired('injected cleanup show',2)
   if fault=='interrupt' and not injected:injected=True;raise KeyboardInterrupt('injected cleanup interruption')
   current=show()
   if current.get('Description')==description:
    if fault=='stop' and not injected:injected=True;raise subprocess.TimeoutExpired('injected cleanup stop',2)
    stopped=subprocess.run(['systemctl','--user','stop',unit],capture_output=True,text=True,timeout=2)
    assert stopped.returncode==0, 'owned stop failed'
    after=show();assert after.get('ControlGroup')=='' and after.get('TasksCurrent')=='[not set]', 'owned quiescence unconfirmed'
    cleanup={'owned_unit':unit,'stop_exit':stopped.returncode,'final_state':after,
     'no_unrelated_units_stopped':True,'accounting_captured_before_stop':bool(result)}
   elif current.get('LoadState')=='not-found' and current.get('ControlGroup')=='':
    cleanup={'owned_unit':unit,'stop_exit':0,'final_state':current,'no_owned_unit_remains':True,'no_unrelated_units_stopped':True}
   else:raise RuntimeError('unit identity or quiescence unknown; unrelated unit untouched')
   break
  except BaseException as cleanup_error:
   retained+=1
   event={'event':'lease_retained_until_recovery_event','label':label,'unit':unit,
    'controller_PID':os.getpid(),'start_ticks':owner['start_ticks'],'lease_fd':fd,
    'lease_device':owner['device'],'lease_inode':owner['inode'],
    'error_type':type(cleanup_error).__name__,'error':str(cleanup_error),
    'catchable_cleanup_signals_blocked':True,'recovery_signal':'SIGUSR1','no_polling':True}
   # Diagnostic publication failure must not terminate the still-owning process.
   try:save(ROOT/(label+'.lease-retained-'+str(retained)+'.json'),event)
   except BaseException:pass
   try:print(json.dumps(event),flush=True)
   except BaseException:pass
   signal.sigwait({signal.SIGUSR1})
 cleanup.update(catchable_cleanup_signals_blocked=True,lease_retention_events=retained,
  pending_catchable_signals=[s.name for s in signal.sigpending() if s in (signal.SIGINT,signal.SIGTERM,signal.SIGHUP)])
 save(ROOT/(label+'.unit-cleanup.json'),cleanup)
 if fd is not None:
  # Scientific descendants are gone before publication and remain gone before release.
  assert result.get('quiescent') or cleanup.get('final_state',{}).get('ControlGroup')=='', 'owned unit quiescence unconfirmed'
  accepted={'passed':bool(result.get('passed') and cleanup.get('stop_exit')==0 and not retained and not cleanup['pending_catchable_signals']),
   'final_CPU_receipt':ident(ROOT/(label+'.final.json')),'cleanup_receipt':ident(ROOT/(label+'.unit-cleanup.json')),
   'lease_still_held':True,'scientific_job':bool(cfg.get('scientific_job',False)),
   'requires_matching_release_receipt':True}
  save(ROOT/(label+'.acceptance.json'),accepted)
  fcntl.flock(fd,fcntl.LOCK_UN);os.close(fd);fd=None
  save(ROOT/(label+'.release.json'),{'released_after_final_publication_and_owned_unit_cleanup':True,
   'quiescence_confirmed':True,'external_controller_PID':os.getpid(),'monotonic_ns':time.monotonic_ns()})
print(json.dumps({**{k:result.get(k) for k in ('label','deferred_lock_busy','final_CPU_ns','wall_ns','quiescent','outer_error')},'passed':accepted.get('passed',False)}))
if not accepted.get('passed'):raise SystemExit(125)
