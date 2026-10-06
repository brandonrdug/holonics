"""One-CPU projected units; sampled stop plus external final aggregate acceptance."""
from pathlib import Path
import ctypes, hashlib, json, os, resource, signal, shutil, subprocess, sys, time
ROOT=Path(__file__).resolve().parent
WORKSPACE=ROOT.parents[2]
CAP_NS=None
GROUP_BYTES=None

class Timeval(ctypes.Structure):
    _fields_=[('tv_sec',ctypes.c_long),('tv_usec',ctypes.c_long)]
class Rusage(ctypes.Structure):
    _fields_=[('ru_utime',Timeval),('ru_stime',Timeval)]+[(n,ctypes.c_long) for n in ('ru_maxrss','ru_ixrss','ru_idrss','ru_isrss','ru_minflt','ru_majflt','ru_nswap','ru_inblock','ru_oublock','ru_msgsnd','ru_msgrcv','ru_nsignals','ru_nvcsw','ru_nivcsw')]
LIBC=ctypes.CDLL(None,use_errno=True)
LIBC.wait4.argtypes=[ctypes.c_int,ctypes.POINTER(ctypes.c_int),ctypes.c_int,ctypes.POINTER(Rusage)]
LIBC.wait4.restype=ctypes.c_int

def ident(path):
    p=Path(path);h=hashlib.sha256()
    with p.open('rb') as stream:
        while block:=stream.read(2**20):h.update(block)
    return {'sha256':h.hexdigest(),'bytes':p.stat().st_size}
def save(path,value):
    with Path(path).open('x') as out:json.dump(value,out,indent=2);out.write('\n')
def memory_events(group):
    return {k:int(v) for k,v in (line.split() for line in (group/'memory.events').read_text().splitlines())}

configpath=Path(sys.argv[1]).resolve();config=json.loads(configpath.read_text())
WORKSPACE=Path(config.get('cwd',str(WORKSPACE))).resolve()
assert WORKSPACE.is_dir() and WORKSPACE.is_relative_to(ROOT.parents[2]), 'cwd outside the owned workspace'
GROUP_BYTES=int(config.get('group_memory_max_bytes',2**32)); assert 2**28<=GROUP_BYTES<=2**32
CPU_CAP_US=int(config['aggregate_cpu_limit_us']); assert 0<CPU_CAP_US<=17_000_000
CPU_MARGIN_US=int(config['aggregate_cpu_stop_margin_us']); assert 0<CPU_MARGIN_US<CPU_CAP_US
CPU_STOP_US=CPU_CAP_US-CPU_MARGIN_US
FLOOR_KIB=int(config['system_floor_MemAvailable_KiB']); FLOOR_PERIOD_NS=10_000_000
assert FLOOR_KIB==4_194_304
CAP_NS=int(config['projection_ns']); assert 0<CAP_NS<=60_000_000_000
os.sched_setaffinity(0,{min(os.sched_getaffinity(0))})
mem={k:int(v.split()[0])*1024 for k,v in (line.split(':',1) for line in Path('/proc/meminfo').read_text().splitlines()) if v.strip().endswith('kB')}
HOST_GATE=int(config['minimum_MemAvailable_KiB'])*1024
assert HOST_GATE==8_589_934_592
assert mem['MemAvailable']>=HOST_GATE,('fresh host memory gate refused',mem['MemAvailable'],HOST_GATE)
cgline=next(line for line in Path('/proc/self/cgroup').read_text().splitlines() if line.startswith('0::'))
cgpath=Path('/sys/fs/cgroup')/cgline[3:].lstrip('/')
assert cgpath.name==config['scope_unit']+'.service',('not the declared isolated service',str(cgpath))
assert [int(x) for x in (cgpath/'cgroup.procs').read_text().split()]==[os.getpid()],('scope is not exclusive at admission',str(cgpath))
assert int((cgpath/'memory.max').read_text())==GROUP_BYTES,('required transient group cap absent',str(cgpath))
assert int((cgpath/'memory.swap.max').read_text())==0
before_events=memory_events(cgpath)
def cpu_used_us():
    return int(dict(line.split() for line in (cgpath/'cpu.stat').read_text().splitlines())['usage_usec'])
# The dedicated scope begins before the controller and retains exited children's CPU usage.
# Charge the whole scope, including preparation/monitor/cleanup; do not subtract live PID samples.
def signal_owned_scope():
    for pid in [int(x) for x in (cgpath/'cgroup.procs').read_text().split() if int(x)!=os.getpid()]:
        fd=None
        try:
            before=Path('/proc/'+str(pid)+'/stat').read_text().rpartition(')')[2].split()[19]
            fd=os.pidfd_open(pid,0)
            member=next(x[3:].lstrip('/') for x in Path('/proc/'+str(pid)+'/cgroup').read_text().splitlines() if x.startswith('0::'))
            after=Path('/proc/'+str(pid)+'/stat').read_text().rpartition(')')[2].split()[19]
            if before!=after or Path('/sys/fs/cgroup')/member!=cgpath:raise RuntimeError('owned member identity/scope changed')
            signal.pidfd_send_signal(fd,signal.SIGKILL)
        except (FileNotFoundError,ProcessLookupError):pass
        finally:
            if fd is not None:os.close(fd)
def quiesce():
    # Our subreaper adopts escaped-session descendants. Signals stay within this declared scope.
    deadline=time.monotonic_ns()+1_000_000_000
    while True:
        signal_owned_scope()
        while True:
            try:
                pid,_=os.waitpid(-1,os.WNOHANG)
                if not pid:break
            except ChildProcessError:break
        remaining=[int(x) for x in (cgpath/'cgroup.procs').read_text().split() if int(x)!=os.getpid()]
        if not remaining:return
        if time.monotonic_ns()>=deadline:raise RuntimeError('owned scope cleanup incomplete')
        time.sleep(1/1000)
assert LIBC.prctl(36,1,0,0,0)==0,('PR_SET_CHILD_SUBREAPER unavailable',ctypes.get_errno())
EXECUTION['quiesce']=quiesce
paths={Path(p).resolve() for p in config['inputs']}
paths.update([configpath,Path(__file__).resolve(),Path(shutil.which(config['argv'][0]) or config['argv'][0]).resolve()])
for directory in config.get('input_directories',[]):
    paths.update(p.resolve() for p in Path(directory).rglob('*') if p.is_file())
pin={'argv':config['argv'],'cwd':str(WORKSPACE),'inputs':{str(p):ident(p) for p in sorted(paths)},
     'source_scope':config['scope'],'CPU_count':1,'CPU_affinity':sorted(os.sched_getaffinity(0)),
     'cap_ns':CAP_NS,'projection_ns':CAP_NS,'system_floor_MemAvailable_KiB':FLOOR_KIB,'system_floor_sampling_period_ns':FLOOR_PERIOD_NS,'host_MemTotal_bytes':mem['MemTotal'],
     'host_MemAvailable_bytes':mem['MemAvailable'],'minimum_MemAvailable_bytes':HOST_GATE,'group_memory_max_bytes':GROUP_BYTES,
     'group_swap_max_bytes':0,'cgroup':str(cgpath),'memory_events_before':before_events,
     'group_cap_includes_page_cache_and_is_stricter_than_RSS':True,'sealed_before_execution':True}
pin.update(aggregate_cpu_limit_us=CPU_CAP_US,aggregate_cpu_source='dedicated cgroup cpu.stat usage_usec, including exited children and controller',aggregate_cpu_at_seal_us=cpu_used_us())
pin.update(aggregate_cpu_stop_margin_us=CPU_MARGIN_US,aggregate_cpu_stop_us=CPU_STOP_US)
expected=config['expected_inputs']; assert expected, 'exact expected input pins required'
assert {str(Path(p).resolve()) for p in expected}==set(pin['inputs'])-{str(configpath)}, 'input membership differs from the planned seal'
assert all(pin['inputs'].get(str(Path(path).resolve()))==value for path,value in expected.items()), 'expected input seal mismatch'
label=config['label'];save(ROOT/(label+'.input_seal.json'),pin)
def limits():
    signal.pthread_sigmask(signal.SIG_SETMASK, child_signal_mask)
    address_cap=int(config.get('address_space_max_bytes',GROUP_BYTES))
    resource.setrlimit(resource.RLIMIT_AS,(address_cap,address_cap))
    cpu_seconds=min(17,(CAP_NS+999_999_999)//1_000_000_000)
    resource.setrlimit(resource.RLIMIT_CPU,(cpu_seconds,cpu_seconds))
outpath=ROOT/(label+'.stdout');errpath=ROOT/(label+'.stderr')
start=time.monotonic_ns();timed_out=False;floor_breached=False;cpu_exceeded=False;floor_samples=[];next_floor=start;cpu_samples=[]
with outpath.open('x') as out,errpath.open('x') as err:
    fresh_mem={k:int(v.split()[0])*1024 for k,v in (line.split(':',1) for line in Path('/proc/meminfo').read_text().splitlines()) if v.strip().endswith('kB')}
    gate={'MemAvailable_bytes':fresh_mem['MemAvailable'],'minimum_bytes':HOST_GATE,'passed':fresh_mem['MemAvailable']>=HOST_GATE,'before_native_child':True}
    save(ROOT/(label+'.memory-gate.json'),gate)
    assert gate['passed'],('fresh prelaunch memory gate refused',gate)
    child_signal_mask=signal.pthread_sigmask(signal.SIG_BLOCK,{signal.SIGINT,signal.SIGTERM,signal.SIGHUP})
    try:
        p=subprocess.Popen(config['argv'],cwd=WORKSPACE,stdout=out,stderr=err,start_new_session=True,preexec_fn=limits)
        EXECUTION['child']=p
        child_start=Path('/proc/'+str(p.pid)+'/stat').read_text().rpartition(')')[2].split()[19]
        EXECUTION['child_start_ticks']=child_start
        save(ROOT/(label+'.child-identity.json'),{'PID':p.pid,'start_ticks':child_start,'process_group':os.getpgid(p.pid)})
    finally:
        signal.pthread_sigmask(signal.SIG_SETMASK,child_signal_mask)
    status=ctypes.c_int();usage=Rusage()
    while True:
        answer=LIBC.wait4(p.pid,ctypes.byref(status),os.WNOHANG,ctypes.byref(usage))
        if answer==p.pid:break
        if answer==-1 and ctypes.get_errno()!=4:raise OSError(ctypes.get_errno(),'wait4')
        now=time.monotonic_ns()
        group_cpu=cpu_used_us();cpu_samples.append({'since_start_ns':now-start,'usage_usec':group_cpu})
        if group_cpu>=CPU_STOP_US and not cpu_exceeded:
            cpu_exceeded=True;signal_owned_scope()
        if now>=next_floor:
            available=next(int(x.split()[1]) for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:'))
            floor_samples.append({'since_start_ns':now-start,'MemAvailable_KiB':available})
            next_floor=now+FLOOR_PERIOD_NS
            if available<FLOOR_KIB and not floor_breached:
                floor_breached=True;signal_owned_scope()
        elapsed=now-start
        if elapsed>=CAP_NS and not timed_out:
            timed_out=True;signal_owned_scope()
        # A bounded pause in the monitor only; all work shares the pinned CPU.
        time.sleep(1/1000)
wall=time.monotonic_ns()-start;code=os.waitstatus_to_exitcode(status.value)
p.returncode=code
EXECUTION['child_reaped']=True
quiesce()
remaining=[int(x) for x in (cgpath/'cgroup.procs').read_text().split() if int(x)!=os.getpid()]
assert not remaining,('own cgroup not quiescent',remaining)
save(ROOT/(label+'.system-floor.json'),{'minimum_MemAvailable_KiB':FLOOR_KIB,'sampling_period_ns':FLOOR_PERIOD_NS,'breached':floor_breached,'samples':floor_samples})
save(ROOT/(label+'.quiescence.json'),{'native_PID':p.pid,'native_exit':code,'child_reaped':True,'own_group_other_PIDs':remaining,'lease_still_held':True})
after_events=memory_events(cgpath)
produced={str(Path(p).resolve()):ident(p) for p in config['outputs'] if Path(p).exists()}
receipt={'exit':code,'wall_ns':wall,'CPU_count':1,'CPU_affinity':pin['CPU_affinity'],
         'CPU_user_us':usage.ru_utime.tv_sec*1_000_000+usage.ru_utime.tv_usec,
         'CPU_system_us':usage.ru_stime.tv_sec*1_000_000+usage.ru_stime.tv_usec,
         'CPU_reading_grain_ns':1000,'timing_source':'monotonic_ns wall; glibc wait4 integer timeval CPU',
         'peak_child_RSS_KiB':usage.ru_maxrss,'cap_ns':CAP_NS,'projection_ns':CAP_NS,
         'projection_kill_triggered':timed_out,'system_floor_breached':floor_breached,'system_floor_sampling_period_ns':FLOOR_PERIOD_NS,'group_memory_max_bytes':GROUP_BYTES,
         'group_memory_peak_bytes':int((cgpath/'memory.peak').read_text()),
         'group_memory_current_bytes':int((cgpath/'memory.current').read_text()),
         'memory_events_after':after_events,'memory_events_delta':{k:after_events[k]-before_events[k] for k in before_events},
         'stdout':ident(outpath),'stderr':ident(errpath),'outputs':produced,
         'all_outputs_present':len(produced)==len(config['outputs']),
         'inputs_unchanged':all(ident(path)==expected for path,expected in pin['inputs'].items()),
         'within_projection':code==0 and wall<=CAP_NS and not timed_out and not floor_breached,
         'sealed_before_audit':True}
receipt.update(aggregate_cpu_limit_us=CPU_CAP_US,aggregate_cpu_used_us=cpu_used_us(),aggregate_cpu_guard_triggered=cpu_exceeded,aggregate_cpu_samples=cpu_samples,aggregate_cpu_scope='whole dedicated cgroup, including controller and already-reaped descendants',CPU_kernel_hard_total_limit=False)
receipt['within_projection'] &= receipt['aggregate_cpu_used_us']<=CPU_CAP_US and not cpu_exceeded
receipt.update(aggregate_cpu_stop_margin_us=CPU_MARGIN_US,aggregate_cpu_stop_us=CPU_STOP_US,acceptance_provisional_until_external_final_CPU_read=True)
save(ROOT/(label+'.output_seal.json'),receipt)
print(json.dumps({'label':label,**receipt}))
if not(receipt['within_projection'] and receipt['inputs_unchanged'] and receipt['all_outputs_present']):
    print(errpath.read_text()[:3000],file=sys.stderr);raise SystemExit(code or 125)
