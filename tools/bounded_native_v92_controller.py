"""One pinned repaired gate: one absolute attempt window, no blocking child waits."""
import time
START = time.monotonic_ns()
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import signal
import subprocess
import sys
from rate_guard_v92 import training_projection, validate_v92_budget

config_path = Path(sys.argv[1])
config_raw = config_path.read_bytes()
assert hashlib.sha256(config_raw).hexdigest() == sys.argv[2]
c = json.loads(config_raw)
validate_v92_budget(c)
TOTAL = c['total_reservation_ns']
assert c.get('model_budget_status') == 'APPROVED_TRUSTED_USER_AUTHORIZATION_RECORDED', 'model budget is proposal-only'
assert c['native_remaining_ns'] >= TOTAL, 'approved native balance is insufficient'
CLEANUP = c['maximum_cleanup_ns']
END = START + TOTAL
PROCESS_END = END - CLEANUP
assert isinstance(c['argv'], list) and all(isinstance(a,str) for a in c['argv'])
assert c['total_reservation_ns'] == TOTAL
assert c['maximum_process_ns'] == TOTAL - CLEANUP
assert c['maximum_cleanup_ns'] == CLEANUP
assert c['cpus'] == 4 and c['memory_bytes'] == 8_589_934_592
root = Path(c['cwd'])
out = Path(c['output_dir'])
assert not out.exists()
out.mkdir()
allowed = sorted(os.sched_getaffinity(0))
assert len(allowed) >= 4
offset = c.get("cpu_offset", 0)
assert len(allowed) >= offset + 4
cpus = allowed[offset:offset+4]
os.sched_setaffinity(0, cpus)
resource.setrlimit(resource.RLIMIT_AS, (c['memory_bytes'], c['memory_bytes']))
env = dict(os.environ, CARGO_NET_OFFLINE='true', CARGO_BUILD_JOBS='4',
           CARGO_INCREMENTAL='0', CARGO_PROFILE_DEV_DEBUG='0',
           CARGO_PROFILE_TEST_DEBUG='0', RAYON_NUM_THREADS='1',
           RUST_TEST_THREADS='1', CARGO_TERM_COLOR='never',
           RUSTC_BOOTSTRAP='1', GIT_OPTIONAL_LOCKS='0')
env.update(c['env'])
owned = {}
groups = set()
children = []
samples = []
stop = None
gate = None
peak = 0
last_training_projection = None
alarm_fired = False

def stamp():
    from datetime import datetime, timezone
    return datetime.now(timezone.utc).isoformat()

def limits():
    resource.setrlimit(resource.RLIMIT_AS, (c['memory_bytes'], c['memory_bytes']))
    os.sched_setaffinity(0, cpus)

def processes():
    result = {}
    for p in Path('/proc').iterdir():
        if not p.name.isdigit():
            continue
        try:
            f = (p / 'stat').read_text().rsplit(')', 1)[1].split()
            result[int(p.name)] = (int(f[1]), int(f[2]), int(f[19]),
                                  int((p / 'statm').read_text().split()[1]) * os.sysconf('SC_PAGE_SIZE'))
        except (OSError, ValueError, IndexError):
            pass
    return result

def observe():
    global peak
    ps = processes()
    live = {pid: ps[pid] for pid, born in owned.items()
            if pid in ps and ps[pid][2] == born}
    changed = True
    while changed:
        changed = False
        live_groups = {item[1] for item in live.values()}
        for pid, (parent, group, born, rss) in ps.items():
            if pid in live:
                continue
            if parent in live or group in live_groups:
                owned[pid] = born
                groups.add(group)
                live[pid] = ps[pid]
                changed = True
    rss = sum(item[3] for item in live.values())
    peak = max(peak, rss)
    return live, rss

def kill_owned():
    # Only groups created/discovered from our children; never the controller's group.
    ps = processes()
    live_groups = {ps[pid][1] for pid, born in owned.items()
                   if pid in ps and ps[pid][2] == born}
    assert os.getpgrp() not in live_groups
    for group in live_groups:
        try:
            os.killpg(group, signal.SIGKILL)
        except ProcessLookupError:
            pass

def alarm(signum, frame):
    global alarm_fired
    alarm_fired = True
    kill_owned()

def spawn(argv, stdout):
    p = subprocess.Popen(argv, cwd=root, env=env, stdout=stdout,
                         stderr=subprocess.STDOUT, start_new_session=True,
                         preexec_fn=limits)
    children.append(p)
    groups.add(p.pid)
    try:
        f = Path('/proc', str(p.pid), 'stat').read_text().rsplit(')', 1)[1].split()
        owned[p.pid] = int(f[19])
    except (OSError, ValueError, IndexError):
        pass
    return p

def git_read(name, args, deadline):
    if time.monotonic_ns() >= deadline:
        raise TimeoutError('metadata deadline')
    pth = out / name
    with pth.open('xb') as f:
        p = spawn(['git', *args], f)
        while p.poll() is None and time.monotonic_ns() < deadline:
            time.sleep(.01)
        if p.poll() is None:
            kill_owned()
            raise TimeoutError('metadata deadline')
    if p.returncode:
        raise RuntimeError('git metadata failed: ' + name)
    return pth.read_text().strip()

def source_ok(prefix, deadline):
    if git_read(prefix + '-head.txt', ['rev-parse', 'HEAD'], deadline) != c['actual_head']:
        return False
    paths = git_read(prefix + '-diff.txt', ['diff', '--name-only', 'HEAD'], deadline).splitlines()
    if paths != c['tracked_modified_paths']:
        return False
    if git_read(prefix + '-untracked.txt', ['ls-files', '--others', '--exclude-standard'], deadline).splitlines() != c['untracked_paths']:
        return False
    for i in c['source_files']:
        if time.monotonic_ns() >= deadline:
            raise TimeoutError('source verification deadline')
        if hashlib.sha256(Path(i['path']).read_bytes()).hexdigest() != i['sha256']:
            return False
    return True

before = None
after = None
began = stamp()
signal.signal(signal.SIGALRM, alarm)
signal.setitimer(signal.ITIMER_REAL, max(.001, (PROCESS_END - time.monotonic_ns()) / 1e9))
log_path = out / 'gate.log'
try:
    before = source_ok('pre', PROCESS_END)
    assert before, 'preflight source mismatch'
    assert hashlib.sha256(Path(__file__).read_bytes()).hexdigest() == c['controller_sha256']
    if time.monotonic_ns() >= PROCESS_END:
        raise TimeoutError('no process window after preflight')
    launched = time.monotonic_ns()
    with log_path.open('xb') as log:
        gate = spawn(c['argv'], log)
        (out / 'started.json').open('x').write(json.dumps({
            'utc': stamp(), 'pid': gate.pid, 'source': c['custody_source'],
            'argv': c['argv'], 'process_window_ns': PROCESS_END - launched,
            'total_reservation_ns': TOTAL, 'cpus': cpus,
            'config_sha256': hashlib.sha256(config_raw).hexdigest()}, indent=2) + '\n')
        print(json.dumps({'launched': c['argv'], 'source': c['custody_source'],
                          'maximum_process_ns': PROCESS_END - launched}), flush=True)
        while gate.poll() is None:
            live, rss = observe()
            free = os.statvfs(root).f_bavail * os.statvfs(root).f_frsize
            samples.append({'elapsed_ns': time.monotonic_ns() - START,
                            'owned_rss_bytes': rss, 'free_bytes': free})
            if c.get('training_progress_log'):
                progress_path = Path(c['training_progress_log'])
                if progress_path.exists():
                    with progress_path.open('rb') as progress_file:
                        progress_file.seek(max(0, progress_path.stat().st_size - 1048576))
                        last_training_projection = training_projection(
                            progress_file.read().decode(errors='replace'),
                            epochs=c['training_epochs'], phase_ns=c['training_phase_ns'])
            if last_training_projection and last_training_projection['exceeds_cap']:
                stop = 'training_projection_exceeds_fixed_phase_cap'
            elif alarm_fired or time.monotonic_ns() >= PROCESS_END:
                stop = 'process_deadline'
            elif rss > c['memory_bytes']:
                stop = 'aggregate_rss_ceiling'
            elif free < 536_870_912:
                stop = 'disk_floor'
            elif log_path.stat().st_size > 134_217_728:
                stop = 'log_ceiling'
            if stop:
                kill_owned()
                break
            time.sleep(.05)
        if alarm_fired:
            stop = stop or 'process_deadline'
except BaseException as error:
    stop = stop or type(error).__name__ + ': ' + str(error)
finally:
    signal.setitimer(signal.ITIMER_REAL, 0)
    cleanup_start = time.monotonic_ns()
    cleanup_end = min(END, cleanup_start + CLEANUP)
    live, _ = observe()
    if live:
        kill_owned()
    # One cleanup deadline, with nonblocking poll only. No p.wait(), pipe thread or stacked grace.
    while live and time.monotonic_ns() < cleanup_end:
        for p in children:
            p.poll()
        live, _ = observe()
        if live:
            time.sleep(.01)
    for p in children:
        p.poll()
    remaining, _ = observe()
    if remaining:
        kill_owned()
        stop = stop or 'cleanup_uncertain'
    if time.monotonic_ns() < END:
        try:
            after = source_ok('post', END)
        except BaseException as error:
            stop = stop or 'postflight_' + type(error).__name__
    if not after:
        stop = stop or 'source_postflight_unconfirmed'
    for p in children:
        p.poll()
    remaining, _ = observe()
    if remaining:
        kill_owned()
        stop = stop or 'cleanup_uncertain_after_metadata'
    elapsed = time.monotonic_ns() - START
    if elapsed > TOTAL:
        stop = stop or 'attempt_deadline_overrun'
    raw = log_path.read_bytes() if log_path.exists() else b''
    result = {'started_utc': began, 'ended_utc': stamp(), 'config': c,
              'config_sha256': hashlib.sha256(config_raw).hexdigest(),
              'wall_ns_through_receipt_preparation': elapsed,
              'total_reservation_ns': TOTAL, 'maximum_process_ns': c['maximum_process_ns'],
              'effective_process_window_ns': PROCESS_END - launched if gate else None,
              'cleanup_wall_ns': time.monotonic_ns() - cleanup_start,
              'cleanup_deadline_ns_from_start': cleanup_end - START,
              'gate_exit': gate.returncode if gate else None, 'stop': stop,
              'source_preflight': before, 'source_postflight': after,
              'owned_cleanup_remaining': list(remaining),
              'owned_cleanup_scope': 'initial child groups and identity-tracked discovered descendants',
              'peak_owned_rss_bytes': peak, 'cpu_affinity': cpus,
              'training_rate_guard_last': last_training_projection,
              'log_sha256': hashlib.sha256(raw).hexdigest(), 'log_bytes': len(raw),
              'gate_lines': re.findall(r'^gate .*', raw.decode(errors='replace'), re.M),
              'native_experiment_jobs': 1, 'native_remaining_ns_before': c['native_remaining_ns'],
              'original_180s_step_closed_unchanged': True}
    (out / 'control.json').open('x').write(json.dumps(result, indent=2) + '\n')
    (out / 'resources.json').open('x').write(json.dumps(samples) + '\n')
    landing = {'utc': stamp(), 'charged_wall_ns_through_primary_receipts': time.monotonic_ns() - START,
               'reservation_ns': TOTAL, 'overrun_ns': max(0, time.monotonic_ns() - END),
               'controller_pid': os.getpid()}
    (out / 'landing.json').open('x').write(json.dumps(landing, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ['gate_exit', 'stop', 'gate_lines',
                                           'source_postflight', 'owned_cleanup_remaining']}), flush=True)
    print(json.dumps(landing), flush=True)
    sys.exit(0 if gate and gate.returncode == 0 and not stop and not remaining
             and landing['charged_wall_ns_through_primary_receipts'] <= TOTAL else 1)
