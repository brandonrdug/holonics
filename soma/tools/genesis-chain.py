#!/usr/bin/env python3
"""THE GENESIS CLIMB — boundary staging for the sleep-chained genesis (2026-07-10).

Drives `life --stage` (first cycle) then `life --stage-continue <archive> <paths...>` per batch,
in the world's own temporal order. This is OUR staging at OUR seam: batch boundaries are
world-delivery framing, never engine law; the RSS guard is a substrate wall sharded around,
never a felt limit. Each cycle's print (occupancy before→after, carries, the breath, timings)
is appended to the climb log — the curve IS the measurement the W⁻ derivation waits on.

Usage: genesis-chain.py <climb-dir> [--start-at N] [--dry-run]
"""
import os, sys, subprocess, time, json

LAB = '/home/b/Workspaces/laboratory'
LIFE = f'{LAB}/src/soma/target/release/life'
LOGS = os.path.expanduser('~/.claude/projects/-home-b-Workspaces-laboratory')
EXPORT = os.path.expanduser('~/style/claude_ai_export')
RSS_HALT_KB = 24 * 1024 * 1024           # the measured-wall detector (halt-first; 30 GB host, iGPU desktop ~5 GB)


def manifest(_unused):
    """THE WORLD'S FRAMES (§XXXIV-c corrected — the batcher struck): one cycle per world-delivered
    frame, in the world's own temporal order. Cadence comes from collocation about the information
    topology — sessions and files ARE the collocation events; no byte-size enters anywhere."""
    batches = []
    logs = sorted(
        (os.path.getmtime(f'{LOGS}/{n}'), f'{LOGS}/{n}')
        for n in os.listdir(LOGS) if n.endswith('.jsonl')
    )
    for _, p in logs:
        batches.append([p])
    export = [f'{EXPORT}/conversations.json', f'{EXPORT}/memories.json']
    design = f'{EXPORT}/design_chats'
    if os.path.isdir(design):
        export.append(design)
    batches.append([p for p in export if os.path.exists(p)])
    tracked = subprocess.run(['git', 'ls-files'], cwd=LAB, capture_output=True, text=True
                             ).stdout.splitlines()
    workspace = []
    for rel in tracked:
        p = f'{LAB}/{rel}'
        try:
            if os.path.getsize(p) >= 2:
                workspace.append(p)
        except OSError:
            continue
    batches.append(workspace)
    return batches


def run_cycle(cmd, log_path):
    peak = 0
    with open(log_path, 'ab') as log:
        proc = subprocess.Popen(cmd, stdout=log, stderr=subprocess.STDOUT)
        while proc.poll() is None:
            try:
                with open(f'/proc/{proc.pid}/status') as st:
                    for line in st:
                        if line.startswith('VmRSS'):
                            peak = max(peak, int(line.split()[1]))
            except OSError:
                pass
            if peak > RSS_HALT_KB:
                proc.terminate()
                proc.wait()
                return None, peak
            time.sleep(0.5)
    return proc.returncode, peak


def latest_archive(climb_dir):
    state = f'{climb_dir}/climb-state.json'
    return json.load(open(state)) if os.path.exists(state) else {'cycle': 0, 'archive': None}


def main():
    climb_dir = sys.argv[1]
    os.makedirs(climb_dir, exist_ok=True)
    dry = '--dry-run' in sys.argv
    batches = manifest(f'{climb_dir}/split')
    total = sum(os.path.getsize(p) if os.path.isfile(p) else 0 for b in batches for p in b)
    print(f'genesis climb: {len(batches)} cycles · {total/1048576:.0f} MB staged light', flush=True)
    if dry:
        for i, b in enumerate(batches):
            size = sum(os.path.getsize(p) for p in b if os.path.isfile(p))
            print(f'  cycle {i}: {len(b)} paths · {size/1048576:.1f} MB')
        return
    state = latest_archive(climb_dir)
    log_path = f'{climb_dir}/climb.log'
    for i in range(state['cycle'], len(batches)):
        started = time.time()
        if state['archive'] is None:
            cmd = [LIFE, '--stage', *batches[i]]
        else:
            cmd = [LIFE, '--stage-continue', state['archive'], *batches[i]]
        with open(log_path, 'a') as log:
            log.write(f'\n══ CYCLE {i} · {len(batches[i])} paths ══\n')
        code, peak = run_cycle(cmd, log_path)
        # the cycle prints its archive path; recover it as the newest stage archive
        periplus = f'{LAB}/src/soma/diet/periplus'
        archives = sorted(
            (os.path.getmtime(f'{periplus}/{n}'), f'{periplus}/{n}')
            for n in os.listdir(periplus) if 'stage' in n
        )
        if code != 0 or not archives:
            print(f'CYCLE {i} HALTED: exit {code} · peak RSS {peak//1024} MB — the wall is measured, '
                  f'the climb stops cleanly at cycle {i}; archives through cycle {i-1} stand',
                  flush=True)
            sys.exit(1)
        state = {'cycle': i + 1, 'archive': archives[-1][1]}
        json.dump(state, open(f'{climb_dir}/climb-state.json', 'w'))
        print(f'cycle {i}: exit {code} · peak RSS {peak//1024} MB · {time.time()-started:.1f}s · '
              f'archive {os.path.basename(state["archive"])}', flush=True)
    print('THE CLIMB IS COMPLETE', flush=True)


if __name__ == '__main__':
    main()
