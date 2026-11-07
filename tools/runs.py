#!/usr/bin/env python3
"""Dispatch runs that outlive the agent (Brandon, November 7 18:23: runs "fully complete without being attached as
processes to the Claude app and your thread's lifetime").

A local run is a transient systemd user service, so the user manager is its parent (lingering is on), never the agent's
shell. A scope made by `systemd-run --scope` still belongs to the caller, and on November 7 near 18:14 UTC lap 12 died
with the session that launched it. A Colab run is a `nohup` job on the session's VM. The VM is the run's own machine,
but Colab can reclaim it (lap 12's first run was lost that way overnight), so a Colab run saves its states the same way.

Each run has a registry entry `.local/dispatch/<name>.json`, its output `<cwd>/<name>.out`, and on exit `.local/dispatch/<name>.exit`
(`<code> <UTC time>`; a Colab run's exit file lives on the VM). A run that is gone with no exit file was killed.

  runs.py start NAME SCRIPT [--log FILE] [--progress REGEX]   launch `bash SCRIPT` in its own directory as a service
  runs.py adopt NAME UNIT --out FILE [--log FILE]              register a service already running
  runs.py colab NAME SCRIPT --session S [--log FILE]           upload SCRIPT and run it detached on a Colab session
  runs.py status [NAME ...]                                    one line a run: state, elapsed, last progress line
  runs.py stop NAME                                            stop a run (its service, or its VM job)
  runs.py watch [NAME ...] [--every SECONDS]                   events for a Monitor: ends, kills, failure lines, and
                                                               a heartbeat with the UTC time every SECONDS (1800)

`watch` exits once every run it watches has ended. Under the Monitor tool, its 30-minute expiry also wakes the agent,
so a waiting agent always gets the time and every run's state at least every half hour (Brandon, November 7 18:23).
"""
import argparse, json, os, re, subprocess, sys, time
from datetime import datetime, timezone
from pathlib import Path

def _main_checkout():
    # One registry for the machine: the main checkout's `.local/runs`, whichever worktree the tool runs from.
    here = Path(__file__).resolve().parent.parent
    r = subprocess.run(["git", "-C", str(here), "rev-parse", "--path-format=absolute", "--git-common-dir"], capture_output=True, text=True)
    return Path(r.stdout.strip()).parent if r.returncode == 0 and r.stdout.strip() else here


REG = _main_checkout() / ".local" / "dispatch"
COLAB = os.path.expanduser("~/.local/bin/colab")
FAILURE = re.compile(r"error|panic|Killed|refused|Traceback|LOCK_BUSY", re.I)
DEFAULT_PROGRESS = r"^FIELD_\w+ lap="


def utc(t=None):
    return datetime.fromtimestamp(t or time.time(), timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def entry(name):
    p = REG / f"{name}.json"
    if not p.exists():
        sys.exit(f"no run named {name}")
    return json.loads(p.read_text())


def save(e):
    REG.mkdir(parents=True, exist_ok=True)
    (REG / f"{e['name']}.json").write_text(json.dumps(e, indent=1) + "\n")


def unit_active(unit):
    r = subprocess.run(["systemctl", "--user", "is-active", unit], capture_output=True, text=True)
    return r.stdout.strip() in ("active", "activating", "deactivating")


def colab_exec(session, code, timeout=60):
    r = subprocess.run([COLAB, "exec", "-s", session, "--timeout", str(timeout)], input=code, capture_output=True, text=True, timeout=timeout + 60)
    # The CLI's own notices (`[colab] …`) are not the run's.
    return "\n".join(l for l in r.stdout.splitlines() if not l.startswith("[colab]") and l.strip()) + "\n"


def tail_match(path, pattern, lines=4000):
    try:
        with open(path, "rb") as f:
            f.seek(0, 2)
            f.seek(max(0, f.tell() - (1 << 20)))
            text = f.read().decode(errors="replace").splitlines()[-lines:]
    except OSError:
        return None
    rx = re.compile(pattern)
    for line in reversed(text):
        if rx.search(line):
            return line
    return None


def state(e):
    """(state, exit text, last progress line, failure lines)."""
    if e["backend"] == "colab":
        code = (f"import os,subprocess\nx='/content/{e['name']}.exit'\nprint('EXIT', open(x).read().strip() if os.path.exists(x) else '-')\n"
                f"print('ALIVE', subprocess.run(['pgrep','-f','/content/{e['name']}.sh'],capture_output=True).returncode==0)\n"
                f"print(subprocess.run(['bash','-c',\"grep -E '{e['progress']}' {e['log']} | tail -1; grep -iE 'error|panic|Killed|refused' {e['log']} | tail -3\"],capture_output=True,text=True).stdout)")
        try:
            out = colab_exec(e["session"], code)
        except subprocess.TimeoutExpired:
            return ("unreachable", "-", None, [])
        ex = re.search(r"EXIT (.*)", out)
        alive = "ALIVE True" in out
        rest = out.split("\n", 2)[2] if out.count("\n") >= 2 else ""
        lines = [l for l in rest.splitlines() if l.strip()]
        ext = ex.group(1).strip() if ex else "-"
        st = "running" if alive else ("exited" if ext != "-" else ("gone" if ex else "unreachable"))
        return (st, ext, lines[0] if lines else None, [l for l in lines[1:] if FAILURE.search(l)])
    xf = REG / f"{e['name']}.exit"
    ext = xf.read_text().strip() if xf.exists() else "-"
    if e.get("adopted") and ext == "-" and not unit_active(e["unit"]):
        m = tail_match(e["out"], r"^MAIN exit|^RUN_EXIT")
        ext = m or "-"
    st = "running" if unit_active(e["unit"]) else ("exited" if ext != "-" else "gone")
    fails = []
    try:
        with open(e["log"], errors="replace") as f:
            fails = [l.rstrip()[:200] for l in f if FAILURE.search(l) and not l.startswith(("FIELD_COMMAND", "#"))][-3:]
    except OSError:
        pass
    return (st, ext, tail_match(e["log"], e["progress"]), fails)


def line(e, st):
    s, ext, prog, _ = st
    end = time.time()
    if ext != "-":
        try:
            end = datetime.strptime(ext.split()[-1], "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc).timestamp()
        except ValueError:
            pass
    el = int(end - e["started_epoch"])
    p = (prog or "-").strip()
    m = re.findall(r"\b(?:n|sections|ms)=[\d/]+", p)
    short = " ".join(m) if m else p[:120]
    return f"{e['name']} [{e['backend']}] {s}{'' if ext == '-' else ' (' + ext + ')'} elapsed {el // 3600}h{el % 3600 // 60:02d}m  {short}"


def cmd_start(a):
    script = Path(a.script).resolve()
    cwd = script.parent
    out = cwd / f"{a.name}.out"
    unit = f"holonics-run-{a.name}"
    if unit_active(unit):
        sys.exit(f"{unit} is already running")
    xf = REG / f"{a.name}.exit"
    REG.mkdir(parents=True, exist_ok=True)
    xf.unlink(missing_ok=True)
    wrapper = f'bash {script}; c=$?; echo "$c $(date -u +%FT%TZ)" > {xf}; echo "RUN_EXIT $c $(date -u +%FT%TZ)"'
    subprocess.run(["systemd-run", "--user", "--quiet", f"--unit={unit}", "--collect", f"--working-directory={cwd}",
                    "-p", f"StandardOutput=append:{out}", "-p", f"StandardError=append:{out}", "bash", "-c", wrapper], check=True)
    save({"name": a.name, "backend": "local", "unit": unit, "script": str(script), "cwd": str(cwd), "out": str(out),
          "log": str(Path(a.log).resolve()) if a.log else str(out), "progress": a.progress, "started": utc(), "started_epoch": time.time()})
    print(f"started {unit} at {utc()}; output {out}")


def cmd_adopt(a):
    if not unit_active(a.unit):
        sys.exit(f"{a.unit} is not running")
    r = subprocess.run(["systemctl", "--user", "show", a.unit, "-p", "ActiveEnterTimestamp", "--value", "--timestamp=unix"], capture_output=True, text=True)
    t = float(r.stdout.strip().lstrip("@") or time.time())
    out = str(Path(a.out).resolve())
    save({"name": a.name, "backend": "local", "unit": a.unit, "adopted": True, "out": out, "log": str(Path(a.log).resolve()) if a.log else out,
          "progress": a.progress, "started": utc(t), "started_epoch": t})
    print(f"adopted {a.unit} (since {utc(t)})")


def cmd_colab(a):
    script = Path(a.script).resolve()
    remote = f"/content/{a.name}.sh"
    subprocess.run([COLAB, "upload", "-s", a.session, str(script), remote], check=True)
    log = a.log or f"/content/{a.name}.out"
    code = (f"import subprocess\np=subprocess.Popen(['bash','-c','nohup bash -c \"bash {remote} > /content/{a.name}.out 2>&1; "
            f"echo \\\\$? \\\\$(date -u +%FT%TZ) > /content/{a.name}.exit\" > /dev/null 2>&1 & echo $!'],stdout=subprocess.PIPE,text=True)\n"
            f"print('pid', p.communicate()[0].strip())")
    print(colab_exec(a.session, code).strip())
    save({"name": a.name, "backend": "colab", "session": a.session, "script": str(script), "log": log, "progress": a.progress,
          "started": utc(), "started_epoch": time.time()})


def cmd_status(a):
    names = a.names or sorted(p.stem for p in REG.glob("*.json"))
    for n in names:
        e = entry(n)
        print(line(e, state(e)))


def cmd_stop(a):
    e = entry(a.name)
    if e["backend"] == "colab":
        print(colab_exec(e["session"], f"import subprocess\nsubprocess.run(['pkill','-f','/content/{e['name']}.sh'])\nprint('stopped')"))
    else:
        subprocess.run(["systemctl", "--user", "stop", e["unit"]])
        print(f"stopped {e['unit']}")


def cmd_watch(a):
    names = a.names or [p.stem for p in REG.glob("*.json") if state(json.loads(p.read_text()))[0] == "running"]
    if not names:
        print(f"{utc()} no run is running")
        return
    entries = {n: entry(n) for n in names}
    last_state: dict = {n: None for n in names}
    seen_fail = {n: set() for n in names}
    beat = 0.0
    poll = 20 if all(e["backend"] == "local" for e in entries.values()) else 120
    while True:
        now = time.time()
        live = 0
        sts = {}
        for n, e in entries.items():
            st = sts[n] = state(e)
            if st[0] != last_state[n] and last_state[n] is not None or st[0] in ("exited", "gone") and last_state[n] is None:
                print(f"{utc()} {line(e, st)}", flush=True)
            last_state[n] = st[0]
            for f in st[3]:
                if f not in seen_fail[n]:
                    seen_fail[n].add(f)
                    print(f"{utc()} {n} FAILURE LINE: {f}", flush=True)
            live += st[0] in ("running", "unreachable")
        if now - beat >= a.every:
            beat = now
            print(f"{utc()} heartbeat: " + "; ".join(line(entries[n], sts[n]) for n in names), flush=True)
        if not live:
            print(f"{utc()} every watched run has ended", flush=True)
            return
        time.sleep(poll)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("start"); s.add_argument("name"); s.add_argument("script"); s.add_argument("--log"); s.add_argument("--progress", default=DEFAULT_PROGRESS)
    s = sub.add_parser("adopt"); s.add_argument("name"); s.add_argument("unit"); s.add_argument("--out", required=True); s.add_argument("--log"); s.add_argument("--progress", default=DEFAULT_PROGRESS)
    s = sub.add_parser("colab"); s.add_argument("name"); s.add_argument("script"); s.add_argument("--session", required=True); s.add_argument("--log"); s.add_argument("--progress", default=DEFAULT_PROGRESS)
    s = sub.add_parser("status"); s.add_argument("names", nargs="*")
    s = sub.add_parser("stop"); s.add_argument("name")
    s = sub.add_parser("watch"); s.add_argument("names", nargs="*"); s.add_argument("--every", type=int, default=1800)
    a = ap.parse_args()
    {"start": cmd_start, "adopt": cmd_adopt, "colab": cmd_colab, "status": cmd_status, "stop": cmd_stop, "watch": cmd_watch}[a.cmd](a)


if __name__ == "__main__":
    main()
