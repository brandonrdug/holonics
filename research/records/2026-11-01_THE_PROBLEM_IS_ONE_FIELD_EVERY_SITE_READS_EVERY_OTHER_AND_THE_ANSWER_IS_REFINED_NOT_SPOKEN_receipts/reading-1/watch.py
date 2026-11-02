"""Early stop for train-field (the waiting standard): a lap before growth past A ms, or a lap after a growth
past B ms, stops the run. Lap time runs from the trainer's start or its last FIELD_LAP line.
    watch.py LOG PIDFILE A_MS B_MS"""
import os, re, signal, sys, time
log, pidfile, a_ms, b_ms = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
start = time.monotonic(); grown = False; seen = 0; laps = 0
while True:
    time.sleep(1)
    try:
        text = open(log, errors="replace").read()
    except FileNotFoundError:
        continue
    if "FIELD_DONE_MARK" in text or not os.path.exists(pidfile):
        break
    for line in text.splitlines()[seen:]:
        if line.startswith("FIELD_LAP "):
            start = time.monotonic(); laps += 1
        if line.startswith("FIELD_GROW "):
            grown = True
        if line.startswith("FIELD_HELD lap=-1"):
            start = time.monotonic()
    seen = len(text.splitlines())
    bound = b_ms if grown else a_ms
    if (time.monotonic() - start) * 1000 > bound:
        try:
            pid = int(open(pidfile).read().strip())
            os.kill(pid, signal.SIGTERM)
            print(f"EARLY_STOP lap={laps} grown={grown} bound_ms={bound}", flush=True)
        except Exception as e:
            print(f"EARLY_STOP_FAILED {e}", flush=True)
        break
