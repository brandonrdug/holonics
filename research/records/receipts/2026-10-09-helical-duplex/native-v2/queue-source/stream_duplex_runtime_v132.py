"""One exact native process; preserve output and mark actual test completion events."""
from pathlib import Path
import json, os, re, selectors, subprocess, sys, time

d=json.loads(Path(sys.argv[1]).read_text())
start=time.monotonic_ns();last=start
out=Path(d['native_stdout']).open('xb');err=Path(d['native_stderr']).open('xb')
p=subprocess.Popen(d['native_argv'],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
sel=selectors.DefaultSelector();sel.register(p.stdout,selectors.EVENT_READ,1);sel.register(p.stderr,selectors.EVENT_READ,2)
pending=b'';events=[];exceeded=False
try:
    while sel.get_map():
        timeout=max(0,(d['per_unit_upper_ns']-(time.monotonic_ns()-last))/10**9)
        ready=sel.select(timeout)
        if not ready:
            exceeded=True;p.terminate()
            print('\nUNIT_EVENT '+json.dumps({'event':'unit_projection_exceeded','unfinished_after':len(events),'elapsed_ns':time.monotonic_ns()-last,'fixed_unit_upper_ns':d['per_unit_upper_ns']}),flush=True)
            # The enclosing owned cgroup performs final descendant cleanup on failure.
            break
        for key,_ in ready:
            b=os.read(key.fileobj.fileno(),65536)
            if not b:sel.unregister(key.fileobj);continue
            (out if key.data==1 else err).write(b);os.write(key.data,b)
            if key.data==1:
                pending+=b
                while b'\n' in pending:
                    line,pending=pending.split(b'\n',1)
                    m=re.fullmatch(rb'test (\S+) \.\.\. (ok|FAILED|ignored)',line)
                    if m:
                        now=time.monotonic_ns();e={'event':'test_completed','selector':m[1].decode(),'result':m[2].decode(),'unit_wall_ns':now-last,'elapsed_ms':(now-start)//10**6};events.append(e);last=now
                        print('UNIT_EVENT '+json.dumps(e),flush=True)
    status=p.wait(timeout=1)
finally:
    out.close();err.close();sel.close()
receipt={'native_exit':status if not exceeded else None,'projection_exceeded':exceeded,'wall_ns':time.monotonic_ns()-start,'events':events,'expected_names':d['expected_names']}
with Path(d['result']).open('x') as f:json.dump(receipt,f,indent=2);f.write('\n')
assert not exceeded,'actual native unit exceeded its fixed measured upper'
assert status==0,'native test process failed'
assert [e['selector'] for e in events]==d['expected_names'],'native names/order differ from source-bound selection'
assert all(e['result']=='ok' for e in events)

