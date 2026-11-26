"""Her wave writes by the law's release (write-forms: every place of a span opened, resolved by octaves of distance from the prompt,
then REFINE passes rereading each place against every other), chained: each span's prompt is the last PROMPT samples written so far.

python3 -I release_chain.py BIN PANEL OUT SPANS RUN REFINE PROMPT UPPER_S   (each call on the card; stops when a call passes UPPER_S)
"""
import hashlib, os, subprocess, sys, time
ROOT = os.environ['HOLONICS_ROOT']; W = os.environ['HOLONICS_RUN']  # the repository's root and the run directory, private paths
U0 = f'{ROOT}/.local/wt/section-edge/.local/run/gsm8k/UNITS0'; K = f'{ROOT}/.local/wt/field-card/.local/run/KEYS8'
C = open(f'{W}/widths/w124.codec').read().strip(); M = f'{W}/front/arm_W127w/MEAN.3000'
binary, panel, out, spans, run, refine, keep, upper = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6]), int(sys.argv[7]), float(sys.argv[8])
sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
rows = [l.rstrip('\n').split('\t') for l in open(panel)]
prompts = {r[0]: bytes.fromhex(r[1][4:]) for r in rows}; refs = {r[0]: r[2] for r in rows}
written = {r[0]: b'' for r in rows}
os.makedirs(out)
env = {'HOME': os.environ['HOME'], 'PATH': '/opt/cuda/bin:' + os.environ['PATH']}
for s in range(spans):
    table = f'{out}/span_{s}.tsv'
    with open(table, 'w') as f:
        for label in prompts:
            ctx = (prompts[label] + written[label])[-keep:]
            f.write(f"{label}\thex:{ctx.hex()}\thex:00\n")
    o = f'{out}/span_{s}'; t0 = time.time()
    r = subprocess.run([binary, 'train', 'complete-language', 'write-forms', U0, sha(U0), K, sha(K), C, sha(C), table, sha(table), str(run), o, M, sha(M), str(refine)], env=env, capture_output=True, text=True)
    dt = time.time() - t0
    print(f"SPAN {s} exit={r.returncode} s={dt:.1f} {[l for l in r.stdout.splitlines() if 'DONE' in l][:1]}", flush=True)
    if r.returncode != 0:
        print(r.stderr[-400:]); sys.exit(1)
    for line in open(f'{o}/forms.written'):
        label, _, w, _ = line.rstrip('\n').split('\t')
        written[label] += bytes.fromhex(w[4:])
    if dt > upper:
        print(f"SPAN_STOP call {s} took {dt:.1f} s against the upper {upper} s"); break
with open(f'{out}/forms.written', 'w') as f:
    for label in prompts:
        f.write(f"{label}\thex:{prompts[label].hex()}\thex:{written[label].hex()}\t{refs[label]}\n")
print('CHAIN_DONE', {k: len(v) for k, v in written.items()})
