"""A ruler for the section's launch graph (the engineering report of November 20, §11 item 3): which buffers each card kernel reads and
writes, read from the kernels' source, joined to a section's launch order (the profile's `FIELD_TRACE` lines), so a reader sees the
section's dependency levels, how many launches stand at each level (the most that could run at once), and which maps read the same input.

The source read (`kernels/field.cu` and its headers): for each `extern "C" __global__` entry, every `w.NAME[...]` (a field of the words
struct) and every pointer parameter `NAME[...]` it indexes, classed a write where an index is followed by `=`, `+=`, `-=`, `|=` or taken as
`&NAME[...]` into an atomic, and a read otherwise. A buffer is named by its words field or parameter (the role a tick re-points), so two
launches of one kernel in one tick share buffers and launches in different ticks may not: the levels read here are an upper bound on the
dependency, a lower bound on the concurrency. The `add` and `x` arguments of the generic maps are read from the trace's own order only.

Outside the machine; source and counts only. Usage: python3 -I section_graph.py KERNELS_DIR [TRACE_LOG]"""
import sys, os, re, collections

src_dir = sys.argv[1]
text = ''
for f in sorted(os.listdir(src_dir)):
    if f.endswith(('.cu', '.cuh')):
        text += open(os.path.join(src_dir, f), encoding='utf-8').read() + '\n'
# strip comments
text = re.sub(r'//[^\n]*', '', text)
text = re.sub(r'/\*.*?\*/', '', text, flags=re.S)

def body_at(i):
    depth = 0; j = text.index('{', i)
    for k in range(j, len(text)):
        if text[k] == '{': depth += 1
        elif text[k] == '}':
            depth -= 1
            if depth == 0: return text[j:k + 1]
    return text[j:]

# device helpers are inlined by name: collect their bodies too, so a kernel that calls one inherits its accesses
fn_re = re.compile(r'(?:__device__[^;{(]*?|__global__ void|static[^;{(]*?)\s(\w+)\s*\(([^)]*)\)\s*\{')
bodies = {}
for m in fn_re.finditer(text):
    bodies[m.group(1)] = (m.group(2), body_at(m.start()), 'extern "C"' in text[max(0, m.start() - 12):m.start()] or text[max(0, m.start() - 40):m.start()].strip().endswith('extern "C"'))
acc_re = re.compile(r'(?<![\w.])(?:w\.)?(\w+)\[')
def accesses(name, seen=None):
    seen = seen or set()
    if name in seen or name not in bodies: return set(), set()
    seen.add(name)
    params, body, _ = bodies[name]
    ptrs = set(re.findall(r'\*\s*(\w+)', params))
    reads, writes = set(), set()
    for m in re.finditer(r'(&?)\b(w\.)?(\w+)\[', body):
        amp, isw, nm = m.group(1), m.group(2), m.group(3)
        if not isw and nm not in ptrs: continue
        key = ('w.' if isw else '') + nm
        # find the matching close bracket
        d = 0; k = m.end() - 1
        while k < len(body):
            if body[k] == '[': d += 1
            elif body[k] == ']':
                d -= 1
                if d == 0: break
            k += 1
        after = body[k + 1:k + 4].lstrip()
        if amp or re.match(r'(=(?!=)|\+=|-=|\|=)', after): writes.add(key)
        else: reads.add(key)
    for callee in re.findall(r'\b(\w+)\s*\(', body):
        if callee in bodies and callee != name and not bodies[callee][2]:
            r, w_ = accesses(callee, seen)
            reads |= r; writes |= w_
    return reads, writes

kernels = {}
for m in re.finditer(r'extern "C" __global__ void (?:__launch_bounds__\([^)]*\)\s*)?(\w+)\s*\(', text):
    kernels[m.group(1)] = accesses(m.group(1))
print(f'GRAPH_KERNELS {len(kernels)} entries read from {src_dir}')

if len(sys.argv) < 3:
    for k, (r, w_) in sorted(kernels.items()):
        print(f'KERNEL {k} reads={",".join(sorted(r))} writes={",".join(sorted(w_))}')
    sys.exit(0)

seq = []
for line in open(sys.argv[2], errors='replace'):
    if line.startswith('FIELD_TRACE seq='):
        f = dict(x.split('=', 1) for x in line.split()[1:] if '=' in x)
        seq.append((f['entry'], f.get('phase', '-'), int(f.get('ns', 0)), f.get('run', '0')))
print(f'GRAPH_TRACE {len(seq)} launches, {len(set(e for e, *_ in seq))} entries')
last_write = {}; last_read = collections.defaultdict(int); level = []
for i, (e, ph, ns, run) in enumerate(seq):
    r, w_ = kernels.get(e, (set(), set()))
    dep = 0
    for b in r: dep = max(dep, last_write.get(b, -1) + 1)
    for b in w_: dep = max(dep, last_write.get(b, -1) + 1, last_read.get(b, 0))
    level.append(dep)
    for b in w_: last_write[b] = dep
    for b in r: last_read[b] = max(last_read[b], dep + 1)
depth = max(level) + 1 if level else 0
width = collections.Counter(level)
ns_total = sum(ns for _, _, ns, _ in seq)
crit = collections.defaultdict(int)
for (e, ph, ns, run), lv in zip(seq, level): crit[lv] = max(crit[lv], ns)
print(f'GRAPH_LEVELS launches={len(seq)} levels={depth} mean_width={len(seq)/max(1,depth):.2f} widest={max(width.values()) if width else 0} '
      f'levels_of_one={sum(1 for v in width.values() if v == 1)} ns_sum_ms={ns_total/1e6:.1f} critical_path_ms={sum(crit.values())/1e6:.1f}')
hist = collections.Counter(min(v, 9) for v in width.values())
print('GRAPH_WIDTHS ' + ' '.join(f'{k}{"+" if k == 9 else ""}:{hist[k]}' for k in sorted(hist)))
# maps that read one input in one level
groups = collections.defaultdict(list)
for (e, ph, ns, run), lv in zip(seq, level):
    if 'affine' in e or 'transposed' in e or 'outer' in e: groups[(lv, ph)].append(e)
stack = sum(1 for v in groups.values() if len(v) > 1)
print(f'GRAPH_MAP_STACKS levels_with_two_or_more_maps={stack} maps_in_them={sum(len(v) for v in groups.values() if len(v) > 1)}')
by_entry = collections.Counter(e for e, *_ in seq)
print('GRAPH_TOP_ENTRIES ' + ' '.join(f'{e}:{c}' for e, c in by_entry.most_common(12)))
