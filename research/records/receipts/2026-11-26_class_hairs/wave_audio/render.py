"""Her wave writes as audio: each row's prompt then her write, and the prompt then the held reference, both at the chart's 13 levels.

python3 -I render.py FORMS_WRITTEN CHART_TSV CLOCK_HZ OUTDIR   (a ruler's rendering; a level is heard at its range's middle)
"""
import sys, wave, struct
forms, chart, clock, outdir = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
rows = [l.rstrip('\n').split('\t') for l in open(chart)][1:]
amp = {}
for level, octet, low, high, _ in rows:
    low, high = int(low), int(high)
    low, high = max(low, -3600), min(high, 3600)  # the end levels heard near their inner edge
    amp[int(octet)] = (low + high) // 2
def samples(h):
    b = bytes.fromhex(h[4:]) if h.startswith('hex:') else h.encode()
    return [amp.get(o) for o in b]
def write(path, xs):
    with wave.open(path, 'wb') as w:
        w.setnchannels(1); w.setsampwidth(2); w.setframerate(clock)
        w.writeframes(b''.join(struct.pack('<h', max(-32768, min(32767, 4 * x))) for x in xs))
for line in open(forms):
    label, prompt, written, ref = line.rstrip('\n').split('\t')
    p, wr, rf = samples(prompt), samples(written), samples(ref)
    off_chart = sum(1 for x in wr if x is None)
    wr = [0 if x is None else x for x in wr]
    n = len(wr)
    name = label.replace(':', '_')
    write(f"{outdir}/{name}_her_write.wav", p + wr)
    write(f"{outdir}/{name}_held_reference.wav", p + rf[:n])
    hist = lambda xs: [sum(1 for x in xs if x == a) for a in sorted(amp.values())]
    print(f"RENDER {label} prompt={len(p)} written={n} seconds={n / clock:.2f} off_chart={off_chart} levels_written={hist(wr)} levels_reference={hist(rf[:n])}")
