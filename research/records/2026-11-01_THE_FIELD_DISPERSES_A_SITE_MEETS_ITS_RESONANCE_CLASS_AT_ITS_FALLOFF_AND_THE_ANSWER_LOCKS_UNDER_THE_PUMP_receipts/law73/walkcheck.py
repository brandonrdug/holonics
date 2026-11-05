import sys, re, importlib.util
spec = importlib.util.spec_from_file_location("w", sys.argv[1]); w = importlib.util.module_from_spec(spec); spec.loader.exec_module(w)
text = open(sys.argv[2], "rb").read(); keys = open(sys.argv[3], "rb").read()
seed = int.from_bytes(keys[-8:], "big")
probs = w.problems_of(text)
keyed = sorted(range(len(probs)), key=lambda i: (w.mix(seed, 1 << 61 | i), i))
rest = sorted(keyed[128:], key=lambda i: (len(probs[i][0]) + 1 + len(probs[i][1]), i))
sections = [rest[k:k + 16] for k in range(0, len(rest), 16)]
ok = bad = 0
for log in sys.argv[4:]:
    first = None
    laps = {}
    for line in open(log):
        m = re.match(r"FIELD_SECTION lap=(\d+) n=(\d+) .* length=(\d+) ", line)
        if m:
            laps.setdefault(int(m[1]), []).append((int(m[2]), int(m[3])))
        m = re.match(r"FIELD_LAP lap=(\d+) read=(\d+)", line)
        if m:
            read = int(m[2]) - 1
            walk = sorted(range(len(sections)), key=lambda s: (w.mix(seed, ((read << 40) ^ s) & w.M), s))
            for n, length in laps[int(m[1])]:
                pred = max(len(probs[i][0]) + 1 for i in sections[walk[n]]) + 1229
                ok += pred == length; bad += pred != length
print(f"section lengths reproduced: {ok} equal, {bad} unequal")
