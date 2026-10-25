"""The tower's written rests read against the true ones (read-lines-stream LINES.tsv): by operation,
and for the sums by the operands' lengths, the whole written rest right, its length right, and its
last two digits right. Usage: WRITTEN_SUMS.py LINES.tsv [LINES.tsv ...]"""
import codecs, re, sys
def dec(s): return codecs.escape_decode(s.encode())[0].decode("latin-1")
for path in sys.argv[1:]:
    rows = [l.rstrip("\n").split("\t") for l in open(path)]
    by = {}
    for r in rows:
        head, rest, wrote = dec(r[1]), dec(r[2]), dec(r[3])
        m = re.fullmatch(r"(\d+)([-+*])(\d+)=", head)
        if not m: continue
        a, op, b = m.groups()
        w = wrote.split("\n")[0]
        k = (op, f"{len(a)}{op}{len(b)}") if op == "+" else (op, "all")
        s = by.setdefault(k, [0, 0, 0, 0])
        s[0] += 1; s[1] += w == rest; s[2] += len(w) == len(rest); s[3] += w[-2:] == rest[-2:]
    print(path)
    for op in "+-*":
        ks = sorted(k for k in by if k[0] == op)
        tot = [sum(by[k][i] for k in ks) for i in range(4)]
        if op == "+":
            for k in ks: print(f"  {k[1]}: {by[k][0]} lines; whole right {by[k][1]}, length right {by[k][2]}, last two digits right {by[k][3]}")
        print(f"  {op} all: {tot[0]} lines; whole right {tot[1]}, length right {tot[2]}, last two digits right {tot[3]}")
