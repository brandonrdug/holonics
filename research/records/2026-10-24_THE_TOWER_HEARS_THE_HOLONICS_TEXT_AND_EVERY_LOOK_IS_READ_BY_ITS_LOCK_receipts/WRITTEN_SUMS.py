"""The tower's written rests read against the true ones (read-lines-stream LINES.tsv): by operation,
and for the sums by the operands' lengths, the whole written rest right, its length right, and its
last two digits right; each operation's wrong lines by where they go wrong (the length, the tens
alone, the units alone, or both, the last two places read from the line's end); with `--train FILE …`,
each operation's lines also read apart by whether a training file holds the whole line (met) or none
does (never met).
Usage: WRITTEN_SUMS.py LINES.tsv [LINES.tsv ...] [--train FILE ...]"""
import codecs, re, sys

def dec(s): return codecs.escape_decode(s.encode())[0].decode("latin-1")

args = sys.argv[1:]
paths, train_files = (args[:args.index("--train")], args[args.index("--train") + 1:]) if "--train" in args else (args, [])
train = set()
for f in train_files:
    for l in open(f, encoding="latin-1"):
        train.add(l.rstrip("\n"))
for path in paths:
    rows = [l.rstrip("\n").split("\t") for l in open(path)]
    by, seen, wrong = {}, {}, {}
    for r in rows:
        head, rest, wrote = dec(r[1]), dec(r[2]), dec(r[3])
        m = re.fullmatch(r"(\d+)([-+*])(\d+)=", head)
        if not m: continue
        a, op, b = m.groups()
        k = (op, f"{len(a)}{op}{len(b)}") if op == "+" else (op, "all")
        s = by.setdefault(k, [0, 0, 0, 0])
        s[0] += 1; s[1] += wrote == rest; s[2] += len(wrote) == len(rest); s[3] += wrote[-2:] == rest[-2:]
        e = wrong.setdefault(op, [0, 0, 0, 0])
        if wrote != rest:
            if len(wrote) != len(rest): e[0] += 1
            else:
                units, tens = wrote[-1:] == rest[-1:], wrote[-2:-1] == rest[-2:-1]
                e[1] += units and not tens; e[2] += tens and not units; e[3] += not units and not tens
        t = seen.setdefault((op, head + rest in train), [0, 0])
        t[0] += 1; t[1] += wrote == rest
    print(path)
    for op in "+-*":
        ks = sorted(k for k in by if k[0] == op)
        tot = [sum(by[k][i] for k in ks) for i in range(4)]
        if op == "+":
            for k in ks: print(f"  {k[1]}: {by[k][0]} lines; whole right {by[k][1]}, length right {by[k][2]}, last two digits right {by[k][3]}")
        print(f"  {op} all: {tot[0]} lines; whole right {tot[1]}, length right {tot[2]}, last two digits right {tot[3]}")
        e = wrong.get(op, [0, 0, 0, 0])
        print(f"  {op} wrong: the length {e[0]}, the tens alone {e[1]}, the units alone {e[2]}, both {e[3]}")
        if train_files:
            met, new = seen.get((op, True), [0, 0]), seen.get((op, False), [0, 0])
            print(f"  {op} never met in training: {new[1]} of {new[0]} right; met: {met[1]} of {met[0]}")
