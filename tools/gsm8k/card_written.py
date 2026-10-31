"""Written-rule reads through the card's release route (record 2026-10-30_THE_COARSE_LEVEL_HEADS…, §43).

    python3 -I tools/gsm8k/card_written.py prompts HELD
    python3 -I tools/gsm8k/card_written.py convert UNITS DIR_FREE DIR_MARKS OUT

Run from the directory that holds (or receives) FREE.prompts, MARKS.prompts and MARKS.map.
"""
# Written-rule reads through the card's release route (record 2026-10-30 §43). `prompts`: from the
# held-out text (problems as written_rules.problems_of reads them) write FREE.prompts (each question,
# its END, then the separator 0x1F) and MARKS.prompts (each question, its END, the answer through each
# calculation's '=', then 0x1F) and MARKS.map. `convert UNITS DIR_FREE DIR_MARKS OUT`: decode the two
# releases into OUT/FREE.tsv and OUT/MARKS.tsv as written_rules.py reads them (a calculation's release
# is its bytes past the '=', cut after its first '>>', which later units cannot change).
import sys, struct, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "tools", "gsm8k"))
END, SEP = b"\x1e", b"\x1f"
def problems_of(text):
    out = []
    for p in text.split(b"\n\n"):
        if p.strip(b"\n"):
            q, _, a = p.partition(b"\n")
            out.append((q, a + b"\n" if not a.endswith(b"\n") else a))
    return out
def calculations_of(answer):
    found, i = [], 0
    while i + 1 < len(answer):
        if answer[i:i + 2] == b"<<":
            close = answer.find(b">>", i + 2)
            close = len(answer) if close < 0 else close
            eq = answer.find(b"=", i + 2, close)
            if eq >= 0:
                found.append((answer[i + 2:eq], eq + 1))
            i = close
        else:
            i += 1
    return found
def field(b):
    out = []
    for c in b:
        if c == 0x7c: out.append("\\x7c")
        elif c == 9: out.append("\\t")
        elif c == 10: out.append("\\n")
        elif c == 13: out.append("\\r")
        elif c == 0x27: out.append("\\'")
        elif c == 0x22: out.append('\\"')
        elif c == 0x5c: out.append("\\\\")
        elif 0x20 <= c < 0x7f: out.append(chr(c))
        else: out.append("\\x%02x" % c)
    return "".join(out)
if sys.argv[1] == "prompts":
    problems = problems_of(open(sys.argv[2], "rb").read())
    free, marks, rows = bytearray(), bytearray(), []
    for i, (q, a) in enumerate(problems):
        free += q + END + SEP
        for j, (e, at) in enumerate(calculations_of(a)):
            marks += q + END + a[:at] + SEP
            rows.append(f"{i}\t{j}\t{field(e)}\n")
    open("FREE.prompts", "xb").write(bytes(free)); open("MARKS.prompts", "xb").write(bytes(marks))
    open("MARKS.map", "x").write("".join(rows))
    print("problems", len(problems), "calculations", len(rows))
elif sys.argv[1] == "convert":
    units, dfree, dmarks, out = sys.argv[2:6]
    lines = open(units).read().split("\n"); n = int(lines[0].split()[1])
    table = [bytes([i]) for i in range(256)]
    for l in lines[1:1 + n]:
        x, y = map(int, l.split()); table.append(table[x] + table[y])
    def releases(d):
        data = open(f"{d}/RELEASES.classes", "rb").read(); cls = struct.unpack(">%dH" % (len(data) // 2), data)
        rows = [r.split("\t") for r in open(f"{d}/RELEASES.tsv").read().strip().split("\n")[1:]]
        at, out_ = 0, []
        for r in rows:
            k = int(r[3]); seg = cls[at:at + k]; at += k
            out_.append(b"".join(table[c] for c in seg).split(END)[0])
        assert at == len(cls)
        return out_
    os.makedirs(out, exist_ok=False)
    free = releases(dfree)
    open(f"{out}/FREE.tsv", "w", encoding="latin-1").write("".join(f"{i}\t{field(r)}\n" for i, r in enumerate(free)))
    marks = releases(dmarks)
    mp = open("MARKS.map").read().strip().split("\n")
    assert len(mp) == len(marks)
    rows = []
    for line, r in zip(mp, marks):
        cut = r.find(b">>"); r = r[:cut + 2] if cut >= 0 else r
        rows.append(f"{line}\t{field(r)}\n")
    open(f"{out}/MARKS.tsv", "w", encoding="latin-1").write("".join(rows))
    print("free", len(free), "marks", len(marks))
