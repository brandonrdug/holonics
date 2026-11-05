#!/usr/bin/env python3
"""How the written answers end and what fills their length (§16.47, the unified-theory reading of November 5, 14:47).

Usage: endings.py HELD.txt SAMPLE.tsv

For each written answer beside its held answer: whether it ends with a final line (`#### ` and a number) at its boundary,
whether a final line stands earlier, its lines, its steps (`<<...>>`), and its bytes; summarized over the shorter, the
equal-ish and the longer answers. Aggregates only; nothing here is a text.
"""
import re
import statistics
import sys



def problems_of(text):
    blocks, cur = [], []
    for line in text.split(b"\n"):
        if line == b"":
            blocks.append(cur); cur = []
        else:
            cur.append(line)
    blocks.append(cur)
    return [(b[0], b"\n".join(b[1:])) for b in blocks if len(b) >= 2]


FINAL = re.compile(rb"^#### ?-?[0-9][0-9,]*(\.[0-9]+)?$")


def shape(a):
    lines = a.split(b"\n")
    return {
        "bytes": len(a),
        "lines": len(lines),
        "steps": len(re.findall(rb"<<[^<>]*>>", a)),
        "ends_final": bool(FINAL.match(lines[-1].strip())),
        "ends_hash": lines[-1].startswith(b"####"),
        "early_final": any(l.startswith(b"####") for l in lines[:-1]),
        "last_line_bytes": len(lines[-1]),
        "line_bytes": statistics.mean(len(l) for l in lines[:-1]) if len(lines) > 1 else 0,
    }


def unescape(s):
    return s.encode("utf-8", "surrogateescape").decode("unicode_escape").encode("latin-1", "replace")


def main():
    held = problems_of(open(sys.argv[1], "rb").read())
    rows = []
    for line in open(sys.argv[2], "rb"):
        k, _, text = line.rstrip(b"\n").partition(b"\t")
        if not k.isdigit():
            continue
        w = text.decode("latin-1").encode("latin-1").decode("unicode_escape").encode("latin-1", "replace")
        rows.append((int(k), shape(w), shape(held[int(k)][1])))
    groups = {"shorter by over 25%": [], "within 25%": [], "longer by over 25%": []}
    for k, w, h in rows:
        r = w["bytes"] / h["bytes"]
        groups["shorter by over 25%" if r < 0.75 else "longer by over 25%" if r > 1.25 else "within 25%"].append((w, h))
    print(f"answers {len(rows)}; written ending with a final line at the boundary {sum(w['ends_final'] for _, w, _ in rows)} (a '####' line {sum(w['ends_hash'] for _, w, _ in rows)}); a final line before the end {sum(w['early_final'] for _, w, _ in rows)}")
    print("group\tn\tends final\tbytes w/h\tlines w/h\tsteps w/h\tbytes a line w/h")
    for g, xs in groups.items():
        if not xs:
            print(f"{g}\t0"); continue
        m = lambda key, i: statistics.mean(x[i][key] for x in xs)
        print(f"{g}\t{len(xs)}\t{sum(w['ends_final'] for w, _ in xs)}\t{m('bytes',0):.0f}/{m('bytes',1):.0f}\t{m('lines',0):.1f}/{m('lines',1):.1f}\t{m('steps',0):.1f}/{m('steps',1):.1f}\t{m('line_bytes',0):.0f}/{m('line_bytes',1):.0f}")
    cut = [w for _, w, _ in rows if not w["ends_hash"]]
    print(f"not ending on a '####' line: {len(cut)}; their last line's bytes mean {statistics.mean(w['last_line_bytes'] for w in cut):.0f}" if cut else "every answer ends on a '####' line")
    ws = [w['steps'] for _, w, _ in rows]; hs = [h['steps'] for _, _, h in rows]
    print(f"steps against held: correlation {statistics.correlation(ws, hs):+.3f}; lines {statistics.correlation([w['lines'] for _, w, _ in rows], [h['lines'] for _, _, h in rows]):+.3f}; bytes {statistics.correlation([w['bytes'] for _, w, _ in rows], [h['bytes'] for _, _, h in rows]):+.3f}")


if __name__ == "__main__":
    main()
