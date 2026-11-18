#!/usr/bin/env -S python3 -I
"""A ruler: what a count of the places before a place writes from the panel's prompts (the lead, November 18; the record of the two
streams §16).

The machine's writes are judged by the words they hold, and its code is set against a count of the places before a place. This sets
the two beside each other in the writes' own measure: from each prompt of a panel, the count of at most K places before (the
Witten-Bell count of `frontier_excess_ruler.py`, fitted on the first TRAIN octets of the slice's training documents) writes PLACES
octets, each drawn from its face after the octets before it, DRAWS times with seeded draws. The share of written words (alphabetic
strings of two letters or more, lowered) that stand in the slice's lexicon is printed for every K from 1 to KMAX, over all the write
and by quarter of its places, with the same share of the panel's own writes and of its reference continuations where the panel
holds them. So a machine's share of lexicon words can be read against the order of count whose writes hold as many.

PANEL is a `forms.written` of the panel (`label<TAB>prompt<TAB>write[<TAB>reference]`, a label `slice:...`, newlines written `\\n`);
its labels, prompts, writes and references are read. LEXICON is a pickle of `{slice: set of words}`, the scorer's own. A host
instrument: a count table enters no law and writes nothing the machine reads. It prints counts and shares only, never a text.

Usage: count_writer_ruler.py STORE LEXICON PANEL SLICE TRAIN_OCTETS KMAX PLACES DRAWS"""
import os, pickle, random, re, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from frontier_excess_ruler import fit

WORD = re.compile(r"[A-Za-z]{2,}")

def face_at(model, seq, k_at_most, base):
    """The count's face over the octets after `seq`, backing off from at most `k_at_most` places before."""
    _, counts, totals = model
    face = base
    for k in range(1, min(k_at_most, len(seq)) + 1):
        ctx = seq[len(seq) - k:]
        t = totals[k].get(ctx)
        if t is not None:
            cn, scale = counts[k], 1.0 / (t[0] + t[1])
            face = [(cn.get(ctx + bytes((a,)), 0) + t[1] * face[a]) * scale for a in range(256)]
    return face

def score(text, lexicon, bins):
    for m in WORD.finditer(text):
        q = min(m.start() * 4 // max(len(text), 1), 3)
        hit = m.group(0).lower() in lexicon
        for b in (q, 4):
            bins[b][0] += 1
            bins[b][1] += hit

def line(bins):
    names = ["q1", "q2", "q3", "q4", "all"]
    return " ".join(f"{names[b]}={bins[b][1]}/{bins[b][0]}({100 * bins[b][1] // max(bins[b][0], 1)}%)" for b in (4, 0, 1, 2, 3))

def main():
    store, lexp, panel, name = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
    train_n, kmax, places, draws = (int(a) for a in sys.argv[5:9])
    lexicon = pickle.load(open(lexp, "rb"))[name]
    prompts, refs, own = [], [], []
    for l in open(panel, newline="\n", errors="replace"):
        f = l.rstrip("\n").split("\t")
        if f[0].split(":")[0] == name:
            prompts.append(f[1].replace("\\n", "\n").encode("utf-8", "replace"))
            own.append(f[2].replace("\\n", "\n"))
            if len(f) > 3:
                refs.append(f[3].replace("\\n", "\n"))
    model = fit(open(f"{store}/DOCS_{name}.bin", "rb").read(train_n), kmax)
    uni = model[0]
    tot, seen = sum(uni), sum(1 for v in uni if v)
    base = [(u + seen / 256.0) / (tot + seen) for u in uni]
    octets = list(range(256))
    if refs:
        bins = [[0, 0] for _ in range(5)]
        for r in refs:
            score(r, lexicon, bins)
        print(f"COUNT_WRITER slice={name} prompts={len(prompts)} the_reference: {line(bins)}", flush=True)
    bins = [[0, 0] for _ in range(5)]
    for w in own:
        score(w, lexicon, bins)
    print(f"COUNT_WRITER slice={name} prompts={len(prompts)} the_panels_write: {line(bins)}", flush=True)
    for k in range(1, kmax + 1):
        bins = [[0, 0] for _ in range(5)]
        for p, prompt in enumerate(prompts):
            for d in range(draws):
                rng = random.Random(f"{name}:{p}:{d}:{k}")
                seq = bytearray(prompt[-kmax:])
                for _ in range(places):
                    seq.append(rng.choices(octets, weights=face_at(model, bytes(seq), k, base))[0])
                score(bytes(seq[len(prompt[-kmax:]):]).decode("utf-8", "replace"), lexicon, bins)
        print(f"COUNT_WRITER slice={name} prompts={len(prompts)} draws={draws} places={places} train_octets={train_n} k={k}: {line(bins)}", flush=True)

if __name__ == "__main__":
    main()
