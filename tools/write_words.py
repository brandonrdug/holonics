"""A ruler: the words a write shares with its slice's passage, and the write's commonest byte (the theory thread's W2 and W3 of
November 16 16:37 UTC).

Usage: python3 -I tools/write_words.py STORE WRITES [WRITES ...]. For each WRITES directory (a write-store output: `{slice}_{nn}.written`)
and each slice, prints the share of the writes' whitespace-separated strings of two or more octets that occur as whitespace-separated
strings in the slice's training prefix (its share of the line's first gigabyte, read from the front of `DOCS_{slice}.bin`, whose shares
are `STORE.tsv`'s), and the share of the slice's written octets taken by its commonest octet. A ruler on the host, outside the machine:
it measures what a write holds and never enters a law. It prints counts and shares only, never a text (the held documents and the writes
are private)."""
import os
import sys
from collections import Counter

GIGABYTE = 1_000_000_000
CHUNK = 64 << 20


def shares(store):
    out = {}
    with open(os.path.join(store, 'STORE.tsv')) as f:
        head = f.readline().rstrip('\n').split('\t')
        for line in f:
            row = dict(zip(head, line.rstrip('\n').split('\t')))
            if row.get('role') == 'train':
                out[row['slice']] = int(row['share'])
    return out


def words_of(path_bytes):
    return [w for w in path_bytes.split() if len(w) >= 2]


def present(store, name, octets, wanted):
    """The wanted strings met as whitespace-separated strings in the first `octets` of the slice's documents."""
    found = set()
    with open(os.path.join(store, f'DOCS_{name}.bin'), 'rb') as f:
        left = octets
        carry = b''
        while left > 0 and len(found) < len(wanted):
            block = f.read(min(CHUNK, left))
            if not block:
                break
            left -= len(block)
            block = carry + block
            cut = max(block.rfind(b' '), block.rfind(b'\n'))
            body, carry = (block[:cut], block[cut:]) if cut > 0 else (block, b'')
            for w in body.split():
                if w in wanted:
                    found.add(w)
    return found


def main():
    store, dirs = sys.argv[1], sys.argv[2:]
    share = shares(store)
    per = {}
    for d in dirs:
        for fn in sorted(os.listdir(d)):
            if fn.endswith('.written'):
                name = fn.rsplit('_', 1)[0]
                text = open(os.path.join(d, fn), 'rb').read()
                per.setdefault(name, {}).setdefault(d, []).append(text)
    for name in sorted(per):
        wanted = set()
        for d in dirs:
            for text in per[name].get(d, []):
                wanted.update(words_of(text))
        found = present(store, name, share.get(name, 0) * GIGABYTE // 100, wanted)
        for d in dirs:
            texts = per[name].get(d, [])
            ws = [w for t in texts for w in words_of(t)]
            octets = b''.join(texts)
            top = Counter(octets).most_common(1)
            top_share = top[0][1] / len(octets) if octets else 0.0
            met = sum(1 for w in ws if w in found)
            print(f'WRITE_WORDS writes={os.path.basename(d.rstrip("/"))} slice={name} strings={len(ws)} in_passage={met} share={met / len(ws) if ws else 0.0:.3f} commonest_octet={top[0][0] if top else -1} commonest_share={top_share:.3f}')


if __name__ == '__main__':
    main()
