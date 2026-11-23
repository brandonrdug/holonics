#!/usr/bin/env -S python3 -I
"""Rows for the word-start presence read (the lead, November 23): passages of the held theory and the held books, each up to 320 bytes
cut at a line start, as `read-strand-states`'s rows (`id \t text \t \n`, line feeds escaped). Usage: word_rows.py STORE N OUT"""
import sys
store, n, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
rows = []
for sl in ('theory', 'books'):
    data = open(f'{store}/HELD_{sl}.bin', 'rb').read().decode('utf-8', 'replace')
    at, k = 0, 0
    while k < n and at < len(data) - 400:
        cut = data[at:at + 320]
        cut = cut[:cut.rfind('\n') + 1] if cut.rfind('\n') > 120 else cut
        if '\t' not in cut and '\\n' not in cut and cut.isprintable() is False or True:
            text = cut.replace('\t', ' ')
            if len(text.encode()) > 100 and '\\' not in text:
                rows.append((f'{sl}:{k}', text))
                k += 1
        at += 4096
with open(out, 'w') as f:
    for ident, text in rows:
        f.write(f"{ident}\t{text.replace(chr(10), chr(92) + 'n')}\t\\n\n")
print('ROWS', len(rows))
