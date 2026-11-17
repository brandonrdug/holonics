#!/usr/bin/env -S python3 -I
"""Windows of a store's own text as a `read-tension` table (the lead, November 17).

Usage: store_windows.py STORE OUT KEY WIDTH PLACES SLICE:COUNT [SLICE:COUNT …]

For each named slice of STORE (`DOCS_<slice>.bin`, the training documents; never a held file) it draws COUNT windows by KEY: an
offset from SHA-256 of `KEY:<slice>:<n>`, moved past the next space or line feed, WIDTH octets long. A window is kept where it is
printable ASCII with line feeds and holds no backslash and no tab (the table writes a line feed as a backslash and an `n`, and its
fields are tab-separated), and the draw goes on until COUNT are kept. Each row is `win:<slice>:<n>`, the window's first symbol as the
prompt, the rest as the run, and PLACES of the run's places drawn by the key, each to be opened alone.

Why: a ruler that closes a menu of the field's rows (`tools/loop_closure_ruler.py text`) is read on the store's own mixture, text
beside arithmetic, where the short sums were a specimen. The table holds private text and stays under `.local/`; only counts and
symbols leave a ruler that reads it."""
import hashlib
import mmap
import sys


def main():
    if len(sys.argv) < 7:
        sys.exit(__doc__)
    store, out, key, width, places = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5])
    rows = []
    for spec in sys.argv[6:]:
        name, count = spec.split(":")
        with open(f"{store}/DOCS_{name}.bin", "rb") as f:
            data = mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ)
            kept, n = 0, 0
            while kept < int(count):
                seed = int.from_bytes(hashlib.sha256(f"{key}:{name}:{n}".encode()).digest(), "big")
                n += 1
                # A window starts after the next space or line feed within 200 octets of the drawn offset (a slice may hold documents
                # with no line feed at all, so a search for one is bounded).
                at = seed % (len(data) - 300 - width)
                near = data[at : at + 200]
                cuts = [k for k in (near.find(b" "), near.find(b"\n")) if k >= 0]
                start = at + (min(cuts) if cuts else -1)
                window = data[start + 1 : start + 1 + width]
                if len(window) < width or any((c < 0x20 or c > 0x7E) and c != 0x0A for c in window) or b"\\" in window or window[0] in (0x0A, 0x20):
                    continue
                text = window.decode("ascii")
                order = sorted(range(width - 1), key=lambda j: hashlib.sha256(f"{key}:{name}:{n}:place:{j}".encode()).digest())
                chosen = sorted(order[:places])
                rows.append("\t".join([f"win:{name}:{kept}", text[0], text[1:].replace("\n", "\\n"), ",".join(map(str, chosen))]))
                kept += 1
            print(f"WINDOWS slice={name} kept={kept} drawn={n}")
    with open(out, "x") as f:
        f.write("\n".join(rows) + "\n")
    print(f"WINDOWS_TABLE rows={len(rows)} places={len(rows) * places} width={width}")


if __name__ == "__main__":
    main()
