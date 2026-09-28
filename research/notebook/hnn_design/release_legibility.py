"""Count-only readings of released text: what emerges, monitored and never forced (F0 and F4;
#73, #148).

Brandon, September 28, on the first native releases: "you can see that it went for quotes multiple
times, meaning that will be a local statistic that we'll end up being able to monitor". These
readings watch such structure appear. They are receipts, never constraints on the release, and
never a reward.

An exterior codec step, stdlib only. It reads the owner-only blind input (`f5-blind-input.json`:
each diagnostic request with its native release and its request-aware retrieval control) and the
pinned choosing cut (u16 little-endian curated cells; codes below 256 are bytes, and the others are
section letters). It prints counts only, never text.

    HOLONICS_ROOT=<main checkout> python3 research/notebook/hnn_design/release_legibility.py

The readings, per corpus (the native releases, the controls, the requests):
- **texts**: the releases that are text rather than typed refusals;
- **paired delimiters**: for `()`, `[]`, `{}` and the curly quotes `“”`, the opens and closes, and
  the texts in which every close has an earlier open (a stack reading); for the self-paired
  backtick, straight quote and `**`, the texts in which the count is even;
- **word shape**: alphabetic tokens of at least two letters, and those met in the choosing cut's
  vocabulary. The choosing families are disjoint from the diagnostic requests' families, so the
  requests and the controls give the rate for legible text the vocabulary has not read.
"""

import json
import os
import re
import sys
from array import array

ROOT = os.environ.get(
    "HOLONICS_ROOT",
    os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))),
)
CUTS = os.path.join(ROOT, ".local", "cuts")
PAIRED = {"()": ("(", ")"), "[]": ("[", "]"), "{}": ("{", "}"), "“”": ("“", "”")}
SELF_PAIRED = {"backtick": "`", "straight quote": '"', "bold": "**"}
WORD = re.compile(r"[A-Za-z]{2,}")


def vocabulary(path):
    with open(path, "rb") as handle:
        codes = array("H")
        codes.frombytes(handle.read())
    if sys.byteorder != "little":
        codes.byteswap()
    parts, current = [], bytearray()
    for code in codes:
        if code < 256:
            current.append(code)
        else:
            parts.append(bytes(current))
            current = bytearray()
    parts.append(bytes(current))
    words = set()
    for part in parts:
        words.update(w.lower() for w in WORD.findall(part.decode("utf-8", errors="ignore")))
    return words


def closes_matched(text, opener, closer):
    depth = 0
    for char in text:
        if char == opener:
            depth += 1
        elif char == closer:
            if depth == 0:
                return False
            depth -= 1
    return True


def readings(texts, vocab):
    out: dict[str, object] = {"texts": len(texts)}
    for name, (opener, closer) in PAIRED.items():
        out[name] = {
            "opens": sum(t.count(opener) for t in texts),
            "closes": sum(t.count(closer) for t in texts),
            "texts with every close opened": sum(closes_matched(t, opener, closer) for t in texts),
            "texts balanced": sum(
                closes_matched(t, opener, closer) and t.count(opener) == t.count(closer)
                for t in texts
            ),
        }
    for name, mark in SELF_PAIRED.items():
        out[name] = {
            "marks": sum(t.count(mark) for t in texts),
            "texts with an even count": sum(t.count(mark) % 2 == 0 for t in texts),
        }
    tokens = [w.lower() for t in texts for w in WORD.findall(t)]
    out["word tokens"] = len(tokens)
    out["in the choosing vocabulary"] = sum(w in vocab for w in tokens)
    return out


def main():
    if sys.argv[1:]:
        sys.exit(__doc__)
    with open(os.path.join(CUTS, "f5-blind-input.json"), "rb") as handle:
        cases = json.load(handle)["cases"]
    vocab = vocabulary(os.path.join(CUTS, "curated-f5-choosing-cut.bin"))
    native = [c["responses"]["athena"]["text"] for c in cases]
    released = [t for t in native if not t.startswith("[typed refusal")]
    corpora = {
        "native releases": released,
        "retrieval controls": [c["responses"]["control"]["text"] for c in cases],
        "requests": [c["request"] for c in cases],
    }
    report = {
        "choosing vocabulary (distinct words)": len(vocab),
        "diagnostic cases": len(cases),
        "typed refusals": len(native) - len(released),
        "corpora": {name: readings(texts, vocab) for name, texts in corpora.items()},
    }
    print(json.dumps(report, indent=1, ensure_ascii=False))


if __name__ == "__main__":
    main()
