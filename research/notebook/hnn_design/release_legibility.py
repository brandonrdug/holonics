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

    HOLONICS_ROOT=<main checkout> python3 research/notebook/hnn_design/release_legibility.py [releases.json [choosing-cut.bin]]

The optional argument reads another owner-only release file of the same case shape (`request` and
`responses.athena.text`, e.g. F0's token releases `f0-token-releases.json`) in place of the blind
input; a corpus whose field that file does not carry (the retrieval controls) is not read. Every
other response every case carries is its own corpus (F0's acceptance run: `logged`, the held-out
continuation, and `flat`, the flat tree's release). The second argument names the choosing cut whose
vocabulary the words are read against (the F5 choosing cut by default; F0's acceptance run reads its
own split's, `curated-f0-choosing-cut.bin`).

The readings, per corpus (the native releases, the controls, the requests):
- **texts**: the releases that are text rather than typed refusals;
- **paired delimiters**: for `()`, `[]`, `{}` and the curly quotes `“”`, the opens and closes, and
  the texts in which every close has an earlier open (a stack reading); for the self-paired
  backtick, straight quote and `**`, the texts in which the count is even;
- **word shape**: alphabetic tokens of at least two letters, and those met in the choosing cut's
  vocabulary. The choosing families are disjoint from the diagnostic requests' families, so the
  requests and the controls give the rate for legible text the vocabulary has not read;
- **valid UTF-8**: where a response carries its `valid_utf8` flag, the cases whose bytes are valid
  UTF-8 (a native release that is not is a typed refusal, so its texts are all valid).
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
CORPUS = {"control": "retrieval controls", "logged": "logged replies (observed conduct, not targets)", "flat": "flat tree releases"}
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
    if len(sys.argv) > 3 or sys.argv[1:2] in (["-h"], ["--help"]):
        sys.exit(__doc__)
    path = sys.argv[1] if sys.argv[1:] else os.path.join(CUTS, "f5-blind-input.json")
    with open(path, "rb") as handle:
        cases = json.load(handle)["cases"]
    choosing = sys.argv[2] if sys.argv[2:] else os.path.join(CUTS, "curated-f5-choosing-cut.bin")
    vocab = vocabulary(choosing)
    native = [c["responses"]["athena"]["text"] for c in cases]
    released = [t for t in native if not t.startswith("[typed refusal")]
    corpora = {"native releases": released}
    flags = {}
    names = [name for name in cases[0]["responses"] if name != "athena"] if cases else []
    for name in ["athena"] + names:
        if all("valid_utf8" in c["responses"].get(name, {}) for c in cases):
            flags[name] = sum(bool(c["responses"][name]["valid_utf8"]) for c in cases)
    for name in names:
        if all(name in c["responses"] for c in cases):
            corpora[CORPUS.get(name, name)] = [c["responses"][name]["text"] for c in cases]
    corpora["requests"] = [c["request"] for c in cases]
    report = {
        "choosing vocabulary (distinct words)": len(vocab),
        "diagnostic cases": len(cases),
        "typed refusals": len(native) - len(released),
        "corpora": {name: readings(texts, vocab) for name, texts in corpora.items()},
    }
    if flags:
        report["valid UTF-8 (cases)"] = {
            ("native releases" if name == "athena" else CORPUS.get(name, name)): count
            for name, count in flags.items()
        }
    print(json.dumps(report, indent=1, ensure_ascii=False))


if __name__ == "__main__":
    main()
