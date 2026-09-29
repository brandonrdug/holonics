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
continuation, and `flat`, the flat tree's release; U6's symmetric comparison: `tree`, the control
tree's release over the whole stream, stopping at its own drawn letter, and `logged`). A released
corpus's typed refusals (a text beginning `[typed refusal`) are counted and not read as text. The
second argument names the choosing cut whose vocabulary the words are read against (the F5 choosing
cut by default; F0's acceptance run reads its own split's, `curated-f0-choosing-cut.bin`, and U6's
`curated-u6-choosing-cut.bin`).

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

A release file or a choosing cut whose manifest does not name the development reserve as excluded
(every one written before the reserve was named) is refused unless the logged flag `--read-reserve`
is passed (`development_families.py`).
"""

import json
import os
import re
import sys
from array import array

from development_families import require_reserve_excluded, reserve_flag
from standing_cut import OUT_DIR as CUTS
CORPUS = {"control": "retrieval controls", "logged": "logged replies (observed conduct, not targets)", "flat": "flat tree releases",
          "tree": "control tree releases (the whole stream, its own stop)"}
REFUSAL = "[typed refusal"
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
    arguments, read_reserve = reserve_flag(sys.argv[1:], "release_legibility.py")
    if len(arguments) > 2 or arguments[:1] in (["-h"], ["--help"]):
        sys.exit(__doc__)
    path = arguments[0] if arguments else os.path.join(CUTS, "f5-blind-input.json")
    choosing = arguments[1] if arguments[1:] else os.path.join(CUTS, "curated-f5-choosing-cut.bin")
    with open(choosing[:-len(".bin")] + ".json" if choosing.endswith(".bin") else choosing + ".json", "rb") as handle:
        require_reserve_excluded(json.load(handle), "the choosing cut", read_reserve)
    with open(path, "rb") as handle:
        released_file = json.load(handle)
    require_reserve_excluded(released_file, "the release file", read_reserve)
    cases = released_file["cases"]
    vocab = vocabulary(choosing)
    native = [c["responses"]["athena"]["text"] for c in cases]
    released = [t for t in native if not t.startswith(REFUSAL)]
    corpora = {"native releases": released}
    refusals = {"native releases": len(native) - len(released)}
    flags = {}
    names = [name for name in cases[0]["responses"] if name != "athena"] if cases else []
    for name in ["athena"] + names:
        if all("valid_utf8" in c["responses"].get(name, {}) for c in cases):
            flags[name] = sum(bool(c["responses"][name]["valid_utf8"]) for c in cases)
    for name in names:
        if all(name in c["responses"] for c in cases):
            texts = [c["responses"][name]["text"] for c in cases]
            corpus = CORPUS.get(name, name)
            if all("status" in c["responses"][name] for c in cases):
                # A released corpus (each release carries its status): its typed refusals apart.
                corpora[corpus] = [t for t in texts if not t.startswith(REFUSAL)]
                refusals[corpus] = len(texts) - len(corpora[corpus])
            else:
                corpora[corpus] = texts
    corpora["requests"] = [c["request"] for c in cases]
    report = {
        "choosing vocabulary (distinct words)": len(vocab),
        "diagnostic cases": len(cases),
        "typed refusals": refusals["native releases"] if len(refusals) == 1 else refusals,
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
