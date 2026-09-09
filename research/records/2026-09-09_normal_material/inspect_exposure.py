"""Read the actual exposed duplex octets from retained native lineage.

Usage: python inspect_exposure.py PRIVATE_REPORT.json NEW_RECEIPT.json --word the
The ASCII word observer is exterior: it supplies no tokenizer or frequency law to HNN.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import re
import runpy

packet = runpy.run_path(str(Path(__file__).with_name("inspect_phase_comparison.py")))["packet"]
WORDS = re.compile(rb"[A-Za-z]+(?:'[A-Za-z]+)?")
OCTET_CARDINALITY = 1 << 8  # The exterior byte chart, with EndPart immediately after it.


def inspect(document, word):
    width = document["material_target"]["factor_width"]
    parts = {"incoming": [], "outgoing": []}
    pending = bytearray()
    direction = None
    cut = document["development_native_until"]
    for event in document["body"]["lineage"][:cut]:
        coordinate, amplitude = packet(event["incoming"], width)
        side = {(1, 0): "incoming", (0, 1): "outgoing"}[amplitude]
        assert direction is None or direction == side
        direction = side
        if coordinate == OCTET_CARDINALITY:
            parts[side].append(bytes(pending))
            pending.clear()
            direction = None
        else:
            assert coordinate < OCTET_CARDINALITY
            pending.append(coordinate)
    assert direction is None and not pending, "observation cut is inside a part"
    returned = {}
    for side, texts in parts.items():
        counts = Counter(w.decode("ascii").lower() for text in texts for w in WORDS.findall(text))
        others = [(key, count) for key, count in counts.most_common() if key != word]
        maximum = others[0][1] if others else None
        returned[side] = {
            "parts": len(texts),
            "source_octets": sum(map(len, texts)),
            "ascii_word_occurrences": sum(counts.values()),
            "queried_word": word,
            "queried_count": counts[word],
            "largest_other_count": maximum,
            "largest_other_words": [key for key, count in others if count == maximum],
        }
    return returned


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path)
    parser.add_argument("receipt", type=Path)
    parser.add_argument("--word", required=True)
    args = parser.parse_args()
    document = json.loads(args.report.read_text())
    result = {
        "grade": "established-bounded",
        "evidence": ["measured"],
        "scope": "Actual exposed octets only, before prompt and generation. ASCII words are "
                 "lowercased; curly apostrophes split words. No corpus-wide frequency or causal claim.",
        "native_development_until": document["development_native_until"],
        "word_pattern": WORDS.pattern.decode("ascii"),
        "measurement": inspect(document, args.word.lower()),
    }
    with args.receipt.open("x") as out:
        json.dump(result, out, indent=2)
        out.write("\n")


if __name__ == "__main__":
    main()
