"""Cold exact witness for the declared fixed-condition source assay; never a native learner."""
import argparse
import json
import struct
from collections import Counter, defaultdict, deque
from fractions import Fraction
from pathlib import Path


def derive(dataset, model):
    calibration = json.loads((model / "source-return.json").read_text())
    wanted = {f["sequence"] for f in calibration["fields"]}
    frames = {}
    with dataset.open() as stream:
        for line in stream:
            value = json.loads(line)
            if value.get("sequence") in wanted:
                frames[value["sequence"]] = value
    rows, by_pair, symbols = [], defaultdict(dict), set()
    for field in calibration["fields"]:
        frame = frames[field["sequence"]]
        assert frame["partition"] == "development"
        parts = [(p["text"], view["event"]) for view in frame["views"]
                 for p in view["visible_parts"] if p["ordinal"] == field["part"]
                 and p.get("text") is not None]
        assert len({text for text, _ in parts}) == 1
        text, event = parts[0]
        assert len(text) - 2 == field["observations"]
        symbols.update(text)
        for at in range(len(text) - 2):
            p, c, y = text[at:at + 3]
            row = {"source_pair": [p, c], "target": y,
                   "occurrence": {"sequence": frame["sequence"], "part": field["part"],
                                  "row": at, "event": event}}
            rows.append(row)
            by_pair[p, c].setdefault(y, row)
    assert len(rows) == calibration["observations"]
    parent = {x: x for x in symbols}

    def root(x):
        while parent[x] != x:
            x = parent[x]
        return x

    witnesses = []
    for variants in by_pair.values():
        first = next(iter(variants))
        for other in variants:
            a, b = root(first), root(other)
            if a != b:
                parent[b] = a
                witnesses.append([(1, variants[other]), (-1, variants[first])])
    direct_rank = len(witnesses)
    active = {v["target"] for v in rows}
    active_components = {root(x) for x in active}
    # The native input is (c-p,c,p,h=1,(c-p,c,p)*h). Thus a signed input-pair cycle
    # cancels all native feature coordinates, including the constant condition.
    tree = defaultdict(list)
    for item in rows:
        p, c = item["source_pair"]
        start, end = ("p", p), ("c", c)
        todo, paths = deque([start]), {start: []}
        while todo and end not in paths:
            node = todo.popleft()
            for other, edge in tree[node]:
                if other not in paths:
                    sign = 1 if node[0] == "p" else -1
                    paths[other] = paths[node] + [(sign, edge)]
                    todo.append(other)
        if end not in paths:
            tree[start].append((end, item)); tree[end].append((start, item))
            continue
        combination = [(1, item)] + [(-sign, edge) for sign, edge in paths[end]]
        quotient = Counter()
        for sign, edge in combination:
            quotient[root(edge["target"])] += sign
        if any(quotient.values()):
            # This actual assay has two target components after direct equal-pair contrasts.
            # The nonzero cycle identifies their remaining rational difference direction.
            assert len(active_components) == 2
            witnesses.append(combination)
            break
    vectors = []
    for combination in witnesses:
        source, target = Counter(), Counter()
        for sign, item in combination:
            p, c = item["source_pair"]
            source["p", p] += sign; source["c", c] += sign
            target[item["target"]] += sign
        assert not any(source.values()) and sum(target.values()) == 0
        vectors.append({x: Fraction(v) for x, v in target.items() if v})
    reduced = {}
    for vector in vectors:
        for p in sorted(active):
            if not vector.get(p):
                continue
            if p not in reduced:
                factor = vector[p]
                reduced[p] = {x: v / factor for x, v in vector.items() if v}
                break
            factor = vector[p]
            for x, v in reduced[p].items():
                vector[x] = vector.get(x, 0) - factor * v
    assert len(reduced) == len(active) - 1

    def blob(stream):
        length, = struct.unpack("<Q", stream.read(8))
        value = stream.read(length)
        assert len(value) == length
        return value

    with (model / "local-law.fibre").open("rb") as stream:
        magic = b"HOLONIC-CONSTITUTIVE-FIBRE\x01"
        assert stream.read(len(magic)) == magic
        header = json.loads(blob(stream)); packed = blob(stream)
        assert stream.read() == b"HOLONIC-CONSTITUTIVE-END\x01"
    count_rows, width, count = struct.unpack_from("<QQQ", packed)
    assert count_rows == width and count == width * width and len(packed) == 24 + 8 * count
    basis = memoryview(packed)[24:].cast("q")
    assert struct.pack("=q", 1) == struct.pack("<q", 1), "declare little-endian cold chart"
    alphabet = json.loads((model / "exterior-chart.json").read_text())
    spelling = [bytes(v).decode() for v in alphabet["octets"]]
    indices = {v: i for i, v in enumerate(spelling)}
    n = len(spelling); f = header["source_width"]
    assert header["occurrences"] == len(rows) and header["target_width"] == 2 * n
    assert f == 2 * (3 * n + 1 + 3 * n) and width == f + 2 * n
    assert header["source_chart"] == {"kind": "bilinear-contact", "source_complex": 3*n, "condition_complex": 1}
    sparse, vertical_rank = {}, 0
    for p in range(width):
        row = basis[p * width:(p + 1) * width]
        assert row[p] >= 0 and not any(row[:p])
        if not row[p]:
            assert not any(row)
            continue
        sparse[p] = {j: value for j, value in enumerate(row) if value}
        assert sum(row[2 * n + 2 * j] for j in range(n)) == row[6 * n]
        assert row[6 * n + 1] == 0
        assert sum(row[f + 2 * j] for j in range(n)) == 0
        # y = eta + source.current: its support is precisely the observed target alphabet.
        for j, label in enumerate(spelling):
            assert row[f + 2*j + 1] + row[2*n + 2*j + 1] == 0
            if label not in active:
                assert row[f + 2*j] + row[2*n + 2*j] == 0
        if p >= f:
            vertical_rank += 1
    assert vertical_rank == len(active) - 1
    source_basis = {}
    for previous, current in by_pair:
        vector = {indices[previous]: Fraction(1), n + indices[current]: Fraction(1)}
        while vector:
            pivot = min(vector)
            if pivot not in source_basis:
                scale = vector[pivot]
                source_basis[pivot] = {j: v / scale for j, v in vector.items()}
                break
            scale = vector[pivot]
            for j, v in source_basis[pivot].items():
                vector[j] = vector.get(j, 0) - scale * v
                if not vector[j]: del vector[j]
    assert len(source_basis) + len(reduced) == len(sparse)
    # Check each actual presented pair against the detached native relation, not just its count.
    for item in rows:
        p, c = map(indices.__getitem__, item["source_pair"]); y = indices[item["target"]]
        phi = Counter({2*n + 2*c: 1, 4*n + 2*p: 1})
        phi[2*c] += 1; phi[2*p] -= 1
        value = Counter(phi); value[6*n] = 1
        for j, v in phi.items(): value[6*n + 2 + j] += v
        value[f + 2*y] += 1; value[f + 2*c] -= 1
        value = {j: Fraction(v) for j, v in value.items() if v}
        while value:
            p = min(value); assert p in sparse
            factor = value[p] / sparse[p][p]
            for j, v in sparse[p].items():
                value[j] = value.get(j, 0) - factor * v
                if not value[j]: del value[j]
    return {"scope": "exact fixed-condition local-relation collapse witness",
            "observations": len(rows), "source_pairs": len(by_pair),
            "conflicting_source_pairs": sum(len(v) > 1 for v in by_pair.values()),
            "source_symbols": len(symbols), "target_symbols": sorted(active),
            "direct_contrast_rank": direct_rank, "witness_rank": len(reduced),
            "native_vertical_rank": vertical_rank, "native_relation_rank": len(sparse),
            "presented_source_rank": len(source_basis),
            "native_equals_presented_span_by_inclusion_and_rank": True,
            "all_presented_rows_in_native_relation": True,
            "unit_source_condition_forced": "h=(1,0)",
            "unit_mass_fibre_minimum_norm_coordinate": str(Fraction(1, len(active))),
            "witnesses": [[{"coefficient": a, **row} for a, row in witness] for witness in witnesses]}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("dataset", type=Path); parser.add_argument("model", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    result = derive(args.dataset, args.model)
    with args.output.open("x") as stream:
        json.dump(result, stream, indent=2, ensure_ascii=False); stream.write("\n")
    print(json.dumps({k: v for k, v in result.items() if k not in {"witnesses", "target_symbols"}}, indent=2))
