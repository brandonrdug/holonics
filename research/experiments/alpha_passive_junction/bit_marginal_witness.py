"""Exact exterior-codec witness; no learner, corpus replay, or native morphology selection."""
from fractions import Fraction
import json


def face(distribution):
    # TextSymbol::inputs: one unit current in each of nine addressed bit pairs.
    return [sum((weight for word, weight in distribution if (word >> bit) & 1 == value),
                Fraction()) for bit in range(9) for value in range(2)]


def decode(mean):
    assert all(mean[2*b] != mean[2*b+1] for b in range(9))
    return sum((mean[2*b+1] > mean[2*b]) << b for b in range(9))


if __name__ == "__main__":
    ensemble = [(ord(c), Fraction(1, 3)) for c in "356"]
    mean = face(ensemble)
    emitted = decode(mean)
    assert emitted == ord("7") and emitted not in dict(ensemble)
    left = [(ord(c), Fraction(1, 2)) for c in "03"]
    right = [(ord(c), Fraction(1, 2)) for c in "12"]
    assert face(left) == face(right)
    assert set(dict(left)).isdisjoint(dict(right))
    print(json.dumps({
        "schema": "holonics.bit-marginal-receiver-witness.v1",
        "scope": "Exact receiver-chart counterexample, not an Athena language diagnosis or learner",
        "mixture": {chr(c): str(w) for c, w in ensemble},
        "mean_bit_pair_currents": list(map(str, mean)),
        "certain_marginal_decoding": chr(emitted),
        "decoded_symbol_in_ensemble": False,
        "distinct_joint_fibres": ["03", "12"],
        "same_marginal_face": list(map(str, face(left))),
        "joint_distinction_retained_by_full_source_history": True,
    }, indent=2))
