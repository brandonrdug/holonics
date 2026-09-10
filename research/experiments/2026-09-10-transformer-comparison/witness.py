"""Exterior exact witnesses for the accompanying architecture review.

These calculations inspect declared maps. They neither run nor train native HNN,
and do not test language quality or replace a production owner.
"""

from collections import Counter
from fractions import Fraction as F
import json


def dot(a, b):
    return sum(x * y for x, y in zip(a, b, strict=True))


def normal_signature(word):
    basis = {"0": (1, 0), "1": (0, 1)}
    rows = []
    for previous, current, following in zip(word, word[1:], word[2:]):
        p, c, v = map(basis.__getitem__, (previous, current, following))
        x = tuple(a - b for a, b in zip(c, p)) + c + p
        y = tuple(a - b for a, b in zip(v, c))
        rows.append((x, y))
    h = [[int(i == j) + sum(x[i] * x[j] for x, _ in rows)
          for j in range(6)] for i in range(6)]
    b = [[sum(y[i] * x[j] for x, y in rows)
          for j in range(6)] for i in range(2)]
    return {"H": h, "B": b, "target_energy": sum(dot(y, y) for _, y in rows),
            "observations": len(rows), "seed": [basis[word[0]], basis[word[1]]]}


left, right = "000100", "001000"
triples = lambda word: Counter(word[i:i + 3] for i in range(len(word) - 2))
assert left != right and triples(left) == triples(right)
assert normal_signature(left) == normal_signature(right)
assert left[2] != right[2]

# A fixed admitted population and fixed values can return different responses.
values = [F(-1), F(1)]
old_weights, new_weights = [F(3, 4), F(1, 4)], [F(1, 4), F(3, 4)]
old_output, new_output = dot(old_weights, values), dot(new_weights, values)
assert (old_output, new_output) == (F(-1, 2), F(1, 2))

# Full finite difference: changing transported values AND contact weights.
new_values = [F(2), F(3)]
value_change = dot(new_weights, [v2 - v for v2, v in zip(new_values, values)])
contact_change = dot([a2 - a for a2, a in zip(new_weights, old_weights)], values)
full_change = dot(new_weights, new_values) - old_output
assert full_change == value_change + contact_change

# A present receiver's kernel need not remain invisible after one operation.
state_a, state_b = [0, 0], [0, 1]
swap = lambda state: [state[1], state[0]]
receiver = lambda state: state[0]
assert receiver(state_a) == receiver(state_b)
assert receiver(swap(state_a)) != receiver(swap(state_b))

print(json.dumps({
    "scope": "exact exterior map witnesses; no native execution or model-quality claim",
    "local_stencil_collision": {
        "words": [left, right], "trigram_population": dict(sorted(triples(left).items())),
        "same_normal_geometry_energy_count_seed": True,
        "separating_exterior_third_symbols": [left[2], right[2]],
        "normal_signature": normal_signature(left),
    },
    "same_standing_and_support_new_response": list(map(str, [old_output, new_output])),
    "finite_attention_difference": {
        "value_term": str(value_change), "contact_term": str(contact_change),
        "complete_difference": str(full_change),
    },
    "present_receiver_is_not_future_receiver": {
        "present": [receiver(state_a), receiver(state_b)],
        "after_swap": [receiver(swap(state_a)), receiver(swap(state_b))],
    },
}, indent=2))
