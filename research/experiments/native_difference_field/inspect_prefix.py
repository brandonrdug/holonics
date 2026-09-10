"""Cold comparison receiver for a completed conversation_difference_field run.

Reads the supplied source only to compute comparison data terms. It does not fit or change
native coefficients, select developmental material, or enter a cultivation/inference pipeline.
Usage: inspect_prefix.py PRIVATE_RUN SOURCE_EXPOSURE NEW_PUBLIC_RECEIPT
"""
import json
import sys
from collections import Counter, defaultdict
from fractions import Fraction
from pathlib import Path


def integer(value):
    sign, limbs = value
    return sign * sum(word << (32 * at) for at, word in enumerate(limbs))


def rational(value):
    return Fraction(integer(value[0]), integer(value[1]))


def inspect(directory, source):
    summary = json.loads((directory / "summary.json").read_text())
    returned = json.loads((directory / "returns.json").read_text())
    state = json.loads((directory / "native-state.json").read_text())
    words = state["intervals"]
    assert state["schema"] == "holonics.normal-state-data.v1"
    assert all(a == b for a, b in words)
    n = summary["alphabet_coordinates"]
    m = 3 * n
    # The published normal source chart: complex matrix plus three wide bounds, followed by
    # Gram, cross-source and four exact moments. Derive wire extent from the actual section.
    matrix_words = 2 * (2 * m * n + 3)
    gram_scalars, cross_scalars = 2 * m * m, 2 * m * n
    extent = gram_scalars + cross_scalars + 4
    moment_words, remainder = divmod(len(words) - matrix_words, extent)
    assert remainder == 0 and moment_words > 1
    cross_at = matrix_words + moment_words * gram_scalars
    for component in range(2 * m):
        total = 0
        for row in range(n):
            at = cross_at + moment_words * (row * 2 * m + component)
            block = [a for a, _ in words[at:at + moment_words]]
            magnitude = sum(word << (32 * j) for j, word in enumerate(block[:-1]))
            assert block[-1] in (0, 1)
            total += -magnitude if block[-1] else magnitude
        assert total == 0, "constant output receiver does not annihilate the exact cross-source matrix"
    probes = 0
    for record in returned:
        for probe in record["probes"]:
            for side in ("before", "after"):
                ball = probe[side]
                real = sum((rational(v["real"]) for v in ball["center"]), Fraction())
                imag = sum((rational(v["imaginary"]) for v in ball["center"]), Fraction())
                radius = rational(ball["radius"])
                assert real * real + imag * imag <= n * radius * radius
                probes += 1
    objective = {
        key: ({side: str(rational(q)) for side, q in value.items()}
              if isinstance(value, dict) else str(rational(value)))
        for key, value in summary["objective"].items()
    }
    counts, conditioned = Counter(), defaultdict(Counter)
    population = unchanged_error = 0
    with source.open() as file:
        next(file)  # source manifest
        for _ in range(summary["calibrated_frames"]):
            frame = json.loads(next(file))
            if frame["partition"] != "development":
                continue
            # Successful source intake already requires agreement of captured presentations.
            for part in frame["views"][0]["visible_parts"]:
                text = part.get("text") or ""
                for previous, current, later in zip(text, text[1:], text[2:]):
                    counts[later] += 1
                    conditioned[current][later] += 1
                    population += 1
                    unchanged_error += current != later
    assert population == summary["observed_local_comparisons"]
    mean = (population - sum(Fraction(v * v, population) for v in counts.values())) / 2
    conditional = sum(
        (sum(row.values()) - sum(Fraction(v * v, sum(row.values())) for v in row.values())) / 2
        for row in conditioned.values()
    )
    data = Fraction(objective["nominal_data_term"])
    summary.update({
        "objective": objective,
        "native_field_seconds_sum": sum(r["native_seconds"] for r in returned),
        "native_field_seconds_range": [min(r["native_seconds"] for r in returned), max(r["native_seconds"] for r in returned)],
        "native_deeds_total": sum(r["native_deeds"] for r in returned),
        "numerical_section_readouts_during_operations": sum(r["numerical_section_readouts_during_operation"] for r in returned),
        "ingress_octets_during_operations": sum(r["ingress_octets_during_operation"] for r in returned),
        "exact_cross_source_constant_receiver_zero": True,
        "constant_receiver_probe_enclosure_checks": probes,
        "native_state_file_octets": (directory / "native-state.json").stat().st_size,
        "comparison_receivers": {
            "scope": "In-sample squared-error data terms on the same eligible source sites; no source choice or coefficient enters native development from these references.",
            "unchanged_current_data_term": str(unchanged_error),
            "unconditional_next_face_mean_data_term": str(mean),
            "current_face_conditional_mean_data_term": str(conditional),
            "native_difference_response_data_term": str(data),
            "native_below_unconditional_mean": data < mean,
            "native_below_current_face_conditional_mean": data < conditional,
        },
    })
    return summary


if __name__ == "__main__":
    result = inspect(Path(sys.argv[1]), Path(sys.argv[2]))
    with Path(sys.argv[3]).open("x") as file:
        json.dump(result, file, indent=2)
        file.write("\n")
