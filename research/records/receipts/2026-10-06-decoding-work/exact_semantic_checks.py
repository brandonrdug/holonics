"""Exterior exact semantic witnesses; no HNN solver, simulation or floating operand."""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import resource
import signal
import time

ROOT = Path(__file__).resolve().parent
PRIOR_UNIT_UPPER_NS = 6_956_621  # pinned October 4 whole exact-fixture development read
COUNT = 5
PROJECTION_NS = COUNT * PRIOR_UNIT_UPPER_NS


def norm_energy(x):
    return sum(t * t for t in x) / 2


def decoder_signs():
    def reconstruct(x):
        return (x[0] + 2 * x[1], Q(0))
    readings = []
    for x, expected in (((Q(0), Q(1)), Q(3, 2)), ((Q(-2), Q(1)), Q(-5, 2))):
        decoded = reconstruct(x)
        assert reconstruct(decoded) == decoded
        error = norm_energy(decoded) - norm_energy(x)
        assert error == expected
        readings.append(str(error))
    return {"decoded_minus_physical_energy": readings, "decoder_idempotent": True}


def material_area_work():
    # Declared exact exterior units: C0=3 compliance units, L0=5 inertance units.
    c0, l0 = Q(3), Q(5)
    c1, l1 = 2 * c0, l0 / 2
    def energy(q, phi, c, ell):
        return q * q / (2 * c) + phi * phi / (2 * ell)
    kinetic = energy(Q(0), Q(11), c1, l1) - energy(Q(0), Q(11), c0, l0)
    potential = energy(Q(7), Q(0), c1, l1) - energy(Q(7), Q(0), c0, l0)
    assert kinetic == Q(121, 10) > 0
    assert potential == Q(-49, 12) < 0
    assert c1 * l1 == c0 * l0  # doubling area need not change this mode frequency
    return {"kinetic_material_work": str(kinetic), "potential_material_work": str(potential),
            "volume_ratio": "2", "LC_unchanged": True}


def pressure_face_future_separator():
    c, ell = Q(6), Q(5, 2)
    states = ((Q(0), Q(0)), (Q(0), Q(11)))
    pressure = [q / c for q, phi in states]
    # An actual declared one-mode incidence is 1; qdot=phi/L, pdot=qdot/C.
    rate = [phi / (ell * c) for q, phi in states]
    assert pressure == [0, 0]
    assert rate == [0, Q(11, 15)]
    return {"same_pressure_face": [str(x) for x in pressure],
            "different_actual_pressure_rates": [str(x) for x in rate]}


def modulo_future_separator():
    def face(x):
        return x - 2 * (x // 2)
    initial = (Q(0), Q(2))
    assert tuple(face(x) for x in initial) == (0, 0)
    ending = tuple(face(x / 2) for x in initial)
    assert ending == (0, 1)
    return {"period": "2", "same_initial_faces": ["0", "0"],
            "ending_faces_under_half_transport": [str(x) for x in ending]}


def folded_quantized_energy_error():
    period, y, n, nhat, eta, g = Q(2), Q(1, 3), 1, 0, Q(1, 7), Q(3)
    actual = y + period * n
    decoded = y + eta + period * nhat
    error = actual - decoded
    assert error == period * (n - nhat) - eta == Q(13, 7)
    physical_difference = g * (actual * actual - decoded * decoded) / 2
    cross = g * error * decoded
    self_energy = g * error * error / 2
    assert physical_difference == cross + self_energy == Q(767, 98)
    assert physical_difference != self_energy  # omitting the cross term changes the answer
    return {"actual_reconstruction_error": str(error), "energy_error": str(physical_difference),
            "cross_term": str(cross), "self_term": str(self_energy)}


checks = (decoder_signs, material_area_work, pressure_face_future_separator,
          modulo_future_separator, folded_quantized_energy_error)
start = time.monotonic_ns()


def stop_at_deadline(signum, frame):
    raise TimeoutError("fixed exact-fixture projection expired")


signal.signal(signal.SIGALRM, stop_at_deadline)
# Float is used only by the foreign operating-system timer API, never by a mathematical operand.
signal.setitimer(signal.ITIMER_REAL, PROJECTION_NS / 1_000_000_000)
results = []
for check in checks:
    before = time.monotonic_ns()
    result = check()
    elapsed = time.monotonic_ns() - before
    if elapsed > PRIOR_UNIT_UPPER_NS:
        raise TimeoutError("unit exceeded its fixed measured upper bound")
    results.append({"case": check.__name__, "wall_ns": elapsed, "reading": result})
wall = time.monotonic_ns() - start
signal.setitimer(signal.ITIMER_REAL, 0)
assert wall <= PROJECTION_NS
receipt = {"status": "PASS: five exact semantic witnesses", "mathematical_arithmetic": "Fraction",
           "threads": 1, "projection_scope": "fixture computation; Python startup excluded",
           "prior_read": "/home/b/Workspaces/holonics/research/records/receipts/2026-10-04_finite-step-work/source-validation.json",
           "largest_prior_unit_upper_ns": PRIOR_UNIT_UPPER_NS, "declared_count": COUNT,
           "projection_ns": PROJECTION_NS, "deadline_ns": PROJECTION_NS, "wall_ns": wall,
           "measured_to_projected": [wall, PROJECTION_NS],
           "peak_RSS_KiB": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
           "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           "checks": results, "compiler_or_native_invocations": 0,
           "scope": "independent algebraic semantic witnesses; not native WaveChain or physical ADC execution"}
(ROOT / "exact-semantic-checks.json").write_text(json.dumps(receipt, indent=2) + "\n")
print(json.dumps({k: receipt[k] for k in ("status", "wall_ns", "projection_ns", "peak_RSS_KiB")}))
