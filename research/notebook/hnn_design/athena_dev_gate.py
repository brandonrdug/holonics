"""Exercise Athena's development safety gate on the private provisional native path.

This does not publish an answer: the native path lacks key provenance, compatible-source fibre
and numerical health, so the one protocol must return a typed refusal. The output and checkpoint
stay owner-only; stdout contains only counts, hashes and the refusal code.

    HOLONICS_ROOT=<checkout with private cuts> python3 athena_dev_gate.py

The request comes from F5's spent diagnostic split, which holds the development reserve, so it is
refused unless the logged flag `--read-reserve` is passed (`development_families.py`).
"""

import hashlib
import json
import os
import sys
from pathlib import Path

from athena_protocol import AtomicCheckpoint, EngineTransition, Protocol
from development_families import require_reserve_excluded, reserve_flag
from standing_cut import OUT_DIR


class ProvisionalNativeEngine:
    """Expose the private provisional candidate to the product gate, with missing receipts."""

    def __init__(self, candidate: str):
        self.candidate = candidate
        self.calls = 0

    def ask(self, payload, standing):
        self.calls += 1
        return EngineTransition({"text": self.candidate, "simplex_covering": False}, standing)

    def inspect(self, payload, standing):
        return EngineTransition({"kind": "native-probe", "release_owner": "incomplete"}, standing)


def owner_only(path):
    mode = Path(path).stat().st_mode & 0o777
    assert mode == 0o600, "the private artifact remains owner-only"


def main():
    arguments, read_reserve = reserve_flag(sys.argv[1:], "athena_dev_gate.py")
    if arguments:
        sys.exit(__doc__)
    with open(os.path.join(OUT_DIR, "f5-dev-request.json"), "rb") as handle:
        require_reserve_excluded(json.load(handle), "the F5 development request", read_reserve)
    request_path = os.path.join(OUT_DIR, "f5-dev-request.bin")
    candidate_path = os.path.join(OUT_DIR, "f5-native-probe.bin")
    owner_only(request_path)
    owner_only(candidate_path)
    request = Path(request_path).read_bytes().decode("utf-8")
    candidate = Path(candidate_path).read_bytes().decode("utf-8")
    checkpoint_path = Path(OUT_DIR) / "f5-dev-gate.checkpoint"
    if checkpoint_path.exists():
        owner_only(checkpoint_path)
    engine = ProvisionalNativeEngine(candidate)
    frame = json.dumps(
        {"version": 1, "sequence": 1, "command": "Ask", "payload": {"request": request}},
        ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode()
    protocol = Protocol(AtomicCheckpoint(checkpoint_path), engine)
    already_pending = protocol.replay_pending() is not None
    first = protocol.process(frame)
    receipt = json.loads(first)
    assert receipt["status"] == "refused" and candidate not in first.decode()
    restarted = Protocol(AtomicCheckpoint(checkpoint_path), engine)
    replay = restarted.process(frame)
    assert replay == first and engine.calls == (0 if already_pending else 1)
    owner_only(checkpoint_path)
    checkpoint = checkpoint_path.read_bytes()
    print(json.dumps({"status": receipt["status"], "refusal_type": receipt["result"]["type"],
                      "native_calls": engine.calls, "replay_identical": replay == first,
                      "output_bytes": len(first), "output_sha256": hashlib.sha256(first).hexdigest(),
                      "checkpoint_bytes": len(checkpoint),
                      "checkpoint_sha256": hashlib.sha256(checkpoint).hexdigest()}, indent=2))


if __name__ == "__main__":
    main()
