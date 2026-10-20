"""V92 completed-epoch admission projection with explicit workload and phase."""
import re


def validate_v92_budget(c):
    """Reject any controller config that drifts from the proposed fixed V92 envelope."""
    expected = {
        "total_reservation_ns": 2_400_000_000_000,
        "maximum_process_ns": 2_390_000_000_000,
        "maximum_cleanup_ns": 10_000_000_000,
        "training_phase_ns": 1_800_000_000_000,
        "evaluation_phase_ns": 500_000_000_000,
        "receipts_phase_ns": 90_000_000_000,
        "training_epochs": 1128,
        "cpus": 4,
        "memory_bytes": 8_589_934_592,
    }
    for key, value in expected.items():
        if c.get(key) != value:
            raise ValueError(f"V92 controller config {key} must equal {value}")
    if c["training_phase_ns"] + c["evaluation_phase_ns"] + c["receipts_phase_ns"] + c["maximum_cleanup_ns"] != c["total_reservation_ns"]:
        raise ValueError("V92 phase limits must exactly consume the fixed reservation")
    return True


def training_projection(text, *, epochs, phase_ns):
    if not isinstance(epochs, int) or isinstance(epochs, bool) or epochs <= 0:
        raise ValueError("declared V92 epoch count must be positive")
    if not isinstance(phase_ns, int) or isinstance(phase_ns, bool) or phase_ns <= 0:
        raise ValueError("declared V92 training phase must be positive")
    events = re.findall(r"complete-language epoch=(\d+) cells=\d+ elapsed_ns=(\d+)", text)
    if not events:
        return None
    completed, elapsed = map(int, events[-1])
    if completed <= 0 or completed > epochs:
        raise ValueError("training progress count outside declared workload")
    projected = (elapsed * epochs + completed - 1) // completed
    return {"completed_epochs": completed, "elapsed_ns": elapsed,
            "projected_training_ns": projected, "fixed_phase_ns": phase_ns,
            "exceeds_cap": elapsed * epochs > phase_ns * completed,
            "scope": "observed average cost including setup/cuts; admission projection only, not an ETA"}
