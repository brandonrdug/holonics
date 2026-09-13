"""Plot the actual measured roundtrip distribution; no inference of a population tail."""
import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

root = Path(__file__).resolve().parent
record = json.loads((root / "result.json").read_text())
fig, axes = plt.subplots(1, 2, figsize=(10, 4), constrained_layout=True)
for ax, key, title, label, color in zip(
    axes,
    ["mathematical_c5_power_apply", "wave_receive_next_symbol"],
    ["C5¹⁶ receiver-face delivery", "Committed wave observation"],
    ["apply", "state-update"],
    ["#166f8c", "#8f4f91"],
):
    raw = record["workloads"][key]["warm"]["raw"]
    values = sorted(dt / 1e6 for dt, role in zip(raw["roundtrips_ns"], raw["labels"]) if role == label)
    ax.step(values, [(i + 1) / len(values) for i in range(len(values))], where="post", color=color, linewidth=2)
    ax.scatter(values, [(i + 1) / len(values) for i in range(len(values))], s=5, color=color)
    ax.set(title=title, xlabel="Measured roundtrip latency (ms)", ylabel="Fraction of observed requests",
           ylim=(0, 1.03))
    ax.grid(alpha=0.18)
    ax.spines[["top", "right"]].set_visible(False)
fig.suptitle("128 requests per workload · setup/warmup excluded · consumer desktop · debug build", fontsize=11)
fig.savefig(root / "latency.png", dpi=180)
