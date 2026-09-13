"""Measure the exact navigation application using the shared exterior process receiver."""
import json
from pathlib import Path
import sys

root = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(root / "research/experiments/native_performance_benchmark"))
from benchmark import measured_process, host_info, clock_info, workstation_snapshot

binary = root / "target/debug/examples/rubik_corner_quotient_navigation"
before = workstation_snapshot()
completed, outer_ns, resources = measured_process([str(binary)])
completed.check_returncode()
result = json.loads(completed.stdout)
assert result["local_optimality_certificate"]["unit_edges_checked"] == 483_840
assert result["farthest_representative_certificate"]["all_54_stickers_solved"]
here = Path(__file__).resolve().parent
(here / "result.json").write_text(json.dumps(result, indent=2) + "\n")
reading = {"host": host_info(binary), "clock": clock_info(), "outer_process_wall_ns": outer_ns,
           "process_resources": resources,
           "workstation": {"before": before, "after": workstation_snapshot()},
           "scope": "one debug-build exterior exact group construction and full-state certificate; timings include all source/optimality checks; no GPU or energy measurement"}
(here / "resources.json").write_text(json.dumps(reading, indent=2) + "\n")
print(json.dumps({"preprocessing": result["preprocessing"],
                  "timing_ns": result["timing_nanoseconds"], "process_resources": resources}, indent=2))
