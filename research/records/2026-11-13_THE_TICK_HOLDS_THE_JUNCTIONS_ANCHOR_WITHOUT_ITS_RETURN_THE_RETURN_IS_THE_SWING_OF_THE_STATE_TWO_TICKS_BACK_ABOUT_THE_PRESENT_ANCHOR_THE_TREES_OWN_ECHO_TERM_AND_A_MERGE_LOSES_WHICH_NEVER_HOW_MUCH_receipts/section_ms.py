"""section_ms: each log's STORE_SECTION ms= (a section's wall time on the card and the host's deposit), its count, mean, median and the mean of
sections 10 on (past the pool's warm-up). usage: python3 -I section_ms.py LOG..."""
import sys, statistics
for path in sys.argv[1:]:
    ms = [int(w[3:]) for line in open(path) if line.startswith("STORE_SECTION ") for w in line.split() if w.startswith("ms=")]
    if not ms:
        print(f"SECTION_MS log={path} sections=0"); continue
    rest = ms[10:] or ms
    print(f"SECTION_MS log={path.rsplit('/',1)[-1]} sections={len(ms)} mean={statistics.mean(ms):.1f} median={statistics.median(ms):.1f} mean_from_10={statistics.mean(rest):.1f} min={min(ms)} max={max(ms)}")
