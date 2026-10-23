# Run receipt

Host: the session's cloud container, one thread, Python 3, exact integer arithmetic (the bit costs
are exterior readings of the counts).

| Script | What it reads | Projection | Deadline (outer `timeout`) | Measured wall | Peak resident |
|---|---|---|---|---|---|
| `faces.py` | each held-back draw's kept and lost faces; per-place costs of sums and differences, operands 0–99 | unmeasured, planned under 1 min | 120 s | 625 ms | 31,076 KiB |
| `intersect.py` | fibre closure of the 8,100 two-digit products by size and the cheap rings 10, 9, 11, 101 | unmeasured, planned under 1 min | 120 s | 7,317 ms | 11,444 KiB |
| `rings.py` | per-place product cost, operands 0–99, with the result's ring faces held | unmeasured, planned under 1 min | 120 s | 453 ms | 28,936 KiB |
| `order.py` | per-place product cost, operands 0–99 padded to four places, read leading first, units first and each place given all others, with size and ring faces held | unmeasured, planned under 1 min | 120 s | 1,328 ms | 17,184 KiB |

Each ran once to completion inside its deadline. The draws are Athena's held-back outputs on
generated arithmetic, as the design thread published them; no private data.
