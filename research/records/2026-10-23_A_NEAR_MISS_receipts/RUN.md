# Run receipt

Host: the session's cloud container, one thread, Python 3, exact integer arithmetic (the bit costs
are exterior readings of the counts).

| Script | What it reads | Projection | Deadline (outer `timeout`) | Measured wall | Peak resident |
|---|---|---|---|---|---|
| `faces.py` | each held-back draw's kept and lost faces; per-place costs of sums and differences, operands 0–99 | unmeasured, planned under 1 min | 120 s | 625 ms | 31,076 KiB |
| `intersect.py` | fibre closure of the 8,100 two-digit products by size and the cheap rings 10, 9, 11, 101 | unmeasured, planned under 1 min | 120 s | 7,317 ms | 11,444 KiB |
| `rings.py` | per-place product cost, operands 0–99, with the result's ring faces held | unmeasured, planned under 1 min | 120 s | 453 ms | 28,936 KiB |
| `order.py` | per-place product cost, operands 0–99 padded to four places, read leading first, units first and each place given all others, with size and ring faces held | unmeasured, planned under 1 min | 120 s | 1,328 ms | 17,184 KiB |
| `binding.py` | the four-cycle of each result face on unit squares, operands 0–99; the index chart on the units of ℤ/9, ℤ/10, ℤ/11, ℤ/101 by rectangles anchored at `(1, 1)` | unmeasured, planned under 1 min | 60 s | 450 ms | 15,520 KiB |
| `compose.py` | the defect composition on rational matrices, the carry cocycle over 0–99 cubed, the face return | unmeasured, planned under 1 min | 60 s | 502 ms | 11,336 KiB |

Each script above ran once to completion inside its deadline, except `binding.py`. Its first run
tested the index chart on every rectangle of units, 24,502,500 = 2²·3⁴·5⁴·11² rectangles for ℤ/101
alone. It was planned under a minute with no per-unit read and took 110,890 ms (15,464 KiB): inside
its 120 s deadline, about twice the plan. The projection error was the count. The law changed, not
the limit: a face is separable exactly when every rectangle anchored at `(1, 1)` vanishes, which is
9,801 checks for ℤ/101. Both runs gave zero nonzero four-cycles on the units; the committed script
and output are the second run.

The draws are Athena's held-back outputs on generated arithmetic, as the design thread published
them; no private data.
