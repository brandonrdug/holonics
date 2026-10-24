# Run receipt

Host: the session's cloud container, one thread, Python 3, exact integer arithmetic.

| Script | What it reads | Projection | Deadline (outer `timeout`) | Measured wall | Peak resident |
|---|---|---|---|---|---|
| `faces.py` | face pairs and plural fibres of each face under concatenation (14,641 word pairs), the matrix product (6,561 pairs), the polynomial product read at 2 (729 pairs) and permutation composition (576 pairs); the right congruence of "contains `th`" (1,093 words × 121 suffixes) and its two-sided congruence (1,093 words × 40 × 40 contexts); its four-cycle over 3,025 rectangles; the typed application census | unmeasured, planned under 1 min | 60 s | 360 ms | 13,940 KiB |

It ran to completion inside its deadline. A first run counted 8 plural fibres for the seam face
without the unit; adding "is empty" to the face (the empty word is the unit of concatenation) closes
them, and the record reports the face with the unit. No private data.
