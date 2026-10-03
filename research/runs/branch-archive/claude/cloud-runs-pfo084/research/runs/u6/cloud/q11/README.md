# Q11: K's diagonal arm split into its 1/θ_t part and its 1/K_tt part (C0, lock-dec, 8 requests)

Run: `executed kinetic-coupling order2 2026093061 8 lock-dec c0=<C0>` at 2 threads, timeout 1800 s
(projection from Q10's 1,400 s read); wall 1,400 s, peak resident 244,817,920 bytes = 2^12·59,770 + 0.

Signed cos² against the native gradient d (Euclidean / M's metric), /4096:

| arm | Euclidean | M's metric |
|---|---|---|
| left out (μ = w = e_t/θ_t only) | [1942, 1943) | [1870, 1871) |
| diagonal (μ = (1/θ_t)/K_tt) | [662, 663) | [621, 622) |
| by term | [852, 853) | [800, 801) |
| by request | [355, 356) | [339, 340) |
| joint (Exhausted after 320) | [37, 38) | [37, 38) |

The 1/θ_t weighting alone turns d from 4096/4096 to [1942,1943)/4096; dividing by K_tt takes it to
[662,663)/4096; coupling within and across requests finishes the turn to [37,38)/4096.

Joint residual energy over the opening's, /2^32: iterate 188 [10933, 10934); iterate 258 [262, 263);
iterate 320 [16, 17). The cosine settles at [37,38)/4096 from iterate 258 while the residual still
falls by 2^4 to iterate 320.
