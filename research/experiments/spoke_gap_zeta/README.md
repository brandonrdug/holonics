# Fixed-spoke polygon pursuit gap receipt

[established-bounded; computational-witness] This is an exterior geometric reference for the
current candidate displayed by the `spiral-matrix` visualization. It uses the same simultaneous
update

```text
p_j <- (1-t) p_j + t p_(j+1 mod n),   t = 0.15
```

from a regular unit-circumradius polygon for `n=8` and `n=12`, through 100 updates. Eight fixed
rays measure each polygon by ray/segment intersection. The rays are a common ruler family; they do
not assert that the polygon has eightfold shape symmetry. The `n=8` case happens to have equal
spoke readings because the candidate remains an eightfold regular polygon under this circulant
update. That equality is geometric symmetry, not an inferred construction origin.

`analyze.py` retains every vertex, layer radius, spoke gap, `q^k`-normalized gap, envelope row,
telescoping check, and comparison sum as decimal strings in `spoke_gap_zeta.json`. The ray
intersection routine solves the two-dimensional ray/segment equations and deduplicates a ray that
lands exactly on a shared polygon vertex.

The vertex contraction comparison is

```text
q_n = |(1-t) + t exp(2πi/n)|.
```

For each spoke, `g_k = r_k - r_(k+1)` is positive and telescopes over the measured finite window:

```text
Σ_(k=0)^99 g_k = r_0 - r_100.
```

The receipt compares the measured gaps with the ideal log-spiral sequence `g_0 q^k`. For real
`s=1,2`, its ideal gap zeta is the power sum

```text
Σ_(k≥0) (g_0 q^k)^s = g_0^s / (1-q^s),
```

and the recorded tail is `g_0^s q^(100s)/(1-q^s)`. These tails belong to the ideal comparison
sequence, not to a rigorous outward interval bound for the measured polygon gaps.

## Recorded numerical scope

[established-bounded; computational-witness] The following summaries pool the 100 positive gaps
from all eight fixed rays. Min/mean/max/CV use all 800 values. Lag-1 uses only the 792 within-spoke
adjacent pairs (`8 × 99`); it does not join the last layer of one spoke to the first layer of the
next. The JSON records the paired left/right means alongside each correlation. The complete
per-ray and per-layer values remain in the JSON receipt.

| shape | gap family | min | mean | max | CV | lag-1 |
|---|---|---:|---:|---:|---:|---:|
| n=8 | raw | 0.0000731133 | 0.00979791 | 0.0746878 | 1.37878 | 0.809456 |
| n=8 | `g_k/q^k` | 0.00110638 | 0.0363149 | 0.0746878 | 0.573289 | 0.398159 |
| n=12 | raw | 0.000138913 | 0.00810994 | 0.0341635 | 0.814489 | 0.622050 |
| n=12 | `g_k/q^k` | 0.000333445 | 0.0168876 | 0.0341635 | 0.576059 | 0.370374 |

The finite telescoping sum `Σ g_k = r_0-r_100` is `0.9797908938559263` on every n=8 spoke.
Across the n=12 rays it ranges from `0.7920473506290314` to `0.8299414501558140`, with mean
`0.8109944003924228`. All 800 gaps in each shape are positive and all 808 ray/layer
intersections are present (including the 8 rays at each of 101 layers).

For spoke 1, the ideal gap-zeta comparisons are:

| shape | `q` | `s` | measured finite power sum | ideal infinite `g₀ˢ/(1−qˢ)` | ideal tail after 100 |
|---|---:|---:|---:|---:|---:|
| n=8 | 0.961931510 | 1 | 0.979790894 | 1.961931510 | 0.0404668072 |
| n=8 | 0.961931510 | 2 | 0.0278497624 | 0.0746877708 | 0.0000317746 |
| n=12 | 0.982769799 | 1 | 0.829941450 | 1.982769799 | 0.348700437 |
| n=12 | 0.982769799 | 2 | 0.0115807234 | 0.0341635220 | 0.0010566302 |

Run from the repository root with the configured research environment:

```sh
/home/b/scratch/huggingface/.venv/bin/python research/experiments/spoke_gap_zeta/analyze.py
```

The script writes the numeric receipt and a standalone scientific plot beside itself. It performs
no native HNN execution, learning, or physical interpretation.

## Special-value witness

`verify_special_values.py` checks the pentagonal values used by the adjoining mathematical source:

- the Gamma ratio for φ;
- the Hurwitz-zeta derivative expression for `log φ`;
- the `χ_5` value `2 log φ / √5`;
- the two dilogarithm identities at `φ⁻¹` and `φ⁻²`; and
- optionally, the finite dynamical-zeta sum for `B=[[0,1],[1,1]]` at `z=0.1`, against
  `1/(1-z-z²)` with its declared geometric tail expression.

Run it with:

```sh
/home/b/scratch/huggingface/.venv/bin/python research/experiments/spoke_gap_zeta/verify_special_values.py
```

It writes `special_values.json` with 80-digit mpmath values and absolute residual magnitudes.
Those are numerical witness values at the declared precision, not outward interval bounds or
formal proofs; the formal source anchor is `formal/elementary-holonics/ElementaryHolonics/Millennium/FiveTheta.lean`.
