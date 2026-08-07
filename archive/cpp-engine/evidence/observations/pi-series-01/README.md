# PI SERIES 01 · TWO ORDERS OF ONE EXACT UNFOLDING

**Grade:** CHOSEN · FIXTURE BUILT/VERIFIED · CUDA MEASURED · EXACT SERIES
RE-EXPRESSION / ORDERED-PATH DIFFERENCE MEASURED

This observer-only fixture presents the first 32 terms of the Gregory–Leibniz unfolding as two
whole, co-present ASCII currents. The forward current carries source terms `k=0..31`; its foil
carries the same terms in exact reverse order. Every partial construction remains an unreduced
integer pair:

```text
F[k]=(P;Q)+(n;d)=(P*d+n*Q;Q*d)
d=2*k+1
n=+4 for even k, -4 for odd k
```

[`forward.txt`](forward.txt) begins `GL/F;F[-1]=(0;1);`; [`reverse.txt`](reverse.txt) begins
`GL/R;R[-1]=(0;1);`. Neither file names π, contains a decimal-point or radix-prefix assertion,
supplies a target digit, or performs floating-point arithmetic. The recurrence deliberately never divides by a common
factor: construction identity retains every denominator crossing. The two orders terminate at the
same exact pair, but their lived paths remain different.

The generated current pins are:

| current | octets | SHA-256 |
|---|---:|---|
| `forward.txt` | 3,185 | `565765a5fd9af9449e49926c0752c8525aa410c288976e065074b1ba857cf070` |
| `reverse.txt` | 3,987 | `ecbff0f5c2a7b26d9957e72374825181f2b857e1a42a700df43a63119b129875` |

Their common terminal pair is
`(349216366319154387719358175674864373100400000;112275575285571389562324404930670903477890625)`.

The immutable parent is the measured successor of the whole ascending/descending number-line
traversal:

```text
observations/prime-traversal-01/results/run-a-bodies/
  1783956848407681432-cuda-continue-next.body
SHA-256 9e6d4020d364b2d053719c4e3a95a399d27dda0d5d52c17dc1f76bba57e3fbda
```

## Exact observer reading

[`pi_series.py`](pi_series.py) independently reconstructs both files with integer arithmetic. It
requires the source-term orders to be exact reversals, every pair recurrence to retain
`Q'=Q*d`, and both complete currents to reach one byte-identical terminal pair.

For the forward construction, the ordinary alternating-series enclosure places `F[31]` below the
series limit and `F[30]` above it. The verifier checks the nested odd/even hands and their final
exact width `4/63` using cross-products. It then reads radix cells by integer quotient only:

```text
depth 1: floor(10*F[31]) = 31  · floor(10*F[30]) = 31
depth 2: floor(100*F[31]) = 311 · floor(100*F[30]) = 317
```

The first radix face is shared while the next remains unresolved. These cells are boundary
observations over the exact pair enclosure; they are not delivered labels and do not identify any
finite prefix with π.

## Measured crossing

The two whole currents continued the immutable prime-traversal successor together on CUDA. The
receiving chart remained at axis 1,024 and changed from
`[289842,289842,63573,2553]` to `[294254,294254,64136,2570]`. Their complete paths remained
different, while repeated exact material re-expressed locally: terms `k=5..24` have byte-identical
raw and typed term rows in both orders, and all 92 internal rows of the common terminal pair are
byte-identical despite different preceding constructions. The exact observer read and all
whole-lineage faces are recorded in [`results/RESULTS.md`](results/RESULTS.md).

## Generate, verify, and reproduce

From `src/soma`:

```bash
python3 observations/pi-series-01/pi_series.py generate
bash observations/pi-series-01/verify.sh
```

After the fixture and workspace gates pass, conduct the CUDA observation by passing the two files
explicitly. Each path is one complete world-delivered current; they must not be concatenated or
split:

```bash
SOMA_OBSERVATION_OUT=observations/pi-series-01/results/run-a.txt \
SOMA_PERIPLUS_DIR=observations/pi-series-01/results/run-a-bodies \
  cargo run --release -p life -- --cuda-continue \
  observations/prime-traversal-01/results/run-a-bodies/1783956848407681432-cuda-continue-next.body \
  --later observations/pi-series-01/forward.txt observations/pi-series-01/reverse.txt
```

`SHA256SUMS` pins the two delivered currents. The generator, verifier, digest record, and README
remain observer-side boundary instruments and are never passed after `--later`.
