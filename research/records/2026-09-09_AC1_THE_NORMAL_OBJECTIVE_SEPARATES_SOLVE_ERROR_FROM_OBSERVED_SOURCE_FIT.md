# AC1: numerical solve error and observed-source fit are different returns

[definition] This continuation applies the
[parallel normal-geometry derivation](2026-09-09_MATHEMATICAL_REVIEW_NORMAL_GEOMETRY_AND_CLOSED_RETURNS.md)
to `OperativeNormal` after `ca5dba5b`. It observes the actual stored statistics and numerical
matrix. The observer neither changes native conduct nor opens the original conversation source.

## Exact cold comparison

[proved-derived] With the declared unit prior, H=I+sum xx†, B=sum yx† and C=sum ||y||²,
the nominal objective is `Phi(M)=(tr(M H M†)-2 Re tr(M B†)+C)/2`. Writing R=MH-B gives
`Phi(M)=(C+Re tr(M(R-B)†))/2`, so the existing signed-residual decoder supplies the objective
without a second matrix multiplication. The prior term is `||M||_F²/2`; subtraction returns
the data term `sum ||M x-y||²/2` for the actually accumulated nominal observations.

[proved-derived] Square completion gives `Phi(M)-min Phi=tr(R H^-1 R†)/2`. Since H≥I,
the exact minimum lies in `[max(0,Phi(M)-||R||_F²/2),Phi(M)]`. This bound needs no new inverse
or solve. A small solve gap says the numerical matrix nearly minimizes this declared objective;
it does not say the data are well fitted or the current source chart is useful for language.

[proved-derived] Existing source-family bounds EH, EB and EC give an objective error at fixed
numerical M of at most `(||M||_F² EH+2||M||_F EB+EC)/2`. The implementation keeps the exact
squared norm and uses a rational L1 upper bound only where an unsquared norm is needed.
Both true and nominal minimizers have norm at most `K=||B_nominal||_F+EB`; substituting an
exact upper bound for K bounds the difference of their minimum objectives. Intersecting these
nonnegative objective intervals with `[0,infinity)` loses no admitted value. This does not
select the nominal observations as the unique source or optimize on the host.

[established-bounded; source-inspected] `NativeNormalMaterialState::objective` exposes data,
prior, total objective, exact residual squared, numerical gap and nominal/family minimum
intervals. Its domain is the native unit-prior accumulated state. The `alpha_text` observer
is opt-in and runs after development/generation; ordinary calls incur no objective readout.
It records the exact native cut and keeps diagnostic errors separate from productive conduct.

## Control and actual-model comparison

[established-bounded; implemented-exact; computational-witness] The exact control uses two
different targets at one scalar source. At the exact normal solution the solve gap is zero,
while data cost is 5/9 and prior cost is 1/9. A deliberately complex nonoptimal matrix agrees
with independent direct sums of the original data discrepancies. An explicit changed member
of the source/target family and its exact minimum lie within the returned family intervals.
The focused Rust control passes; the example builds. Neither check changes a model.

[established-bounded; measured] Both saved-model observers return without enacting a new
occurrence. The [exact receipt](2026-09-09_normal_material/objective.json) retains the full
rational results and process costs. Rounded displays of the nominal returns are:

| Native occurrences / observed relations | Data term | Prior term | Upper bound on further solve improvement |
|---|---:|---:|---:|
| 75 / 74 | 24.217064013 | 0.608586503 | 2.13 × 10⁻³⁷ |
| 1,930 / 1,929 | 836.691024405 | 0.492519855 | 1.76 × 10⁻³³ |

[established-bounded; measured] The second source-family data interval is
[836.691024403758, 836.691024405453] when displayed with outward decimal rounding.
Its family minimum regularized objective lies within [837.106569414859, 837.260519103711].
The source-family uncertainty therefore does not turn this into a numerical-solve failure.
The cold first-family process takes 65.03 seconds, of which diagnostics take 63.07; the
1,930-occurrence process takes 235.90 seconds, of which diagnostics take 174.02. These are
opt-in exterior rational observations, not native learning or generation costs.

[definition] Additional normal-solve precision cannot materially improve this declared fit.
This does not prove that every source is inseparable, that a different prior has no effect,
or that these scalar discrepancies determine text accuracy. It redirects the active question
from numerical solving to source/feedback representation and its reuse. The eight-part exposure
contains only one human request; general language cannot be assessed as if broad cultivation
had already occurred. AC1 and AC2 remain open.
