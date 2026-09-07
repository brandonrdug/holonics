# AC2: the full internal current has an addressed prefix pairing

[definition] This construction follows the [128-family return](2026-09-07_AC3_THE_COMPLETE_HISTORY_MOVES_TO_AN_EXTERIOR_CHART_AND_ITS_ADDRESSED_SOURCE_RETURNS.md)
at `c154c9cb`. The model's `Tm.` response remains unusable. The current material transport reads
the retained coupled outgoing current; the complete internal-current population has an existing
decoder but is not yet productive in that transport. This record derives its precise source
geometry and continuing receiver factorization. It does not declare a new useful alpha.

## Complete source and actual overlap

[definition] Use the existing native junction's root chart and occurrence index `j`. Its contact
`i` is born at the actual receiving occurrence `a_i`, with exact row `d_i` and prefix before birth
`P_(a_i-1)` (zero before the first occurrence). The existing decoder gives

```text
epsilon_j = (-1)^j,
b_i(j) = epsilon_j d_i* (P_j - P_(a_i-1)),  for a_i <= j.
```

Rows not yet born are absent. Let `p_j` be the full coupled outgoing current, and define the
complete current source `x_j = (p_j, (b_i(j))_(a_i<=j))`. Alignment between sources uses their
actual shared born-contact population. Equal row values or outputs do not merge contacts.

[definition] Write

```text
c_i = d_i* P_(a_i-1),
C_j = sum_(a_i<=j) d_i d_i*,
ell_j = sum_(a_i<=j) d_i c_i,
kappa_j = sum_(a_i<=j) |c_i|^2,
G_j = [ C_j       ell_j ],       z_j = (P_j, -1).
      [ ell_j*   kappa_j ]
```

The last coordinate is the affine chart for the retained birth current. `C` is the existing
contact moment. `ell` and `kappa` retain the additional birth terms that `C` alone omits.

[proved-derived] Put `a_i=(d_i, conjugate(c_i))`. Then `a_i* z_j=d_i* P_j-c_i` and
`G_j=sum_(a_i<=j) a_i a_i*`. Expanding the inner product over the common contact population gives

```text
K(j,k) = <x_j,x_k>
       = p_j* p_k + epsilon_j epsilon_k z_j* G_min(j,k) z_k.
```

Every term follows from the same contact appearing in both sources. A contact born after the
older cut contributes zero. Replacing the older prefix by the current global moment inserts
contacts that were not present in that source and changes the pairing.

[proved-derived] The whole matrix `G_j` need not be copied into each historical source. Retain

```text
v_j = G_j z_j = (u_j, w_j),
u_j = C_j P_j - ell_j,
w_j = ell_j* P_j - kappa_j.
```

For `j<=k`, `K(j,k)=p_j* p_k + epsilon_j epsilon_k (u_j* P_k-conjugate(w_j))`.
For the reverse order use Hermitian conjugation. The diagonal is `||x_j||^2>=0` because it is the
norm of the complete source above. The contact population and birth history remain available for
the executable decoder; this source-pairing factorization does not identify the full source with
one arbitrary vector of the same norm.

## Continuing material transport

[definition] Apply the already admitted coercive material law to this complete source:

```text
T' = T + beta x_s*,       beta = (y - T x_s)/(1 + ||x_s||^2).
```

`s` is the actual receiving source, and `y` is the actual incoming material current. New contact
coordinates extend older source vectors by zero. Source-time forward current and contemporary
forward current remain different retained carriers, as in the existing material return.

[proved-derived] For any finite sequence of such rank-one increments, let the initial transport
on the internal coordinates be zero, and define

```text
M = T_out_initial + sum beta_s p_s*,
A = sum beta_s epsilon_s u_s*,
a = sum beta_s epsilon_s conjugate(w_s).
```

For a newly produced source `t` after all those source cuts, distributivity and the older-prefix
pairing give `T x_t = M p_t + epsilon_t (A P_t-a)`. Each new increment updates these same three
factors. For an older still-available source `j`, retain its contemporary receiving current and
update it by `F_j' = F_j + beta K(s,j)`. This is exactly `(T+beta x_s*)x_j`. Both equalities retain
complex phase and the original source cut; neither depends on token wording or an evaluation
answer. A material receiver with several output channels applies the equality to every row.

[conditional] A native implementation may fold the material operator for the admitted future
receiver family consisting of new sources and actual live source capabilities if it carries
those factors, updates every live receiving current after the same complete return, and retains
the source-qualified increment expression for cold reconstruction. Dropping a cache requires
proof that its capability is no longer available, not an authored relevance rule. The full
successor, forward chronology, numerical defect and logical resources remain obligations of
the implementation. The algebra above does not authorize a rollback clone or missing adjoint.

## Numerical chart

[proved-derived] Let the existing native prefix centre and radius be `P_hat_j, E_Pj`, and the
coupled outgoing centre/radius be `p_hat_j, E_pj`. Exact contacts give numerical internal sources
by the same decoder with the numerical prefix at each actual birth. Prefix radii are monotone,
so for every born contact `|b_i(j)-b_hat_i(j)| <= 2 E_Pj ||d_i||`. Hence a complete-source bound is

```text
E_xj <= E_pj + 2 E_Pj sqrt(trace(C_j)).
```

The complete source remains a ball with a retained decoder. The existing projector proof for the
[coercive return](2026-09-07_AC2_THE_RETAINED_CONTEXT_RECEIVES_A_NATIVE_MATERIAL_TRANSPORT.md)
then applies in this larger finite Hilbert space. The implementation still owes its additional
arithmetic defects; a centre cannot be substituted for the exact current.

[definition] In an integral-contact chart with numerical prefixes on grid `S=2^g`, `C` is
integral, `ell` and `u` have denominator `S`, and `kappa`, `w` and source pairings have denominator
`S^2`. The latter numerators can exceed 128 bits even though prefix centres fit that word. Exact
mixed-scale storage avoids rounding the Gram form or losing its positive diagonal. General
rational contacts require their actual denominator representation or a precise obstruction.

## Returned evidence and construction position

[established-bounded; computational-witness] `current_history_source.py` reads the actual
794-occurrence four-family/prompt report. It verifies the complete numerical source norm at every
cut, the displayed aggregate source-error bound against all born contact bounds, all 64 pairings
among eight declared cuts, and 43 full/folded/cached scalar-receiver equalities. Separate Gaussian
integer controls return 25 pairings and 31 receiver equalities with nonzero imaginary pairings,
late returns to older sources and repeated returns. The covectors in this observer are declared
algebraic controls, not a trained model or target answers.

[established-bounded; computational-witness] In that actual aperture, maximum numerator widths
are 85 bits for `ell`, 162 for `kappa`, 82 for `u`, and 156 for `w` and the source norm square.
Thus the present signed-128 report alone cannot hold the exact full-source moment in the current
72-bit chart. The result selects a concrete arithmetic construction requirement, not a language
score or a semantic capacity. The observer runs no native event, model update or text emitter.

## Native source construction and a strict missing-port witness

[established-bounded; measured] `field_current_history_source.cuh` now constructs the birth moment
and complete source on the device, using the existing exact signed-limb arithmetic extracted into
`exact_integer.cuh`. The original integer definitions and conic body are preserved byte-for-byte
across that extraction. The moment keeps its mixed `S`/`S^2` scales, with 256-bit birth-square and
pairing numerators. Narrowing and unsupported nonintegral root contacts return obstructions.

[proved-derived] If `N_j` bounds the numerical source norm from above, the actual pairing error
is bounded by `E_j N_k + E_k N_j + E_j E_k`, by expanding the two source errors and applying
Cauchy–Schwarz to each term. The native source receiver computes the exact upward integer square
root of the numerical norm numerator. Its pairing receiver returns the exact numerical pairing
as a centre and the displayed full-source error bound as its radius.

[established-bounded; measured] Four new native controls pass within the full 75-test constitutive
scope. They compare complete numerical sources with the existing internal-current decoder, and
check source and pairing balls against exact residual-decoded currents. The scope includes
complex phase, source-time births, recharting, physical incidence change, an unlinked interval,
delayed shared-source returns, numerators beyond 128 bits, and unsupported-contact refusal.
Source construction leaves the field's complete native rest unchanged.

[counterexample; measured] There is an actual reachable distinction that the outgoing-only
material input cannot see. In the one-node unit field, enter `1`, retain its source, and receive
`1` twice through that same anchor. Both actual contacts have `d=(0,1,-1)`. Their internal
currents after the second reception are `4/15` and `14/15`. An unlinked `-9/10` input sets their
sum to zero; successive unlinked zeros then give, at occurrences 5 and 6,

```text
outgoing_5 = outgoing_6 = 0,     held_5 = held_6 = 0,
b(5) = ( 1/3, -1/3),           b(6) = (-1/3,  1/3).
```

The exact native residual decoder establishes these equalities. The complete-current source
pairing is `2/9` on the diagonal and `-2/9` between the two sources; the native pairing balls
strictly separate the positive and negative values. Every linear material map whose sole input
is the outgoing current returns zero on both sources, regardless of its coefficients. This is a
concrete missing receiver port, not a claim that it explains every failed language response.

[definition] `NativeCurrentHistorySourceReceiver` is currently a construction receiver over
completed returns of one native field. It computes on the device and owns no second ecology.
Its returned source carriers authorize observation, not new receiving events. The productive
material map still uses its earlier outgoing-only source; no language improvement is claimed
from these new source primitives. `alpha_current_source` mounts actual exposure through the
public text session and observes this construction without defining a learner or text emitter.

[established-bounded; measured] The actual four-family construction probe completes 732 native
field occurrences and 732 native source constructions. The independent observer verifies every
source vector, birth offset, numerical norm, upward norm bound, full-source radius and source
cut, plus the final birth moment and its agreement with the field covariance. The field lineage
matches the earlier uninterrupted four-family report. The native admission/construction phase
performs zero numerical section readouts; its 1,464 deeds are explicitly the 732 field operations
plus 732 construction observations. This is a source-construction return, not a changed model.

[established-bounded; measured] The debug probe takes 23.789 seconds for admission/construction
and 24.886 seconds for the whole process, with Linux child maximum RSS 250,904 KiB. Native payload
is 34,957,520 bytes before diagnostics and peaks at 35,597,508 bytes. The retained source views
belong to this declared observation population. These costs do not describe a productive
complete-source material transport, which is still unimplemented.

[definition] Private outputs are under `.local/artifacts/athena-alpha/ac3-placement/`:
`native-complete-current-source-v1.json`, its process/stdout/stderr receipts, and
`native-complete-current-source-certificate-v1.json`. The cold algebra receipts are
`complete-current-source-geometry-v1.json` and `v2.json`; v2 adds explicit complete-history and
chronology validation. Reproduction uses fresh paths and the standing CUDA setup:

```sh
env PATH=/opt/cuda/bin:$PATH cargo test -p holonic-engine --lib native_ecology::constitutive_fibre -- --ignored --test-threads=1
env PATH=/opt/cuda/bin:$PATH cargo build -p holonics-hna --example alpha_current_source
target/debug/examples/alpha_current_source .local/datasets/athena-alpha-exposure-source-context-2026-09-06.jsonl --families 4 --report .local/artifacts/athena-alpha/ac3-placement/new-native-source.json
python -P research/experiments/alpha_passive_junction/current_history_source.py .local/artifacts/athena-alpha/ac2/first-learned-transport-v1.json --output .local/artifacts/athena-alpha/ac3-placement/new-source-certificate.json --native-source .local/artifacts/athena-alpha/ac3-placement/new-native-source.json
```

[open] The factorized material return, live contemporary receiving currents, complete parameter
error/adjoint expression and durable integration still need construction. Join the complete source
to the same native material/reaction operation, preserving the old forward carrier and staged
successor. Existing numerical and persistence returns remain valid at their scopes; useful
Athena-alpha remains unachieved. Lean remains outside this cultivation/inference construction.
