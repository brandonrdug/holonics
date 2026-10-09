# The additive source budget enters the existing fluid receiver

Refs #32, #62, #146.

[proved-derived; formal-checked] The existing
[transported-scalar maximum-principle owner](../../lean/HolonicsResearch/Fluid/NavierStokesTransportedScalarMaximumPrinciple.lean)
now consumes an additive source through its accumulated return. Its strict-event consumer
uses the resulting bound over the whole admitted passage. Four new statements and the eight
existing audit statements passed the same focused whole-owner kernel check: `12 = 2²·3`
queries, each using only `propext`, `Classical.choice` and `Quot.sound`.

The computational object is the participating Holon's scalar receiving face, its constituted
diffusion, and the source arriving during its clock passage. This touches the helical pair's
faces and placement and its longitudinal tube. The scalar theorem supplies no new material
law for the pair, spatial transport, transverse tower, or cell holonomy.

## The consuming equation and its hypotheses

[proved-derived; formal-checked] Let `nu ≥ 0`, `a ≥ 0`, and let `theta(x,t)` be
one-periodic in space. Require continuity on `Space × [a,T)`, spatial `C²` on `(a,T)`,
and time differentiability there. Let `A` be continuous on the real line with
`A'(t) = S(t)` on `(a,T)`. The caller supplies the complete inequality

```text
theta_t + (u·grad)theta ≤ nu Delta theta + S(t),
theta(x,a) ≤ M.
```

`transportedSubsolution_le_additive_source_budget` subtracts `A(t)` and calls the
existing `transportedSubsolution_le_of_le_at`, returning

```text
theta(x,t) ≤ M + A(t) − A(a),       a ≤ t < T.
```

The drift `u` is supplied; this abstract scalar theorem requires neither incompressibility
nor a bound on `u`. Periodicity and the stated regularity remain premises. There is no
conclusion at the omitted terminal face `T`.

[proved-derived; formal-checked] `strict_event_absent_of_additive_source_budget` consumes
that pointwise conclusion and the caller's budget

```text
M + A(t) − A(a) ≤ threshold       for every a ≤ t < T
```

to exclude every strict event `threshold < theta(x,t)` on that passage. Equality at the
threshold is allowed. The source's instantaneous amplitude alone cannot replace this
accumulated budget.

[definition; caller obligation] For a comparison of two scalar passages with different
drifts, the source bound must include the drift return
`−(u−u0)·grad theta0` as well as the supplied source difference. Applying the theorem to
a derived fluid face requires proving its complete scalar inequality first. Pressure,
moving boundary work, changing receiver terms and unresolved stress remain in their
producing balance until that derivation explicitly accounts for them. This owner does not
establish such a derivation or an estimate for those terms.

## The strict face arithmetic

[proved-derived; formal-checked] For `epsilon > 0`,
`sustained_source_receiver_event_iff` proves exactly

```text
1/2 < epsilon·t/2   iff   1/epsilon < t.
```

`arbitrarily_small_sustained_source_crosses` consumes that equivalence: for any positive
tolerance it chooses `epsilon = tolerance/2` and `t = 2/epsilon`, giving a positive
amplitude strictly below the tolerance and a nonnegative time with a strict face event.
These are real scalar arithmetic statements. Identifying `epsilon·t/2` with a particular
PDE solution or spatially integrated detector is a separate analytic obligation.

## Acceptance and source provenance

[established-bounded; kernel-receipt] The accepted source is exactly `32726 = 2·16363` bytes with
SHA-256 `22e65267ba870093c1e9b917fa90d619234ee728eee38443f3df088993a27ea1`.
It was admitted from source base `3c67beee7f656798f912c974f12c482ea12c5e42`.
This publication uses base `f2c03e8dfff3a0fa153e6b072863625bdbb441cf`: all
`18 = 2·3²` reused provider sources match that public base byte for byte, and the original
owner at that base matches the admitted pre-change owner. The provider objects were reused,
not rebuilt. The exact source preserves its pre-acceptance `source-only` comments; the
receipt establishes the focused status recorded here without altering accepted bytes.

The durable publication evidence is in
[VALIDATION.json](receipts/2026-10-09-additive-source-budget/VALIDATION.json),
[KERNEL_VALIDATION.json](receipts/2026-10-09-additive-source-budget/KERNEL_VALIDATION.json),
[compiler.stdout](receipts/2026-10-09-additive-source-budget/compiler.stdout), and
[PROVENANCE.json](receipts/2026-10-09-additive-source-budget/PROVENANCE.json).
The provenance map fingerprints the original technical receipts and the accepted output
objects. [PROVIDER_BINDINGS.json](receipts/2026-10-09-additive-source-budget/PROVIDER_BINDINGS.json)
gives each canonical provider path and its source/object hashes.
[SELECTED_IMPORT_BINDINGS.json](receipts/2026-10-09-additive-source-budget/SELECTED_IMPORT_BINDINGS.json)
projects the ordered `5072 = 2⁴·317` module bindings from the native seal. This projection
does not reproduce machine namespace precedence, absence proofs or metadata; the original
seal's fingerprint is retained. No copied provider library or binary object is published.

| Unit | Measured wall time, seconds | Fixed wrapper projection, seconds | Aggregate CPU time, seconds | Group peak, bytes |
|---|---|---|---|---|
| Preparation | `5950572190/1000000000` | `17` | `5379406000/1000000000` | `325283840 = 2¹²·5·7·2269` |
| Compile wrapper | `13817982878/1000000000` | `21132554884/1000000000` | `8746339000/1000000000` | `4678791168 = 2¹²·3·67·5683` |

The compiler's own wall time was `11767799416/1000000000` seconds. Its child wall and
aggregate CPU limits stayed at `17` seconds, with one thread and the admitted memory
controls. The exact measured/projected ratios and group limits are in the validation
receipt; both units released quiescently. Rejected v1/v2 source fingerprints are retained
there, and their original failed sources and logs remain preserved. This publication ran
no new compiler job.

[agent-inferred] Publication keeps this existing owner and its two consuming equations.
This avoids the recorded failures of adding an unconsumed parallel law and carrying an
unrepaired cause into a new consumer. The cumulative return is the missing term; increasing
a native limit or declaring a small source amplitude would not discharge it. The relevant
practice is [the failures that repeated](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md).

[open] The focused receipt covers the complete named scalar owner and its twelve selectors.
It does not cover a full-library build, an importing consumer build, a plane PDE/heat-kernel
solution, engineered computational force stability, general real or complex NS regularity,
finite-time breakdown, a uniform spectral gap on an unbounded domain, or a continuum MHD
closure. Terminal pressure, boundary and stress estimates remain source-specific obligations
under #62.
