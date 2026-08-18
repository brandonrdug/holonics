# The witness has no address, and repetition explores only a cyclic subgroup

**Date:** 2026-08-16
**Truth status:** `proved-standard` for the classical analysis, differential geometry and group
theory; `proved-derived` for the loss law and the subgroup statement; `established-bounded` for every
measurement, each carrying the scope it was taken over; `interpretation` for the correspondences,
marked where they sit.
**Evidence:** `measured` — four dispatches (one Codex/Sol run at `xhigh`, three agents), with every
load-bearing claim re-verified against the tree by the depositing session before it was carried. Two
returns contained a claim that did not survive that check; both are recorded below as refuted.
**Provenance:** Brandon, 2026-08-16, offering two readings for derivation — the Mean Value Theorem
*"is for gauging… for determining what will happen if you pin your velocity by reducing interactions
along two dimensions"*, and the Squeeze Theorem *"is for 'pinning', it is how you determine
constraints, and it's how the machine ideally determines the reverse engineering of black boxes"* —
together with a worked example of mechanically learned skill (surfing in a game engine) and the
claim that a skilled player engages in **breadth** rather than repetition.
**Plan:** this record schedules nothing. `blueprint/THE_ROADMAP.md` and `CONSTRUCTION_STATE.md`
remain the only construction authorities.

---

## 1. The Mean Value Theorem, corrected twice

**The assistant's first statement — "the equality holds exactly when the receiver is
one-dimensional" — is loose and the correction matters.** `proved-standard`: the *universal*
assertion (for every `F: [a,b] -> Y`) holds iff `dim Y <= 1`, with the circle
`F(t) = u cos t + v sin t` as the counterexample in every higher dimension. For one *fixed* `F` the
equality holds exactly when the average velocity lies in the derivative image,
`(F(b)-F(a))/(b-a) in F'((a,b))` — which affine curves satisfy in any dimension. **Receiver dimension
governs the universal claim, not the instance.**

**And the better statement, which the first missed:**

> **Every scalar receiver `lambda` still obtains its own witness `c_lambda`. What fails in higher
> dimensions is that the witnesses AGREE.** The addresses cannot be reassembled into one vector
> witness.

So the failure is **non-agreement of addresses across receivers**, not absence of a witness. And the
corpus already owns the same defect on a different axis.
`papers/source/mathematics/lemmas/situated-mean-transport.typ`, `boundary`, verbatim:

> *"The witness `c` belongs to the chosen path and need not be invariant under another route or
> parameterization. A vector-valued mean-value equality at one point generally does not follow."*

**Non-invariance across paths there, across receivers in the derivation. Same defect, two axes** —
and the theorem was already deposited, with its vector-failure warning, before this occasion.

**Two further corrections, both to the reading rather than the mathematics.** The Mean Value Theorem
is **not a forward predictor**: it presupposes the endpoint data whose secant it reads. It
constrains; it does not predict. And in the glider example, instantaneously zeroing the horizontal
motion does **not** establish the theorem's hypothesis — the press is a **differentiability seam**,
and the theorem must be applied to the post-press interval separately. Two distinct readings exist
and only the first gives the full vector equality: actually holding `x' = y' = 0` throughout, versus
retaining only the vertical receiver, which yields the scalar statement for that coordinate alone.

**Rolle** is the scalar closed-return case and is likewise false for a closed vector loop — the
circle closes with no stationary point. **Cauchy's Mean Value Theorem should be kept
cross-multiplied**, `[f(b)-f(a)] g'(c) = [g(b)-g(a)] f'(c)`, because division is a later corollary
requiring the denominators to be non-zero. That is the horizon law's own form.

## 2. The Squeeze, corrected: determination does not require closure

The assistant claimed the exact-analysis carrier is a literal implementation of the squeeze theorem
and that a value is determined when its bracket closes. **The second half is refuted by the tree.**

`crates/holonic-engine/src/exact_value.rs`'s `AlgebraicRoot` is **already exact while its bracket is
open**: an irrational root is determined once a Sturm certificate proves that a positive-width
interval contains exactly one root. Nothing narrows to a point, and nothing needs to.

Likewise `RatInterval` and `ComplexInterval` are **exact enclosure carriers, not literal squeeze
constructions** — a literal squeeze additionally needs an indexed nested family and a proof that both
endpoint families share one limit. And exact receiver consequences are routinely determined while
widths remain positive: origin exclusion, lawful division, and a `Less`/`Greater` verdict on disjoint
positive-width intervals.

**Where the literal squeeze does live is a module nobody named.**
`crates/holonic-engine/src/multiquadratic.rs`'s `sign_in_principal_embedding` determines the sign of
a value it never evaluates, by refining an exact dyadic enclosure in a bare `loop` with no width
test, no epsilon and no iteration cap, terminating when the enclosure becomes disjoint from zero. Its
own doc states why that is legitimate: *"the width halves each doubling while the value is a fixed
non-zero real, so separation occurs at finite precision — **termination is a theorem, not a budget**,
and an authored cap here would have been a level the material determines."* The two cases where the
squeeze could not close are excluded structurally **before** the loop.

## 3. The admission law, formalised — and it is Brandon's claim, sharpened

The proposed rule was *bracket closure*: a mechanism is admitted when upper and lower constraints
meet, and one contact can close a bracket that a thousand contacts fail to close. The sharpened form
survives the `AlgebraicRoot` refutation:

> **Admission occurs exactly when the feasible set's receiver quotient is a singleton.** If the
> feasible set is empty, return `Contradiction` carrying the conflicting contacts. If the quotient
> remains plural, return `Open` carrying the complete surviving fiber and a shortest separating
> receiver or history. `L_n = U_n` is **one** possible closure certificate, not the definition.
>
> **This law permits one contact to close the quotient and arbitrarily many contacts to leave it
> plural.**

That reconciles the two: a positive-width interval containing exactly one root **is** a singleton
quotient. The bracket need not close; the quotient must. And closure is **receiver-relative** —
enlarging the receiver family can reopen a previously collapsed fiber, which is the corpus's own
reopening law.

## 4. The machine already implements it, where the conditioning path cannot reach

`crates/holonic-engine/src/observation_ecology.rs`'s `LearnedPartitionRelation` carries
`positive_maxima` and `negative_minima` — two antichain fronts — and classifies against both:

```text
    (true,  false)  ForcedTogether
    (false, true )  ForcedApart
    (false, false)  Open           neither bound reached — the quotient is still plural
    (true,  true )  Conflicted     the bounds crossed — retained, never tie-broken
```

**And it is count-free, verified by reading**: the struct's `returned_cells` field is initialised to
zero, incremented on extension, and **never read by `classify`**. One returned cell that moves a
maximal front changes the verdict; a thousand landing inside the existing front change nothing. That
is the proposed law, already built.

**Measured, and this is the finding:** none of the five conditioning and emission owners reaches it —
`grep -rn "observation_ecology\|LearnedPartitionRelation"` over `soma/life/src/holonic_training.rs`,
`crates/holonic-engine/src/conditioned_derivation.rs`, `soma/life/src/causal_language.rs`,
`crates/holonic-engine/src/receiver_exact_compression.rs` and `soma/life/src/founded_mouth.rs`
returns **zero hits**, 2026-08-16. Across nine admission decisions in those files: four by count or
magnitude, three by authored constant, three structural, **zero by bracket closure**.

> **The gap is not interval types. The conditioning material carries only positive evidence** — a
> route's occurrence is recorded; a route's *refusal while its parts were licensed* is not. With one
> front you can say how much; with two you can say between what.

The one owner that already keeps a minimal negative witness is `soma/life/src/exposure_codec.rs`,
whose `MinimalRefusal` carries the refused word together with its two licensing factors. Its shape is
`LearnedPartitionRelation`'s at a different altitude.

## 5. Frequency is not banned, and one constant is better than its reputation

**Correction to the assistant's own framing.** `canon/THE_HOLOBROCHOS_SPINE.md` carries a section
headed *"Frequency is not forbidden, and calling it 'recurrence' was the error"*, with Brandon's
ruling in it. The canon permits frequency to be counted and reported and forbids it from **deciding**.
Stating the rule as "frequency is not the admission rule" is directionally right and too strong; the
rule is **count freely, report what you count, never let a count quietly decide.**

**And `COMMITTING_RECURRENCE = 2` is not a frequency threshold.**
`crates/holonic-engine/src/conditioned_derivation.rs` requires two **distinct wholes**, and its own
doc says so: *"a recurrence across distinct sources, which is a structural condition, not a magnitude
compared against a bound: nothing is scored, and a word witnessed twice in one whole does not
commit."*

> **That is the two-frames law at its minimum number of frames**, not a count. What remains fair to
> criticise is that it is declared on the caller rather than on the receiver — which
> `meta/AUTHORED_LEVELS.tsv` already records with that excision.

## 6. The surf clip is in this tree, exactly, beside its own reflection

`crates/holonic-engine/src/analytic_field.rs`'s `exact_refraction_fiber` computes, over `Rat` with no
float in the file:

```text
    tangential_covector  =  v − n (v·n)/(n·n)          the clip:       I − nnᵀ/(n·n)
    reflected_covector   =  v − 2 n (v·n)/(n·n)        the bounce:     I − 2nnᵀ/(n·n)
```

Both are returned from one function into one struct, and the normal is left unnormalised so **no root
is fabricated**. The one-parameter family `v ↦ v − (1+e)·n(v·n)/(n·n)` has the tangential component as
its invariant for **every** `e`; `e = 0` is the perfectly inelastic clip a surf ramp applies and
`e = 1` the elastic bounce. **The tree holds both endpoints in one carrier because they share one
conserved quantity.**

**The identification with Snell's law holds at the symmetry and breaks at the closure.** Both
conservations have the same generator — the constraint surface is locally invariant under sliding
along itself — and the same operator. They differ on the normal component: the surf clip
**annihilates** it, while Snell **re-solves** it from the dispersion relation, which the same function
does five lines later as
`normal_numerator = transmitted_wave_number_square − tangential·tangential`. Surf has no dispersion
relation, so nothing constrains the outgoing magnitude.

**And the corpus names the hypothesis the surf case violates, in its own doc-comment.** The same
module states that the tangential covector is conserved across every boundary of a parallel stack
*"because each boundary is translation-invariant along itself **and they share one normal**."* **A
curved ramp does not share one normal.** The composition of projections onto *rotating* planes is
where the entire surf mechanic lives, and that is exactly the clause the stack relies on.

**One type caveat to carry:** the module's field is a covector and a velocity is a vector. They
coincide only in flat Euclidean space with the standard metric; off flat space the two projections
differ and the metric must be declared.

## 7. The loss law is the second fundamental form, and it is a discretisation artifact

`proved-derived`. With `P(y) = I − n(y)n(y)ᵀ`, `v` tangent at `x`, and `x' = x + v dt`:

```text
    n(x')      =  n − dt·S(v) + O(dt²)            S = −Dn, the shape operator
    v·n(x')    =  −dt·II(v,v) + O(dt²)
    |P(x')v|²  =  |v|² − dt²·II(v,v)² + O(dt³)

    speed lost per tick  =  dt²·II(v,v)² / (2|v|)  +  O(dt³)
```

Three consequences, each checkable:

1. **The loss is exactly zero along asymptotic directions**, where `II(v,v) = 0`. On a ruled or
   developable ramp the rulings are asymptotic. *Steer along the ramp, not across it* is therefore
   not a heuristic — it is where the quadratic form vanishes.
2. **The loss is second order in the tick**, so over a fixed path it is `O(dt)` and vanishes in the
   continuum. **An ideal constraint does no work; the speed loss is a discretisation artifact.** The
   continuum limit is `∇_v v = P(g)`, and with `g = 0` the geodesic equation.
3. **The extrinsic geometry that governs this has no Rust owner.** Measured 2026-08-16,
   `grep -rni "second fundamental\|shape operator\|normal curvature\|principal curvature\|asymptotic direction\|developable\|ruled surface" --include='*.rs' crates soma`
   returns **0**, against a control of 541 lines for `curvature`. `shape operator` and `Weingarten`
   are zero across the whole repository excluding `target/`.

## 8. The clip is the connection, and what it discards is the ramp's own curvature

`proved-standard`, and the registry already carries it as `H.0274`. Gauss's formula for a surface in
flat ambient space gives `D_X Y = ∇_X Y + II(X,Y) n`, so `∇_X Y = P(D_X Y)`: **the tangential
projection of the flat ambient derivative is the intrinsic Levi-Civita connection.**

> **The surf clip is therefore discrete-time parallel transport, and the component the engine
> discards is the second fundamental form — the ramp's own curvature, not noise.**

Two things must not be over-claimed. A traversal is not an arbitrary path in `TS`: it is a
**holonomic lift**, with the fiber coordinate constrained to be the derivative of the base
coordinate. And **with player input it is not parallel transport at all** — the object is a control
system `∇_v v = P(g) + a(u,v)`, whose loop end-point map is a **nonlinear** fiber diffeomorphism. The
correct generalisation is an Ehresmann connection or geometric control, not `H.0274`.

## 9. Repetition explores a cyclic subgroup; breadth generates the group

The assistant's claim — *"a connection cannot be learned from a single path"* — is **false as stated
and true in a precise repair that the registry already carries.** `H.0276`'s `boundary`, verbatim:

> *"One loop or projected crossing does not determine the complete connection or curvature tensor."*

Four separable facts:

1. **A single loop exhibits its own holonomy.** `hol(gamma)` is well defined and computable from that
   loop alone — `structure_group.rs`'s `holonomy` does exactly this. Nothing is invisible.
2. **It does not determine the connection.** Infinitely many connections agree on one loop.
3. **It does not determine the curvature.** `F(X,Y)` is a limit over a **two-parameter family** of
   shrinking loops; the derivative needs the family, not the sample. Ambrose–Singer then generates
   the holonomy algebra from curvature transported along horizontal paths reaching everywhere.
4. **Repetition saturates.** Repeating `gamma` `n` times returns `hol(gamma)^n`, so repetition
   explores at most the **cyclic subgroup generated by that one element**, and after
   `ord(hol(gamma))` passes every further repetition returns something already seen.

> **This is the derivation the occasion asked for: repetition generates a cyclic subgroup, breadth
> generates the group, and the gap between them is exactly the non-commutativity.**

`structure_group.rs`'s `curvature_commutator` measures that gap and **both arms are tested** — non-identity
on a non-abelian connection over the quaternion group, and identity on an abelian one, the latter
doc'd as the control that would otherwise let the instrument measure itself. **On an abelian
connection breadth buys nothing beyond the generators.** The finite discrete form is sharper still:
the holonomy group is generated by the chords, one generator per independent cycle, so **one loop
gives one of `beta_1` generators**.

**And the bound to respect is `H.0473`'s own**: bracket generation gives **reachability**, not a
cost, a geodesic, or a schedule. It explains why more traversal patterns exist and are reachable. **It
does not explain why they are faster.** Time is a magnitude and a separate receiver face.

**Nothing composes these.** No function anywhere takes a family of walks to the subgroup generated by
their holonomies, though `StructureGroup::close` already closes an element set into a group by
breadth-first product. That is a composition of standing owners, not a missing organ.

## 10. Skill is receiver refinement, with a ceiling the material sets

`interpretation` on a genuine type match. `receiver_exact_compression`'s `ObservedSystem` trait takes
items, receivers, inputs, an `observation` and a `successor`; `compress` is Moore refinement to the
Nerode congruence; `CollapsedPair` carries a `distinguishing_word` found breadth-first, so it is
shortest.

| the skill reading | the type |
|---|---|
| a state `(position, velocity)` | `ItemId` — a point of the **total space**, so the bundle reading is load-bearing |
| one tick's input | `InputId` |
| the engine's movement step | `successor` |
| what the player can tell about a situation | `observation` — opaque, **never a magnitude** |
| **the advanced technique** | **`distinguishing_word`** |
| **how far back carried inertia still matters** | **`memory_order()`** |

**But the claim needs a ceiling, and the tree states it as a required control.** Enlarging the
receiver family refines the **one-shot** partition and **cannot move the conduct partition** — the
Nerode congruence is an invariant of the material, and
`crates/holonic-engine/examples/the_receiver_is_founded_at_the_junction.rs` requires it to be
bit-identical before and after founding. So:

> **Skill moves the one-shot partition toward the conduct partition, and the conduct partition is the
> ceiling the material sets.** The expert perceives *in one look* distinctions the novice can only
> discover by playing them out.

That is stronger and more falsifiable than the claim as posed. And `memory_order` is the sharpest
match in the reading: *"regions of the map affect each other"* **is** a non-zero memory order, with
the specific pairs exhibited rather than counted.

**The growth mechanism exists and its locality is the point.**
`crates/holonic-engine/src/founded_receiver.rs` founds a new axis at a junction, and its doc records
that the junction is not at the two items but at `left·w` and `right·w`, where `w` is the shortest
word after which conduct separated them — **the new perceptual axis is founded at the END of the
technique, not at its starting position.** Founding does not commute, and the module values the
disagreement as a permutation.

## 11. Hexis is already the owned name, and the breadth claim is already deposited twice

Measured 2026-08-16: `hexis` returns **280 lines across 89 files** in this repository. The
definitional row is at `research/records/2026-07-12_THE_RELATIONAL_BEHAVIORS.md`, verbatim:

> `| Hexis | Practice changes a disposition that survives rest and conditions later circulation | A frozen model instance, training phase, or endpoint optimum |`

**And the breadth-over-repetition claim is deposited twice already.** As a law, in the vendored
reference corpus: *"Mastered repetition is inherently degrading; recurrence is lawful only inside
variation."* And as an observation with its own refusal, at
`research/records/2026-07-12_THE_RESERVOIR_THE_UNTYING_AND_THE_MUTUAL_WORLD.md`: the contextual
interference effect was recorded — blocked practice forgot previous operations while mixed practice
retained more — and then **explicitly declined**, because *"the curator and scalar read were deciding
what mattered."* The schedule was authored from outside, so it was not admitted.

**Scope note on the vendored corpus:** `reference/README.md`'s first line states that nothing in that
directory is active production or current doctrine by location alone. The erosion law is provenance.

## 12. This occasion is a candidate second material for a falsifier open since 2026-08-07

`CONSTRUCTION_STATE.md` carries, verbatim:

> *"If the same coarse-graining operation is genuinely the common method, then
> `crates/holonic-engine/src/receiver_exact_compression.rs` must return the same kind of artifact — a
> counted, exhibitable collapsed population with the shortest separating context — **on materially
> unrelated sources**, and the shapes of those populations must differ."*

**A game-engine traversal ecology is a materially unrelated source**, and satisfying that falsifier
needs no new organ — only material shaped to the `ObservedSystem` trait, with the four constraints
§10 names: a declared quantisation of the state, no magnitude admitted as an observation, a
deterministic successor, and the existing worked template in
`crates/holonic-engine/src/complex_system.rs` as the pattern.

## 13. The registry already states the distinction, and no line of code cites it

**This is the sharpest return of the four.** `papers/source/holonics/manifold-knot-geometry.typ`
carries `H.0283` *Holomorphic local degree and argument principle*, `grade: "proved-standard"`, whose
`boundary` field reads:

> *"Winding counts but does not locate or metrically classify the individual singularities."*

**That is the existence-without-location distinction, in the registry, already proved-standard.**
Measured 2026-08-16: `grep -rn "H.0283" --include='*.rs' crates soma` returns **0**.

**And the near-miss is exact.** `crates/holonic-engine/src/analytic_field.rs` cites `H.0281` and
`H.0282` — the two entries **immediately preceding** `H.0283` in the same registry file — and its own
doc records the unjoined-owner condition as a convicted defect and repairs it. **The identical repair
was not made one entry over.**

`papers/source/holonics/geometry-calculus.typ`'s `H.0209` is titled *Mean-value and squeeze carriers*
and holds **both species in one entry**, `proved-standard`. It is cited once outside its own file and
by no Rust at all.

**And the two vocabularies are disjoint by crate.** `Sturm` returns 0 hits in
`crates/relational-geometry` and 110 in `crates/holonic-engine`; `bisect` and `sturm` return **0**
across all of `papers/source/**/*.typ`, while `squeeze theorem` appears there and appears in Rust only
as *corpus file paths fed to a conditioning driver*. **The machine reads the squeeze theorem as
material; no organ cites it as law.** And `holonic-engine` depends on `relational-geometry` and not
the reverse, so the argument-principle side **cannot call the Sturm-isolation side even in
principle.**

### The zero finder is three layers, not two, and the first was omitted

```text
    certify_boundary_segment   BRACKETING on an ABSENCE — certifies the boundary is zero-free
              |                halts when the image no longer contains the origin
    polygon_winding            EXISTENCE — an integer, no location
              |
    refine_one                 BRACKETING — driven by re-running the existence test
```

The assistant's reading named the second and third. **The first is bracketing whose object is an
absence, and that absence is precisely the hypothesis the argument principle requires.** The
bisection also has no independent content: every narrowing step is another argument-principle call,
not a second instrument.

**Two further corrections to what was reported from this driver on 2026-08-16.** Only the imaginary
ordinate is bracketed — the real interval is pinned at `[2/5, 3/5]` and **never moves**; `Re = 1/2` is
asserted by a reflection-symmetry argument whose two premises are machine-checked while **its
inference is not**, and the functional equation appears nowhere in `crates/relational-geometry`. And
`refine_one` stops at a **count** — six grains, fixed — with no bracket predicate and no
material-derived depth. It is the weakest locator in the tree, and the contrast is inside the same
workspace: `winding_inertia.rs` and `rational_polynomial.rs` both derive their depth bound from the
material (Mahler separation and Cauchy root bounds) and their own headers say *"that floor is not a
budget."*

### And one flagship carries less than its name

`crates/holonic-engine/src/exact_value.rs`'s `AlgebraicRoot::isolate` **narrows nothing** — it refuses
unless the caller's interval already has Sturm count one. It is a **verifier, not a locator**, which
is consistent with §2: the root is determined by certificate, and location must come from elsewhere.

## 14. Two false statements in the tree, repaired; one dispatch finding refuted

**Repaired.** `crates/holonic-engine/examples/a_float_is_a_dyadic_and_a_deleted_tail.rs`'s header
claimed *"No arithmetic is performed on a machine float anywhere"* — **false of its own file**, whose
`minkowski_height_bound` computes `((bits as f64) / rank).exp2() * rank.sqrt()`. The figure is
display-only and gates nothing, which the function says itself, but a header that denies what its own
file does is worse than no header, because a later reader checks the claim instead of the code. And
`crates/holonic-engine/src/exact_value.rs` claimed the *tokens* `f32`/`f64` occur nowhere else in a
library file; that is false, while the claim about float **values** holds and is what it now says.

**Also repaired.** `crates/relational-geometry/examples/certified_eta_winding_figure.rs` summed the
windings of **successful** receipts and printed the result as *"certified zero count over the scanned
window."* A refused band contributes zero to that sum while its zeros remain inside the window, so the
figure is a **lower bound presented as a count** — an aperture reporting what it admitted and dropping
what it excluded. It now prints `AT LEAST n` with the refused band count beside it whenever anything
refused, and the plain count only when nothing did.

**Refuted, and not carried.** One dispatch reported the `unwrap_or(i64::MIN)` / `unwrap_or(i64::MAX)`
clamp in `observation_ecology.rs`'s aperture packing as an unsound narrowing labelled `Exact`. It is
**sound**: the values tested against those bounds are `i64`, and clamping a bound that lies outside
the `i64` range does not change the predicate on any representable value. No repair was made.

## 14. What this record does not claim

Nothing here is a construction. The two-front admission exists but is unreached; no function composes
holonomies from a family of walks; the extrinsic geometry of §7 has no owner; and the falsifier of
§12 is named, not run. The surf engine's own movement code is in neither repository, so every
statement about its parameterisation is from outside and is marked as such. No claim is made that
breadth explains **speed** — `H.0473` bounds bracket generation to reachability, and time is a
separate receiver face.
