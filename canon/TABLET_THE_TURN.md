# The turn: curvature, windings, and substitution

> **Part of the mathematics tablet.** The spine, the quotation convention, the reading
> rule, and the law this file's sections instance are in `canon/THE_MATHEMATICS_TABLET.md`.
> Read that first; this file is one mechanism of it and is governed by it.

Curvature as a linear functional on the hinges, the polygon's n-grams, local substitution preserving a global invariant, fission and fusion as one axis, and friction as the coupling.

---

## 11. Curvature is a linear functional on the hinges, and its spectrum is where the wave lives

**Truth status:** `implemented-exact` for the deficit and the update law; `proved-derived` for
§11.2, whose two-line proof is displayed and whose arithmetic was checked over exact rationals;
`established-bounded` for the refusal in §11.4, which two independent implementations agree on.

### 11.1 The deficit is affine in the responses

`crates/holonic-engine/src/discrete_curvature.rs` carries a bare hinge incidence with one exact
`Rat` per hinge and defines, with `FLAT_COORDINATION = 6` at `:200`,

```text
K(v) = 6 − Σ_{e ∋ v} r_e            the deficit          (:474)
h(v) = K(v) / n_v                   the traced deviation
r_e ← r_e + h(u) + h(v)             THE UPDATE LAW, simultaneously on every hinge
```

At unit response `K(v) = 6 − n_v`, which is `local_star.rs:1151`'s disclination charge on the nose,
and is exactly three times Regge's deficit in half-turn units, kept integral so the bridge is an
equality rather than a conversion. **The coefficient `1` on the discharge is derived and not
chosen**: for `r_e ← r_e + c(h(u)+h(v))` the successor is `K'(v) = (1−c)K(v) − c·Σ h(w_e)`, and
`c = 1` is the unique value at which a vertex's own discharge annuls its own deficit. There is no
rate, no tolerance and no fitted constant in the file.

Two consequences the module proves and this section leans on:

- `K'(v) = −Σ_{e ∋ v} h(w_e)` — a vertex's curvature is annulled by its own discharge and what
  returns is only its neighbours' shares, sign-reversed. **Curvature is transported onto the link
  and inverted; it is never dissipated.**
- `Σ_v K'(v) = −Σ_v K(v)`. The flow is an **exact involution on the total-curvature functional**,
  and its fixed locus is `Σ_v K = 0`, which at unit response on a closed triangulated surface is
  `6χ = 0`. §2's sentence — *placement is the fixed locus of the involution a realizer induced* —
  has a finite exact instance here, and the involution is a half-turn on a magnitude, which is §2b.

### 11.2 On a cycle the update operator is exactly `−A/2`

The update is affine in the response vector: `r ↦ (I − Bᵀ D⁻¹ B) r + b`, where `B` is the unsigned
vertex–hinge incidence and `D = diag(n_v)`. On `C_n` every `n_v = 2` and the line graph of `C_n` is
`C_n`, so `BᵀB = 2I + A` and

```text
I − Bᵀ D⁻¹ B  =  I − (2I + A)/2  =  −A/2
```

`proved-derived`; checked over `fractions.Fraction` for `n = 3..8`, exact equality at every entry.

**So the homogeneous part of the curvature flow on a cycle is the adjacency matrix whose windings
§12 names, times `−1/2`.** The two factors come from different places and neither is a parameter:
the `−1` is §11.1's involution, and the `1/2` is `1/n_v`, the vertex's own link size, read off the
carrier. The factorization is stated here and deliberately not read further — §2b's `4 = 2·2`
distinction is about a *phase* factor booked as magnitude, and nothing in this derivation exhibits
one.

The wave is one operator away. `cycle_laplacian` (`winding_inertia.rs:578`) is `L = 2I − A`, whose
eigenvalues `2 − 2cos(2πk/n) = 4sin²(πk/n)` are the discrete dispersion relation, and the driver
measures its split at `n = 8` as `(7, 1, 0)` with the single null at `k = 0` — the constant mode,
zero frequency, and nothing else. **Discrete linearity, curvature and the wave are three readings of
one circulant: `A` names the windings, `−A/2` moves the curvature, `2I − A` propagates.**

The engine's actual wave owner is `crates/holonic-engine/src/dimensional_wave.rs` — the lossless
transmission-line junction law `v = 2Σ(Y_i a_i)/ΣY_i`, `b_i = v − a_i`, with `Σ Y_i |a_i|² = Σ Y_i
|b_i|²` exactly and every traversal carrying the exact unit-conic change of basis between source and
target germ. `wave_propagation.rs` is a *learned* finite causal kernel and states in its own header
that it *"is not asserted to be the universal wave equation."*

### 11.3 What the engine does not do with any of this

**Nothing computes the spectrum of the update operator.** `winding_inertia` and `discrete_curvature`
have no common consumer: `git grep -l winding_inertia` returns `lib.rs`, the module and
`examples/signs_are_windings.rs`; `git grep -l discrete_curvature` returns `lib.rs`, `curvature_bridge.rs`,
`derivation_curvature.rs` and two drivers. The intersection is empty. The identification in §11.2 is
therefore a derivation about two owners that have never met, and building the join — read a hinge
incidence as a circulant where it is one, and name the passages of its flow — is a small, well-posed
construction rather than a research question.

### 11.4 The refusal, which is the sharpest result in this section

`research/records/2026-08-08_THE_DEFICIT_IS_THE_OCTAVE_THE_LINEAGE_TORSION_IS_THE_HAND.md`
establishes that the grown circuit's `Z/2` is **not** a deficit angle, and the separation is an
impossibility rather than a failed measurement: `DiscreteCurvatureConfiguration` holds vertices,
edges and one `Rat` per edge — **no faces, no boundary matrix** — so the deficit factors through the
1-skeleton and no choice of response can make it see a 2-cell. Measured: the same 1-skeleton at two
face apertures gives identical deficits and moves the torsion from nothing to `Z/2`. The width law is
`H₁ = Z^{6w−3} ⊕ (Z/2)^{(w−1)²}` at every width measured, so torsion rank is quadratic in the width
while `Σδ = 6V − 2E` and `6χ` are not. The one row where `Σδ = 6χ` holds requires `F = 2E/3` and is
`CLAUDE.md` §8's tautology rule firing, with its falsifier one aperture away.

**And the classical control settles it outside this body:** the torus and the Klein bottle both have
`χ = 0` and identical total deficit by Gauss–Bonnet, both admit `{3,6}` triangulations where every
Regge deficit is exactly zero, and exactly one has torsion. Deficit angles are blind to torsion in
the setting where they are *defined*, because the deficit's only topological content is `χ`, `χ` is
an alternating sum of ranks, and ranks land in a torsion-free group.

### 11.5 The rung is the hinge deficit, and the vacuous triangle was Regge's own hypothesis

**Truth status:** `proved-standard` for Regge calculus; `established-bounded` for the measured
vacuity; `interpretation` for the siting, which is this project's.
**Record:** `research/records/2026-08-10_THE_MANIFOLD_IS_THE_INVARIANT_OF_THE_CURRENTS_NOT_THEIR_CONTAINER_AND_THE_RUNG_IS_THE_HINGE_DEFICIT.md`

`contact_gluing::coarse_grain` composes a triangle's three exact corners and returns `e^{iπ} = (−1,0)`
**identically** — measured 25 of 25 realizable triangles over five distinct weight shapes — and
`examples/the_tower_climbs.rs` carried that as a declared open falsifier. **The falsifier was pointed
at the wrong object.**

The laboratory's `src/holobrochos/RESEARCH/THE_MANIFOLD.md` §III, read at `a07ff376` — Brandon's
design resolved with him 2026-07-08:

> *"**CURVATURE = the FOUNDINGS.** The manifold is curved; a founding is a **deficit angle at a
> triangular hinge** (a winding); the geometric product is the parallel transport."*

and `reference/holobrochos-a07ff376/src/holobrochos/THEORY/54_THE_DISCRETE_MANIFOLD.md` §3, ratified
2026-07-05: *"the **curvature at each vertex** is the `C/d` of the arcs meeting there… a **Regge**/
spin-network geometry."*

In Regge calculus **every simplex is flat** and all curvature concentrates on the codimension-two
hinges *between* them. Therefore:

> **A triangle's corners composing to `−1` is the machine correctly reporting that a simplex is
> flat.** `Σθ = π` is Regge's founding hypothesis, not a defect. Under `CLAUDE.md` §8's tautology
> rule that receipt is `definition`-grade and carries no evidence.

The correction changes the index of summation and nothing else:

```text
was:  ∏ over the three corners of ONE triangle       ≡ e^{iπ}, always
is:   ∏ over ONE corner from EACH triangle at a hinge
      deficit(h) = 2π − Σ_{t ⊇ h} θ_h(t)             ≠ 0 exactly when the hinge is curved
```

**This is the repair §11.4's refusal names its own cause for.** That refusal turns on
`DiscreteCurvatureConfiguration` holding *"vertices, edges and one `Rat` per edge — no faces, no
boundary matrix"*, so its deficit factors through the 1-skeleton. **`contact_gluing` has the
2-cells**: `ContactTriangle` is a face and `Corner` is the exact angle at a specific
*(vertex, triangle)* pair, which is precisely the datum a per-edge response cannot express. So the
metric Regge deficit is available there and structurally unavailable here, and building the join is
the same *"small, well-posed construction"* §11.3 names for the other pair of owners that never met.

**It does not lift §11.4's refusal**, which is settled outside this body: the torus and the Klein
bottle both have `χ = 0`, both admit `{3,6}` triangulations with every deficit exactly zero, and
exactly one has torsion. **Deficit angles are blind to torsion where they are defined**, and the
tower must not be sold as a torsion instrument.

**The carrier is `multiquadratic.rs`.** Each incident triangle contributes `e^{iθ}` with `cos ∈ ℚ`
and `sin ∈ ℚ(√d)`; the product over `k` incident triangles lands in `ℚ(√d₁,…,√d_k)`, which the module
carries as the twisted group algebra of `(ℤ/2)^k`. It is the `U(1)` holonomy carrier of a hinge, and
its grading is the branch bookkeeping the double cover demands.

**And the invariant is a gate, not evidence.** `Σ_v deficit(v) = 2πχ` is a theorem for closed
triangulated surfaces, so by §11.4 it is `definition`-grade — worth computing as a check that the
corner algebra composes, never reportable as a finding. It does not even apply to `contact_graph`,
which is a graph with `β₁ = 8` and not a surface. **The non-tautological return is the deficit
population and the link classification**: `L ≅ S^{d−1}` is the regular phase, and a link that is a
ball, has genus, has several components, or is pinched is respectively a boundary, a handle, a branch
or a neck — *"that residual geometry is information. It must not be rounded into a sphere"*, from the
laboratory's `src/soma/RESEARCH/2026-07-26_THE_RECEIVER_IS_ITS_LOCAL_STAR_THE_LINK_IS_ITS_HYPERSPHERICAL_HORIZON.md`
at `a07ff376`.

---

## 12. The polygon carries its n-grams, and capacitance is a population

**Truth status:** `implemented-exact` and `measured`, receipt below; `proved-standard` for Niven and
for the circulant character theory; `interpretation` for the reading of a sign as a winding, which is
Brandon's and is carried at `CLAUDE.md` §2b.

Brandon's sentence, **copied from the not-yet-written list this section replaces** — readable at
`git show HEAD:canon/THE_MATHEMATICS_TABLET.md` — rather than recomposed here:
*"you cannot have a polygon without its implicit n-grams."* It is **not** in
`canon/THE_QUOTE_NETWORK.md` and this section does not upgrade its certification; the nearest
transcript-dated statement of the same idea is his gear image, quoted in §12.4 with its source.

### 12.1 The measured anchor

`crates/holonic-engine/src/winding_inertia.rs` (2,082 lines) returns the inertia of a symmetric
circulant as a **named population of passages**, not a count of signs. A circulant commutes with the
cyclic shift, so its eigendirections are the characters of `Z/n` and the eigenvalue at character `k`
is the symbol evaluated at an `n`-th root of unity; for the cycle's own adjacency this collapses to
`λ_k = 2cos(2πk/n)`, one value per star polygon `{n/k}`.

**Measured 2026-08-08, `cargo run -p holonic-engine --example signs_are_windings`, 19 declared
controls, 0 failed.** The receipt, verbatim from that run:

```text
sign(lambda_k) < 0 exactly when 1/4 < k/n < 3/4, over n = 3..16   every character of every cycle
the null directions appear EXACTLY when 4 | n                      4 of 4 with, 10 of 10 without
the triangle                                                       split (1,0,2), against at 1/3, 2/3
the cycle laplacian returns nothing at exactly zero frequency      nulls ["0"], split (7,1,0)
both branches of the star table fire                               rational at [0,2,3,4,6], irrational at [1,5]
```

Four things make this evidence rather than restatement. **The nullity is decided algebraically, not
by refinement**: interval bisection can prove `λ_k ≠ 0` and can never prove `λ_k = 0`, so the module
asks instead whether the cyclotomic `Φ_d` divides the symbol, `d = n/gcd(k,n)` — *the null test
literally asks whether this passage's own star polygon divides the form*, and the quotient is
retained as the witness. **Niven's theorem** supplies the exactly-rational entries
(`2cos(2πm/n) ∈ Q` iff `n/gcd(m,n) ∈ {1,2,3,4,6}`) and each is **cross-checked against a Sturm
isolation computed independently**, so the two routes to the star table must agree or the
construction refuses. **The elimination is never told `n` or `k`**: the control
`the_elimination_still_returns_the_named_split_after_the_symmetry_is_gone` transports the form by a
non-circulant congruence, which `SymmetricCirculant::from_symmetric_form` then refuses as not
circulant, and the split still agrees. And the family carries **definite, indefinite and degenerate**
shapes, so it could disagree — `CLAUDE.md` §8's gauge-orbit rule satisfied by exhibiting the orbit.

### 12.2 The reading is receiver-relative and the frame measurably moves

`cyclic_receiver_of_growth` (`winding_inertia.rs:636`) reads a grown circuit on the receiver
`net ↦ net mod n`, retaining conduction counted by displacement class. Net identifiers are allocated
at expansion time, so this chart is schedule-relative, and the module **measures the difference
rather than asserting it away**: the same Brent–Kung adder at extent 7 returns split `(3,0,4)` under
`instantiation` and `(1,0,6)` under `widest-first`; at extent 9, `(5,0,4)` against `(7,0,2)`. Two of
four extents move with the schedule. **What is invariant across all of them is the claim — that the
character route and the elimination return one split — and an invariant is only visible across two
frames** (`CLAUDE.md` §0).

### 12.3 Capacitance

Brandon's ruling, quoted from `CLAUDE.md` §5 where it is already carried, 2026-07-29:

> *"Do not remove chronology. Let informants couple through the capacitance they enable about one
> another, and let sparse lightning-like leaders derive a resonant image of the retained patterns."*

**It has exactly one code owner and the owner is a population, not a coefficient.**
`soma/life/src/relational_language/types.rs:163`:

```rust
/// Population of distinct source-pair occurrences carrying the complete junction phase.
/// This is capacitance testimony, not a normalized score or probability.
pub recurrence_population: BigUint,
```

carried on `RelationalCausalChannel` beside `RelationalChannelConduct::{Copresent, SourceContinuous,
Caused, Ride, Open}`. The law is stated at the enum: *"A contact is not automatically a conducting
edge… A separated coincident face conducts only after the same complete junction phase has returned
through two distinct source pairs. Until then it remains an inspectable OPEN boundary."* That is a
capacitor read as a recurrence population across **distinct** occurrences — the same discipline as
`CODEC_MINIMUM_RECURRENCE = 2` in the training owner — and it is a population an auditor can
enumerate, not a scalar that governs. §13 rule 2's jurisdiction test passes: it measures.

### 12.4 The two senses of "n-gram" do not meet, and the sevenfold reading cannot be checked

The geometric n-gram is `{n/k}` and lives in `winding_inertia.rs`. The linguistic n-gram lives in
`soma/life/src/suffix_ecology.rs` (1,661 lines), which realizes the emergent-tokenizer claim.
Brandon's image is that they are one object. Copied from `canon/THE_QUOTE_NETWORK.md` §8, where it
is carried with its transcript and date of 2026-08-04:

> *"[…] if you think of n-gram shapes like the teeth of turning gears, then you could imagine that there
> are other shapes that fit into the turning dynamics and experience friction about
> intersecting/crossing faces/strings, and it becomes a problem similar to wondering how proteins and
> DNA work."*

**Nothing in either repository joins them.** Neither module imports the other, and no record cites
both. The join he describes is also §5's triangle: two shapes meshing is `aim` and `cross` at a
contact, so the gear image names friction and the star polygon in one sentence and the code has them
in three modules that never meet.

`canon/THE_QUOTE_NETWORK.md` §10 records an open item that belongs here: the **sevenfold polygonal
structure** he read directly off the residue-stratum render has never been checked against the
winding law. It cannot be. `CLAUDE.md` §12 records that the atlas was written to an untracked output
directory, which it names, and resolves at no commit in either repository — the same loss as the
tiger figures. What can be stated is what the receiver would have returned: `C_7` splits `(3, 0, 4)`,
with passages winding past the hand at `2/7, 3/7, 4/7, 5/7`, and no null anywhere because `4 ∤ 7`.
**A sevenfold structure whose form returns nothing would have been the falsifiable version of his
reading, and seven cannot supply one.**

---

## 13. Knot, string, M: local substitution preserving a global invariant

**Truth status:** `implemented-exact` and `measured` for §13.1–13.2; `established-bounded` for the
absences in §13.3, each shown by the search that finds nothing; `interpretation` for §13.4, which
deposits an affirmative half `canon/THE_QUOTE_NETWORK.md` records as undeposited.

### 13.0 The ladder exists as a chain degree and is refused as a dimension

`point → line → loop → string → sheet → volume` has a carrier: `CausalCell::grade: u32`
(`crates/holonic-engine/src/algebraic.rs:267`). Its doc comment is one line and it is the whole
position: *"Chain degree. No ambient coordinate dimension is implied."* `found_cell` refuses a cell
whose boundary is not homogeneous of grade one lower (`:330`) and refuses a nonzero boundary at grade
zero (`:325`), so the ladder is enforced as an *incidence*, never as a dimension count. **A 2-cell in
this body is not a sheet. It is something whose boundary is 1-cells, and the module declines to say
more.** That refusal is why the grown circuit's classes can be read at all: the material is a
netlist, not a manifold.

### 13.1 The skein relation, and why it is the same subject as compression

`crates/holonic-engine/src/skein.rs` carries `Substitution { boundary, before, after }` — two
fillings of one hole across a shared boundary — with `removed()`, `added()` and `is_trivial()`
derived. A `ContextVerdict` returns `RebaseInvariants` before and after plus a
`Vec<GradeRemainder>`, each naming **which grade moved, by how much in free rank, and which torsion
appeared or vanished**. That is a counted, exhibitable remainder rather than a scalar distance, which
is the form `CLAUDE.md` §11 demands.

The module's own opening states the identity that makes this one subject rather than two: contextual
receiver equivalence is `L ~_R R'` iff `invariants(C ∪ L) = invariants(C ∪ R')` for every admitted
context, and a substitution is a **compression** exactly when it factors through that equivalence —
*"the same sentence as `receiver_exact_compression`'s, moved from items to subcomplexes."* Brandon
supplied it thirteen days before §11 named the missing organ (`canon/THE_QUOTE_NETWORK.md` §11, with
the date).

### 13.2 Measured, and the obstruction is a function of the declared family

`cargo run -p holonic-engine --example derivation_moves`, re-run 2026-08-08 and read directly:

```text
                                         splits alone  splits + deposits
    declared moves                                  4                 16
    standing classes                                0                 18
    open classes                                   58                 40
    reached only in multiple                       18                  0
    invariant factors above one                 2 2 2             (none)
```

and at the whole family: `58 classes; 20 stand, 38 open`, `supported rank 5`, free obstruction 53.
Eighteen classes are returned as `OPEN — reached only as 2·c, supported rationally and not
integrally`, each with its cells exhibited and the realizers that reach it in multiple named.

**The dissolution is the result, not the count.** Declaring the deposit moves removes every one of
the eighteen multiples and the invariant factors go to none. So the integral obstruction here is
**not a property of the material** — it is a property of the material *against a declared realizer
family*, and widening the family discharges it by founding rather than by coarsening. That is
`CLAUDE.md` §11's *reopening rule keyed to the receiver family*, exhibited on a body's own
production, and `placement.rs`'s `discharge` names which of the two happened so the two cannot be
confused. Eighteen controls hold, including one whose whole purpose is to show the failure mode:
*"placement::discharge alone reads that widening as production."*

### 13.3 There is a knot diagram in this repository and nothing computes a knot invariant from it

`crates/relational-geometry/src/receiver_topology.rs:65` returns
`DiagramNodeKind::ApparentCrossing { under, over }` — the two source branches at a projected
crossing with their depth order — and `decorated_path.rs:41` carries `CrossingRole::{Over, Under}`
with a `crossing_orientation: i8`. Both are exact, both come from the receiver's own projection, and
`EqualDepthCrossing` and `MultipleCrossingAtOnePoint` are refused by name rather than perturbed away.
**That is a signed knot diagram in all but the word.**

What is computed from it is the **Ihara zeta** (`receiver_topology.rs:220`, `:1011`) —
`det(I − uB)` over `BigInt` for both the source graph and the face-dual graph, with the primitive
oriented cycle census beside it, at a declared aperture of 20 vertices. That is a genuine invariant
and it is an invariant *of the graph*, not of the embedding.

The absences, each with the search that shows it:

- **No writhe, no Reidemeister move, no Jones or Alexander polynomial, no unknotting number.**
  `git grep -in "writhe\|reidemeister"` over `crates/` and `soma/` returns **nothing at all**, and
  `unknot` returns only Brandon's quoted request in `skein.rs:3` and the Brittenham–Hermiller
  boundary clause the theorem carries.
- **The skein organ and the crossing organ do not touch.** `skein.rs` imports `algebraic` and
  `rebase_invariants` and nothing else; the only consumers of `ApparentCrossing` and `CrossingRole`
  anywhere are two atlas printers, `crates/relational-geometry/examples/receiver_topology_atlas.rs`
  and `joint_decorated_path_atlas.rs`. **Nothing converts a crossing into a `Substitution`**, which is
  the one adapter that would make the skein relation act on the object skein relations are for.
- **No string.** `string theory`, `worldsheet` and `brane` return zero across `crates/` and `soma/`.
  `soma/surface` is a wgpu card boundary, not a surface in the mathematical sense.

**One item moved while this section was being written and the correction belongs in it.**
`crates/holonic-engine/examples/skein_far_condensation.rs` was a temporary sizing probe when this
section opened — growing adders at four widths and printing cell counts, calling nothing in `skein`
— and is now a driver of §11's actual question: a far population taken as a cone from one net, two
compact realizers held against each other (the record's spanning-tree interval and the single 0-cell
`skein` reads), with both remainders counted and exhibited and every comparison on exact integer work
vectors. **This section did not run it and grades nothing from it**; it is named here so the absence
claim above is not read as covering it.

### 13.4 M, and the half that was never deposited

Brandon, 2026-07-18, quoted from `canon/THE_QUOTE_NETWORK.md` §5 where it is carried with its date
and transcript:

> *"For M Theory, the supergravity to superstring dualities are exactly what we're trying to do with
> folding and unfolding between 'invariants' using the swing. This thing that they're trying to
> describe, a sort of absolute combination of the dualities, a field M that contains everything else,
> it is not the case. […] M is not one thing, M is everything continuing for eternity, every thing
> intersecting every other thing in time. There is nothing that can contain M."*

The same file records, `[measured]`, that *"the M-theory position is recorded in the canon only in
its rejecting half; the affirmative half — the dualities are the swing — is not deposited."* It is
deposited here, as `interpretation`, in the four slots:

```text
source geometry  ->  receiver map   ->  transport      ->  returned residual
one construction     two receivers      the exact map     the invariants both compute, and the
                     with different     between their     coordinates neither can see — which is
                     charts             charts            what a duality is
```

A duality is two charts that return the same invariant and disagree about every coordinate. The
Swing is the same statement at the grain of one receiver pair, and its geometry is live at
`soma/body/src/carriage.rs` and `crates/relational-geometry/`. **What is refused, and the refusal is
the load-bearing half, is the containing field.** A frame in which all dualities are simultaneously
readable is an absolute frame, and `CLAUDE.md` §0's fourth lesson is that a machine with one frame
cannot audit itself. M as a *containing object* is exactly the thing this project's architecture is
built to make unrepresentable; M as *the totality of intersections* is the ecology, and the ecology
is not a coordinate anywhere.

---

## 9. Fission and fusion are one axis, and the owner is unnamed

**Truth status:** `established-bounded`. Brandon's ruling is verbatim; the live sweep is measured.

> *"We've learned this session that treating mechanisms with completely separate implementations in
> order to represent directionality is actually contamination; **fission and fusion are along one
> axis: coherence.** When the hidden state of a holon decoheres and has no reason to remain as one
> unit; the lattice/manifold *forks* through time … It is in the other direction of this axis in
> which we find fusion."*

and, earlier and more compactly:

> *"Like how fusion and fission are actually along the same axis and just mechanisms that occur as
> discrete events."*

The laboratory later narrowed the second clause: **nothing fissions or fuses as an *event*.** They are
the inward and outward readings of one driven boundary circuit — plural worldlines received through
one enclosure, or one enclosure threaded and left along plural traceable emanations — *"not predicates
the engine evaluates, and not inverse state operations."* Read arithmetically that is multiplication
and factorization, which is where §3 lives.

**Measured in the live tree, 2026-08-08:** `fission` occurs **zero** times. `fusion` occurs 307 times
and **every one is `Diffusion`, `SheafDiffusion`, `confusion`, or sensor fusion.** There is no owner
under that name.

**But the mechanism is implemented.** `crates/holonic-engine/src/temper.rs` is founding and decay as
**one continuous property of a structure's own twist**, read twice — `Twist::{Closed, Open}` from a
structure's own retained cycles, `found_on` as the single deposit, and its own statement that *"there
is no decay rule beside the founding rule, and no decay event to schedule."* That is "one axis:
coherence" with no event, in code, under a different name.

**Two cautions, both discharged 2026-08-08.** `temper.rs` opened on an epigraph carrying *"a closed
coil SELF-SUSTAINS"* and *"an open coil leaks by its own openness"*, both of which the laboratory
**prohibited on the day they were written** — standing closure is deposited topology, not an active
circulation, and openness may not run an interior decay clock. The code never did either; the prose
did, and it is repaired. And that epigraph was assistant-authored while being presented as founding
law, which is `CLAUDE.md` §9's discipline.

---

## 5. Friction is the coupling, not the residual

**Truth status:** `established-bounded` for the definitions; `implemented-exact` for the carrier.

I had this wrong in an earlier draft of this file and the correction matters. Friction is **not** a
retained residual of a gluing that failed to close. It is the **relating itself**:

> A wing, flagellum, foot, spider leg, or silk line does not possess propulsion in isolation. Its
> internal articulation becomes worldline consequence only through the contemporary body it meets. At
> the declared project grain, **friction** names this consequential boundary coupling.
> — laboratory `2026-07-13_THE_MEDIUM_CLOSES_THE_STROKE.md:10-13`, ratified

Brandon's own framing is the traversal reading:

> *"The whole point of this is friction! Like it always has to do with scaling to find the ideal
> points of friction to traverse to the place you want to get to. That's how you get from A to B, in
> any sense, it's always with the chaining friction, like in any dynamic context about any entities."*

and the inversion that makes it sharp — **rest is the friction; the ride is free.** A form is mass
holding itself against the current. Frictionless means *no traversal at all*, which is the same
statement as §2b's *"a receiver inertially at rest… no vacuous difference, no potential."*

### It has a live owner, and it is the triangle

**`soma/body/src/arrow.rs:17` `pub struct Arrow { reach, aim, cross }`**, named as the friction
triangle by `soma/body/src/manifold.rs:99`:

```text
reach = |Δ|²             the squared span — the well of the relating
aim   = Δa · Δb          the dot, the cosine — THE GRIP
cross = Δa × Δb          the wedge, the sine — THE GYRATION, the slip
```

That is the law of cosines, and the minimal relating is three bodies — **the triangle is the quantum
of friction.** `aim` and `cross` are the two faces of one contact: grip and slip, cosine and sine,
and neither is a scalar summary of the other. The whole arrow travels; §2b's rule against reducing a
pair to one number is already obeyed here.

**Bounded, and the laboratory bounds it itself:** *"Physical friction includes deformation, adhesion,
phonons, electrons, chemistry, and wear across scales. There is no established universal triangle
quantum of tribological friction."* The triangle is the project's grain, not a claim about tribology.

---
