# The corner breaks the group law and its remainder is a holonomy

**Date:** 2026-08-16
**Truth status:** `proved-standard` for the classical mathematics; `proved-derived` for the group-law
criterion and the involution identification; `interpretation` for the correspondences;
`established-bounded` for every measurement, each carrying the scope it was taken over.
**Evidence:** `measured` for the counts; direct source inspection for every claim about this tree.
**Provenance:** Brandon's RH/Hodge thread of 2026-08-16, and his instruction to synthesize the four
dispatches rather than relay them. The dispatches are evidence that was checked; every load-bearing
claim below was re-verified against the tree by the session that deposited it.
**Supersedes in part:**
[`2026-08-16_WEIL_POSITIVITY_IS_A_TRACE_ON_A_RETAINED_REMAINDER_AND_A_PROOF_TRANSPORT_IS_A_ONE_BIT_COMPRESSION.md`](2026-08-16_WEIL_POSITIVITY_IS_A_TRACE_ON_A_RETAINED_REMAINDER_AND_A_PROOF_TRANSPORT_IS_A_ONE_BIT_COMPRESSION.md)
— two of its claims are withdrawn in §3 below and its four open questions are answered in §2.
**Plan:** this record schedules nothing. [`blueprint/THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md)
and [`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.

---

## 1. The corpus already owned the construction, and the named entry point could not reach it

Yesterday's record posed four identifications as open questions and sent three dispatches to settle
them. **Three of the four were already deposited in this tree, in the corpus's own vocabulary,
between 20 and 24 July.** Not as analogies to be built — as exact registry entries.

The most direct instance. `papers/source/mathematics/theorems/prime-power-aperture-incidence.typ`
writes the compression of the scaling action onto a cutoff range, under the word *aperture*:

```text
    <a, U_t a>  =  <a, P_R U_t P_R a>        P_R = multiplication by the indicator of I_R
    P_R U_t P_R = 0                          whenever |t| >= L
```

And `papers/source/mathematics/theorems/archimedean-remainder-amplitude.typ` transcribes
Connes–Consani's archimedean construction whole — `P_0` the orthogonal projection,
`B_2 = −P_0 N_2 P_0` the compression, the prolate/Sonin kernel named in it, `status: Exact
factorization` — with a boundary restricting it to the one-place aperture.

**And `papers/source/mathematics/theorems/weil-support-induction-reduction.typ` is an RH induction
reduction.** Its title is *RH reduces to one uniform conditioned support-successor law*. Brandon said
on 2026-08-16, before any of this was located: *"I think holonics can prove RH with some sort of proof
by induction."* The induction architecture was deposited on 2026-07-24 and neither of us knew.

### Why it was not found, measured 2026-08-16

`CLAUDE.md`'s entry rule names three entry points, the first being `THE_CLAIM_INDEX.md` *"when you do
not know which file owns a subject."* Measured:

```text
    ls research/records/*.md | wc -l           400
    ls research/records/2026-07-*.md | wc -l   292
    ls research/records/2026-08-*.md | wc -l   108
    tools/claim_index.py:297                   glob("2026-08-*.md")
```

**The claim index reaches 108 of 400 records by design, and the entire RH / Sonin / prolate / Weil
line lives in the 292 it cannot reach.** The generator's heading declares the ratio honestly, so
nothing is false; but the entry rule points at an index that is structurally unable to answer this
subject, and that is the mechanical cause of the failure rather than a lapse in reading.

`canon/THE_CORRESPONDENCE_ATLAS.md` **does** reach it — it carries `Geometric semilocal Sonin/prolate
carrier`, `Adele-class semilocal trace`, and `Mellin transport and Weil positivity` as cards with line
numbers. The atlas is the entry point for this subject and the claim index is not.

> **A generated index inherits its generator's aperture, and an entry rule that names it without
> naming the aperture will send a reader confidently to a place that cannot hold the answer.**

**And the second reason compounds the first: there are two registries and they do not cross-reference
by id.** `papers/source/holonics/registry.typ` keys entries as `H.NNNN` / `RH.NNNN` under a schema with
a closed grade vocabulary. `papers/source/mathematics/catalogue.typ` keys entries by **string** —
`"theorem:weil-support-induction-reduction"` — with fields `key`, `kind`, `title`, `status`, `depends`,
`claim`, `proof`, `boundary`. Measured: `grep -rn "id:" papers/source/mathematics/` returns **0**, so
no entry in the mathematics registry carries a numeric id, and `grep -rn "lemma:\|theorem:\|definition:"
papers/source/holonics/*.typ` returns **1**, a prose mention. **The entire RH theorem corpus is in the
registry that has no ids and no grades**, which is why an earlier sweep looking for a `grade:` field on
these theorems found none — they carry `status:` instead, and the two schemas are disjoint by design.

## 2. The four questions, answered

Yesterday's §8 posed these with question marks. Each now has an answer with its ground.

| question | answer |
|---|---|
| cutoff projection ↔ an **aperture**? | **Yes in the corpus's receiver sense, no under the literal reading.** The instrument ladder says an aperture is *an index condition on a group*; `[−1,1]` is not a subgroup and has no index. It is a support condition on a group coordinate. The registry already calls it an aperture — `prime-power-aperture-incidence.typ` — so the corpus's own usage is the broad one, and the ladder's sentence is itself graded `interpretation`. |
| orthogonal complement ↔ a **retained remainder**? | **No, and the guess landed one level away from the truth.** The Sonin space is the *retained range*; the collapsed population is `S^⊥ = closure(Ran P₁ + Ran P̂₁)`. The retained remainder is not a subspace at all — it is the **trace-level discrepancy `E(f)`** in `Tr(ϑ(f)S) = W_∞(f) + E(f)`, and `E` is exactly what the prolate expansion resolves. |
| scaling action ↔ the `dx ↔ dx/x` **rebase**? | **Same law, different map, and they occur successively.** The logarithm carries multiplicative scaling to additive translation — the homomorphism law `exp(a+b) = exp(a)exp(b)`, `H.0351`. The half-density rebase is the *separate* unitary `(wξ)(v) = v^{1/2}ξ(v)` intertwining the two presentations. **The scaling action is not the rebase; it is the representation transported through it.** |
| prolate ↔ the eigenbasis of a **double aperture**? | **Yes, exactly, and the standing refusal does not bite.** |

### The prolate question, settled, because getting it wrong either way is a defect

`canon/THE_INFORMATION_ENGINE.md` refuses every uncertainty / Gabor / time-bandwidth framing, and
prolate spheroidal functions are the eigenbasis of simultaneous time-and-band limiting. The refusal
does not reach them, on four independent grounds, and the fourth is the decisive one.

**The refusal's own source record states the mechanism approvingly.**
`research/records/2026-08-11_THE_RUNG_REFUSES_BY_NAME_AND_THE_UNRESOLVED_PAIR_IS_THE_REMAINDER.md`:

> *"A bounded-bandwidth window is a finite crystal: it cannot resolve two zeros closer than the
> reciprocal of its aperture."*

That **is** the time-bandwidth statement, in mechanism, in the document that issues the refusal. The
sentence immediately following names what such a receiver must return instead: the pair **collapsed**,
counted, never placed individually — *"the collapsed-pair population of a declared receiver family."*

**So what is refused is a scalar inequality standing in for an exhibited population — and the prolate
eigenbasis IS that population.** It names every direction the double aperture retains and every one it
collapses, with the spectrum ordering them. It is the strictly stronger object the refusal demands,
not the weaker one it bars. The time-bandwidth inequality is a magnitude face **of** it, and by the
phase-object law a magnitude face may not decide what the object is allowed to be.

**And the corpus imported the construction twenty-six days before the refusal was written.**
`papers/source/papers/riemann-receiver-geometry/main.typ` defines

```text
    Son_(S,λ) = { ξ ∈ H_S : ξ = 0 and F_S ξ = 0 on the phase-space hole |x|_S < λ }
```

A vector and its transform both vanishing on one region is simultaneous limiting, exactly; and the
2026-07-20 record already types `λ` as an aperture parameter with a stated non-equivalence.

**The bar that does bind, stated so it is checkable.** Never quote a prolate eigenvalue as a
concentration measure, a time-bandwidth product, or how much energy an aperture keeps. That is the
scalar dial inside one rung and it is refused. Return the eigenbasis and the partition it induces —
which directions the declared family retains, which it collapses, and what separates each collapsed
pair.

## 3. Two claims of yesterday's record are withdrawn

**The Weil route is not a rebase with remainder zero.** Yesterday's record derived that
`Tr(αα†) > 0` gives radical `{0}`, hence nothing identified, hence a rebase. The derivation confuses
two stages. Weil's correspondence ring is

```text
    R(C) = Div(C × C) / { valence-zero correspondences }
```

— **the quotient is taken before positivity is stated.** Trivial radical proves the form is
nondegenerate on the space that already survives that quotient; it says nothing about the quotient's
invertibility. The function-field construction contains **three species, not one**: a quotient of
correspondences with a real collapsed population, an involutive anti-automorphism `†` which is the
rebase-like part, and a positive form. The corrected sentence is better than the withdrawn one:

> **The valence-zero correspondences are the collapsed population, and `Tr(αα†) > 0` is the statement
> that after that quotient nothing further collapses.**

Note also that positivity does not make the readout injective: `Q(a) = Tr(aa†) = Q(−a)`. What is
invertible is `†`.

**Two figures were overstated in conversation and the record repeats one.** `holonic_eta_ratio_atlas`
scans `σ ∈ [2/5, 3/5]`, not the critical strip; and the returned four-point value is an exact rational
**outer interval** `[417695/267264, 420291/264668]` enclosing the cross-ratio, not the cross-ratio.
Both are certified enclosures and were reported as if they were the objects they enclose. The
distinction is the whole discipline of that module.

A third figure survives with a sharpening: `formal_chebyshev_departure` is `ψ(x) − x` as a **formal
expression** over exact integer coefficients and an exact integer product. The owner does not evaluate
the transcendental value, decide its sign, or certify a real bound — and its own field name says
`formal`.

## 4. The corner breaks the group law, and that is the operational test

The corpus distinguishes rebase from compression by remainder. The Sonin construction supplies a
**checkable criterion** for the same distinction, and the criterion is already the corpus's own law.

A **rebase is an intertwiner**: `w T(λ) w⁻¹ = T'(λ)`. The group law survives it — which is exactly
`H.0351`, `exp(a+b) = exp(a)exp(b)`, the whole content of a chart transition.

A **compression is a corner**: `A ↦ S A S` restricted to `Ran S`. Because the Sonin space is not
invariant under the scaling action,

```text
    S ϑ(λ) S · S ϑ(μ) S  ≠  S ϑ(λμ) S
```

**The group law fails, and the failure is computable in one line:**

```text
    S ϑ(λ) S ϑ(μ) S  −  S ϑ(λμ) S
      =  S ϑ(λ) (S − I) ϑ(μ) S
      =  − S ϑ(λ) P_(S⊥) ϑ(μ) S
```

> **The defect is exactly the amplitude that leaves the retained space, passes through the collapsed
> population, and returns.**

So the two species separate by a test that needs no vocabulary the corpus lacks:

| | intertwiner | corner |
|---|---|---|
| group law | preserved | broken |
| remainder | zero | the failure of the group law |
| reversible | yes | no |

**And they occur successively in one construction.** The half-density rebase `w` is reversible and
comes first; the Sonin corner is irreversible and comes second. That ordering is why the `1/2` is
present before any compression happens — §8 below.

## 5. The remainder is a holonomy, and this is the first family in this corpus whose holonomy is not forced to zero

`crates/holonic-structure/src/relating.rs` declares, in `Composes`:

> *"What separates a directly declared transport from one composed through intermediates. Zero defect
> is the exact cocycle; anything else is **holonomy** and is the chain's remainder."*

and its `Remainder` is documented as *"what a transport turned back rather than carried — a retained
fiber, not a magnitude."*

**That is the corner's structure exactly.** The direct transport is `S ϑ(λμ) S`; the composed one is
`S ϑ(λ) S · S ϑ(μ) S`; the defect is `−S ϑ(λ) P_{S⊥} ϑ(μ) S`, which is precisely a retained fiber of
what was turned back rather than carried.

**This matters because every previous holonomy claim in this repository was refuted for the same
reason, twice, eight days apart.** `crates/holonic-engine/src/traversible_chain.rs` carries the
honest boundary in its own source — *"the interface family is abelian and one-parameter, so a closed
chain's holonomy is the identity **by construction**"* — measured rather than assumed, in a test
named for it. The ratio cocycle was refuted the same way: a coboundary, holonomy identically zero.

And the RH corpus states the abelian half itself:
`papers/source/mathematics/theorems/semilocal-sonin-prime-induction.typ` proves
`Δ_p Δ_q = Δ_q Δ_p` because *"translations by `log p` and `log q` commute."*

> **The space-level transport is abelian, so its holonomy is trivial by construction and nothing can
> be found there. `S` does not commute with `ϑ`, so the corner's defect is not forced to zero — and
> that defect is what the archimedean theorem exists to control.**

This is the phase-object law arriving from arithmetic: the corpus measured on 2026-08-14 that flipping
an orientation left every magnitude invariant while twenty-four traversal readers failed. Here the
commuting square is the magnitude face, and the Hermitian form carried across it is the phase.

## 6. The successor obligation is `H.0127`, and `inertia.rs` is its fifth name

`weil-support-induction-reduction.typ` states `P(n) → P(n+1)` as two conditions on the conditioned
block `H_(n+1) = [[H_n, C_n],[C_n*, D_n]]`:

```text
    (RANGE)           Ran(C_n) ⊆ Ran(H_n^(1/2))
    (OPERATOR SHORT)  D_n − Y_n* Y_n ≥ 0          where C_n = H_n^(1/2) Y_n
```

That pair is the block-positivity condition (Albert's condition; Douglas's factorization lemma for
the range half). Its finite form is registered here already, `proved-standard`, as **`H.0127` *Schur
complement and inertia***:

```text
    A > 0  ⟹  [[A, C],[C*, D]] ≥ 0  ⟺  D − C* A⁻¹ C ≥ 0
    and the block matrix has the inertia of A plus the inertia of its Schur complement
```

The second sentence is inertia additivity under elimination (Haynsworth). So:

> **RH, through this reduction, is the statement that widening the support aperture never adds a
> negative direction — at every step, forever.**

In `canon/THE_HOLOBROCHOS_SPINE.md`'s converted language, where a count of signs is a state reading
and the lawful return names the windings: *the elimination never founds a passage that winds past the
hand.*

**And the corpus already knows this organ is duplicated.** `canon/THE_INFORMATION_ENGINE.md` says the
Schur complement is *"one organ under FOUR names… None of the four cites the others"* — `diffusion.rs`,
`H.0219`, `conditioned-effective-tension.typ`, `H.0127`.

**There is a fifth, and it is the one that computes the law.**
`crates/holonic-engine/src/inertia.rs` implements Sylvester's law by symmetric elimination, and its
own header states the step:

> *"take the Schur complement `a'_jk = a_jk − a_ji · a_ik / a_ii` on the survivors and recurse."*

So `inertia_with_schedule` is `H.0127` iterated, exactly over `Rat`, with the hyperbolic-plane branch
that a naive `LDLᵀ` gets wrong — and it cites neither `H.0127` nor any of the other four. Measured:
`grep -n "H.0127\|Haynsworth\|diffusion" crates/holonic-engine/src/inertia.rs` returns nothing.

**And the RH corpus states `inertia.rs`'s governing law as an RH-line theorem.**
`papers/source/mathematics/theorems/weil-signature-transport.typ` — live in this tree, wired into
`catalogue.typ` and depended on by `corollaries/transported-positive-atlas-rh.typ` — is titled
*A genuine negative direction cannot be removed by recharting*:

```text
    T invertible,  W_μ(Tf, Tg) = c · W_λ(f, g)  for one real c > 0
    ⟹  q_μ(Tf) = c · q_λ(f)
    ⟹  T carries the positive, null and negative cones bijectively,
       and the maximal negative-subspace dimensions agree
```

That is Sylvester's law of inertia, stated on the Weil form. Its boundary carries the phase-object law
in the same breath: *"A transformation which flips the sign of the form is not a harmless orientation
change; it changes the positive structure being tested."*

**One distinction must be held, and Sol supplied it against my own reading.** The Schur complement is
**not** the corner. `A_∂∂ − A_∂I A_II⁻¹ A_I∂` retains the eliminated interior — recoverably, with an
inverse residual certificate — so it is a condensation with remainder zero. `S A S|_{Ran S}` deletes
three blocks. Both appear in the RH line and they are different species:

```text
    the Sonin trace          S A S|_(Ran S)          COMPRESSION — collapsed population S⊥
    the successor obligation D − C* A⁻¹ C            CONDENSATION — interior retained, remainder zero
```

`diffusion.rs` implements the second and is not an implementation of the first.

## 7. A positivity that can fail needs a block sourced independently of the other

`CLAUDE.md` §11 holds one of the four parts of its demanded organ open: **the positive form**, noting
that `positive_form`'s `MᵀM` is positive semi-definite for every integer matrix, so its positivity
cannot fail. This thread supplies the structural criterion the section lacked.

| owner | why positivity can or cannot fail |
|---|---|
| `supported_realizers::positive_form` | `xᵀ(MᵀM)x = ‖Mx‖² ≥ 0`. **Cannot fail** — one construction paired against itself. |
| `diffusion.rs`'s Schur response | `D` is `M_∂∂`, a principal block of the *same* positive `M`; capacity and conductance are both refused non-positive at construction. So the split is constant by construction. **Cannot fail.** |
| `matroid_hodge_riemann` | the ample class is **chosen independently** of the matroid's incidence, and classes certified outside the cone are *required* to break Hodge–Riemann and do. **Can fail.** |
| the Weil successor's `D_n` | comes from an independently sourced zeta screw kernel. **Can fail** — which is why it is the obligation. |

> **A form can only fail when its two blocks have independent sources. A form built by pairing a
> construction with itself is a tautology wearing a signature.**

That is `CLAUDE.md` §2's own correction one level down: `Eff ⊋ Amp`, effectivity supplies nothing and
ampleness supplies everything, **because ampleness is a choice and effectivity is not.** §2 and §11
are one statement, and the criterion is now checkable before a form is built rather than after a green
result is reported.

## 8. The `1/2` is one involution on the logarithmic covering, at four sites

Brandon wrote `2^{e^{iπ}}` to provoke the derivation. Here it is, with the species error corrected.

`s ↦ 1 − s̄` is affine anti-holomorphic; `α ↦ q/ᾱ` is anti-holomorphic **inversion**. They are not two
instances of one linear species. **But they are the same involution on the logarithmic covering:**

```text
    s = 1/2 + z ,   α = q^(1/2) e^z      ⟹     both become    z ↦ −z̄
```

with `E_q(s) = q^s` the covering map and `E_q(1 − s̄) = q / conj(E_q(s))`. Conjugacy on the covering,
not global conjugacy on `ℂ^×`.

**And the corpus owns the one-parameter family these are instances of.**
`papers/source/mathematics/lemmas/weighted-mellin-basis-rebase.typ` gives, for the weighted
multiplicative measure `dμ_β(r) = r^β dr/r`, the involution and its locus in general:

```text
    J_β(s) = β − s̄        Fix(J_β) = { Re(s) = β/2 }        s = s' + (β − β')/2
```

with the last equation the affine spectral rebase carrying one seam to another. **So the sites below
are the `β = 1` instances of an owned family, not four coincidences** — and the entry point for the
whole subject is `lemma:mellin-return-seam`, which has `depends: ()` and is a root of the RH tree.

`z ↦ −z̄` is the mirror across the imaginary axis in the centered chart. Four sites, one mirror:

```text
    Re(s) = 1/2        Fix(s ↦ 1 − s̄)                the critical line
    |α| = q^(1/2)      Fix(α ↦ q/ᾱ)                  the function-field placement
    Re(β) = 1/2        Fix(β ↦ 1 − β̄)                unitarity of the dilation, CUT-R0
    p = R^(1/2)        Fix(p ↦ R/p)                  half-overlap, ω_p(p²) = 1/2
```

The fourth is new here and it is elementary: the normalized overlap
`ω_p(R) = (log R − log p)₊ / log R` equals `1/2` exactly when `p = √R`, and `p ↦ R/p` is the divisor
involution whose fixed point that is. On the positive reals conjugation is invisible — which is
`THE_HOLOBROCHOS_SPINE.md`'s own reading that ℝ sees only the two fixed points of conjugation — so the
divisor involution is the same map with its hand deleted.

**And this tightens the corpus's P-versus-NP passage rather than merely decorating it.**
`canon/TABLET_THE_CHART.md` says the transport population below the square-root frontier is *finite and
exhaustible*, which is why finding meets verifying there. The reason is this involution: `p ↦ n/p`
pairs every divisor above `√n` with one below it, so the frontier is the pairing's fixed point and
exhaustion below it is exhaustion of everything.

**The one sentence that governs, and it is `CLAUDE.md` §2's doctrine confirmed by an independent
route:**

> **The fixed locus is the same at every site; what *produces* it differs, and the producer is the
> theorem.** The function-field chart produces it from polarization, Rosati positivity and `π†π = q`.
> The archimedean chart produces it from the Jacobian of `dx ↔ dx/x`. **The Sonin compression does not
> produce the half at all — the half-density exists before the compression.**

Exhibiting a fixed locus is free. That is why *"there is a chart where the real part is `1/2`"* proves
nothing, and it is the same bar `RH.0900` already carries, `proved-derived`: *"Moving an obstruction
to another receiver is useful only when the transition reduces it, supplies a new invariant, or yields
a counterexample."* Yesterday's record derived that bar independently as *name what the transition
deleted*; the registry had it first.

## 9. Brandon's four mechanisms, graded

He proposed: *"The proof likely requires both the mechanisms of rebasing and compression; lightning
integration (integration by reflection) and hyper geometry about fractals and crystals."*

**Rebasing — present everywhere, and provably not the mechanism that closes it.** Sixteen rebases are
registered (`RH.0030`'s Möbius `w = 1 − 1/ρ`, `RH.0040`'s fold `w = z²`, the Mellin half-density chart,
`J_β`'s whole seam family, the function-field route). `RH.0900`'s boundary observes that none reduces
the obstruction. **`weil-signature-transport.typ` upgrades that observation to a theorem:** an
invertible transport that carries the Weil form up to a positive constant carries the negative cone
bijectively, so the maximal negative-subspace dimension is a rebase invariant.

> **No rebase can remove a negative direction, and the corpus proved it.** Rebasing is how the problem
> is *carried* between charts; it is structurally incapable of being how the problem is *closed*. The
> half of Brandon's pair that felt strongest is the half that cannot do the work — and knowing which
> half is which is worth more than the intuition it corrects.

**Compression — present, and it is the corner rather than the tablet's codec.** Connes–Consani's
compression is genuine: three of four blocks deleted, `S^⊥ ≠ 0`. But it carries **no decoder** — there
is no map recovering `x` from `Sx` or `A` from `SAS` — so it fails the compression tablet's own
requirement. *And so does the corpus's flagship organ:* `receiver_exact_compression` has no
arbitrary-source decoder field either. **The tablet demands more than its own best implementation
supplies**, and that is a defect in the tablet's statement, not in the organ.

**Integration by reflection — present exactly once, and it is the reverse of what he expects.**
`H.0308`, `proved-standard`: theta inversion `θ(t) = t^{−1/2}θ(1/t)` by Poisson summation over `ℤ`,
whose `transformations` field names `t^{−1/2}` as *"the analytic source of the centered `s ↦ 1−s`
symmetry."* A periodization over a lattice **is** an image sum. But the lattice is `ℤ` — infinite — so
**the series does not terminate, and the non-termination is the analytic content.** The engine's
termination law says the reflection series terminates exactly when the reflection group is finite;
here the group is crystallographic *and* infinite, and ζ is analytic rather than algebraic precisely
because of it.

**Hypergeometry about fractals and crystals — absent, with a theorem saying why.** `ζ` is
**hypertranscendental**: it satisfies no algebraic differential equation over `ℂ(s)` (Hölder's theorem
for `Γ`, carried to `ζ` through the functional equation). `hypergeometric_closure` decides finiteness
of the return group of a *three-singularity Fuchsian equation*; ζ satisfies no such equation, so the
criterion cannot be posed on it. **This is an outside fact, not deposited in this tree, and it is the
one claim here with no local source.**

**And one suggested join is refused by the bar this thread itself set.** The functional equation and
conjugation generate a **finite** reflection group — `V₄`, two perpendicular mirrors, with the critical
line as one wall — which is genuinely *"the simplest crystallographic reflection group"* the corpus
names. It is real and it is worth having: RH is exactly the statement that **every orbit is
degenerate**, four points collapsing to two, which is *why* `Q(g) = Σ_ρ ĝ(ρ) conj(ĝ(1−ρ̄))` becomes a
sum of squared moduli on the wall. But it is not an image series: the explicit formula sums over
infinitely many orbits, so finiteness of the group bounds each orbit and not the sum. **The
restatement is exact, therefore invertible, therefore free.**

**A further refusal, plainly:** `winding_inertia::lattice_admits_order` takes a *rotation order*. The
zeros are a point set on a line, and in one dimension the crystallographic restriction admits only
orders 1 and 2. The organ cannot be posed on the zero set at all.

## 10. What this means for the Eros cycle

Two joints, one buildable and one refused.

**The deposit is a condensation, and nothing reads whether it cost anything.** `ErosRest`'s
deposit-and-resume eliminates a process's interior and hands the boundary forward; a later process
mounts that boundary and conducts. That is the same operation `diffusion.rs` performs on a complex —
eliminate the interior, keep the boundary, retain the interior recoverably. **What is returned today
is a count** — `72 of 1200 cut positions moved` — where the object is an inertia. The deed that
follows is to return the resumed terrain's split against the primed terrain through `inertia.rs`,
which already computes it exactly by the elimination this whole thread is about. That composition
uses no new organ.

**And the aperture question is the same question at both altitudes.** `founded_mouth` widens a radius
and the grain changes; the support successor widens `I_n` and the form must stay positive. In both
cases the honest reading is *what did the widening admit, and did anything the aperture excluded
matter* — which is `ArrivalResponse`'s shape and the prolate spectrum's shape, at two scales.

**The refused joint, named so it is not proposed again.** The body is float-free by law; routes
through the archimedean place require trace-class operators on `L²(ℝ)`, a real cutoff, prolate
eigenvalues, and an admissible space of Schwartz functions. Measured over `--include='*.rs' crates
soma`: `prolate` 0, `Sonin` 0, `semilocal` 0, `adele` 0, `cutoff projection` 0, `projection operator`
0; the ten `Hilbert` hits are all the Hilbert *transform*. **There is no Hilbert space, no operator
trace, and no projection operator in the body**, and the obvious fix is the one thing the no-float law
forbids. This is a carrier conflict, not a gap, and it should be stated that way rather than entered
on a roadmap.

## 11. Two measurement notes worth carrying

**A case-insensitive substring search for `sonin` returns roughly twice the truth**, because it
matches inside *rea·sonin·g*. The word-boundary count over the live governing tree is 163; the naive
count is 334. Any presence or absence claim about this subject from a substring grep is wrong by
about a factor of two.

**And the convicted false-zero defect fired live during this campaign.** A first sweep returned all
zeros, including `Hilbert = 0` against a true 136, because the shell here is fish and does not
word-split an unquoted path variable — the whole list became one nonexistent path. The rule that a
search establishes an absence only over the scope it actually covered exists for exactly this, and a
false zero from a failed expansion is indistinguishable from a measured zero.

---

## What this record does not do

It claims no movement on RH and no movement on Hodge. It corrects two claims deposited yesterday,
answers four questions posed yesterday, supplies one criterion (§4), one identification (§5), one
structural condition (§7), and one derivation (§8), and names one composition that uses only standing
organs (§10). `blueprint/THE_ROADMAP.md` and `CONSTRUCTION_STATE.md` remain the only construction
authorities.
