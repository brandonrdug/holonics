# The reflection is the first slot of the form

**Date:** 2026-08-20
**Kind:** the return of a two-wave parallel orchestration, authorized by Brandon this session. It
schedules nothing. [`blueprint/THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Position under the active plan.** Exterior mathematical material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../archive/plans/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
The active deed is W1 and it is Sol's. **No engine source was touched.**
**Truth status:** `proved-derived` for every theorem, kernel-checked and audited free of `sorryAx`.

**Cold-audit scope note (2026-08-21):** the Lean results below are exact statements about the
declared finite carriers, forms, involutions, and subspaces. Their reflection-positivity and GNS
connections are `interpretation` or `conditional` unless the corresponding analytic, algebraic,
and receiver hypotheses are explicitly included. This record does not formalize the full
Osterwalder–Schrader theory or the full C*-algebraic GNS construction.

---

## 0. The result

**The reflection is not an organ beside the form. It is the form's first slot.**

```lean
def toCompressedPositivity : CompressedPositivity V where
  form      := R.roundTripForm        -- form ∘ reflection
  form_symm := R.theRoundTripIsSymmetric
  remainder := R.half
  definite  := fun v hv => by rw [one_mul]; exact R.roundTrip_nonneg v hv
```

Fold an involution into a symmetric form's first slot and the round trip **is** a standing
`CompressedPositivity` on this declared carrier. Its null population is `Paying.radical` — `Iff.rfl`,
not a new object — and the descent criterion and the faithful-quotient trichotomy apply by
projection with nothing reproved. The identification with the classical
`H₊ / Θ / N_Θ / H₊÷N_Θ` is an `interpretation` until the missing analytic/algebraic structure and
receiver maps are supplied.

Owner: `soma/formal/elementary-holonics/ElementaryHolonics/Millennium/ReflectedPositivity.lean`,
373 lines, **18 theorems, 3 named open `Prop`s, zero `sorry`**, every theorem audited by
`#print axioms` and depending only on `propext`, `Classical.choice`, `Quot.sound`.

### And the positivity can fail

This project's standing positivity organ computes `xᵀ(MᵀM)x = ‖Mx‖² ≥ 0`, which cannot fail for
any integer matrix and any probe, so by the project's own tautology rule it carries no evidence.
`§11` of the operating contract names **a form whose positivity CAN fail** as the one part of its
four-part demand that has stood open.

```lean
theorem theTwoReflectionsDisagreeOnTheSameVector :
    0 ≤ gram (bond (0, 0, 1, 0)) ((0, 0, 1, 0) : Sites)
      ∧ gram (shear (0, 0, 1, 0)) ((0, 0, 1, 0) : Sites) < 0
```

One carrier — four sites in a row. One form — `2I + A(P₄)`, proved positive definite as an exact
sum of five squares. One declared half — the two right-hand sites. **Two reflections, both
involutive, both self-adjoint for that form, hence both legal inputs to the structure.** The bond
reflection's round trip on the half is `u·u`; the shear reflection's is `−2u² − 2uv + v²`, which is
`−2` at the inner site.

> **Every declared input is held fixed except the reflection, and the sign moves with it.** That is
> the control the project's own rule demands: a check whose material cannot vary the property under
> test wears a passing result while carrying nothing.

### The other three that survived

- **The two candidate compatibilities are one condition.** For an involution, being a form-isometry
  and being self-adjoint for the form are the same statement, and that statement is exactly what
  makes the round trip symmetric. Both directions are the same substitution, and both spend the
  involutivity.
- **The two faces cannot see each other.** For a form-isometric involution, a fixed vector and an
  anti-fixed vector pair to zero: `⟨a,b⟩ = ⟨θa,θb⟩ = ⟨a,−b⟩ = −⟨a,b⟩`, so `2⟨a,b⟩ = 0`, so
  `⟨a,b⟩ = 0` — **two is invertible in the values though not in the carrier**, which is why the
  conclusion is available where the halved eigenprojectors are not. `soma/life/examples/eros_formula_ecology.rs`
  checks exactly this numerically, as an exactly-zero cross term. Nothing proved it until now.
- **The declared half is a declaration.** The set on which a form is non-negative is not in general
  a subgroup, so which half is retained is never read off the form.

---

## 1. How it was reached, and the method finding is the larger one

Two workflows, fifteen agents, both authorized by Brandon this session after a review of fifteen
serial loop iterations.

**Wave one — five readers over disjoint source regions, read-only.** July arithmetic/spectral ·
July reflection/transport · the engine's exact owners · the 279-row driver catalog · the registries
and papers. It returned **29 corrections**, and its finding refuted the wave it was preparing:

> **Every structural piece of the target was already built, exactly, driven, in owners that had
> never met.** The involution with both eigenprojectors and its fixed point retained
> (`causal_reflection.rs`, 2,122 lines); the involution as a typed group object with `z² = e`
> checked (`structure_group::CentralDoubleCover`); the θ-isometric pairing with metric-orthogonal
> faces (`eros_formula_ecology.rs`); a positivity that can fail on a declared perp (`matroid_chow.rs`,
> whose driver prints `P^k = ω^⊥`); restriction to a subspace returning both splits and the kernel as
> exact vectors (`inertia::pullback_inertia_bound`); the radical proved to be the relation ideal
> (`the_matroid_names_its_windings.rs`); a transfer operator with an exact spectrum
> (`the_plaquette_carries_a_group_element.rs`); and the quotient-by-the-radical step registered
> `proved-standard` at `H.0126`.

The eight-angle derivation wave that had been planned would have rebuilt six standing owners. **The
sweep cost fourteen minutes and prevented the explorative failure the corpus convicts by name.**

**Wave two — five Lean angles, each pipelined straight into an adversarial reviewer.** Verdicts:
**five WEAKENED, zero CONFIRMED, zero REFUTED.** The reviewers wrote and kernel-checked their own
counter-witnesses. What they killed:

| angle | what the reviewer refuted |
|---|---|
| the involution field | the isometry is a **declaration**, not forced by `form_symm` — counter-witness built: a hyperbolic form with an anti-isometric involution and a nonzero reflected pairing |
| the involution field | "the half splits as null ⊕ seam" is an **authored partition** — refuted on the same carrier, same form, same involution by a different reflection-positive half |
| the failing witness | the headline failure was **illegal** (violating the structure's own self-adjointness field) and the legal one was **content-free** |
| the contraction | the involution is **inert** — the reviewer deleted `theta_involutive`, re-ran every proof verbatim and instantiated with a non-involutive `θ = 0`, at exit 0 |
| the round-trip cone | **both** open `Prop`s are false, refuted on the file's own carriers |

**And the adversarial reviewer that killed the failing witness named the witness that works** —
`s ↦ (a, b, −b−c−d, d)`, round trip `−2u² − 2uv + v²`. Its self-adjointness was verified by hand
(`GΘ` symmetric) and then in the kernel. **The headline deliverable of this session came out of a
refutation, not out of a derivation.**

> Fifteen serial iterations produced five self-corrections, every one in the author's own framing.
> Two parallel waves produced twenty-nine corrections plus five refutations, most of them in canon
> and in code the author did not write.

---

## 2. Corrections this work forces

Each verified at the source by the orchestrator, not accepted from an agent.

**`ExactTraversalQuadraticBalance` cannot be handed an antisymmetric form.**
`crates/holonic-engine/src/causal_traversal.rs`, `fn validate_quadratic_balance`, refuses with
`MalformedQuadraticBalance` whenever `input_form.transpose() != input_form`. A nonzero antisymmetric
`J` has `Jᵀ = −J ≠ J`. `CLAUDE.md` records this as a path awaiting a driver — *"an antisymmetric form
it has never been handed"* — and it is **a gate, not an accident**. Moreover
`crates/holonic-engine/src/traversible_chain.rs` states that at `2×2` the antisymmetric identity
holds for every matrix, carrying only the determinant, *"which is why that one would carry no
information."* **The owed item is mis-specified, not merely open.**

**A form that pays on a perp is not the open item.** It was built in July.
`research/records/2026-07-23_THE_ARCHIMEDEAN_REMAINDER_HAS_AN_AMPLITUDE_THE_PRIME_ENTERS_THROUGH_APERTURE_OVERLAP.md`
constructs `B₂ = −P₀N₂P₀` restricted to `ξ₀^⊥`, proves it non-negative, takes its positive square
root, and closes `W_∞(g*g^♯) − Σ_∞(g) = ‖A₂ξ_g‖²`, citing Connes–Consani arXiv 2006.13771 Thm 4.7 /
Prop 5.5 / Lemma 6.10 / Thm 6.11. **The headline open item of
[`2026-08-20_THE_FIFTEEN_ITERATIONS_CONSOLIDATED.md`](2026-08-20_THE_FIFTEEN_ITERATIONS_CONSOLIDATED.md)
is withdrawn.** What that region names as open is three narrower things, all one step past the perp
compression, the sharpest being an arithmetic construction whose contractivity follows from its
construction rather than from an assumed completed Weil sign.

**The theorem count in that record was wrong.** It said 195 over `Millennium/`. Measured
2026-08-20 by `grep -cE '^[[:space:]]*theorem ' ElementaryHolonics/Millennium/*.lean` summed:
**175 before this file, 193 after.** The file and line figures in that record (16 files, 3,516 lines)
are correct and reconcile exactly with the present 17 files and 3,889 lines. Only the theorem count
was inflated, by 20.

**Two live defects in `crates/`, reported and not touched** — that tree is Sol's:

- `sheaf_diffusion::hodge_laplacian` builds `δδᵀ + δᵀδ` with **bare transposes**, and
  `harmonic_dimension` is the kernel dimension of that operator, read as a result in tests.
  `exact_linear.rs` refuses exactly this by name: *"a bare transpose is this object only when both
  metrics are the identity, which is an orthonormal Euclidean declaration nobody made."*
- `analytic_field::ExactAnalyticAdvectionLaw` calls `Ω` the symplectic form and cites `H.0281`/
  `H.0282` as `proved-standard`, while constructing `ExactRatMatrix::from_diagonal(capacities)`
  with every capacity refused unless positive — **symmetric positive-definite, so the group is
  `O(Ω)`, not `Sp`.** What the code builds is more useful to this line than what it claims: an
  exactly certified isometry of a declared positive-definite form, refused by name when the
  certificate fails.

**Three documentation figures have drifted.** `canon/THE_MILLENNIUM_FRAME.md` gives
`lattice_gauge.rs` as about 1,255 lines; `wc -l` returns **1,695**. `canon/THE_DRIVER_ATLAS.md`'s
mechanism index was written at the 203-driver census and the ledger now carries **279**, so its
rebuild rule under-covers by 76 drivers — and the two drivers holding the involution half are both
in that gap, both with an empty `subject` column. And the five documents naming reflection
positivity are **one measurement repeated four times**: all descend from a single 2026-08-11
sentence and none re-took its scope; one of the five does not mention it at all (that hit is a
different Schrader paper, on Kirchhoff's rule for quantum wires), and a sixth document does.

---

## 3. What is owed, with falsifiers

| owed | falsifier |
|---|---|
| **The half exchange.** The classical involution carries the negative half to the positive one; nothing here requires the reflection to move the half, and a datum whose reflection fixes its half satisfies every field while carrying no reflection content. | A field relating the reflection to the half under which the section-6 witness pair no longer separates — which would show the witness is about the structure rather than about the reflection. |
| **The antilinear anti-morphism.** Over an `AddCommGroup` with rational values there is no conjugation and no multiplication, so this is the real-symmetric special case. | A statement of the round-trip condition over a carrier with a conjugation under which the symmetry theorem fails. |
| **`H₊/N_Θ` is characterised, not constructed.** The criterion names which quotiented population leaves no null classes; no quotient group, induced form, or descended transport is built here. One of the wave-two files constructs it for a semi-definite form with no reflection and was not merged. | A constructed quotient carrying an induced form that is not faithful where the criterion says it is. |
| **The composition as a driver.** Hand `causal_reflection`'s eigenprojector to `inertia::pullback_inertia_bound` and read the split `(p, z, n)`: positivity iff `n = 0`, the radical the `z` block. Every piece verified standing. **It lives in `crates/holonic-engine/examples/`, which is Sol's tree, and awaits Brandon's ruling.** | A composed driver whose returned split disagrees with the Lean criterion on the same data. |
| The three July items past the perp compression, and the mis-specified antisymmetric-form item above. | As recorded in their sources. |

---

## 4. Boundaries

Eighteen theorems, all audited by `#print axioms`; none depends on `sorryAx`; the library builds at
3,294 jobs. The witness is one carrier of four sites with one form and one declared half, and it
establishes that admissibility of a reflection is not determined by the carrier or the form — it
says nothing about how reflections vary in general. **No named conjecture is formalized, nothing
here is a claim about the Yang–Mills problem, and the phrase "mass gap" appears nowhere as a
claim** — `crates/holonic-engine/examples/the_plaquette_carries_a_group_element.rs` sets that bar
in its own module doc and it is adopted unchanged: no such language without a lattice-spacing,
volume and correlation-length scaling family, and nothing in this repository carries one. The trees
written are `soma/formal/` and `research/`; `crates/` and the engine's `soma/` subtrees carry only
Sol's W1 work and were neither staged nor modified.

---

## 5. Corrections from the third wave, 2026-08-20

Twelve more agents — six deriving, six refuting — against the same file. **Six WEAKENED, zero
CONFIRMED.** Two findings correct this record and one corrects the standing library.

### The load-bearing lemma is mathlib's, and more general than ours

`Paying.theNullConeIsTheRadical` — carried in
[`2026-08-20_THE_FIFTEEN_ITERATIONS_CONSOLIDATED.md`](2026-08-20_THE_FIFTEEN_ITERATIONS_CONSOLIDATED.md)
as the loop's best result, the one that "paid three times" — **is a special case of a mathlib
lemma.** Verified at the source 2026-08-20:

```text
Mathlib/LinearAlgebra/SesquilinearForm/Basic.lean:906
  variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup M] [Module R M]
  :908  apply_mul_apply_le_of_forall_zero_le   -- "The Cauchy-Schwarz inequality for positive
                                               --  semidefinite forms"
  :947  apply_apply_same_eq_zero_iff (hs : ∀ x, 0 ≤ B x x) (hB : B.IsSymm) :
          B x x = 0 ↔ x ∈ LinearMap.ker B
```

The hand proof is not wrong and is not currently redundant, because `CompressedPositivity.form` is
a `V →+ V →+ ℚ` on an abelian group rather than a `BilinForm R M` on an `R`-module, so mathlib's
lemma does not apply to it. **It becomes redundant exactly on restating the development over
`LinearMap.BilinForm`, which is the argument for restating it.** `Paying.lean` now carries this
measurement in the theorem's own docstring. A hand proof of a mathlib lemma is a cost, not an asset.

### The witness in §0 is a witness about the weaker structure

The classical involution carries the negative half to the positive one. **The shear does not.**
`shear (0,0,u,v) = (0,0,−u−v,v)` lands back in the declared half — it *preserves* the half rather
than exchanging it, so it is not an admissible reflection for the classical statement at all, and
under the exchange requirement the bond/shear pair stops separating. This is exactly what this
file's own `TheHalfExchangeIsNotRequired` named as its falsifier, and the falsifier fired.

**The separation survives under a different second reflection**, verified by hand and then in the
kernel:

```lean
def twist (s : Sites) : Sites := (s.2.2.1 + s.2.2.2, -s.2.2.1, -s.2.1, s.1 + s.2.1)

theorem theExchangingReflectionsDisagree :
    leftPair (bond (0,0,1,0)) ∧ leftPair (twist (0,0,1,0))
      ∧ 0 ≤ gram (bond (0,0,1,0)) ((0,0,1,0) : Sites)
      ∧ gram (twist (0,0,1,0)) ((0,0,1,0) : Sites) < 0
```

Both involutive, both self-adjoint for the same form — `GΘ` symmetric, checked by hand and proved
— and **both carrying the declared half into the complementary one**, so both are admissible for
the classical statement. The bond's round trip is `u²` and the twist's is `−u²`. The §0 pair is
retained, marked as belonging to the weaker structure, because the difference between the two pairs
is the content of the correction.

### What the third wave establishes that is not yet merged

Each survived adversarial review and is recorded here so it is not rederived:

- **The port is faithful.** Reflection positivity is `LinearMap.BilinForm.IsPosSemidef` of
  `(form.compLeft Θ).restrict positiveHalf`; `N_Θ` is `LinearMap.ker` of that restriction and equals
  `orthogonal ⊤` by mathlib's `orthogonal_top_eq_ker`.
- **An algebraic radical quotient is constructible over an ordered ring** — an induced `BilinForm`
  on `M ⧸ ker B` by a double `Submodule.liftQ`, proved symmetric, non-negative, **anisotropic** and
  `Nondegenerate`, with a genuinely nonzero null space, plus descent of a non-increasing
  endomorphism through `Submodule.mapQ`. **`Conditional/interpretation`:** this is the middle
  quotient step commonly used in a GNS construction, not the full Gelfand–Naimark–Segal theorem:
  there is no C*-algebra/state/adjoint representation or completion here. Mathlib's GNS is in the
  analytic C*-setting (`PositiveLinearMap.PreGNS`, `.GNS`, `gnsStarAlgHom`); the measured absence is
  only of this algebraic-over-an-ordered-ring analogue, not of GNS mathematics in general.
- **Withdrawn correction:** the proposed exchange field must not be stated as either containment or
  disjointness in the abstract OS datum. `Θ(H⁺) ≤ H⁻` is too weak, while
  `Disjoint positiveHalf (positiveHalf.map reflection)` is too strong and rejects the canonical
  site reflection because it fixes the time-zero site. Exchange/disjoint-region structure belongs
  to a concrete net, not to the abstract finite `CompressedPositivity` record.
- **The round-trip case and the Lefschetz case do not share a selection rule.** A datum whose
  operator is an involution and which satisfies the operator-selection clause has the **zero**
  subspace — so the common generalization asked for does not exist by that route. That is a
  negative answer, and it is the honest one.
- **Positivity is supplied by the positive form and never by the invariance.** `!![2,1;1,1]`
  preserves the indefinite form `!![-2,1;1,2]` exactly — an honest isometry, determinant one —
  while stretching a ray by `(3+√5)/2 > 2`, and that eigenray is isotropic; no positive-definite
  form whatsoever is preserved by that transport.
- **The fixed-aperture refusal transcribes.** If a transport has no entry joining two window
  coordinates then `P (1 − aT)ᴴ B (1 − aT) P = B` for every coefficient `a` and every `B` on the
  window — a faithful finite shadow of the July record's own refusal, and genuinely negative.

**Measured after the corrections:** `Millennium/` is 17 files, 3,966 lines, **200 theorems**, zero
`sorry`; the library builds at 3,294 jobs; the seven new theorems audit clean and three of them
depend on no axioms at all.

---

## 6. Wave four: the algebraic GNS quotient lands, and the exchange field is refuted

Twelve more agents against four Millennium lines. **Six WEAKENED, zero CONFIRMED**, and the
reviewers again wrote their own kernel-checked counter-witnesses.

### What landed

`ElementaryHolonics/Millennium/AlgebraicGNS.lean`, 204 lines, **10 theorems**, `sorryAx`-free,
narrow mathlib imports so it can be read on its own. The **algebraic middle quotient used by a
Gelfand–Naimark–Segal construction** is stated **over an arbitrary linearly ordered commutative
ring for an arbitrary positive semidefinite bilinear form**, with no analysis and no completion:

- two lifts build the induced form on `N ⧸ LinearMap.ker B`, the second consuming `B.IsSymm`;
- that form is proved symmetric, non-negative, **anisotropic**, positive definite and
  `Nondegenerate`;
- an endomorphism that does not increase the self-pairing is proved to carry the null space into
  itself and to descend by `Submodule.mapQ`, still contracting — the transfer operator's step, with
  the order doing the work;
- **no Cauchy–Schwarz is proved here.** Every use is an application of mathlib's
  `apply_apply_same_eq_zero_iff`.

**Measured 2026-08-20** by `grep -rn "PreGNS\|gnsStarAlgHom\|gnsNonUnitalStarAlgHom"` over `Mathlib`
at `v4.27.0`, re-run independently by the reviewer: mathlib carries GNS only in the analytic
C\*-setting on `PreInnerProductSpace.Core`, and a sweep for a quotient-by-the-radical across
`BilinearForm/`, `QuadraticForm/` and `SesquilinearForm/` returns nothing. That measures those names
over that scope and is not a claim that no related content exists under another name.

### The exchange field is refuted, and it was mine

The wave-three reviewer found `Θ(H⁺) ≤ H⁻` too weak and proposed
`Disjoint positiveHalf (positiveHalf.map reflection)`. **That is too strong, and it refuses the
canonical Osterwalder–Schrader site reflection — the construction being ported.** Verified
independently at the orchestrator, kernel-checked:

```lean
-- three sites, time t = site − 1, so site 1 IS the reflection plane
-- osForm = 4·M⁻¹ = adj M for M = 2I + A(P₃);  flip reverses the row;  half = {x₀ = 0}
theorem osPaysOnTheHalf (b c : ℚ) : osForm (flip (0,b,c)) (0,b,c) = (2*b - c)^2
theorem theTimeZeroSiteIsFixedAndNotNull :
    half ((0,1,0)) ∧ flip ((0,1,0)) = (0,1,0) ∧ osForm (flip (0,1,0)) (0,1,0) = 4
```

Positivity **holds** — the round trip on the half is a perfect square, which is Gaussian OS
positivity in its textbook form, against the **covariance** rather than the action. And the
reflection **fixes** the time-zero site, which lies in the half, is nonzero, and is not null. The
same obstruction hits every standard setting containing the vacuum: `Θ1 = 1`, so disjointness would
delete it.

> **A containment is too weak and a disjointness is too strong. The classical abstract datum —
> `(H, Θ a unitary involution, H⁺ a subspace, ⟨Θf, f⟩ ≥ 0 on H⁺)` — carries no exchange condition
> at all.** The exchange is a property of the concrete net, where `A₊` and `A₋` are algebras of
> disjoint regions; it is not a field of the abstract structure. The finite structure covers the
> declared *link* reflection, which is what the bond witness is. It does not, by itself, formalize
> the full site-reflection setting of Osterwalder–Schrader; that is the scope boundary, not a
> refusal of the canonical theory.

The strategy sentence proposing the disjointness is withdrawn. `ReflectedPositivity.lean` never
carried the field, so nothing in the library changes; what changes is the target of the port.

### The other four returns, recorded so they are not rederived

- **The negative index is a genuine graded obstruction.** `negativeIndex B H = 0` iff positivity
  holds on the half, with the general theory merge-ready. Two defects: `sSup` over an unbounded
  `Set ℕ` returns `0` in mathlib, so the definition reports *positivity holds* in the
  maximally-failing infinite-dimensional case and needs a boundedness hypothesis; and the
  claimed group-valued upgrade is the span-of-the-witness-set trick and was refuted.
- **The round-trip cone is mathlib's star-ordered cone** — `rfl` — and the null set of a
  round-trip-positive functional **is** closed under left multiplication, which is the GNS left
  ideal the development could not previously reach. But the file dropped the half, so it proves
  whole-algebra state positivity rather than reflection positivity.
- **The tolerance quotient's strongest content is a negative**: a translation-invariant tolerance
  relation is the coset relation of a subgroup, so it is algebraic after all — and the reviewer
  proved all three of that file's declared-open `Prop`s, from the file's own statements.
  `Submodule.span ℚ (convexHull ℚ s) = Submodule.span ℚ s` is four lines, absent from mathlib, and
  upstreamable.
- **BSD's join holds**: the torsion is contained in the radical of a positive semidefinite pairing,
  freely and in a generality the file understated. Its main defect is that the pairing was declared
  with values in the scalar ring, which excludes the Néron–Tate pairing outright; mathlib's
  `LinearMap.BilinMap R M N` is the type it needed.
- **Weil placement**: the operative hypothesis is the one-point null cone, not positivity. The
  correction I stated in strategy — *positivity, not anisotropy, is what works* — is refuted by the
  file's own proof, and the earlier anisotropy reading was closer to right than its refutation was.
  What stands is the control: `!![2,1;1,1]` preserves the indefinite `!![-2,1;1,2]` exactly while
  stretching a ray past 2, and preserves no positive-definite form at all.

**Measured after the merge:** `Millennium/` is **18 files, 4,173 lines, 210 theorems**, zero
`sorry`; the library builds at 3,296 jobs. The atlas stands at **170 equations, 158 relations**, no
dangling endpoints, manifest digests current.
