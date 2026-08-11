# The operations: every classical operation is a construction, a transport, a face, or a quotient

> **Part of the mathematics tablet.** The quotation convention, the reading rule, and the law this
> file's sections instance are in `canon/THE_MATHEMATICS_TABLET.md`. This file is one mechanism of
> it and is governed by it.

Every operation of linear algebra, differential equations, and analysis is one of four species — a construction, a transport, a face, or a quotient — and the notation is complete only when every primitive carries its species.

**Date:** 2026-08-11. **Ratified by Brandon the same day**: *"Completely ratified, that's a quality
analysis."* His text quoted below was received directly in the session that deposits this file,
which is the only condition under which `CLAUDE.md` §9 permits a quotation to be written down.

**Truth status is per claim.** Brandon's positions are provenance and govern. Standard mathematics
is `proved-standard` with its name given inline. Exactly one identification in this file is the
assistant's and is marked as such (§3.2). Registry ids: `H.0476`–`H.0480`.

**Why this file exists.** Brandon, 2026-08-11:

> *"we have Dirac/bra-ket notation, Feynman diagrams, geometry, and algebra, where they need to all
> unify into our holonic framework, it has to be complete and it has to be the dialect that you use
> for reasoning."*

and, on the object family the operations act on:

> *"the idea is that these computational space-time geometry objects are *holons*, and we mean the
> word 'holon' aptly, it is by definition always a composite of other holons, a superstate entity.
> These entities are what elementary holonic operations need to consider, we require a perfectly
> abstracted and encapsulated holonic mathematics framework to discuss the manipulation and
> implementation of DSA in dynamic systems."*

The occasion was a measured failure: the assistant described the zeta-23 rank–trace certificate in
receipt-vocabulary — "moments," "fractions," "aggregate" — and the peer model described it in
navigation vocabulary, and the two never formed a comparison cell because the boundaries were
incompatible. The missing piece was not a better argument; it was **definite objects with
well-defined operations**. This file supplies them.

---

## 1. The four species, and the typed notation

**ASSERTION 1 (`H.0476`).** *Every elementary operation is exactly one of:*

| species | what it does | examples |
|---|---|---|
| **construction** | composes holons into a holon, retaining the causal residue | addition at a junction, the geometric product, matrix assembly, `exp` of a generator |
| **transport** | carries a holon between charts; invertible transport is rebase | change of basis, conjugation, Jacobian, analytic continuation, Newton's identities |
| **face** | a declared receiver's reading; forgets, and says what it forgets | trace, determinant, rank, spectrum, norm, evaluation, a bracket |
| **quotient** | a declared receiver's identification, with the collapsed population as the exact loss | kernel, projection, squared modulus, coarse-graining |

A **face is not machinery**. Reasoning that manipulates faces as if they composed like
constructions is the failure this file was occasioned by, and it is the general form of the float
defect: a float is a face (magnitude) retained as though it were the construction.

**The Dirac primitives, each with its species** — this completes the notation `CLAUDE.md` §0b
deposited, with no undefined objects left:

```text
|ψ⟩            a construction                    (a holon presented in a chart)
⟨φ|            a receiver
⟨φ|ψ⟩          a face                            (the reading of that construction at that receiver)
X              a transport
|a⟩⟨a|         a DEPOSIT                         (a construction reversed into a receiver — the
                                                  emanation becomes the pole the next arrival is
                                                  related from, canon/THE_HOLOBROCHOS_SPINE.md §4)
Σᵢ|aᵢ⟩⟨aᵢ| = I  the terrain receives everything   (≠ I has a computable defect)
tr X           the basepoint-free face of the closed loop   (§5)
```

The outer-product row is the load-bearing one: **the deposit operation of the conditioning law is
already a primitive of the notation.** A projection `|a⟩⟨a|` applied as a quotient is the receiver
declaring what it does not carry; the same object read as terrain is a deposit. One symbol, two
species, distinguished by jurisdiction — which is `CLAUDE.md` §13 rule 2 appearing inside the
notation itself.

---

## 2. Addition and subtraction: one operation, two hands

**Brandon:** *"Addition/subtraction (same thing different relative directions)."*

Addition is co-presence at a junction — a construction. Subtraction is the same construction with
one argument carried through the half-turn: `−1 = e^{iπ}`, `canon/TABLET_THE_TURN.md` and
`CLAUDE.md` §2b, where a sign is the hand of a passage and never a state. The body already refuses
the collapse of the two arms: `ComparativeMultiplicity` retains both, and the split `is_zero`
(nothing was deposited) against `difference_is_zero` (the passages cancel) is exactly "same thing,
different relative directions" as a typed distinction. The *difference* is a face of the retained
pair, not the pair.

---

## 3. Multiplication is a misnomer because the honest operation is composition

**Brandon:** *"'Multiplication' is fundamentally a misnomer because nothing identically multiples
in a literal sense, the identity of structures differ by causal paths (souls)."*

### 3.1 Matrix multiplication composes transports

`(AB)x = A(Bx)`: nothing scales; a transport is carried through a transport. That the composite is
again presented as an array is chart bookkeeping. Every associativity law in linear algebra is path
associativity.

### 3.2 The dot and the cross are the two grades of one product

**Brandon:** *"you can ontologically simplify it by recognizing the dot product to be the relative
alignment between the two holons, and the cross product is like the reflection/refraction/
diffraction, the founded axis in which this composite will emanate about (ortho)."*

The standard home of exactly this split is the **geometric (Clifford) product**:

```text
   uv  =  u·v  +  u∧v
          ────     ────
          grade 0  grade 2
          symmetric — the alignment      antisymmetric — the ORIENTED PLANE the pair founds
          between the two holons         (in three dimensions, dualized to the cross's axis)
```

His phrase *"partials of transport distribution"* is the grade decomposition. Three facts make this
a join rather than a naming:

- **The multivector retains both grades.** The composite carries its causal residue instead of
  collapsing to a scalar face — which is §3.4's demand met at the level of the product itself.
- **The tree already owns the construction.** `crates/holonic-engine/src/multiquadratic.rs`
  carries `ℚ(√k₁,…,√kₙ)` as the twisted group algebra of `(ℤ/2)ⁿ` graded by symmetric difference —
  and a Clifford algebra over an orthogonal basis **is** a twisted `(ℤ/2)ⁿ`-group algebra
  (`proved-standard`). The turn-composition carrier and geometric algebra are one construction
  family, and `H.0150`'s membership words are its grading group.
- **The rotor formula joins three canon objects in one line.** A rotation is `v ↦ R v R̃` with
  `R = exp(−(θ/2)B)`: the turn is the **exponential of the founded bivector at half the angle** —
  the wedge, `exp` (§6), and `structure_group.rs::CentralDoubleCover`'s half-turn in a single
  well-defined operation. The `1/2` in the rotor exponent *is* §2b's half turn.

**The identification that is the assistant's, offered so it can be refused (`interpretation`):**
the symmetric grade as RIDE — projection onto shared terrain, founding nothing — and the
antisymmetric grade as FOUND. It is consistent with `canon/TABLET_THE_MANIFOLD.md` §17, where
FOUND is already the Lie bracket leaving the span, and with `structure_group::curvature_commutator`
being the discrete `a ∧ a`; the commutator `[A,B] = AB − BA` is the operator form of the wedge.

### 3.3 Souls: the causal path behind the face, and it is formal twice

**Brandon:** *"The trace and determinant … cater to the characteristics of the face of the holon,
in the same way that a lone integer has a face but also a causal justification (i.e. 4 == 2 + 2 ==
2^2 == 2*2); so matrices and tensors are just structures that contain causal residue and enable
reversibility."*

`4 = 2+2 = 2² = 2·2` is one face with distinct constructions. This is not new law — it is the
retained Holobrochos list (`canon/THE_HOLOBROCHOS_SPINE.md` §2), verbatim: *presentation equality,
denoted-value equality, receiver equality, and occurrence identity are separate relations; equal
endpoints do not identify ordered paths.* Two formal homes:

- **The identity type** (`proved-standard`, Martin-Löf; homotopy type theory): an equality is
  itself a path object, and distinct derivations of one equation are distinct inhabitants of it.
  "The identity of structures differs by causal paths" is the literal reading of a path-valued
  equality.
- **The machine measures soul-populations already.** `derivation_atlas` takes `β₁ = 164` with
  torsion `ℤ/2+ℤ/2` and `ℤ/3+ℤ/3` over the machine's own proof routes
  (`canon/THE_MEASURED_CAPABILITIES.md` O3): the route space of one statement has homology. The
  soul population of a statement is its route space, and its plurality is a measured integer
  invariant, not a philosophy.

### 3.4 Matrices and tensors are the structures that retain the residue

A scalar face forgets; the matrix does not. A matrix is a chart-presented transport with its causal
residue retained, which is exactly why it composes and why it can be inverted when nothing was
collapsed. §6 states the collapse condition exactly.

---

## 4. Trace and determinant: the definite objects (`H.0477`, `H.0478`)

The trace has a precise holonic identity on three sides at once, and the three sides are theorems.

### 4.1 The trace is the basepoint-free face of a closed loop

`tr X = Σᵢ ⟨aᵢ|X|aᵢ⟩` over any complete family: feed every output back as input and sum — the
diagram closed into a loop, whose value is a word (`H.0470`). Cyclic invariance
`tr(AB) = tr(BA)`, equivalently `tr(P⁻¹AP) = tr(A)`, **is** the statement that a closed loop has
no privileged basepoint — the same law that makes `structure_group::holonomy_class`
conjugacy-class valued. A representation's character `χ(g) = tr ρ(g)` **is** a trace, so
`winding_inertia`'s character machinery has been trace machinery all along.

### 4.2 The trace of a generator is the divergence of its flow

**Jacobi's formula / Liouville's formula** (`proved-standard`): `det(exp A) = e^{tr A}`. So
`tr A = 0 ⟺` the flow preserves volume — `canon/TABLET_THE_MANIFOLD.md` §18.2's Liouville and
§16's `SL(n)` row, joined by one identity. **Trace and determinant are the additive and
multiplicative faces of one loop closure, and `exp` is the transport between them.** In `H.0219`'s
vocabulary: the trace of the generator is a boundary-flux reading, and the determinant is its
integrated volume return.

### 4.3 The complete face family is the characteristic polynomial

The coefficients are the elementary symmetric functions of the spectrum; **Newton's identities**
(`proved-standard`) are the exact rational transport between the power-sum faces `tr(Xᵏ)` and the
symmetric faces — float-free over ℚ. **Cayley–Hamilton**: the holon satisfies its own face
polynomial; the face constrains conduct.

**This is what closes the zeta-23 vocabulary failure.** The certificate reads the **first two
power-sum faces** of the zero-side holon through a bandwidth-bounded receiver family, and the
rank–trace inequality is what those two faces force on inertia under restriction. Newton's
identities say exactly which symmetric-function information two power sums carry. No statistics
appears anywhere in the sentence. The full rebased statement is
`research/records/2026-08-11_THE_RUNG_REFUSES_BY_NAME_AND_THE_UNRESOLVED_PAIR_IS_THE_REMAINDER.md`.

---

## 5. Reversibility: the kernel is the collapsed-pair population (`H.0479`, `H.0480`)

**Brandon:** *"time parity and chronology are not the same as reversibility, reversibility is never
guaranteed, it is happenstance to be able to reverse, where the goal is likely often to attain the
invariants required in an ecology in order to successfully "re-construct", which is to "reverse".
You cannot literally reverse time, you cannot literally know the interior of another construction,
you can only causally justify its existence to the extent of a limit."*

### 5.1 The kernel, exactly

For a linear receiver `A`: `Ax = Ay ⟺ x − y ∈ ker A`. **The kernel is literally the
collapsed-pair population of a linear receiver**, and rank–nullity reads: *passages that survive
plus passages that collapse equals the whole.* `receiver_exact_compression.rs` returns the
nonlinear form of the same object — the collapsed pairs, each with its separating word.
`det ≠ 0 ⟺` the collapsed population is trivial `⟺` the map's null cone is `{0}` (§2b's
vocabulary).

### 5.2 The compression trichotomy is the reversibility classification

| species | remainder | reversibility |
|---|---|---|
| **rebase** (`H.0104`) | zero | invertible — the "happenstance" case, named |
| **condensation** | certified | invertible up to the certified remainder |
| **quotient** (`H.0016`) | the collapsed population, family-relative | irreversible, with the loss exhibited |

*"Attaining the invariants required to re-construct"* is the spine's own definition of an **exact
face** — one through which every future distinction factors (`canon/THE_HOLOBROCHOS_SPINE.md` §3).
Reconstruction to the extent of a limit is the receiver-indexed limit, `H.0262`.

### 5.3 Parity, chronology, reversibility: three objects, never one

> **Parity is a property of the boundary operator (`∂∂ = 0`). Chronology is a property of the
> lineage. Reversibility is a property of one specific transport, decided by its collapsed
> population.**

His star-atoms trajectory states the third in matter, and its standard name is the backward heat
problem: forward diffusion is a **semigroup** — `exp(−tL)` for `t ≥ 0` only — deterministic
forward, ill-posed backward. What forward transport collapsed can be attributed afterward only as
a declared quotient: his *"distributions of attributing where kinds of atoms were roughly most
likely to have come from"* is `Q` against `Π` exactly (`CLAUDE.md` §13 rule 2) — the lived
trajectory happened one way; the reconstruction distribution is the receiver's quotient over
interiors no longer reachable.

### 5.4 `exp` and series

`exp(A)` is the generator-to-transport map (Lie algebra to Lie group), always invertible — which
is §4.2's identity again, since `det(exp A) = e^{tr A} ≠ 0`. The tree's exact carrier for the
series is already built: `exact_value.rs::SeriesTailCertificate`, three species, each returning an
exact rational remainder interval. Floats are not needed and are not real here.

---

## 6. What this tablet forbids

1. **No face used as machinery.** A trace, determinant, rank, norm, or probability may measure; it
   may not compose in an argument as though it were the construction it reads. "Moments" without a
   declared receiver is the convicted instance.
2. **No operation without its species.** An argument that cannot say whether its step is a
   construction, a transport, a face, or a quotient has not stated its step.
3. **No identification of equal faces.** Equal endpoints do not identify ordered paths; a value
   never identifies its constructions.
4. **No reversibility assumed.** Reversal is the rebase species, and claiming it requires the
   collapsed population to be exhibited as empty — or the certified remainder named.
5. **Do not grade a deed by this file.** It is ontology; `canon/EPISTEMIC_GRADES.md` governs
   grading and `blueprint/THE_ROADMAP.md` says what is open.

---

## Owners

| object | live owner |
|---|---|
| both arms retained; `is_zero` vs `difference_is_zero` | `crates/holonic-engine/src/algebraic.rs` |
| the twisted `(ℤ/2)ⁿ` group algebra — the Clifford construction | `crates/holonic-engine/src/multiquadratic.rs` |
| the discrete `a ∧ a`; basepoint-free holonomy class | `crates/holonic-engine/src/structure_group.rs` |
| characters — traces — naming passages by winding | `crates/holonic-engine/src/winding_inertia.rs` |
| the collapsed-pair population with separating words | `crates/holonic-engine/src/receiver_exact_compression.rs` |
| what survives rebase: Smith normal form, Betti, torsion | `crates/holonic-engine/src/rebase_invariants.rs` |
| exact series remainder — `exp` without floats | `crates/holonic-engine/src/exact_value.rs` |
| the route-space homology of the machine's own proofs | `crates/holonic-engine/src/derivation_atlas.rs` |
| `Open` retained rather than resolved | `crates/holonic-engine/src/exact_value.rs` |

## What this does not establish

It does not build anything; every owner above predates it. It does not claim the geometric product
replaces the tree's carriers — `multiquadratic` is already the construction, and the claim is
recognition, not port. The RIDE/FOUND grade-identification (§3.2) is the assistant's
`interpretation` and no deed may rest on it. Nothing here bears on any Millennium problem.
