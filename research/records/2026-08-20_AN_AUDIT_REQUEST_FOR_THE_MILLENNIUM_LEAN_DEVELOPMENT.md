# An audit request for the Millennium Lean development

**Date:** 2026-08-20
**Kind:** a handoff, written to be read by someone who was not in the session that produced the
work. It is a request, not a claim, and it schedules nothing.
[`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Position under the active plan.** Exterior mathematical material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
**No engine source was touched at any point.** `crates/` and `soma/{body,membrane,abi,surface,mount,life,tools}`
carry only the other session's work and were never staged or modified.

**Cold-audit addendum (2026-08-21):** this handoff preserves the historical session's map, but the
following grades are now narrowed: `AlgebraicGNS` is an algebraic radical quotient (the middle
step used by GNS), not the full GNS construction; Difference-Galois/modulus is conditional on a
declared difference/Picard–Vessiot setting and a no-coboundary proof; the softmax/phase and
three-locus joins are interpretations over finite recurrence identities; and the `Lines.lean`
count is only a count of its own declared rows. The corrected source carries the current wording.

---

## 0. What this is, and why it exists

On 2026-08-20 the Lean development at `soma/formal/elementary-holonics/ElementaryHolonics/Millennium/`
went from **16 files / 3,516 lines / 175 theorems** to **26 files / 5,535 lines / 285 theorems**, in
one session, reviewed only by the session that wrote it and by adversarial sub-agents it dispatched
itself. Zero `sorry`; every theorem audited by `#print axioms` and free of `sorryAx`; the library
builds at 3,313 jobs.

**The whole directory is untracked.** `git status` shows `?? …/Millennium/`, so nothing here is
committed and none of it has been read by anyone outside that session.

The request is for a cold reading. The specific question is in section 6 and it is not "is the Lean
correct" — the kernel already answers that. It is whether the connective tissue is real.

### Reproducing

```sh
cd soma/formal/elementary-holonics
lake build                                    # 3,313 jobs; mathlib v4.27.0 is prebuilt
lake env lean ElementaryHolonics/Millennium/<file>.lean       # check one file, ~10-30s
# audit: a scratch file importing the module, then `#print axioms <name>` per theorem
cd /home/b/Workspaces/holonics
bash tools/gates.sh named-paths line-citations claim-index document-law     # 4 passed, 0 failed
```

Never run `lake build` concurrently with another agent's `lake env lean`; the build takes a
workspace lock. Concurrent single-file checks are safe and were used throughout.

---

## 1. The map

Sixteen files predate today and carry the chain/passage/receiver vocabulary: `Gluing`, `Turn`,
`Hand`, `Seam`, `Swing`, `Chronology`, `Navigation`, `Paying`, `Coupling`, `Instance`, `Triangle`,
`Theta`, `Receiver`, `Rebase`, `FormRebase`, `Lines`. **Ten are new today**, and they are one
argument in four movements.

### Movement one — a positivity on a subspace, and the involution that selects it

| file | thm | what it establishes |
|---|---|---|
| `ReflectedPositivity` | 25 | folding an involution into a symmetric form's first slot makes the round trip a standing `CompressedPositivity`; `N_Θ` **is** `Paying.radical` by `Iff.rfl`; the fixed and anti-fixed faces have vanishing cross-pairing; and a **witness pair** — one carrier, one form, one half, two legal reflections, one paying and one not |
| `AlgebraicGNS` | 10 | an algebraic radical quotient over an arbitrary linearly ordered commutative ring: induced form by double `Submodule.liftQ`, proved symmetric, non-negative, **anisotropic**, `Nondegenerate`; a non-increasing endomorphism descends by `mapQ` and still contracts; no state, representation, or completion |
| `LorentzianPerp` | 12 | **the reverse of Cauchy–Schwarz against a class of positive self-pairing IS non-positivity on that class's perp** — an equivalence, with the Hodge-index and archimedean instances |
| `Shadows` | 20 | conjugacy w.r.t. a quadric is the perp relation, so the swing is the primitive; the self-pairing kills the splitting quotient; the sign and factor obstructions are independent, both directions witnessed; placement needs the form to see the ray |

### Movement two — the modulus of a path

| file | thm | what it establishes |
|---|---|---|
| `LandmarksAndModuli` | 16 | the least depth admitting a modulus is the multiplicative order of two; Kummer restated from mathlib (multiplicity = carry count); Bertrand imported; the doubling map's two fixed-point branches giving `2^p ∓ 1`; those as `#𝔾ₘ` and `#P¹` over `F_{2^p}`; **and six named open `Prop`s** — Legendre, Cramér, Baker–Harman–Pintz, RH's gap bound, Mertens, Lucas |
| `Towers` | 3 | both gap scales as logarithms of a tower; the convergent determinant alternates; consecutive convergents differ by `(−1)ⁿ/(kₙkₙ₊₁)`; `Λ₂ = μ∗log²` with `Σ_{d\|n}Λ₂(d) = log²n` |
| `Farey` | 6 | the convergent recurrence **is** a matrix product in `GL₂(ℤ)`, and the alternating sign is multiplicativity of the determinant along the word; Stern–Brocot generators unimodular; Farey neighbours = unimodular pairs |

### Movement three — the recurrence that carries the exponent

| file | thm | what it establishes |
|---|---|---|
| `TraceSequence` | 9 | `t_{p+2} = a t_{p+1} − q t_p`; the root has `normSq q` iff `a² ≤ 4q`; `t_p = 2 Re(αᵖ)`; **the level-one bound gives every level**; genus zero is the same recurrence at `q = 1`; over `F₂` the bound is forced by integrality; past the bound a real root escapes the circle |
| `PartitionFunction` | 5 | `Z_N = Tr(Tᴺ)` obeys that same recurrence with `a = tr T`, `q = det T`, by Cayley–Hamilton; the critical point is where the two roots merge |

### Movement four — one involution, three loci

| file | thm | what it establishes |
|---|---|---|
| `OneInvolution` | 4 | `Re s = ½` is `Fix(s ↦ 1−s̄)`; `\|α\| = √q` is `Fix(α ↦ q/ᾱ)`; `q^s·q^{1−s} = q` so the two are one chart apart; and a palindromic real quadratic with non-real roots has both zeros on the unit circle — the Lee–Yang mechanism at degree two |

---

## 2. The audit queue, in order, with what would refute each

**(a) The two files intended for upstream.** `AlgebraicGNS` and `LorentzianPerp` are the ones worth
contributing, and both rest on a measured absence in mathlib. If either absence is wrong, everything
downstream of it is a rebuild rather than a contribution.

```sh
grep -rli "reflection.positiv|osterwalder|wightman|schwinger function" \
  soma/formal/elementary-holonics/.lake/packages/mathlib/Mathlib --include='*.lean'   # → 0 of 7,516
grep -rn "PreGNS|gnsStarAlgHom|gnsNonUnitalStarAlgHom" <mathlib>/Mathlib   # → analytic C*-setting only
grep -rl "Lorentzian" <mathlib>/Mathlib --include='*.lean'                 # → 0 files
```

*Refuted by:* a mathlib declaration under another name that already states the algebraic
GNS quotient over an ordered ring, or the reverse Cauchy–Schwarz equivalence.

**(b) The `Lines.lean` index.** An adversarial reviewer this session found **four of its eight rows
mis-stated against the classical statements** and the rows were never repaired. The index also
proves `theOpenLines.length = 6 ∧ theOpenLinesWithNoObstructionGroup.length = 3` by `decide` — a
count over its own declarations, which carries nothing about mathematics.
*Refuted by:* naming which rows' `realizer` or `obstructionGroupKnown` field is wrong and why.
The cold audit corrected the Poincare, function-field, Hodge, and P-versus-NP paraphrases and
marked the Riemann row's obstruction-group flag false. The resulting `decide` theorem counts six
open rows and four no-group flags; that remains an index self-count, not evidence about a named
problem.

**(c) The witnesses, for vacuity.** Every structure here carries a concrete instance because the
session's own bar demanded one, but the bar this project actually applies is sharper: **which
declared input, if varied, would move the result?** Two witnesses were already killed this session
for failing it. The ones still standing and worth re-testing: `ReflectedPositivity`'s bond/twist
pair, `Shadows`'s two lattices for obstruction independence, and `TraceSequence`'s five `F₂` traces.
*Refuted by:* a variation of one declared input that leaves the reported reading unchanged.

**(d) The six open `Prop`s in `LandmarksAndModuli`.** Each is a real statement rather than `True`
wearing a name — that failure mode was caught three times in earlier waves — but they are
transcriptions of classical statements and a transcription can be wrong.
*Refuted by:* a `Prop` whose Lean statement is not the theorem or conjecture its docstring names.

---

## 3. What was withdrawn, so it is checked rather than re-litigated

Five reversals happened today. Each is recorded at its site; a cold reader should verify the
**current** statement rather than the history.

1. **"A form that pays on a perp" as the open target** — withdrawn. It was built in July at the
   archimedean base, `B₂ = −P₀N₂P₀` on `ξ₀^⊥`, citing Connes–Consani arXiv 2006.13771.
2. **The exchange field as a containment** `Θ(H⁺) ≤ H⁻` — too weak; admits data with no reflection
   content.
3. **The exchange field as `Disjoint positiveHalf (positiveHalf.map Θ)`** — too strong; it refuses
   the canonical Osterwalder–Schrader **site** reflection, which fixes the time-zero site.
   Kernel-checked. **The classical abstract datum carries no exchange condition at all.**
4. **"Positivity, not anisotropy, is what works" in the placement statement** — refuted by the file's
   own proof; the operative hypothesis is a nonzero self-pairing on the ray.
5. **The theorem count** — a prior record said 195 where the measurement gives 175. Corrected in
   place.

---

## 4. The measured absences everything rests on

These were measured with a stated command and scope. **A path or name search never establishes a
content absence**, and each of these is a name search over a stated scope. They are the load-bearing
ones and the cheapest thing to falsify.

| claim | command | scope | result |
|---|---|---|---|
| reflection positivity not in mathlib | `grep -rli "reflection.positiv\|osterwalder\|wightman"` | 7,516 mathlib files | 0 |
| no `Lorentzian`, no reverse Cauchy–Schwarz | `grep -rl "Lorentzian"` | same | 0 |
| GNS only analytic in mathlib | `grep -rn "PreGNS\|gnsStarAlgHom"` | same | C\*-setting only |
| Lucas' congruence not in mathlib | inspection of `Mathlib/NumberTheory/` | same | absent |
| `Lee-Yang` in the corpus | `grep -rlniE "Lee.Yang"` | `research canon papers crates soma` | 1 file |
| `Knauf`, `Kuzmin` | same | same | 0 |
| `Legendre conjecture`, `Cramér` | same | same | 0 |
| `ray class` | same | same | 1 file |

---

## 5. Two live defects found in the engine tree and only reported

Both were verified at the source by the session that found them. Neither was touched, because that
tree belongs to the other session.

- **`crates/holonic-engine/src/sheaf_diffusion.rs`** builds `δδᵀ + δᵀδ` in `hodge_laplacian` with
  **bare transposes**, and `harmonic_dimension` is the kernel dimension of that operator, asserted
  as a result in its tests. `crates/holonic-engine/src/exact_linear.rs` refuses exactly this by
  name: *"a bare transpose is this object only when both metrics are the identity, which is an
  orthonormal Euclidean declaration nobody made."*
- **`crates/holonic-engine/src/analytic_field.rs`**'s `ExactAnalyticAdvectionLaw` calls `Ω` "the
  symplectic form" and cites `H.0281`/`H.0282` as `proved-standard`, while constructing
  `ExactRatMatrix::from_diagonal(capacities)` with every capacity refused unless positive — that is
  **symmetric positive-definite**, so the group is `O(Ω)` and not `Sp`. What it builds is more
  useful than what it claims: an exactly certified isometry of a declared positive-definite form,
  refused by name when the certificate fails.

---

## 6. The question this deposit is actually asking

Twenty-six files went from *a form on a subspace* to *three circle theorems are one involution* in a
day. Every step compiles and every step is recorded. **What cannot be judged from inside the session
that wrote it is whether the connective tissue is real.**

Specifically:

- Is `positivity on a declared subspace, with the selector varying by line` a thesis, or is it a
  shape loose enough to fit anything? The session found a **measured negative** — the involution
  selector and the Lefschetz selector provably do not share a selection rule — which is evidence for
  the former, but one negative is thin.
- Are the four movements one argument, or four adjacent exercises that share vocabulary? The claimed
  joints are: the round trip is a `CompressedPositivity` (proved), the reverse inequality is the
  index statement (proved), and the trace recurrence is the partition function for a specified finite
  transfer-matrix family (proved). The three fixed-locus equations are proved on their declared
  carriers, while their being “one construction” is `interpretation`. **Every exact joint is a
  theorem; the question is whether the theorems are the joints that matter.**
- The strongest single result, if there is one, and the weakest that is still being carried.

A cold reading answers those. Another adversarial wave from the same session does not — eleven of
eleven results were overturned by such waves today, which improved every one of them and told us
nothing about the shape.

---

## 7. Boundaries

**No named conjecture is proved or approached here.** Legendre, Cramér, Riemann, Hodge,
Birch–Swinnerton-Dyer and the Yang–Mills mass gap appear only as named `Prop`s carrying their status,
or as the classical statements against which a linear-algebra core is compared. The Weil conjectures
are theorems and are not reproved; what is proved about them is a recurrence's own dichotomy.
Lee–Yang is proved only at degree two. Every classical input — that an ample class supplies a
positive form through the Rosati involution, that the archimedean estimate of Connes–Consani holds —
is imported, cited, and not proved.

The arithmetic measurements (`M(x)`, `L(x)`, prime gaps, the prime-power surplus) run to `2²⁴` and
bear on nothing but the aperture. One of them reproduces a **refuted** conjecture: `L(x) < 0` at
every aperture reachable, which is Pólya's, whose first counterexample sits at `906,150,257`. That
is recorded as an aperture control rather than as evidence.

The trees written today are `soma/formal/`, `research/records/`, `research/equation-atlas/` and the
regenerated `THE_CLAIM_INDEX.md`. The equation atlas stands at **198 equations, 180 relations**, no
dangling endpoints, manifest digests current. Four cheap gates pass.
