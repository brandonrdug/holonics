# A published Lean archive claims the Riemann hypothesis for zeta and every Dirichlet character: its statement is Mathlib's, its text adds no axiom, and its key is multiplicity as a carry count won by a chain of theta lifts

November 20, 2026, 19:22 to 20:01 UTC. On that day Levent Alpöge posted a four-page remark
([remark.pdf](https://alpo.ge/remark.pdf)) stating that he, working with Claude, has a proof of the Riemann
hypothesis and of its extension to every Dirichlet L-function, given as Lean alone. Brandon asked for the claim to
be gauged at once and for its theoretical content, set beside what this tree holds on Dirichlet L-functions. This
record states what was read, what was not, the method as its author tells it, and the method read on the objects.
Nothing was compiled, no Lean of this tree changed, and nothing ran on a learner or on the card. The same day's
fluid claims have [their own record](2026-11-20_UNFORCED_BLOW_UP_IS_CLAIMED_FOR_EULER_WITH_A_WHOLE_LEAN_PROOF_AND_FOR_NAVIER_STOKES_AS_AN_IMPLICATION_FROM_UNPOSTED_DATA_THE_NAVIER_STOKES_PROFILE_IS_A_CYCLE_OF_THE_SCALE_FLOW_CLOSED_BY_A_SCREW_AND_A_DYAD.md).
Refs #410.

Each paragraph carries its grade: `source-inspected` (read in the posted files, as text), `remark` (the author's
own account), `reported` (a public report, not verified here), `tree` (read in this repository), `from training`
(a result of the literature, named) and `agent-inferred` (this record's join).

Two atlas rows enter (§9): `rh.multiplicity-route-no-ground` and `rh.count-sign-through-a-chain`. Four rows take a
note in their scope: `rh.rh-statement`, `rh.self-crossing-needs-a-ground`, `rh.theta-crossing-layers-indefinite`
and `coupling.landmarks-and-moduli`. No grade changes.

## 1. The claim and its scope

`remark`. The remark claims the Riemann hypothesis, says the method "easily extends" to the generalized hypothesis
(Dirichlet L-functions), and expects the extended one (Dedekind zeta functions) with more time. It says the
arguments are formalized "without assumptions" and gives the archive as its first footnote, in fourteen parts. It
gives no prose proof: its author writes that a prose rendering of more than 250,000 pages exists and was not
posted, that he has not yet mastered a large neighbourhood of the argument's mathematics (automorphic forms on
groups of higher rank in particular), and that he expects the argument to be shortened greatly and soon.

## 2. What was read here

`source-inspected`. Every item below is a reading of text. None is a kernel's acceptance.

| Item | Reading |
|---|---|
| The archive | 14 parts, 239,275,554 bytes joined, sha256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`; the gzip stream tests whole |
| Its contents | 175,190 entries, all regular files with no path leaving the root; 175,187 `.lean` files, 17,374,215 lines, 1,030,536,719 bytes |
| Toolchain | `leanprover/lean4:v4.33.1`; Mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`, which is the tag `v4.33.1` of `leanprover-community/mathlib4` |
| The package | a declarative `lakefile.toml`, `maxHeartbeats = 4000000`, a deep thread stack; no build script that runs code |
| Reach | 175,184 of the 175,187 files are in the import closure of `Main.lean`; the longest chain of imports has 203 links |

`source-inspected`. **The statements.** `Main.lean` proves five theorems, and their statements are in a file of
their own that imports Mathlib alone:

```lean
theorem riemannHypothesis : RiemannHypothesis := rhOfAll
theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := rhOfAll
theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := allChi
theorem LFunction_eq_zero_re : DirichletLZerosOnLine := claimAll.2.1
theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine := critAll
```

`RiemannHypothesis` is Mathlib's own proposition, the one this tree aliases in `Zeta/Statement`, and the archive
defines no proposition or function of that name at its root to stand in for it. The four others are stated on
Mathlib's `riemannZeta` and `DirichletCharacter.LFunction`:

```lean
def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2
```

The core statement is `UpperTheory.EveryCharacter`, the first of these two under another name: no zero to the
right of the half for every character of every modulus. The zeta statement is derived from it
(`rhOfAll := Formalism.VW.rh_of_every allChi`): the theorem is proved for the family, and zeta is one member.

`source-inspected`. **The text adds nothing to the kernel's trust.** Over all 175,187 files there is no `sorry`
in any letter case, no `axiom`, no `native_decide`, `ofReduceBool` or `trustCompiler`, no `implemented_by`,
`extern`, `unsafe` or `opaque`, no `debug.` option or `skipKernelTC`, no `#eval`, `initialize`, process or file
call. What the archive does with the elaborator: five small files hold a deny list for library suggestions
(`run_cmd`); one file copies declarations through the checked path (`addDecl`); one tactic assigns a term
without the elaborator's own check, which leaves the check to the kernel; and 37 files set
`allowUnsafeReducibility`, which changes how definitions unfold and nothing about what is accepted.

`source-inspected`. **What the seventeen million lines are.** By directory: 99,187 files of abelian variety
theory (57% of the archive), 18,431 of automorphic arithmetic, 15,147 of automorphic spectrum, 7,051 for the Weil
bound, 6,410 for heights and theta, 5,501 of local-to-global formalism, 4,350 of period integrals, 3,093 of sharp
restriction, 1,922 of Hermitian curvature, 1,398 of étale cohomology and 499 for resolution of singularities,
with smaller parts for p-adic Hodge theory, Wach lattices, Witt vectors of formal groups, Harder–Narasimhan slopes
and Mahler measure. By name, the files that mention the remark's steps: theta lifts 2,480, slopes 2,526, the
seesaw 565, Rallis 232, the Gan–Gross–Prasad periods 248, carries 929, Kummer 1,431, Parseval 911, Behrend 17.
The archive names neither Stepanov nor Vandiver. A count of names shows that the text is about what the remark
says it is about, and no more than that.

## 3. What was not read here, and the guess

No compile was run. A public report gives the cost of one as about 1,150 core hours (2.4 hours on 480 cores, with
no error and no `sorry`; `reported`), against the four cores of the container this was read in, and the request
did not ask for one. So this record holds no kernel's acceptance and no printout of the axioms the five theorems
depend on. Those two readings are what the proof-checker's verdict consists of, and a text scan cannot stand in
for them: it does not see a defect of the kernel or of the elaborator that some file leans on, and it reads
Mathlib's definitions on trust.

`reported`. On the day, the efforts to check the archive were being followed in a thread of the Lean community's
chat, and no named reader had confirmed it. Terence Tao's note of that day describes the proof as Lean-only and
writes that it "appears to use the full power of modern developments on the Langlands program and arithmetic
geometry".

`agent-inferred`. **The guess, as sent before 19:34 UTC, after the text readings and with the one public report
of a clean compile in hand:** the archive compiles on the pinned toolchain and its five theorems depend on
`propext`, `Classical.choice` and `Quot.sound` alone, with probability 0.8. What speaks for it: the statement is the library's own, the text is clean, the
Mathlib commit is an official tag, the closure is the whole archive, and a false claim of this kind fails at the
first compile by a stranger. What the remaining 0.2 holds: a checker defect that some agent-written file found
and leaned on, which is the one failure a clean text cannot rule out. The guess is scored when a compile with its
axiom printout is public.

## 4. The method as its author tells it

`remark`. The remark gives one page of motivation and a list of twenty dated steps. In this record's words:

1. The argument descends from Stepanov's proof of the hypothesis for curves over finite fields, which uses a
   function that vanishes to high order (multiplicity) at the points to be counted. The remark says that
   multiplicity "is hard to find over the integers, corresponding to something like differentiating whole
   numbers".
2. A toy setting held two ideas. The first: on a curve with complex multiplication by a field `K`, at a prime `p`
   inert in `K` the invariant derivation `D` satisfies `D^p ≡ 0`, and the values `D^a θ(0)/Ω^a` are divisible by
   `p` to the power `a/p + a/p² + ⋯ − O(log a)`. The second: a proof of the bounds of Weil and Deligne by a sign
   alone, from the identity `qN = M^k + R` for the sum
   `Σ_(h, x₁, …, x_k) t(x₁)⋯t(x_k)·e_q(h·(x₁x₂ + ⋯ + x_(k−1)x_k))`. Summed over `h` first, it is `q` times a
   count `N` on a quadric, of definite sign; summed the other way, the term `h = 0` is `M^k` and the rest `R` is
   of square-root size after `k` uses of Parseval.
3. Over the integers the same moves are made "natively automorphic": the prime sum is the von Mangoldt sum of
   length `X` in the Guinand–Weil explicit formula, a positivity `W(1_(0,1] + X^η·1_(0,1/X]) ≥ 0` gives no zero
   to the right of `1 − η`, and the positivity is a determinant of periods (of Gan–Gross–Prasad kind, whose
   values 0 and 1 are the interlacing of weights).
4. Multiplicity is won by a chain of theta lifts `U(X₀) → U(X₁) → ⋯ → U(X_m)` between totally definite unitary
   groups, each lift adding one block to the parameter (`π ↦ π ⊞ μ_j[t]`) and one unit of multiplicity, with the
   chain's length `m` near `√X`. The remark gives this as the one line that should astonish: the length Claude
   proposed for the chain was `√X`.
5. The norms and levels of the lifts are computed by the Rallis inner product, the seesaw (the period of the
   iterated lift is a Bessel period that does not depend on the Hecke characters), Chowla–Selberg, Weyl and the
   Siegel mass formula, and the comparison of sizes is Bost's slope inequality.
6. The price of each lift, computed, stops the plain argument at `2/3`. The half needs a "division": an integral
   structure glued across Hecke characters (a greatest common divisor, an extra average), a relative trace
   formula, an Iwasawa tower chosen by analogy with the pigeonhole over `F_(q^n)/F_q`, and, for classes that
   twisting could not remove, a weakened form of Vandiver's conjecture, proved on the way.

## 5. What the tree held on Dirichlet L-functions

`tree`. The tree has worked on these functions from three sides, all of them where the Euler product converges or
on finite models.

| Owner | What it holds |
|---|---|
| `Landmarks/CharacterSites` (atlas `rh.character-site-clocks`) | `L(χ, s)` as the prime cycle machine with each site's clock turned by `χ(p)`; the product over the characters of a modulus |
| `Landmarks/PrimeCycles` (`rh.prime-cycle-machine`) | the Euler product as the determinant of a machine of primitive cycles |
| `Landmarks/IharaAbelianCover`, `IharaCoverChebotarev`, `IharaBassConnection`, `IharaBassMatrix` (`trace.abelian-cover-artin`, `trace.double-cover-artin`, `trace.cover-holonomy-equidistribution`, `trace.ihara-bass-matrix`) | on a finite graph: the zeta function of an abelian cover is the product, over the characters of the cover's group, of the base's L-functions; a cycle's colour is its holonomy and the colours equidistribute |
| `EllipticCurve/HeckeTheta`, `FamilyThetaFE`, `FamilyGauss`, `FamilyCentralRatio`, `FamilyTunnellHeckeIntertwining` and their kin (`bsd.hecke-theta-one`, `bsd.completed-l-entire-fe`, `bsd.family-witness`) | theta functions of Hecke characters, their functional equations, Gauss sums and the central ratio in the congruent number family, up to the normalization before Waldspurger and Tunnell |
| `Zeta/WeilPositivity`, `FiniteWeilCriterion`, `ThetaHankelPositive`, the explicit formula receivers (`rh.finite-weil-criterion`, `rh.theta-hankel-positive`) | Weil's criterion on finite families, a positive Hankel form of theta sections, and the consequences of the hypothesis for truncated receivers |
| `Landmarks/LandmarksAndModuli` (`coupling.landmarks-and-moduli`), `radix.digit-face-calculus` | Kummer's theorem, `v_p(C(n,k))` is the count of carries of `k + (n − k)` in base `p`, and Legendre's, `v_p(N!) = (N − s_p(N))/(p − 1)` |

The tree's own reading of where the half comes from stood in two rows. `key.scaled-form-places-modes`
(`Foundation/FiniteKey`): a reversal and a positive form place every mode at the half. `rh.self-crossing-needs-a-ground`
(an interpretation): for a curve the positive form is the meeting of routes on the surface `C ×_k C`, and the
integers have no ground to cross themselves over, so on that route the construction to make is such a ground.

## 6. The method read on the objects

Everything in this section is `agent-inferred` from four pages and the top files of the archive, with the
classical facts it leans on marked `from training`. It is a reading of a method this record did not follow line by
line, offered as the lens through which the archive would be opened.

**6.1 The route is Stepanov's, and it builds no ground.** `from training`: for a curve over `F_q` there are two
classical derivations of the bound. Weil's crosses the curve with itself and uses the positivity of a pairing on
the surface. Stepanov's (in Bombieri's form) builds a function that vanishes to order `M` at each rational point
and has degree `D`, so that `N·M ≤ D`; with `M` near `√q` this is `N ≤ q + O(√q)`. It needs two facts and no
surface: a zero has an order, and a function has no more zeros than its degree. Over the integers the two facts
have known forms. The order of vanishing at a prime is the exponent of that prime, and the degree bound is the
product formula: a nonzero integer that `p^(m_p)` divides for every `p` has size at least `Π p^(m_p)` (atlas
`trace.place-ledger`, `Geometry/PlaceLedger:theProductOverEveryPlaceIsOne`). This is the method of transcendence
theory, and Bost's slope inequality is its form on lattices with metrics. So the claimed proof answers the
tree's row from the side: `rh.self-crossing-needs-a-ground` named the ground as the construction to make on
Weil's route, and this route makes multiplicity instead. Both routes exist for curves, and the row's reading of
Weil's stands as it was.

**6.2 Multiplicity at a prime is a count of carries.** At a prime inert in `K` the curve's reduction is
supersingular, and there the invariant derivation is nilpotent of order `p` (`from training`: the Hasse invariant
vanishes). So `D^a` is divisible by `p` once for each full block of `p` derivations, once more for each block of
`p²`, and so on: the exponent is `⌊a/p⌋ + ⌊a/p²⌋ + ⋯`, which is Legendre's `v_p(a!) = (a − s_p(a))/(p − 1)`, the
remark's `a/p + a/p² + ⋯ − O(log a)` with the digit sum as the correction. The tree holds this count as
`radix.digit-face-calculus` and its sibling for binomials as `theMultiplicityIsTheCarryCount`: the order to which
a prime divides is the number of carries in that prime's base. The remark's "differentiating whole numbers" has a
standard form too (`from training`): the Fermat quotient `(x − x^p)/p` is a derivation at `p`, and it is the carry
of Witt vector addition. On the objects: the order of vanishing at a place is a winding count, read by the carry
of the place's own radix (`winding.carry-cocycle`, `Foundation/CarryTower`, `radix.section-gauge`). The quantity
in which the multiplicity sits is a value of a derivative of a theta function at a point of complex
multiplication, divided by a power of the period, which is an algebraic integer (`from training`: Damerell).
Multiplicity is found at the primes of one colour, the inert ones (`prime.frobenius-colour-chebotarev`), which
is a reason the argument needs a family of fields and characters and a way to glue them.

**6.3 The positivity is a count read at the end of a chain.** Summing an additive character over a full circle
of phases returns a count: `Σ_h e_q(h·Q) = q·[Q = 0]`. A count has a sign that no phase can cancel, and a sum of
`k`-th powers of roots with a definite sign cannot hide its largest term (`from training`: Landau's theorem on
series with nonnegative coefficients). The quadric of the remark is, in its own word, a path. Read with
consecutive terms sharing a variable, `x₁x₂ + x₂x₃ + ⋯ + x_(k−1)x_k`, it is a chain of `k − 1` pair contacts,
each a Fourier kernel `e(h·x_i·x_(i+1))`, and Parseval is the statement that each crossing keeps the norm. The tree's finite criterion says the same thing in one place, a form is nonnegative on a
family exactly when the reversal fixes every member (`rh.finite-weil-criterion`), and the tree had found that no
single layer of theta crossings is positive (`rh.theta-crossing-layers-indefinite`, a counterexample). The remark
does not contradict that row. Its sign is read once, at the end of a chain of crossings, and the chain's length
is the parameter.

**6.4 Theta lifts are that chain over the integers.** `from training`: in the Weil representation the Fourier
transform is the action of one element of the group, a quarter turn, and a theta kernel is the oscillator that
pairs two groups; a lift carries a form from one to the other and adds one block to its parameter. On a totally
definite group an automorphic form is a function on a finite set of classes with integer values, and a Hecke
operator is an adjacency matrix on that set. So the stage of the argument is a finite complex with an integral
structure, the kind of object the tree's graph zeta modules already work on (`trace.ihara-bass-matrix`,
`trace.abelian-cover-artin`), and "a nonzero integer has size at least one" is available on it. Each lift is one
more crossing and one more unit of multiplicity. The length `√X` is Stepanov's `M` near `√q`: the half is the
square root in both, as the number of crossings a sum of length `X` can pay for.

**6.5 The theorem is about the family.** The Lean proves every character first and zeta as a member, and the
remark's tower and its gluing across Hecke characters say the same of the method. `from training`: for curves the
step from a bound on counts to the size of each root uses every extension `F_(q^n)` and a pigeonhole on the
roots' angles. The tree holds both halves on finite models: the zeta function of a cover is the product of the
base's L-functions over the cover's characters (`trace.abelian-cover-artin`), and Dirichlet's near return is
`rotation.dirichlet-from-ledger` (`Aeon/Production/Recurrence:dirichlet`). Over the rationals the tower of
constant extensions is replaced by a tower of cyclotomic fields, whose zeta functions are products of Dirichlet
L-functions. A single member is not the unit of the argument. The cover is.

**6.6 The key fits, and it is long.** A derivation is a finite word that every reader runs (atlas
`key.derivation-finite-word-every-reader`). This one, if the kernel accepts it, is finite and 17.4 million lines,
more than half of it the theory of abelian varieties built from the library up, and its author expects a short
form. For this repository the short form is the subject: compression of a key that fits is landmark discovery on
the same objects, and §6.1 to §6.5 name the three faces a short form would have to keep, multiplicity as a carry
count at each place, a sign read from a count through a chain of crossings, and the family as the unit.

## 7. What the tree's Lean says once the statement holds

`tree`. The tree's zeta lane proved its equivalences and consequences against Mathlib's `RiemannHypothesis`, the
proposition the archive proves. None of these is discharged in this tree by this record: the archive is not a
dependency, and the tree builds on Lean 4.33.0 where the archive pins 4.33.1. Each becomes a statement about the
zeta function with its hypothesis met once the archive's kernel receipt is read.

| Owner | With the hypothesis met |
|---|---|
| `Zeta/DeBruijnSeal:riemannHypothesis_iff_Λ_DN_eq`, `riemannHypothesis_iff_Λ_DN_le` | the de Bruijn–Newman constant is zero (the equivalence is proved with no hypothesis): the heat clock's reading with no horizon |
| `Zeta/CriticalChart:riemannHypothesis_iff_Λstd_eq` | the same in the standard chart |
| `Zeta/PairPopulation:pairPopulation_eq_empty_of_RH` | no pair of zeros off the line |
| `Zeta/ZeroComb:offLineCross_eq_zero_of_RH` | the comb's off-line crossing term vanishes |
| `Zeta/ThresholdRefinement:squareClosed_iff_RH` | the square closes |
| `Zeta/Seam:theComposedStatementIsTheStandardOne` | every mode sits on the self-conjugate seam |
| `Zeta/CarryTick:riemannHypothesis_iff_carry_eq_orderTicks` | at every admissible height the carry of the seam's phase equals the count of zeros with their orders |
| `Zeta/WeilPositivity:truncatedZeroReceiver_nonneg_of_RH`, `riemannXi_zero_re_of_RH` | truncated zero receivers are nonnegative |
| `Mathematics/PrimeSimplex:riemannHypothesis_iff_reducedEuler_growth` | under the classical Mertens equivalence, which that module names as a port and does not prove, the reduced Euler characteristic of the prime simplex grows as the half allows |

## 8. What transfers and what does not

`agent-inferred`. Nothing here enters the machine, and no part is ordered. The discipline's apparatus (higher rank
groups, periods, the tower) stays in the discipline. Two statements carry over as readings to test on the
objects, both offered to whoever next works the zeta lane or the carry:

- A sign is read at the end of a chain of crossings and never at one layer. The tree's counterexample row and the
  remark agree on this, and the tree's finite Weil criterion is the one-crossing case.
- An order of vanishing at a place is that place's carry count. The engine's carry circles and the formal lane's
  `Foundation/CarryTower` are where this would be read, as a count of carries along a chain and not as a size.

A construction this record leaves to be made: a Lean statement of Stepanov's count on a finite model in the
tree's objects (a function on a finite complex, its orders at sites, the degree bound as the product over
places), beside `rh.finite-weil-criterion`, so that the two routes to the half stand side by side on one model.

## 9. Atlas

Two rows enter, both graded `interpretation` with this record as owner:

- `rh.multiplicity-route-no-ground`: the count `N·M ≤ D` and its form over the integers, as the second route to
  the half.
- `rh.count-sign-through-a-chain`: `Σ_h e_q(h·Q) = q·[Q = 0]` and `qN = M^k + R` on the path quadric.

Four rows take a note in their scope and keep their grades: `rh.rh-statement` (the archive, its hash and what was
read; the grade stays until a kernel receipt is read by this repository), `rh.self-crossing-needs-a-ground` (the
second route), `rh.theta-crossing-layers-indefinite` (a chain's sign beside a layer's) and
`coupling.landmarks-and-moduli` (the carry count as the remark's multiplicity).

## 10. Receipts

Read in a cloud container (4 cores, 15 GB), with no build. The archive was fetched from the fourteen addresses of
the remark's footnote, joined and hashed (`sha256sum`), tested (`gzip -t`), listed (`tar -tvf`) and unpacked into
an empty directory. The scan was `rg` over every `.lean` file for the tokens of §2. The import closure was
computed by a script that follows `import` lines from `Main.lean`. The Mathlib commit was resolved with
`git ls-remote` against the library's repository, where it is the target of `refs/tags/v4.33.1`. Times: the fetch
and the readings took about eleven minutes of wall time in all; no run was projected because none was launched.

## 11. The last funnel of the archive (added 20:10 UTC, on a second reader's pointer)

`source-inspected`. Codex read the archive's source the same day and named, in the repository's mailbox, the
place where the analytic content has to enter the final deduction. The files it points to were then read in this
record's copy of the archive, and they read as it says. Three statements make the funnel.

```lean
-- Development/AutomorphicArithmetic/DedekindLFunctions/CharFamily.lean
def Gm (F : CharFamily) (y : ℝ) : ℝ := ∑ i, F.a i * (Gchi (F.χ i) y).re

-- Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ZeroFreeOfRpowWindow.lean
theorem zeroFree_of_rpow_window (F : CharFamily) {θ δ C : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ)
    (h : ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)), Gm F y ≤ C * y ^ θ) :
    ZeroFree F θ

-- Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean
theorem UpperTheory.Comparison₂.core_gm :
    ∀ (Λ : Level) (eD eL K cHH eK C eps : ℝ), 0 < eps → ∃ x1 : ℝ, ∀ x ≥ x1, ∀ (φ : Frame) (H : HostAx φ) (TT : Finset φ.A),
      EAtH Λ H.toHostRaw TT x eps C → CoreAtH H.toHostRaw TT eD eL K cHH eK eps x →
        Λ.Gm x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 7) * eps)
```

`zeroFreeOn_of_chainTied` (`…/PrimitiveCosets/LevelGmLeOnFamilyScales.lean`) joins them: a set of primitive
characters is free of zeros to the right once each character has a level that keeps it, a window scale
`la > 1`, and `ChebyshevInequalityAtWindowScale` for the family `FamP` under the predicate `ChainTied`.

So the deduction ends on a step of Landau's kind. The aggregate `Gm` is a sum over a family of characters with
positive weights `F.a i`; `PoleData` (`LandauZeroFreeCriterion.lean`) asks of its Laplace transform a pole at
each zero of each character with a nonzero residue, real and positive at a real zero; and a bound from one side
on whole windows `[Y, Y^(1+δ)]`, arbitrarily late, puts no zero to the right of `θ`. On the logarithmic clock
the window is `[U, (1+δ)·U]` (`WindowHypU`): its length is a fixed share of how late it starts, and nothing is
asked between windows. What the construction of §4 has to supply is therefore narrow and exact: for each small
`eps`, with the losses `eD` and `eL` fixed before `eps`, whole windows on which the chain's constants hold
at every point. Where `ChebyshevInequalityAtWindowScale` is proved for every primitive character was not traced
here; the names `ExWin` and `ChainWin` in
`Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/TopWin.lean` are where that trace
starts. `reported`: the second reader's note says the residue at an interior zero is a positive weighted sum of
the zeros' multiplicities over the characters and their conjugates, so that no zero of one character cancels
another's; the field `pole` of `PoleData` is consistent with it, and the proof of that field was not read.

The same file states the criterion on a tower:

```lean
def GmLevel (j : ℕ) (y : ℝ) : ℝ :=
  G y + (3 * (2 : ℝ) ^ j + 1)⁻¹ *
    ∑ ξ ∈ Finset.univ.filter (fun ξ : DirichletCharacter ℂ (2 ^ (j + 2)) => ξ.Even ∧ ξ ≠ 1), (Gchi ξ y).re

def ZeroFreeAbove (j : ℕ) (θ : ℝ) : Prop :=
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 ∧
    ∀ ξ : DirichletCharacter ℂ (2 ^ (j + 2)), ξ.Even → ξ ≠ 1 → DirichletCharacter.LFunction ξ s ≠ 0
```

The even characters of conductor dividing `2^(j+2)` are the characters of the `j`-th layer of the cyclotomic
tower over the prime two, whose zeta function is the product of their L-functions (from training). So level
`j` of the criterion is one layer of that tower read as one aggregate, which is the remark's "Iwasawa tower via
analogy to pigeonhole on F_(q^n)/F_q" in the archive's own definitions: the layers of a tower over the integers
stand where the extensions of the constant field stand over a curve (§6.1).

`agent-inferred`. Three things follow for §3 and §6. The guess of §3 stands at 0.8: the pointer names where a
reader of the mathematics should look first, and a kernel's acceptance of `Main.lean` with its axioms printed
covers this funnel with the rest. The sign of §6.3 has its place: it is the one side of Landau's step, and the
positive weights are what let one bound on a family reach each of its members (§6.5). And the amplification of
§6.4 has two towers in it, the chain of theta lifts that wins multiplicity and the tower of layers on which the
count is read.

The same note makes a point on this tree's own heat clock (`Coupling/MeanFieldHeatClock`,
`thermal.mean-field-heat-clock`): every finite model there is periodic in its argument, a pointwise limit of
periodic functions with one period keeps the period, and the function `Ξ` of the zeta lane decays and has no
period. So a passage from the finite locks to `Ξ` through Hurwitz's theorem needs a chart that breaks the
period, and convergence that is uniform on compact sets to `Ξ` itself. The chart of that kind the classical
subject uses is the scaling of the central limit, `z ↦ z/√N`, under which `cos(z/√N)^N → e^(−z²/2)` (from
training). The row `thermal.mean-field-heat-clock` claims no such passage, and none is added here.
