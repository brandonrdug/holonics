# The Millennium finish lines are uneven: three are usable, three require receiver construction, and every source obligation has an exact terminal term

**Date:** 2026-08-29  
**Kind:** graded Lean finish-line and source-obligation audit. This record schedules no Rust construction,
does not alter `CONSTRUCTION_STATE.md`, and does not claim a new solution of an official
Millennium problem.  
**Scope:** Riemann hypothesis, Birch--Swinnerton--Dyer, Hodge, Navier--Stokes,
Yang--Mills existence and mass gap, P versus NP, and the solved Poincare theorem as a
local-to-global regression.

## 1. Lean finish-line readiness and the source-specific obligations

[definition] The first question for each worktrack is whether a candidate proof has a faithful,
closed Lean proposition to inhabit. The present answers are not uniform:

| Grade | Worktrack | Lean finish line | Readiness | Immediate consequence |
|---|---|---|---|---|
| definition | Riemann hypothesis | `RH.Statement`, definitionally Mathlib's `RiemannHypothesis` | faithful and closed | keep the terminal Prop; construct the missing global Weil-to-placement theorem |
| counterexample; source-audit | BSD | `UniversalBSD.TheBirchSwinnertonDyerRankConjecture` and `UniversalBSDLedger.TheBirchSwinnertonDyerConjecture` | malformed: raw possibly singular models, vacuous analytic-data quantification, arbitrary ledgers, and assumed `Sha` finiteness | repair the receiver before treating any family theorem as a route to universal BSD |
| open | Hodge | `TheHodgeConjectureIn Official`, `TheHodgeConjecture Canonical`, and `SourceDeterminedHodgeTheory.Conclusion` | faithful one-instance equation, but no parameter-free official family/theory | construct the actual classical source theory and export its closed `Conclusion` before claiming a universal finish line |
| definition | Navier--Stokes | `TheOfficialNavierStokesProblem := A or B or C or D` | faithful and closed | the periodic development still has no maximal-lifespan/globalization adapter into `StatementB` |
| counterexample; source-audit | Yang--Mills | `TheYangMillsExistenceAndMassGap (P : Problem)` | only a schema; arbitrary or empty `P` can make it vacuous or unrelated to gauge theory | construct a source-determined official `Problem` before a gap proof can reach the prize target |
| definition | P versus NP | `PEqualsNP` and `PNotEqualsNP` over fixed binary TM2 encodings | usable selected-model finish line, with robustness and closure infrastructure incomplete | add the standard inclusions, separator equivalence, reduction closure, and Holonic-history adapters |
| proved-standard | Poincare | `ThePoincareConjecture` and `TheSmoothPoincareTheorem` | faithful and closed; proof external-only | no receiver repair; a local proof requires the actual Perelman/geometrization development |

[open] Consequently the repository currently has three usable open-problem finish lines—RH,
Navier--Stokes, and the selected TM2 formulation of P versus NP. BSD and Yang--Mills require
receiver replacement, while Hodge requires a parameter-free canonical source construction around
its faithful one-instance equality. Poincare has a faithful finish line but no local proof term.

### 1.1 Riemann hypothesis: the finish line exists

[definition] The terminal owner is `ElementaryHolonics/RH/Statement.lean:13-23`:

```lean
abbrev Statement : Prop := RiemannHypothesis
```

and `statement_def` is `Iff.rfl` against the actual zeta-zero proposition. A potential solution can
finish by returning `hRH : Soma.Holonics.RH.Statement` without another receiver definition.

[proved-derived; formal-checked] `Seam.theComposedStatementIsTheStandardOne` gives the direct local
adapter

```lean
EveryModeSitsOnTheSelfConjugateSeam <-> RiemannHypothesis.
```

`RiemannXi.riemannXi_eq_zero_iff_riemannZeta_eq_zero` connects xi and zeta zeros inside the strip.
These are genuine terminal adapters.

[counterexample; source-audit] `WeilPositivity.HasWeilCriterion`,
`PrimeSimplex.HasMertensEquivalence`, and the generic RH `Route`/`Programme` wrappers are not
progress across the finish line: each stores the difficult implication back to RH as an input
field. They are theorem signatures to discharge, not evidence that the theorem is present.

[open] The source-specific terms still required are a cofinal admissible contour family, a proved
weighted argument principle on it, the complete prime/polar/archimedean residual identity, a
vanishing boundary/tail return, a converged global zero pairing on a precisely specified complete
Weil test family, its nonnegativity, and the theorem that this positivity eliminates every
off-seam zero. The last term returns `RiemannHypothesis` directly.

[project-postulate] Keep `RH.Statement` unchanged. Replace opaque implication ports with proved
theorems over an explicit global test-space and convergence carrier. Finite discs, windings, and
tides may test those theorems but do not themselves target the terminal Prop.

### 1.2 BSD: the current finish line must be replaced

[definition] `UniversalBSD.TheRankClauseOn W M D` is a sound conditional equation for one
correctly sourced elliptic analytic datum:

```lean
forall r,
  analyticOrderAt D.L 1 = r <-> RankIsOn (rationalModel W) r.
```

[counterexample; source-audit] Its exported universal wrapper at `UniversalBSD.lean:127-128` is not
the official conjecture. It quantifies over every raw `WeierstrassCurve Z` with no rational
nonsingularity hypothesis, requires no `LDatumOn` inhabitant for any curve, ranges over an arbitrary
level `M` while `D.conductor` is separately supplied, and provides no invariance under changes of
integral model. A source with no admitted datum contributes no obligation.

[counterexample; source-audit] The complete wrapper at `UniversalBSDLedger.lean:159-162` is both
vacuous and overstrong. `HeightDatum` and `ArithmeticDatum` are arbitrary inputs;
`ArithmeticDatum.sha : Nat` assumes finiteness; and arbitrary positive period, Tamagawa, torsion,
and `sha` values can demand mutually incompatible leading-coefficient equations for the same
curve.

[open] The receiver repair requires these source types before the conjectural theorem:

1. a rationally nonsingular elliptic curve or integral model with proved rational ellipticity;
2. invariance under admissible Weierstrass model changes;
3. the source-determined Hasse--Weil `L`-function and conductor;
4. the actual Mordell--Weil group, torsion subgroup, and Neron--Tate height/regulator;
5. the actual local Tamagawa populations and real period; and
6. the Tate--Shafarevich group as a group, not a supplied natural number.

[definition] The repaired parameter-free terminal shape is:

```text
for every rational elliptic curve E,
  Sha(E) is finite,
  ord_{s=1} L(E,s) = rank E(Q), and
  the canonical leading coefficient equals
    Omega_E * Reg_E * product(c_v) * |Sha(E)| / |E(Q)_tors|^2.
```

Finiteness and the two equalities are conclusions; every object on the right is derived from `E`.

[proved-derived; formal-checked] Current family adapters run only from an assumed universal
wrapper to the congruent-number family. `ofFamilyDatum` embeds family analytic data and
`theFamilyPoseIsAnInstance` specializes an assumed universal rank clause. No theorem transports a
family result to the universal quantifier.

[open] After receiver repair, the prime-family source chain still owes finite integral Jones--Pall
reconstruction, reverse Kneser incidence, an actual uniform Tunnell eigen-current, normalized
Shimura/newform transport, and the Waldspurger period square. Closing those terms reaches only the
prime congruent-number family instance of the repaired receiver.

### 1.3 Hodge: the equation exists, the official family does not

[definition] The faithful one-instance finish line is

```lean
Datum.Conclusion D :=
  D.rationalHodgeClasses = LinearMap.range D.cycleClass.hom.
```

For a genuinely realized variety and codimension this is exactly the desired assertion.

[counterexample; source-audit] `TheHodgeConjectureIn Official` is vacuous for an empty `Official`;
`TheHodgeConjecture Canonical` is vacuous for an empty `Canonical`; and taking every arbitrary
realization as canonical is formally refuted by `HodgeSemanticsFaithfulness`. These are relative
schemas, not the final theorem.

[open] `SourceDeterminedHodgeTheory.Conclusion` is the best current terminal candidate, but it
still takes a supplied `SourceDeterminedHodgeTheory`. No canonical inhabitant constructs genuine
complex analytification, rational Betti/de Rham comparison, Hodge decomposition, fundamental
classes, Poincare duality, and the geometric cycle-class map for every smooth projective source.

[open] The finish-line construction therefore has two strictly ordered parts:

1. construct `classicalHodgeTheory : SourceDeterminedHodgeTheory` and the classical
   dimension/Lefschetz/polarization system from actual geometry; then
2. prove that every required nonzero primitive rational `(p,p)` occurrence has an actual
   codimension-`p` algebraic-cycle source.

The exported parameter-free theorem must be

```lean
theorem theHodgeConjecture : classicalHodgeTheory.Conclusion
```

rather than `TheHodgeConjecture Canonical` for a caller-chosen predicate.

[proved-derived; formal-checked] Once part 1 exists, the existing adapters are strong:
`conclusionAt_iff_irreducibleCycleClass_span` reaches the actual irreducible-cycle span;
`conclusion_iff_finiteLowerPrimitiveLiftable` reduces each source to finitely many lower-half
primitive fibres; and `hodge_iff_dimensionBoundedPrimitiveDetection` turns their occupation into
the complete conclusion.

[project-postulate] No further detector wrapper, monodromy package, rank census, or finite family
addresses either missing part. The next Hodge deed is canonical classical source construction,
followed by an actual primitive cycle-production theorem.

### 1.4 Navier--Stokes: the finish line exists, but the runway stops at extension

[definition] `NavierStokes.lean:129-157` supplies closed propositions for the four Clay
alternatives and

```lean
TheOfficialNavierStokesProblem :=
  StatementA or StatementB or StatementC or StatementD.
```

The active periodic regularity route targets `StatementB`.

[proved-derived; formal-checked] The deepest current adapter is
`compatibleOpenPeriodicExtension_of_integrableCanonicalDerivativeRate`. Given one already existing
open-lifespan periodic solution and terminal integrability of its canonical vorticity derivative
rate, it returns `CompatibleOpenPeriodicExtension solution`. It does not return `StatementB`.

[open] Four source-specific theorem layers are still absent between that extension and the finish
line:

1. local periodic existence and uniqueness for every smooth incompressible initial datum;
2. a maximal/cofinal open-lifespan solution construction with pressure-gauge-compatible lineage;
3. the PDE estimate proving terminal integrability of the canonical derivative rate for every
   finite maximal source; and
4. a globalization theorem: if every finite maximal source has a compatible extension, assemble a
   single global `PeriodicSolution` and inhabit `StatementB`.

[counterexample; source-audit] A theorem about every already supplied
`OpenPeriodicSolutionOn T ...` can be vacuous when no local solution has been constructed for the
initial datum. A theorem producing a longer finite solution can also be repeated forever without a
coherent colimit/global field. Both missing quantifier passages must be explicit.

[project-postulate] Keep `StatementB` unchanged. Add named owners for local existence, maximal
lifespan, coherent union/globalization, and a final adapter whose codomain is literally
`NavierStokes.StatementB`. Until that theorem exists, continuation is an intermediate receiver.

### 1.5 Yang--Mills: the current object is not an official finish line

[definition] `YangMills.lean:30-62` defines a useful schema:

```lean
TheYangMillsExistenceAndMassGap (P : Problem) :=
  forall G, P.isCompactSimple G -> exists Q, ... and HasMassGap P G Q.
```

[counterexample; source-audit] `Problem` freely supplies the gauge-group population, the candidate
theory population, every admission predicate, and the energy spectrum. Choosing no admitted gauge
groups proves the proposition vacuously; choosing an unrelated finite theory can prove a statement
with the same shape but no Yang--Mills content.

[open] A faithful finish line first requires actual owners for compact Lie groups with simple Lie
algebra, gauge connections modulo gauge equivalence on four-dimensional Euclidean space, the
Euclidean action and compatible measures, reflection positivity and the remaining
Osterwalder--Schrader/Wightman axioms, continuum reconstruction, the physical Hilbert space and
Hamiltonian, and its actual vacuum-quotient spectrum.

[definition] Only after those owners exist should the repository export a parameter-free

```lean
OfficialYangMillsProblem : YangMills.Problem
OfficialYangMillsExistenceAndMassGap : Prop :=
  TheYangMillsExistenceAndMassGap OfficialYangMillsProblem.
```

The fields must be definitions from those owners, not caller-supplied predicates.

[open] The prize-bearing source terms are then a gauge-covariant lattice/continuum family,
reflection-positive compatible measures, uniform renormalized estimates and tightness, a
nontrivial continuum reconstruction, and one positive spectral separator which survives every
scale and volume limit for each compact simple group.

[counterexample; formal-checked] The existing shrinking-spectrum family proves why the final
uniform passage is required: positive finite-stage gaps can converge to zero. Current finite Hodge
Laplacians and coercive forms have no adapter into a source-determined continuum Hamiltonian.

### 1.6 P versus NP: a selected-model finish line exists, but no Holonic adapter reaches it

[definition] `PVersusNP.lean:81-113` defines `InP`, `InNP`, `PEqualsNP`, and `PNotEqualsNP` over
fixed binary encodings and Mathlib's finite multitape TM2 polynomial-time predicate. This is a
usable closed receiver for the selected standard model.

[proved-derived; formal-checked] The only terminal adapter is

```lean
pEqualsNP_iff_bothInclusions :
  PEqualsNP <->
    PSubsetNP and (forall language, InNP language -> InP language).
```

`PSubsetNP` itself is currently only a definition; no theorem inhabits even this standard easy
inclusion.

[open] The equality route needs polynomial-time composition/pairing/Boolean closure, a proof of
`PSubsetNP`, and the prize-bearing term

```lean
forall language, InNP language -> InP language.
```

[open] The separation route should first add the standard adapter

```lean
PNotEqualsNP <-> exists language, InNP language and not InP language
```

after `PSubsetNP`, then exhibit the language, verifier, certificate bound, and an
encoding-/reduction-stable superpolynomial lower-bound witness.

[open] No current `Border`, `ChainRule`, compression, or complete-history theorem preserves a
Mathlib TM2 polynomial cost into `InP`, `InNP`, or `PNotEqualsNP`. Polynomial closure under the
defined many-one reductions and robustness under polynomially equivalent encodings/machine models
must be constructed before a Holonic separator can be tested at the finish line.

[project-postulate] Keep the terminal propositions. Build the missing complexity closure and
adapter layer; do not replace it with finite state-space compression or trained lookup terrain.

### 1.7 Poincare: the finish line is faithful and wholly external

[definition] `PoincareConjecture.lean:31-44` gives parameter-free topological and smooth
propositions matching Mathlib's `proof_wanted` statement shapes.

[proved-standard] Perelman's theorem settles the mathematical receiver, but Mathlib's
`proof_wanted` declarations create no proof constants and the repository has no local theorem
inhabiting either proposition.

[open] No adapter connects `Ricci.lean` to these propositions. A local proof term requires the
actual three-manifold Ricci flow, entropy/noncollapse, singularity classification, addressed neck
surgery, continuation, extinction/geometrization, and topological reconstruction. The finite
rational flow mechanism instantiates none of those source types.

[project-postulate] No receiver repair is needed. Either retain Poincare as
`proved-standard; external-source`, or begin a genuine formal Perelman development whose terminal
codomain is literally `ThePoincareConjecture`.

### 1.8 Immediate construction order for the finish lines

[project-postulate] Receiver construction precedes further solution campaigns in this order:

1. replace the universal BSD rank/ledger definitions with a canonical, nonsingular,
   model-invariant curve receiver;
2. construct and export the parameter-free classical Hodge source theory;
3. replace the arbitrary Yang--Mills `Problem` parameter with an actual source-determined official
   problem;
4. add the missing Navier--Stokes local-existence, maximal-lifespan, coherent-globalization, and
   literal-`StatementB` adapters;
5. add P-versus-NP closure, separator, reduction, and machine-robustness adapters;
6. complete the RH cofinal/global Weil receiver while leaving its already faithful terminal Prop
   untouched; and
7. keep Poincare as an external regression unless a full formal geometric proof is deliberately
   opened.

[project-postulate] This order is about finish-line readiness, not likelihood of solving the
problems. Until rows 1--3 exist, a candidate proof on those lines cannot even be judged against one
canonical closed proposition in Lean.

## 2. The common mathematical object

[definition] A Millennium worktrack is presented as a source-specific instance of the following
directed closure object:

```text
source occurrence
  -> addressed swing / transported difference
  -> ordered word and local ledger
  -> boundary, annihilator, or remainder
  -> quotient plus complete ReconstructionFiber
  -> chart/scale rebase with holonomy
  -> compatible directed tower
  -> compactness, coercivity, tightness, descent, or gluing
  -> official receiver and its source witness.
```

[definition] The elementary lineage-bearing passage remains the addressed span

```text
X <- W_f -> Y,
```

and serial composition of `f : X -> Y` with `g : Y -> Z` retains the joining population
`W_f x_Y W_g` and its equality at `Y`. Endpoint reachability is only a receiver shadow.

[proved-derived; formal-checked] For entering and returned receivers `E` and `R` on a source
population `S`, an exact descended transformer on `E(S)` exists precisely when

```text
E(x) = E(y)  ->  R(x) = R(y)
```

for every `x,y : S`. An equal-entering/unequal-returned pair is therefore the shortest complete
separator of an invalid Holonic compression.

[definition] Dynamic compression additionally owes descended generators `U_i` satisfying

```text
q T_i = U_i q
```

for every admitted source generator `T_i`, together with the decoder domain, work, residency, and
complete reconstruction fibre. A finite quotient or a finite state census alone supplies none of
those dynamic returns.

[interpretation] Cross-entropy enters this calculus as a receiver-indexed comparison among
continuation families after distinct currents cross declared axes. A scalar loss, count, or trace
is a quotient of that caused comparison and can erase the directional population that the theorem
needs.

### 2.1 Formula/application atlas

| Grade | Holonic formula | Mathematical return | Millennium applications |
|---|---|---|---|
| definition | `Delta_R(f) = R(target f) - transport_f(R(source f))` | situated returned difference | RH seam residual; BSD rank/ledger defect; Hodge quotient class; NS current excess; YM spectral difference; computation-history defect |
| proved-derived; formal-checked | `K = T_right T_left^-1` | curvature/holonomy of two addressed routes | gauge plaquettes; Hodge chart transport; arithmetic local/global comparison; flow/localization commutator |
| proved-derived; formal-checked | `partial^2 = 0` plus a declared constitutive current | local boundary cancellation and global ledger | contour boundary in RH; cycle-class gluing; fluid flux/enstrophy; lattice gauge current; surgery boundary accounting |
| definition | `F = q^-1(q(x))` with all retained antecedents | reconstruction fibre of a receiver occurrence | zero orbit; cycle lifts; Selmer and `Sha`; terminal fluid state; gauge continuum states; certificate/search histories |
| proved-derived; formal-checked | `q T_i = U_i q` | generator-compatible dynamic condensation | all ordered successor words; polynomial-history transport; scale towers; recurrence and continuation |
| definition | `B(v,v) >= 0`, with radical and source map retained | positive/coercive receiver | Weil form; Hodge--Riemann pairing; Neron--Tate regulator; dissipation; YM vacuum-quotient energy |
| definition | `J[a,b] + J[b,c] = J[a,c]` | terminal current with exact chronology | RH cofinal contours; NS maximal-time accumulation; YM scale/volume limit; Ricci-flow/surgery history |
| definition | `r_j s_ij = s'_ij r_i` | compatible directed tower | contour/test refinement; Lefschetz/cover refinement; dyadic fluid scale; lattice gauge continuum; polynomial reductions |
| counterexample; formal-checked | equal coarse receiver, unequal fine return | firing falsifier for overcompression | off-seam RH quartet; erased Hodge cycle map; local Selmer blindness; equal-curl/opposite-stretching jets; shrinking YM gap |

[interpretation] The table is the reusable Holonic arsenal. Its common rows organize the work; the
last column does not permit a proof in one theory to be transported into another without the
source-specific constitutive map and reconstruction theorem.

## 3. Assumption/outcome matrix

[definition] A conjecture is treated as closed only when the official receiver returns one of the
following terminal witnesses, not merely when a suggestive trace or bounded experiment agrees.

| Grade | Worktrack and assumed outcome | Required returned witness | Decisive opposite witness |
|---|---|---|---|
| definition | RH true | a complete admissible Weil form whose positivity and trivial off-seam radical force every nontrivial zero to have `Re(rho)=1/2` | one nontrivial zero with nonzero seam residual, equivalently its symmetry-closed off-line quartet |
| definition | BSD true | canonical curve-derived analytic order equals Mordell--Weil rank and the canonical period/regulator/Tamagawa/torsion/`Sha` leading-term ledger has zero defect | one curve with unequal ranks or a nonzero canonical leading-ledger defect |
| definition | Hodge true | every rational `(p,p)` class returns an actual rational algebraic cycle in its cycle-lift fibre | a nonzero class in cohomology modulo the algebraic span |
| definition | Navier--Stokes regularity | every admitted smooth finite-energy source returns a finite terminal critical current and a compatible high-order restart state | an admitted finite-time singularity or a proved terminal continuation obstruction |
| definition | Yang--Mills gap | a nontrivial continuum gauge theory and a positive vacuum-quotient spectral separator uniform through lattice, volume, and continuum reconstruction | a genuine continuum null sequence or failure of existence/reconstruction |
| definition | `P = NP` | a uniform verifier/certificate-to-decider construction with polynomial cost through every admitted encoding | an encoding-stable superpolynomial history/resource separator for one NP language |
| definition | `P != NP` | one such separator surviving reductions and the relativization, natural-proof, and algebrization audits relevant to its method | a uniform polynomial verifier-to-decider construction |
| proved-standard | Poincare | the established theorem that every closed simply connected three-manifold is homeomorphic to `S^3` | no opposite mathematical outcome remains; local failure is failure to reconstruct the established proof mechanism |

[interpretation] These outcome assumptions are useful because they sort the work into families of
witnesses: positivity with a controlled radical, local-to-global descent, terminal compactness,
spectral separation, and complete computational-history separation. They must remain hypotheses
until a source construction returns the stated witness.

## 4. Riemann hypothesis: the half, the projectile, and the trace

[definition] The spectral normal coordinate and the analytic growth slack are different objects:

```text
rho = 1/2 + epsilon_s + i gamma,
epsilon_s = Re(rho) - 1/2,

M(x) = O(x^(1/2 + epsilon_g)) for every epsilon_g > 0.
```

`epsilon_s` is the directed residual of one spectral occurrence. `epsilon_g` is a universally
quantified tolerance in a family of growth bounds. The present Lean tree does not yet formalize the
classical equivalence that would transport the second family into the first receiver.

[proved-standard] In logarithmic scale `u`, the source mode has the multiplicative-character form

```text
A_rho(u) = exp((rho - 1/2)u)
         = exp(epsilon_s u) exp(i gamma u),
A_rho(u+v) = A_rho(u) A_rho(v),
dA_rho/du = (epsilon_s + i gamma) A_rho(u).
```

Changing the multiplicative pivot rebases `A_rho`; its rebase factor has unit modulus exactly when
`epsilon_s = 0`.

[interpretation] This is the precise safe content of the "projectile through induced fields"
reading: an addressed mode travels along logarithmic scale and every receiver evaluates the same
mode after transport. The critical seam is the fixed locus of the zeta dualities after centering,
not an arbitrarily selected origin.

[interpretation] The absence of a privileged pivot is scale covariance, not yet Lorentz
invariance or a theorem about inertial rest frames. A relativistic reading would require an
independent spacetime action and a proved equivariant identification with this multiplicative
character.

[counterexample; formal-checked] An off-seam quartet

```text
1/2 + epsilon_s + i gamma,
1/2 - epsilon_s + i gamma,
1/2 + epsilon_s - i gamma,
1/2 - epsilon_s - i gamma
```

is closed under functional reflection and conjugation while no member need occupy the fixed seam.
Opposite residuals cancel in symmetric means and traces. Symmetry, aggregate zero count, and a
vanishing first residual moment therefore cannot prove RH.

[proved-derived; formal-checked] The exact RH line already owns the official statement, centered
seam equivalence, entire xi and its symmetry, theta/Mellin transport, zero counting, explicit-formula
receiver components, archimedean components, and the implication from RH to admitted truncated Weil
positivity.

[open] The shortest remaining RH chain is:

```text
cofinal weighted argument principle
 -> prime + archimedean + polar explicit formula
 -> vanishing boundary/tail return
 -> source-realized complete Weil test family
 -> nonnegative form with no off-seam null direction
 -> RiemannHypothesis.
```

[counterexample; source-audit] A finite winding census, symmetry proof, bounded zero count, finite
Gram matrix, or height-blind Mellin upper envelope cannot close that chain. In particular, an upper
bound depending only on `Re(s)` does not make the transform's actual magnitude independent of
height because phase cancellation remains in the reconstruction fibre.

## 5. Status of every worktrack

### 5.1 Birch--Swinnerton--Dyer

[proved-derived; formal-checked] The congruent-number/full-two-torsion line contains exact
duplication, descent, height contraction, finite generation, Selmer-style local receivers,
theta/Hecke/Shimura coefficient transport, Brandt neighbor populations, quotient lattices,
determinant/genus data, and the real Waldspurger--Tunnell defect

```text
2 L_p(1) / Omega_p - c_p^2.
```

[open] The shortest current family chain is finite integral Jones--Pall reconstruction for the two
target forms, reverse two-class Kneser incidence, the actual neighbor census, a uniform Tunnell
`T(p^2)` eigen-current, normalized Shimura/newform transport, and the Waldspurger period square.
Closing it would settle the typed prime family gate, not universal BSD.

[open] The universal path must first replace the freely supplied universal ledger with canonical
curve-derived analytic data, Neron--Tate height, local Tamagawa factors, torsion subgroup, period,
and Tate--Shafarevich group; `Sha` finiteness, rank equality, and the leading-term identity then
remain conclusions.

[counterexample; formal-checked] Existing local/global falsifiers show that a locally admitted
Selmer receiver can be blind to global realization, local form equivalence need not give integral
global equivalence, and positivity plus determinant admits an impostor quadratic form. Finite
coefficient agreement therefore cannot replace the uniform arithmetic transport.

### 5.2 Hodge

[proved-derived; formal-checked] Hodge has the cleanest universal normal form in the tree. For a
source-determined smooth-projective theory with the required Lefschetz system,

```text
Hodge
 <-> every lower-half primitive class is liftable
 <-> every nonzero lower-half primitive detector fibre is occupied,
```

where the required steps satisfy `2(p+1) <= dim_C X`. Each variety contributes exactly
`floor(dim_C X / 2)` such steps before the divisor passage, and hard-Lefschetz reflection plus
above-dimension vanishing returns the other degrees.

[proved-derived; formal-checked] The divisor/exponential passage removes codimension one, leaving
at most `floor(dim_C X / 2) - 1` higher primitive obligations. Point, projective-line,
projective-line-product, sphere-product, and finite projective-line-power constructions are exact
bounded validations of the mechanism.

[open] The universal missing witness is unchanged in kind:

```text
primitive rational (p,p) class h
 -> actual rational codimension-p algebraic cycle Z
 -> cycleClass(Z) = h.
```

The algebraic-to-Hodge fundamental-current construction also still owes its canonical analytic
orientation and Poincare-dual source passage at full generality.

[counterexample; formal-checked] Source typing with an erased cycle-class map, finite dimension,
signed-definite polarization, or repeated lower Lefschetz transport does not produce that witness.
`PrimitiveOrbitSourceCover.nonempty_iff_primitiveLiftable` further proves that an unrestricted
orbit-cover package is equivalent to the same missing proposition.

[project-postulate] Further Hodge work should originate the canonical fundamental current or an
independently founded higher primitive cycle-production mechanism. Another wrapper, census,
finite-rank ledger, or unrestricted seed package should not be counted as progress on the open
edge.

### 5.3 Navier--Stokes

[proved-derived; formal-checked] The periodic line has constructed the large-scale dyadic Hodge
coefficient return and the high-order restart carrier. Direction-depleted Biot--Savart/Hodge
reconstruction, infinite scale summation, and strict-interior time integration reduce the remaining
continuation port to terminal integrability of the genuine critical vorticity current.

[proved-derived; formal-checked] The sharp current reduction presently available is

```text
criticalVorticityRate(t)
  <= (3/2) canonicalVorticityDerivativeRate(t).
```

It holds on the admitted source carrier, while continuity and integrability have been established
only on compact intervals strictly inside the maximal lifespan.

[open] The missing theorem is a PDE-owned estimate proving terminal integrability on `[0,T]`, or a
weaker source rate which still majorizes the critical receiver and is integrable from energy,
viscosity, direction coherence, or another exact constitutive law. A scalar terminal mass must
then be transported into an actual compatible terminal state and restart.

[counterexample; formal-checked] Strict-interior continuity does not imply terminal integrability,
kinetic energy alone cannot control the required derivative rate, and equal-curl divergence-free
jets can return opposite vortex-stretching signs. More scale algebra or a heat/theta magnitude
receiver cannot delete these source faces.

### 5.4 Yang--Mills existence and mass gap

[proved-derived; formal-checked] The current line owns abstract coercive/vacuum-quotient forms,
finite chain-Laplacian models, connection/plaquette holonomy, and the proof pattern relating a
positive separator to a gap in an admitted bounded spectral carrier.

[open] The official theorem still requires, for every compact simple gauge group, a genuine
gauge-covariant scale family, reflection-positive compatible measures, uniform renormalized
estimates and tightness, continuum reconstruction into a nontrivial physical Hilbert space and
Hamiltonian, and one positive vacuum-quotient separator uniform through the complete limit.

[counterexample; formal-checked] The family of finite spectra `{0, 1/(n+1)}` has a positive gap at
every finite stage and no uniform positive gap. Further finite diagonalization cannot close the
continuum receiver.

### 5.5 P versus NP

[proved-derived; formal-checked] The current owner poses binary languages, encodings, Mathlib TM2
polynomial time, polynomial certificates, reductions, `P = NP`, and `P != NP`; locally checked
content is limited to encoding facts, exact pair length, and elementary statement decomposition.

[open] The equality route needs a uniform verifier/certificate-to-decider compiler with polynomial
cost. The separation route needs one NP language and an encoding- and reduction-stable complete
history/resource separator obeyed by every polynomial deterministic decider and violated by that
language.

[counterexample] A finite Holonic quotient, cheap lookup, trained terrain, or compressed state
space does not imply `P = NP`: its construction may already perform exponential search, its size
may be exponential, or it may be nonuniform advice. Endpoint truth values also erase the history
needed for a lower bound.

### 5.6 Poincare as the solved regression

[proved-standard] Poincare is externally solved. The local `PoincareConjecture.lean` gives theorem
shapes, while `Ricci.lean` supplies an exact finite rational flow mechanism with conserved total,
contracted deviation, a monotone quadratic receiver in its admitted aperture, a round fixed shape,
and exact reconstruction away from its collapse value.

[open] The repository has no local Perelman proof and its finite flow model contains no actual
three-manifold, Ricci tensor, conjugate heat kernel, noncollapse theorem, singularity
classification, neck surgery, or extinction-to-`S^3` passage.

[project-postulate] Poincare should remain a calibration of the required topology-changing
Holonic return:

```text
geometric flow -> monotone receiver -> blow-up and neck recognition
 -> addressed surgery -> retained connected-sum/topology fibre
 -> continued flow -> extinction -> source reconstruction.
```

## 6. Cross-problem families without false identification

[interpretation] The seven worktracks fall into overlapping, nonexclusive receiver families:

| Grade | Family | Worktracks | Shared question | Source-specific residue |
|---|---|---|---|---|
| interpretation | fixed locus plus positive form | RH, Hodge, Yang--Mills | does a positive receiver force occupancy of the desired null/fixed sector? | Weil completeness; algebraic-cycle source; continuum gauge Hamiltonian |
| interpretation | local-to-global descent | BSD, Hodge, Poincare | do compatible local antecedents glue without losing the obstruction fibre? | Selmer/`Sha`; cycle class; surgery topology |
| interpretation | terminal current and compactness | RH, Navier--Stokes, Yang--Mills | does every finite/local return survive a cofinal or terminal limit? | contour boundary; BKM/terminal state; tight continuum reconstruction |
| interpretation | rank, kernel, and cokernel | BSD, Hodge, Yang--Mills | what population survives a map or positive form after quotienting its radical? | Mordell--Weil/analytic rank; algebraic span quotient; vacuum quotient |
| interpretation | complete-history resource separation | P versus NP and every dynamic compression | does the condensed carrier preserve all admitted successors at bounded cost? | polynomial uniformity and encoding barriers |
| proved-standard | topology-changing flow regression | Poincare | can a cut change the local body while retaining enough lineage to reconstruct the global source? | Ricci flow, neck classification, and surgery |

[interpretation] The strongest direct analytic bridge currently present is the lattice heat current:
Fourier heat multipliers meet theta winding sums, and Mellin transport returns completed zeta. RH
then owes prime/archimedean positivity; Navier--Stokes separately owes nonlinear triads, direction,
stretching, and terminal restart. The common heat carrier does not identify the two problems.

[interpretation] The strongest prospective arithmetic-geometric bridge is Hodge--BSD through
intersection heights, regulator determinants, cycle classes, Selmer/`Sha` obstruction fibres, and
Arakelov or Beilinson--Bloch passages. No such complete bridge is currently constructed in Lean.

## 7. Paths forward and anti-churn gates

[project-postulate] Work should be prioritized by the shortest source-producing edge, not by the
number of nearby theorem wrappers or the visual appeal of another bounded example.

[project-postulate] The next audit gate is repository health. The 2026-08-28 catalog reported
thirteen failing aggregate targets. During this audit the two newest Hodge universal owners
compiled in focused checks, but a focused `UniversalBSD`/`UniversalBSDLedger` build was blocked by
current failures in `FiveHalving`, `FamilySupport`, `FamilyImage`, and `HeckeEuler`. No station-wide
green claim should be made until one reproducible aggregate build returns.

[project-postulate] The shortest research paths are:

1. RH: assemble the complete cofinal explicit-formula/Weil carrier, with every archimedean,
   polar, tail, and boundary return retained.
2. Navier--Stokes: prove the terminal PDE estimate for the canonical derivative or a strictly
   weaker integrable source rate; then reconstruct the terminal state and restart.
3. Hodge: stop at the established finite primitive normal form and construct a canonical
   fundamental current or a genuine higher primitive algebraic-cycle source.
4. BSD: first repair the universal receiver to canonical source-determined data; in parallel use
   the bounded prime family only to close Jones--Pall/Kneser/Tunnell/Shimura/Waldspurger transport.
5. Yang--Mills: construct the actual scale-indexed gauge measure/QFT family and uniform
   continuum-preserved separator; do not add another finite spectrum.
6. P versus NP: proceed only when the object is a uniform polynomial transformer or a
   reduction-stable complete-history separator; bounded state compression is not the theorem.
7. Poincare: run the local calculus as a regression against the established geometric proof
   shape, not as an open prize campaign.

[project-postulate] Every proposed advance must state five things before construction: the exact
official receiver, the new source occurrence it originates, the old obstruction fibre it reduces,
the commuting transport/reconstruction diagram, and a firing falsifier which would reject the
claim. If it only renames the existing open proposition, the deed returns as churn.

## 8. Validation and ownership boundary

[established-bounded; measured] Focused compilation passed for
`HodgeDimensionBoundedLefschetz.lean` and
`HodgeDimensionBoundedPrimitivePropagation.lean`; their printed theorem audits reported only
Lean/Mathlib's standard `propext`, `Classical.choice`, and `Quot.sound` dependencies.

[established-bounded; measured] Independent focused checks passed for `PVersusNP.lean`,
`Seam.lean`, `RiemannXi.lean`, and `WeilPositivity.lean`, with no `sorryAx` reported in the audited
theorems.

[established-bounded; measured] The attempted focused BSD ledger build did not reach the target
because current dependencies failed in `FiveHalving`, `FamilySupport`, `FamilyImage`, and
`HeckeEuler`. This is a repository-state obstruction, not evidence for or against BSD mathematics.

[project-postulate] This audit changes no live construction position. The Rust roadmap and
`CONSTRUCTION_STATE.md` remain the sole scheduling authorities; the Millennium Lean station remains
an exterior theorem-cartography and falsification apparatus.

## 9. Construction return: the finish lines are now executable objects

[established-bounded; implemented-exact; formal-checked] The follow-on construction pass added one
focused Lean owner for every Millennium worktrack and one aggregate import surface. The pass proves
none of the open conjectures. It replaces an undefined destination with a typed certificate whose
last theorem lands in the existing terminal proposition, or—where the classical source theory is
not yet formalized—with an honestly named repository source-construction finish line.

| Grade | Worktrack | Terminal receiver | Construction certificate | Exact closing adapter | Residual source boundary |
|---|---|---|---|---|---|
| [definition] | RH | `Soma.Holonics.RH.Statement` | `RH.GlobalWeilFinishLine` | `statement_of_globalWeilFinishLine` | Construct the cofinal xi contours and global explicit-formula limits; prove arithmetic positivity and the complete off-line Weil separator on the same receiver. |
| [definition] | BSD | `OfficialBSDReceiver.BSDSourceConstructionFinishLine` | `OfficialBSDReceiver.SourceTheory` plus `CurveConclusion` for every `RationalEllipticCurve` | `rankClauseOn_of_curveConclusion`, `familyRankClause_of_curveConclusion`, `familyRankClause_of_finishLine` | Construct the classical cohomology localization, height, period, Tamagawa, conductor and analytic continuation faces and prove their source faithfulness. The terminal concludes, rather than assumes, finiteness of the actual Sha kernel. |
| [definition] | Hodge | `HodgeOfficialReceiver.HodgeSourceConstructionFinishLine` | `ClassicalHodgeSourceConstruction` plus `PrimitiveAlgebraicity` for its exact theory | `HodgeSourceConstructionFinishLine.to_sourceDeterminedConclusion` and `to_sourceSelectedTheHodgeConjecture` | Construct canonical analytification, Betti/de Rham comparison, pure Hodge decomposition and fundamental-cycle/Poincare-dual passage. No equivalence to the parameter-free classical conjecture is claimed before that source theory exists. |
| [definition] | Navier--Stokes | `NavierStokes.StatementB` and hence `TheOfficialNavierStokesProblem` | `PeriodicStatementBFinishLine` | `statementB_of_finishLine`, `officialProblem_of_finishLine` | Prove local/cofinal construction, overlap uniqueness, terminal integrability of the canonical vorticity-derivative receiver, compatible extension and closed-time globalization. |
| [definition] | Yang--Mills | `YangMillsOfficialReceiver.YangMillsConstructionFinishLine` | `CompactConnectedSimpleGaugeGroup`, `ContinuumYangMillsTheory`, reconstructed `ContinuumHamiltonian` | `FiniteContinuumReconstruction.toContinuumMassGap` plus `YangMillsConstructionFinishLine.theory_for` | Construct the canonical tangent Lie bracket, distributional four-dimensional gauge-field current, full OS/Wightman and unbounded self-adjoint packages, and a uniform finite-to-continuum separator with spectral ancestry. |
| [definition] | P versus NP | `PVersusNP.PEqualsNP` or `PVersusNP.PNotEqualsNP` | `UniformVerifierCompiler` or `ConcreteSeparator` | `pEqualsNP_of_uniformVerifierCompiler`, `pNotEqualsNP_of_concreteSeparator`, `pNotEqualsNP_iff_exists_np_not_p` | Prove the routine fixed-TM2 `PSubsetNP` closure; then either build the uniform polynomial compiler or one actual NP language with a universal deterministic polynomial lower bound. |
| [proved-standard; external-only] | Poincare | `PoincareConjecture.ThePoincareConjecture` | `PerelmanFinishLine` | `thePoincareConjecture_of_finishLine` | The local kernel still owes the established Ricci-flow proof: source metric flow, monotone quantities, noncollapse, typed `S²` necks, retained/discarded component lineage, canonical neighbourhoods, locally finite surgery, extinction and topological reconstruction. |

### 9.1 What each new receiver prevents

[proved-derived; formal-checked] `GlobalWeilFinishLine` does not store RH or an implication to RH.
An alleged off-line zero must originate a Weil square outside the nonnegative ray, while arithmetic
positivity places that very atlas value inside the ray. The closing theorem is the resulting
same-occurrence contradiction and has codomain literally `RH.Statement`.

[established-bounded; source-audit] `BSDSourceConstructionFinishLine` quantifies actual elliptic
Weierstrass models over `Q`, not raw possibly singular integral models. Its analytic datum agrees
with the curve-derived Hasse--Weil series on a right half-plane. Its arithmetic datum contains the
actual rational-point group and torsion subgroup, and its Tate--Shafarevich group is the kernel of a
typed global-to-local cohomology homomorphism. `Finite Sha`, analytic-rank equality and the complete
leading-coefficient ledger occur only in `CurveConclusion`. The first draft's impossible
"equivalent to every arbitrary source theory" requirement was rejected; canonical faithfulness is
now an explicit open construction boundary rather than a contradictory premise.

[established-bounded; source-audit] `HodgeSourceConstructionFinishLine` cannot be discharged by an
empty official-family predicate. It asks for one universal source-determined theory and primitive
algebraicity for that same theory. Because Mathlib does not yet own the canonical classical source
construction, this is intentionally a repository construction target, not a false claim of formal
equivalence to the official conjecture.

[proved-derived; formal-checked] `PeriodicStatementBFinishLine` makes the current Navier--Stokes
endpoint concrete. `CanonicalTerminalControl` is terminal interval-integrability of the compact
radius-three spatial vorticity-derivative population; `CanonicalTerminalExtensionLaw` returns the
existing addressed compatible extension. Pressure normalization fixes the additive gauge before
the cofinal atlas is glued. `statementB_of_finishLine` then returns the literal periodic official
alternative.

[established-bounded; source-audit] `ContinuumYangMillsTheory` removes the two vacuity channels in
the old arbitrary `YangMills.Problem`: gauge sources carry actual compact, connected, Hausdorff Lie
group and simple model-Lie-algebra structures, and the energy spectrum is derived from an operator.
The Hamiltonian is not independent of the Euclidean current: a dense positive-time-observable map
reconstructs its Hilbert carrier, its inner product is the reflected expectation, and its action is
the reconstructed Euclidean-time generator on the retained domain. A finite gap reaches the
continuum only through a uniform separator and a nonzero spectral-ancestor law.

[proved-derived; formal-checked] The P-versus-NP receiver now has both finish directions.
`UniformVerifierCompiler` returns one polynomial-time decider from every retained NP presentation;
with the separately visible `PSubsetNP` theorem it closes `PEqualsNP`. `ConcreteSeparator` retains
one language, its NP presentation and `notInP`, closing `PNotEqualsNP`. Under `PSubsetNP`, the latter
is proved equivalent to the existence of a language in NP and outside P. Polynomial many-one
pullback is separately named so encoding robustness cannot be inferred from an endpoint truth
value.

[proved-derived; formal-checked] `PerelmanFinishLine` is the solved regression rather than a local
proof claim. Its analytic certificate now includes typed surgery events whose necks are actually
homeomorphic to `S²`, explicit retained/discarded populations, chronological and locally finite
event laws, and a no-return lineage condition. The topological reconstruction law remains a
separate source-specific theorem, and its adapter returns the exact existing Poincare proposition.

### 9.2 Anti-churn rule after this pass

[project-postulate] A further theorem wrapper is progress only if it constructs or strictly reduces
one field of these certificates. The next useful object is therefore unambiguous:

1. [project-postulate] RH: a field of `GlobalExplicitFormulaWitness`, `IsPositive`, or
   `offLineSeparation` for the actual global atlas.
2. [project-postulate] BSD: a source-faithful `AnalyticDatum` or `ArithmeticDatum`, or a theorem
   identifying one existing family datum with the constructed source.
3. [project-postulate] Hodge: a canonical field of `SourceDeterminedHodgeTheory`, or one genuine
   primitive algebraic-cycle lift in that theory.
4. [project-postulate] Navier--Stokes: `CanonicalTerminalControl`, its extension law, or the
   cofinal/globalization passage for arbitrary admitted periodic data.
5. [project-postulate] Yang--Mills: a structured gauge source, OS reconstruction field, continuum
   Hamiltonian, or `FiniteContinuumReconstruction` with a uniform separator.
6. [project-postulate] P versus NP: `PSubsetNP`, a `UniformVerifierCompiler`, a
   `ConcreteSeparator`, or the reduction-pullback theorem.
7. [project-postulate] Poincare: a field of the typed Ricci/surgery certificate or its established
   reconstruction theorem.

[counterexample; source-audit] A theorem whose only new premise is the terminal proposition, a
caller-chosen admission predicate, an empty source population, an independent fabricated spectrum,
or a structure field equal to the desired final theorem does not cross any one of these boundaries.

### 9.3 Verification

[established-bounded; measured] The aggregate command

```text
lake build ElementaryHolonics.RH.GlobalWeilFinishLine \
  ElementaryHolonics.Millennium.OfficialBSDReceiver \
  ElementaryHolonics.Millennium.HodgeOfficialReceiver \
  ElementaryHolonics.Millennium.NavierStokesOfficialBridge \
  ElementaryHolonics.Millennium.YangMillsOfficialReceiver \
  ElementaryHolonics.Millennium.PVersusNPOfficialBridge \
  ElementaryHolonics.Millennium.PoincareOfficialBridge \
  ElementaryHolonics.Millennium.OfficialFinishLines
```

[established-bounded; measured] returned `Build completed successfully (4515 jobs)` and exit code
zero on 2026-08-29. The output contains pre-existing linter and deprecation warnings in replayed
dependencies; no new receiver target failed.

[established-bounded; measured] A targeted search over the eight new modules found no occurrence of
`sorry`, `sorryAx`, or a custom `axiom`; targeted `git diff --check` returned clean. Printed axiom
audits for the closing bridges list only `propext`, `Classical.choice`, and `Quot.sound`.

[open; source-audit] The literal adapter into `UniversalBSD.TheRankClauseOn` could not be compiled
through the current Lean 4.33 station because its legacy dependency closure still fails in
`FiveHalving`, `FamilySupport`, `FamilyImage`, and `HeckeEuler`. The new generic adapter proves the
exact rank-biconditional shape, and the concrete congruent-family `TheRankClause` adapter is checked.
This build obstruction neither proves nor weakens any BSD conclusion.

[project-postulate] This construction pass changes no live Rust construction position.
`CONSTRUCTION_STATE.md` remains untouched by this pass; `OfficialFinishLines.lean` is an exterior
Lean theorem-cartography integration gate.
