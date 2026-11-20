# Unforced blow-up is claimed for Euler with a whole Lean proof and for Navier–Stokes as an implication from unposted data; the Navier–Stokes profile is a cycle of the scale flow closed by a screw and a dyad

November 20, 2026, 19:40 to 20:01 UTC. On that day two papers on the blow-up of fluids without a force were
posted with Lean packages: one on the Euler equations by Levent Alpöge, Tristan Buckmaster and Matei Coiculescu
([paper](https://cims.nyu.edu/~tristanb/cc.pdf), [Lean](https://github.com/mcoiculescu/EulerBlowupPublic)), and one
on the Navier–Stokes equations by Alpöge and Buckmaster
([paper and Lean](https://github.com/tristanbuckmaster/navier-stokes/)). Brandon asked for both to be gauged beside
[the same day's zeta claim](2026-11-20_A_PUBLISHED_LEAN_ARCHIVE_CLAIMS_THE_RIEMANN_HYPOTHESIS_FOR_ZETA_AND_EVERY_DIRICHLET_CHARACTER_ITS_STATEMENT_IS_MATHLIBS_ITS_TEXT_ADDS_NO_AXIOM_AND_ITS_KEY_IS_MULTIPLICITY_AS_A_CARRY_COUNT_WON_BY_A_CHAIN_OF_THETA_LIFTS.md),
and recalled that this project had earlier pointed at a blow-up with a force. This record states what each paper
claims, what was read of each, what is not posted, and the two methods read on the objects. Nothing was compiled,
no Lean of this tree changed, and nothing ran on a learner or on the card. Refs #410.

Each paragraph carries its grade: `source-inspected` (read in the posted files, as text), `paper` (the authors'
own account), `reported` (a public report, not verified here), `tree` (read in this repository), `from training`
(a result of the literature, named) and `agent-inferred` (this record's join).

Three atlas rows enter (§11): `ns.scale-cycle-screw-dyad`, `ns.subcritical-contraction-finite-codimension` and
`fluid.craik-criminale-tower`. Two rows take a note in their scope: `ns.official-alternatives` and
`ns.energy-count-cannot-decide`. No grade changes.

## 1. What had been said about forcing

`tree`. The records of September 8 and 9
([the review](2026-09-08_THE_NS_EULER_REVIEW_EXPOSES_THE_GENERATOR_GAP_IN_AC1.md),
[its correction](2026-09-09_RELEVANCE_LOSS_AND_REALIZED_CLASSES.md)) read a repository of OpenAI's that claimed
two things: the breakdown of Navier–Stokes solutions with a smooth force, and a blow-up of the Euler equations
with no force. The Clay statement has four alternatives (`Fluid/NavierStokes:StatementA` to `StatementD`, atlas
`ns.official-alternatives`). C and D ask for a datum and a force with no global solution, so a forced breakdown
is a proof of them as worded. A and B ask for a global solution for every datum with zero force, so only a
breakdown with no force refutes them. The forced half of September was the Navier–Stokes half.

So the two papers of November 20 stand to September as follows. The Euler paper is a second proof of unforced
Euler blow-up, on the torus, with a prose proof beside its Lean; its own note on provenance says it uses the same
wave mechanism as OpenAI's and that its authors' earlier public proofs (Boussinesq, porous media and Euler) had
forces. The Navier–Stokes paper is the first claim of breakdown with no force.

## 2. The Euler paper and what was read of it

`paper`. *Finite-time singularity formation for the three-dimensional Euler equations*, 55 pages (sha256 of the
file read `414f5af635c78e807d674a1bab49a440c3cf1173bc3bc7cd12f8686f80a077a3`). Its theorem: there is an odd,
smooth, divergence-free datum on the torus whose maximal classical solution lives to a finite time `T∗`, with
`∫‖∇u‖_∞ dt = ∫‖curl u‖_∞ dt = ∞`, the velocity bounded, `|curl u(t, 0)| → ∞`, and smooth limits of `u` and
`∂_t u` away from the origin.

`source-inspected`. The Lean package (commit `36d3961161f8e7bba9cc8f671e5d0c4a27281239`): 472 files and 130,940
lines, Lean 4.34.0-rc2. `TorusEuler/Statement.lean` states the theorem as a witness
(`EulerSingularityWitness`: the datum's smoothness, periodicity and oddness, a maximal Euler solution in the sense
that no smooth solution continues it past `T`, the two divergent integrals as `= ⊤`, the bound on the velocity,
the vorticity at the origin tending to infinity, and the limits off the origin), and it proves beside it that the
zero flow is a solution, so the definition of a solution is one a flow can meet. The text holds no `sorry`, no
`axiom`, no `native_decide`, no `unsafe` and no `implemented_by`; two files run a command that collects the axioms
of every declaration of the package and fails on any beyond the three standard ones. The package's README says the theorem is proved with no hypothesis and that the formal proof
follows the manuscript as frozen on November 18, two days before the posted version, which revised one section.

## 3. The Navier–Stokes paper and what was read of it

`paper`. *Finite-time blow-up for the Navier–Stokes equations*, 79 pages (sha256
`4a01929b2f8a595637bbbe1dfef9724e5de768d31283d62415ce045e2ed69901`; repository commit
`ad53419de079eb8f95f60313473374624a348546`). It claims a smooth, compactly supported, divergence-free datum on
`ℝ³` and a smooth datum on the torus whose solutions with no force are smooth up to a finite time and blow up
there, with `‖∇u(t)‖_(L²)` between two multiples of `(T − t)^(−1/4)`. The proof has two parts:

- **Theorem 1.1.** If a profile exists, the blow-up follows. A profile is a smooth, nonzero solution `W(s, y)` of
  the equations in self-similar variables, `∂_s W + ½W + ½(y·∇)W − ΔW + (W·∇)W + ∇q = 0`, that repeats after a
  period `S` up to an isometry `R`, `W(s + S, y) = R·W(s, R⁻¹y)`, with `|W| ≤ C/(1 + |y|)`.
- **Theorem 7.1 with Appendix B.** A profile exists near a computed approximate one, if finitely many functions
  and numbers (a certificate) meet stated conditions, among them a bound for the equation linearized about the
  approximate profile.

`source-inspected`. The Lean package: 2,271 files and 616,060 lines, Lean 4.33.1 at the same Mathlib commit as
the zeta archive. It is laid out for a comparator: ten statement files hold the definitions and the theorems with
`sorry` for their proofs, `Solution.lean` proves them from the library `Breakdown/`, and a JSON file per pair
names the theorems and permits `propext`, `Quot.sound` and `Classical.choice` alone. The 24 uses of `sorry` are
all in the ten statement files. The library and the solution hold none, and no `axiom`, `native_decide`,
`unsafe`, `implemented_by`, `opaque`, `#eval`, tactic definition or elaborator code; the options set are a
heartbeat limit and, once, a recursion depth. The conclusions as stated:

```lean
def BreakdownOnSpace : Prop :=
  ∀ ν > 0, ∃ u₀ : Space → Space, ContDiff ℝ ∞ u₀ ∧ HasCompactSupport u₀ ∧
    (∀ x, divergenceAt u₀ x = 0) ∧
    ¬ ∃ (u : ℝ → Space → Space) (p : ℝ → Space → ℝ), IsSmoothSolution ν u₀ u p ∧
      ∃ C : ℝ, ∀ t ≥ 0, ∫⁻ x, ENNReal.ofReal (‖u t x‖ ^ 2) ≤ ENNReal.ofReal C

theorem breakdown_on_space (h : PeriodicSimilarityProfileExists) : BreakdownOnSpace
theorem breakdown_on_torus (h : PeriodicSimilarityProfileExists) : BreakdownOnTorus
```

The conclusion is a nonexistence, so `IsSmoothSolution` was read for a clause no flow could meet. It asks for the
momentum law at positive times, incompressibility, the datum, and joint smoothness on the closed half space, and
the zero flow meets it for the zero datum. The formal conclusion carries no rate and no convergence to the
profile, and the passage from "blows up" to "no global solution of bounded energy" is proved inside the library.
The further statement files derive the same two conclusions from a certificate, and from fifteen conditions on
finite data of seven kinds (`CellSystemCondition`).

`source-inspected`, from the repository's two README files. **What is not posted.** The package holds no data.
The certificate is named in the paper by its hash alone (`3f7a335b…b22c5`) and "will be released soon". That the
certificate meets the conditions is said to be verified by a computation in interval arithmetic at 128 bits,
which is not part of the formalization and not in the repository. The cell-layer statements and the proofs that
depend on them were patched on November 20 (one weight changed, one constant allowed to be zero, one set of
harmonics restricted), and the patched package "was not rebuilt when this repository was assembled". The Lean
came first and the paper was drawn from it and rewritten, so the formal proofs follow an earlier form of the
argument; the README lists thirteen differences between the formal certificate and the paper's.

So the posted material is an implication: finite data meeting the conditions gives the breakdown. Whether any
data meets them is the content of the unposted computation, and a set of conditions that nothing meets would make
the implication empty. The hash commits the authors to one certificate without showing it.

## 4. The public reading on the day, and the guesses

`reported`. Terence Tao's note of November 20 lists the three results in the order of how far each has been
digested: the Euler proof as readable and formalized; the Navier–Stokes paper as "technically human-readable",
its strategy "broadly clear" and "one of the expected paths", namely a numerically built approximate discretely
self-similar solution corrected by rigorous perturbation theory, with "more work" needed for "a proper,
professionally written proof"; and the zeta proof as Lean alone. No named reader had confirmed any of the three.

`agent-inferred`. Guesses, the first and the third as sent at 19:48 UTC and the second fixed in this record, each
scored when its receipt is public:

| Claim | Guess | What it rests on |
|---|---|---|
| The Euler theorem stands | 0.9 | a prose proof, a Lean proof with no hypothesis and a clean text, and a mechanism already used twice with a force and once without |
| The Navier–Stokes implication (profile, or finite data, gives breakdown) stands | 0.9 | a prose proof of standard kind (§5) and its Lean; the patch of the day was not rebuilt |
| Navier–Stokes breaks down with no force, as claimed | about 2 in 3 | the authors' record in computer-assisted blow-up, and the detail of what is described (§5); against it, the data and its check are not posted |

## 5. The Navier–Stokes method as its authors tell it

`paper`, with the older results `from training`.

- Leray's proposal of 1934 was a profile that does not change in self-similar variables. Nečas, Růžička and
  Šverák (1996) and Tsai (1998) showed there is none. The paper looks for the next thing: a profile that returns
  to itself after a step `S` of self-similar time `s = log(T/(T − t))`, possibly turned. In the original
  variables this is invariance under one scaling factor `e^(−S)` in time, `e^(−S/2)` in length.
- **Why any profile gives blow-up, whatever its spectrum.** The norm `‖∇u‖_(L²)` scales by `μ^(1/4)` under the
  equations' dilation, so the free flow in self-similar variables contracts it by `e^(−s/4)`. The terms that come
  from the profile add a compact operator over one period. So the flow linearized over a period has essential
  spectral radius at most `e^(−S/4) < 1`, and outside a disc of radius `Θ < 1` it has finitely many eigenvalues.
  Each is removed by a correction of the datum in a fixed space `E` of finite dimension (a Lyapunov–Perron
  argument over the periods). A contraction then finds, for every field near the profile's first slice, an
  element of `E` whose sum with it is the datum of a solution that converges to the profile. Cutting the slice
  off at a large radius gives compact support; a torus of large period and a Neumann series give the periodic
  case. The blow-up is stable in finite codimension, and its rate `(T − t)^(−1/4)` is the profile's and Leray's
  lower bound.
- **The computed profile.** It is not axisymmetric. It is invariant under the rotation by `2π/19` about the
  vertical axis and under the rotation by `π` about a horizontal axis; its period is about `0.36`; and an advance
  of `s` by half the period turns it by `π/19`. It holds two patterns that turn about the axis in opposite
  senses, each by `2π/19` in a period; the horizontal half-turn exchanges them, and every other harmonic is a
  product of one harmonic of each. Its vorticity is a column about the axis and, on each side of the horizontal
  plane, a layer that leaves the column in nineteen spiral arms ending in nineteen vortices. Far out the arms are
  logarithmic spirals whose phase, `2 log|y| − s`, is at rest in the original variables, which is why the field
  has a limit at the blow-up time at every point but the origin. The gradient's norm is of order `10⁴`, and the
  true profile is said to lie within `0.017` of an approximate one in that norm.
- **How it was found.** By continuation in a family of equations with a scaling parameter `g` (Navier–Stokes is
  `g = ½`), a viscosity and a force: from an axisymmetric steady state with swirl near `g = 0.502`, with rotating
  waves of azimuthal number 14 to 20 laid on it, the force brought to zero, the wave number carried as a real
  parameter and then brought to the integer 19, and Newton's method through nine discretizations. The paper gives
  no reason the number must be nineteen. Its note on the use of models says a simpler mechanism had first given
  blow-up for a slightly stronger dissipation, `(−Δ)^(501/500)`.

## 6. The Euler method as its authors tell it

`paper`, with the older results `from training`.

- **The building block** is Craik and Criminale's wave (1986): on a linear flow `U = D(t)x`, the field
  `D x + a(t)·F(k(t)·x)` with `a·k = 0` solves the Euler equations when `k′ = −Dᵀk` and
  `a′ = −Da + (2k·Da/|k|²)·k`. The wave vector is carried as a covector, the amplitude as a vector, and the
  pressure term is what keeps their pairing zero.
- **Amplification.** A new wave started across the shear `σ` of the one before, over an older gradient with two
  couplings `ν` and `η`, has amplitudes obeying `ȧ₁ = −2νa₂`, `ȧ₂ = −(σ − ν)a₁`: a growing mode at rate
  `√(2ν(σ − ν))` when `σ > ν`. The coupling `η` turns the wave vector and ends the growth; with `ε = η/ν` small
  the gain before the end is at least a multiple of `exp(ε^(−1/2))`.
- **The hand-off.** The paper says it in so many words: size alone does not determine the successor. The new
  wave must give the next one a large shear and a frame in which the older gradient again has the two couplings
  with a smaller ratio. The turning of the wave vector supplies that frame.
- **The tower.** Each step adds a localized wave at a frequency that is a large power of the one before, small in
  velocity when it starts. The growth intervals have a finite sum, and the vorticity at the origin grows without
  bound in that time while the velocity stays bounded.
- **The corrections.** Each step leaves errors, and with no force to absorb them they are removed by corrections
  that solve the linearized equations. In an amplifying flow a correction chosen by its start excites the
  growing modes. The paper prescribes the particles' final positions and solves for the initial velocity: a
  two-point problem along the flow, the Jacobi equation of Arnold's geodesic picture, whose quadratic form
  `∫∫ |ξ_t|² − ξ·Hξ` is at least `½‖ξ_t‖²` when the pressure Hessian `H` is at most the identity and the
  interval at most one. A wave profile whose slope has a narrow positive bump and a shallow negative part keeps
  the positive part of each wave's pressure Hessian small, and the sum of them under that bound.

## 7. The two methods read on the objects

Everything in this section is `agent-inferred`.

**7.1 The singular arrival is a cycle of the scale flow, read on the clock the tree had named.** The record of
October 9 (atlas `fluid.singularity-arrival-singular-aeon`) read a particle's arrival at a point singularity as
finite in physical time and unbounded on the navigator's log-ratio clock, with epochs accumulating at the
arrival. The paper's `s = log(T/(T − t))` is that clock, and its profile is periodic on it: the epochs are the
periods, each one scale step, and infinitely many of them fit before `T`. Leray's profile was a rest point of the
flow on that clock, and there is none. The claimed one is a cycle.

**7.2 The cycle is closed by a screw and a dyad.** Each of the two patterns is a screw in the pair (log time,
angle): a step of half a period with a turn of `π/19`. The horizontal half-turn is a dyad that maps one pattern to
the other, reversing the turn and keeping the step. That is the pairing of the tree's helical code, two strands
of opposite sense exchanged by a dyad (`helical.dihedral-frames`, `helical.duplex-passage`), and the relation
`USU = S⁻¹` holds on the angle's part; the step in log time is common to both strands, so the dihedral relation
does not extend to it. The products of one harmonic from each pattern are the duplex's contacts. This is also the
case the record of November 15 separated: under a change of scale a mode is a count or a turn. Scale alone leaves
no nonzero profile here, and scale with a turn leaves one.

**7.3 A finite key places the datum.** The stability argument uses one number, the scaling exponent `1/4` of the
gradient norm, and one fact, compactness. It does not locate the unstable directions; it counts them finite and
pays for each from a fixed finite space. On the objects this is the kernel and cokernel of a compression: the
flow toward the profile forgets every direction that contracts, and what it cannot forget is a finite cokernel
that the datum must cancel. The data that blow up this way form a surface of finite codimension near the profile.

**7.4 Energy does not decide, and the claimed profile shows the alternative.** Atlas
`ns.energy-count-cannot-decide` held that an equation with the same energy identity can blow up through a
coherent cascade and that what decides is whether the true triads' phases lock across scales. The profile is a
field whose harmonics form a lattice generated by two counter-turning patterns: phases locked at every scale by a
symmetry. The tree's conditional theorem of September 2
([the record](2026-09-02_STATEMENT_B_FOLLOWS_FROM_ANY_UNIFORM_COHERENCE_DEFECT_ALONG_A_TERMINAL_TAIL.md),
`statementB_of_coherenceDefectTail`) turns around under the claim: a solution that blows up on the torus has no
terminal tail with a uniformly bounded coherence defect (`ns.coherence-defect`), so its feeds interfere
constructively without bound. And `ns.triads-do-no-work` stands beside it untouched: the triads still return the
energy they move, which is the sense in which energy was never the reader of this question.

**7.5 The Euler construction is a tower of parametrons that hand on a frame.** The amplitude system of §6 is a
parametron past its bifurcation: the pump is the preceding wave's shear, one axis boosts and the other is
carried. The tree's nearest owner is `fluid.lift-up-transient` (`Physics/Fluid/LiftUp`), a shear whose response
grows for a time under a stable spectrum; here the spectrum itself has a growing mode while `σ > ν`. What the
tower teaches about towers is the hand-off: loudness does not compound by itself, and a level passes to the next
its strength together with a frame turned so that the next level's growing direction is open.

**7.6 In an amplifying flow a correction is fixed at its end.** Both papers place the datum by where the flow
must land: the Euler paper by a two-point problem with the final positions prescribed, the Navier–Stokes paper by
leaving the datum free in the finite space `E` and solving backward from decay at the blow-up time. Forward, the
problem is unstable; posed from its end, it is coercive. This is the shape of the paired return in the objects:
the navigator runs forward and its adjoint carries the covector back from the comparison.

**7.7 What the force was.** In the September results a force smooth up to the singular time absorbed the errors
of the construction. With no force the same errors must be cancelled by the flow's own datum, which is the whole
added work of the Euler paper and the reason the Navier–Stokes paper needs a profile that solves the equations
with nothing left over. On the objects a force is an exterior port, and the unforced claims are statements about
a region closing its own balance.

## 8. What the tree's Lean says under the claims

`tree`, with the bridges `agent-inferred`.

- `Fluid/NavierStokes:TheOfficialNavierStokesProblem` is `A ∨ B ∨ C ∨ D`. The paper's two conclusions give `C`
  and `D` with the force zero, and refute `A` and `B`, once a bridge between the two forms of statement is
  written. The forms differ in small ways that the bridge must carry: the tree's energy bound asks integrability
  and a strict bound where the paper's asks a bound on a lower integral; the tree's periodic solution asks a
  periodic pressure where the paper's nonexistence allows any pressure, which is the stronger nonexistence; and
  the tree's data conditions are Clay's decay conditions, which compact support meets. The bridge is a short
  module to write when the certificate is public, and it is the construction this record names.
- `statementB_of_coherenceDefectTail` and `officialProblem_of_coherenceDefectTail` give, in contrapositive, the
  unbounded coherence defect of §7.4.
- `ns.bkm-continuation` (`Fluid/NavierStokesCriticalVorticityRate`) gives that the critical vorticity receiver
  is not integrable up to the blow-up time on the torus.

None of this is discharged here. The tree's fluid lane was built toward `B` through conditional regularity, and
under the claim each of its conditions reads as a description of what a blow-up does.

## 9. What transfers and what does not

`agent-inferred`. Nothing here enters the machine and no part is ordered. The fluid apparatus stays in the
discipline. Three readings carry to the objects as statements to test, offered to the threads that own them:

- A level hands the next a frame with its strength (§7.5). A reading of a tower that reports a level's loudness
  and not the frame it leaves the next level reads half of the hand-off.
- A correction in an amplifying chain is posed from its end (§7.6).
- A recurrence in log scale with a turn is a mode in its own right, neither a rest point nor a growth (§7.2).

A second construction left to be made, small and independent of the claims: Craik and Criminale's wave as a Lean
lemma in the tree's fluid lane (the two ordinary equations give a solution, and `a·k = 0` is kept), beside
`fluid.moving-affine-cell-transport`.

## 10. Receipts

Read in a cloud container, with no build. The Euler paper was fetched from its address and both repositories were
cloned at one commit each and read without checkout of anything but their text; the counts are `find` and `wc`
over `.lean` files and the scans are `rg` for the tokens named in §2 and §3. Tao's note was read through a
fetch of its page. Times: the readings behind the gauge took seven minutes of wall time (19:41 to 19:48 UTC) and
the checks of names for this record about ten more; no run was projected because none was launched.

## 11. Atlas

Three rows enter with this record as owner:

- `ns.scale-cycle-screw-dyad` (`interpretation`): the profile equation, the bar on a rest point, and the claimed
  cycle with its screw and dyad.
- `ns.subcritical-contraction-finite-codimension` (`interpretation`): the exponent `1/4`, compactness, and the
  finite space of corrections.
- `fluid.craik-criminale-tower` (`proved-standard` for the wave; the tower is the paper's): the wave, its
  amplitude system and the hand-off of a frame.

Two rows take a note in their scope and keep their grades: `ns.official-alternatives` (the claims and what is
not posted) and `ns.energy-count-cannot-decide` (the claimed profile as a case of locked phases).
