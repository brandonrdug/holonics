# The moving frame returns the null fibre and the physical continuation

**Founded:** Brandon's 2026-09-04 request to combine Tao's singularity strategy, chart-relative
nullity, the RH line and the mathematical purpose of Holonics into a research strategy.
**Position:** MFR0 strategy deposited; Brandon subsequently activated this plan as the standing
mathematical goal. MFR1's scalar moving-frame/endpoint and MFR2's folded-source returns are
complete; MFR3's source-specific fluid concentration conditions are in progress.
**Authority:** [the roadmap](THE_ROADMAP.md) alone orders construction;
[the position](../../CONSTRUCTION_STATE.md) records completed work. The
[MFR1 record](../../research/records/2026-09-04_MFR1_THE_MOVING_FLUID_CHART_RETURNS_ITS_PDE_AND_ITS_PHYSICAL_ENDPOINT.md)
and [MFR2 record](../../research/records/2026-09-04_MFR2_THE_FOLDED_SOURCE_RETURNS_EVERY_HEAT_TIME_WITH_A_GAUSSIAN_REMAINDER_AND_ZERO_COUNT_RECEIVERS.md)
state their returned scopes. The
[MFR3 progress record](../../research/records/2026-09-04_MFR3_THE_PERIODIC_SOURCE_REJECTS_FIXED_PROFILES_AND_RETURNS_ITS_ENERGY_AND_COHERENT_FEEDS.md)
retains the first exclusions and controls; its
[continuation](../../research/records/2026-09-04_MFR3_THE_COHERENT_SOURCE_REACHES_A_PHYSICAL_FIELD_AND_THE_LOCAL_FRAME_RETURNS_ITS_FLUX.md)
returns physical reconstruction, local energy flux and a two-receiver modulated-core obstruction;
the [radial continuation](../../research/records/2026-09-05_MFR3_THE_AXIS_RETURNS_ITS_RADIAL_PRESSURE_JET_AND_THE_UNPAID_SWIRL_REMAINDER.md)
then constructs the first pressure correction of the replacement algebraic axis and retains its
unpaid swirl coefficient. The
[resonance return](../../research/records/2026-09-05_MFR3_THE_RESONANT_ROW_RETURNS_A_COMPATIBILITY_POLYNOMIAL_AND_TWO_AXIS_REPAIRS.md)
continues the finite rows, exposes their compatibility polynomial, and returns two repairs of
the first resonant row. The amplitude branch retains a free axial coefficient after mode 15.
The [analytic and circulation return](../../research/records/2026-09-05_MFR3_THE_ANALYTIC_INVERSE_RETAINS_ITS_RESONANCE_AND_THE_CIRCULATION_DEMANDS_AN_EXTERIOR.md)
then constructs its analytic inverse and homogeneous carrier, certifies a positive next
sensitivity, and derives the circulation condition that the actual exterior must respect.
Later phase requirements are not asserted as results. The concurrent HNP campaign continues.
**Grades:** per claim; written derivations, finite symbolic witnesses and kernel-checked returns
retain their separate scopes.

## 1. Purpose and the latest ruling

[project-postulate] Holonics is a mathematical framework and ontology for situated objects,
causal composition, information transport and physical realization. HNA is an executable
architecture within it. Mathematical investigation supplies reusable methods of constructing,
comparing and explaining systems, including learning systems, biological models and physical
phenomena. Its scope is not exhausted by the current neural product.

[historical] Brandon states in the founding message:

> Holonics has a reason for caring about the Millennium Problems, not just to solve them, but
> because we need to be able ot explain these things. We treat information as something physical.

> I do not feel as if any particular attempt you make is necessarily a "promised path" for a
> proof of any particular Millennium problem

[definition] The research return is an explicit construction, a counterexample narrowing its
domain, or a concrete unresolved relation with its attempted derivation retained. A terminal
Millennium proposition remains a legitimate research objective. An unknown route is reason to
investigate source structure; it is not an instruction to substitute known-theorem formalization
or suspend the line. Claims of success still require their actual mathematical returns.

## 2. What Tao's construction method asks us to locate

[historical; source-inspected] Tao's [September 3 thread, part 3](https://mathstodon.xyz/@tao/117207851360639348)
describes a search for a nearly self-similar profile, a small computed residual, stability in
renormalized coordinates, and a rigorous comparison of that residual with the stability
threshold. His expectation of Navier–Stokes blowup is a research judgment. This strategy does
not presuppose which answer is true. The original post and its five continuations were read
through the public Mastodon API; the supplied quotation agrees with those messages.

[proved-standard] Chen–Hou provide a concrete precedent: smooth finite-energy blowup for
axisymmetric Euler with a boundary, using weighted estimates and rigorous numerical control.
Their analysis separates a leading operator from a finite-rank correction, and the numerical
work verifies the constants needed for nonlinear stability. This is an Euler boundary problem;
it is not the constant-viscosity, boundary-free or periodic Navier–Stokes Millennium statement.
Sources: [analysis, v4](https://arxiv.org/abs/2210.07191v4),
[rigorous numerics, v3](https://arxiv.org/abs/2305.05660v3).

[definition] The desired object is consequently more than initial coefficients. It contains
the equation and domain, initial and boundary data, concentration geometry, moving coordinates,
physical clock, pressure/incompressibility constraints, complete residual, stability mechanism,
and an exact reconstruction of the resulting physical solution. A simulation becomes evidence
for existence only through the analytic passage that closes these relations.

## 3. The null is a transported fibre

[proved-derived] For a receiver `f : X → Y` into an additive group and a comparison value `c`,
the null of `q_c(x) = f(x) - c` is precisely `f⁻¹({c})`. Over `ℝ`, for `g(y) = y + 1`,
`(g ∘ f)⁻¹({0}) = f⁻¹({-1})`. With `f(x)=x`, Brandon's example is
`g(f(-1))=0`. This is the exact meaning of the coupled reference in that example.

[proved-derived; source-inspected] `Foundation/Holon.lean` already provides the general
construction: `Holon.PreimageFibre` retains the occurrences behind a face, and
`Holon.Rebase.preimageFibreEquiv` transports that entire fibre through commuting occurrence,
source, target and receiver equivalences. `Foundation/CausalNaturalHolon.lean` supplies
`mapPreimageFibre` for causal parameter transport, including noninvertible maps. A displayed
zero need not mean an empty source population.

[proved-standard] Three useful realizations preserve different extra structure:

| Receiver | Zero/singular passage | Structure retained |
|---|---|---|
| Analytic `f` near a zero of finite order `m≥1` | `1/f` has a pole of order `m`; `f'/f` has residue `m` | Punctured domain, order, contour and continuation |
| Finite-dimensional linear endomorphism `A` | `ker A` records null directions; invertibility fails at rank loss | Domain/codomain, kernel, cokernel and scale of the inverse |
| Lorentzian quadratic form `g(v,v)` | Its zero fibre is the null cone | Metric and frame transport; Lorentz changes preserve the geometric cone while changing its components |

[definition] A reference translation may move a displayed zero without changing differential
rank. Invertible linear rebasing preserves nullity. Reciprocal compactification sends an
unbounded amplitude to a zero boundary scale; its inverse does not extend as an ordinary
regular chart there. These distinctions make the coupling executable rather than weakening it.
The unknot likewise remains a nonempty embedded loop even when an isotopy-class receiver reads
the trivial knot: the returned equivalence must carry its permitted moves and embedding scope.

[proved-derived; source-inspected] The project already has an especially direct realization in
`Millennium/NavierStokesPhysicalH2ProjectiveTransportLength.lean`:
`ProjectiveTransportPreimageFibre.mode_eq_inv_smul` reconstructs a mode when the transport
scalar is nonzero; `singularProjectiveTransportPreimageOccurrence` retains every original mode
behind a zero transported carrier when that scalar is zero. This finite algebra does not by
itself assert that a physical solution diverges.

## 4. Blowup can be a regular trajectory reaching a singular reconstruction boundary

[proved-derived] The exact scalar model makes the clock explicit. For `a₀>0`,

```text
da/dt = a²,       a(t) = a₀/(1-a₀t),       T = 1/a₀,
r = 1/a,         dr/dt = -1,
t(s) = T(1-e^(-s)),   a(s) = a₀e^s,   r(s) = T e^(-s),   dt/ds = r(s).
```

The renormalized trajectory has infinite `s`-duration, the physical clock has finite total
duration, and the reciprocal tends to zero. This is one solution seen through related charts.
The scale's vanishing and the physical amplitude's divergence are joined by the inverse law;
relabeling the time axis alone would not establish either claim.

[definition] For a PDE realization, the corresponding construction owes

```text
t'(s) = b(s) > 0,       T = t(0) + ∫₀^∞ b(s) ds < ∞,
u(x,t(s)) = a(s) U((x-x*)/ell(s),s),       a(s), ell(s) > 0,
```

with an exact PDE pullback and an actual lower bound on a physical regularity receiver, for
example `‖∇u(t(s))‖∞ = (a/ell) ‖∇U(s)‖∞ → ∞`. Boundedness of `U` alone is insufficient;
it could vanish fast enough to cancel the scale. The witness must obstruct the declared physical
continuation: for example, growth on a fixed compact physical region contradicts a smooth
extension there. On an unbounded domain, a global norm also needs its appropriate continuation
theorem, so escape to spatial infinity is not silently treated as a finite-point singularity.
Initial smoothness, the admitted solution class, spatial tails, and compatibility with local
uniqueness must accompany the reconstruction. Initial data are then pulled back from a finite
renormalized time `s₀` by `u₀(x)=a(s₀)U((x-x*)/ell(s₀),s₀)`, with the complete domain and
boundary conditions, rather than inferred from a plot of the limiting profile.

## 5. The rescaled fluid law supplies testable conditions

[proved-derived] In a fixed-centre chart on `ℝ³`, take `p(x,t(s))=a(s)²P(y,s)` and
`b=ell/a`. The chain rule for unforced incompressible Navier–Stokes gives

```text
U_s + (U·∇_y)U + ∇_y P
  = [nu/(a ell)] Δ_y U + (ell_s/ell)(y·∇_y)U - (a_s/a)U,
div_y U = 0.
```

Thus viscosity is transported with the coefficient `nu/(a ell)`; it cannot disappear merely
because the observer zooms in. Moving centres add their translation current. Moving rotations
and anisotropic scales require the full matrix/Jacobian transport and its time derivative.

[proved-derived] For dimensionless `s`, take `a=a_* e^(αs)` and `ell=ell_* e^(-βs)`,
where the positive reference scales carry velocity and length units. With `α,β>0` and a
nondegenerate profile, the returns below suppress only these fixed reference factors. In
particular, `b=ell/a` has time units and `nu/(a ell)` is dimensionless.

| Quantity | Scale factor |
|---|---|
| Remaining physical time | proportional to `e^(-(α+β)s)` |
| Gradient / vorticity amplitude | `e^((α+β)s)` |
| Kinetic energy | `e^((2α-3β)s) ‖U(s)‖₂²` |
| Critical `L³` norm | `e^((α-β)s) ‖U(s)‖₃` |
| Rescaled viscosity | `nu e^((β-α)s)` |

[conditional] If the profile's `L²` norm stays bounded below, bounded physical energy requires
`2α≤3β`. If `α=β` and the profile's `L³` norm stays bounded, the physical `L³` norm stays
bounded and the standard critical regularity criterion rules out this as a finite-time blowup
of the corresponding smooth Navier–Stokes solution on `ℝ³`. See
[Tao's account of the critical criteria](https://terrytao.wordpress.com/2019/08/15/quantitative-bounds-for-critically-bounded-solutions-to-the-navier-stokes-equations/).

[interpretation] Under these profile assumptions, `β<α≤3β/2` is a scale regime that survives
these two elementary exclusions and has diminishing rescaled viscosity. It is a necessary
bookkeeping window for this proposed shape, not an existence result or an exhaustive
classification of blowup. The pressure equation, full energy/dissipation law, nonlocal coupling,
profile tails and nonlinear stability may exclude it. A core matched to an exterior has extra
boundary fluxes; it cannot borrow the global-profile calculation without carrying them.

[definition] The current formal fluid owners predominantly use a periodic domain. Dilation
changes its period: `u(x+k)=u(x)` becomes `U(y+k/ell)=U(y)`. MFR1 must carry the expanding
rescaled torus or an explicitly matched local core. Treating the profile as living on the same
unit torus after dilation would change the problem. The `ℝ³` calculation above is a derivation
target and comparison chart, not an undeclared replacement of those periodic owners.

## 6. Stability turns a residual into an exact solution

[definition] A candidate carries the momentum residual, divergence residual, pressure/boundary
defects, modulation equations, and spatial/time tails as oriented fields. Scalar norms are
derived receivers used in a declared existence estimate. The candidate and its linearization
must share the same morphology, boundary conditions and chart.

[conditional] One possible analytic closure is a perturbation inequality, after justified
modulation of symmetry modes,

```text
D⁺ e(s) ≤ -γ e(s) + C e(s)² + ε(s),     γ>0, C≥0,
sup_s ε(s) < γ r - C r²,                e(0)<r.
```

For a nonnegative continuous error receiver, `r>0`, and the stated upper-derivative comparison law, the strict
boundary inequality keeps the error inside the radius `r`. This must be joined to local
well-posedness and continuation in the chosen weighted space to produce a global renormalized
solution. It is not itself that well-posedness theorem. A posteriori fixed-point methods or
validated stable-manifold methods may provide a different closure if the linearization has
unstable directions. Those directions and the initial-data constraints must be constructed.

[definition] The stability margin comes from the actual operator estimate. A small residual
without that estimate proves no nearby exact solution. Eigenvalues alone do not bound a
nonnormal evolution; the weighted energy, resolvent or semigroup estimate must control the full
operator including nonlocal pressure and omitted modes. The physical clock and divergence
receiver of §4 must remain controlled under the admitted perturbation.

## 7. Exact existing owners and their integration boundary

[established-bounded; source-inspected] All paths below are under
`formal/elementary-holonics/ElementaryHolonics/`. Inspection used the live source; no fresh
fluid build is claimed by this design.

| Relation already returned | Owner / exact boundary |
|---|---|
| Occurrences, composition, fibre transport | `Foundation/Holon.lean`, `Foundation/CausalNaturalHolon.lean`; the primary carriers, reused rather than wrapped in a second ontology |
| Reciprocal Hodge transport on nonzero windows | `Millennium/NavierStokesReciprocalDifferenceRecurrence.lean`; denominator and retained successor window are explicit |
| Signed finite triad boundary/source identity | `Millennium/NavierStokesPhysicalH2ReciprocalClockRenormalization.lean`; positive viscosity, compact interior interval, finite aperture; its Stokes reciprocal is not the physical `dt/ds` of §4 |
| Moving Hermitian frame and zero crossings | `Millennium/NavierStokesPhysicalH2ProjectiveClockPayment.lean`, `NavierStokesPhysicalH2CombinedProjectiveOuterClock.lean`; derivative laws for the integrating scalar are supplied hypotheses |
| Singular fibre and its reconstruction | `Millennium/NavierStokesPhysicalH2ProjectiveTransportLength.lean`; nonzero-scalar inverse and complete zero-scalar fibre |
| Chronology on the zero fibre | `Millennium/NavierStokesPhysicalH2ProjectiveClockZeroSet.lean`; derivative zero almost everywhere, with isolated nonzero crossings retained pointwise |
| Compatible extension preserving the prior open solution | `Millennium/NavierStokesOpenLifespan.lean`; `CompatibleOpenPeriodicExtension`, `CanExtendCompatibly`, `IsMaximal`; later fields agree on the prior lifespan, with pressure compared modulo its time-dependent gauge |
| Conditional regularity route | `Millennium/NavierStokesEleventhMomentCompactBound.lean`; `officialProblem_of_coherenceDefectOnly` consumes the unproved universal `CoherenceDefectOnly` bound |

[proved-derived; formal-checked] MFR1 now supplies the source-bound dynamic scalar rescaling and
physical-clock/endpoint theorem through `NavierStokesRescalingSpace`,
`NavierStokesDynamicRescaling`, `NavierStokesRescalingClock` and
`NavierStokesRescalingEndpoint`. Its full source equation, transported domain and sufficient
continuation obstruction are stated in the linked record.

[open] An actual residual/stability construction or actual terminal continuation bound remains.
The existing scalar-transport product rule does not construct its assumed integrating scalar.
The earlier `extension_or_controlledTerminalObstruction` is a logical alternative, not a proof
that the extension branch holds. `CanonicalTerminalMajorantReceipt` is a sufficient-control
interface; failure to construct one is not a blowup witness.

[definition] The coherence-defect route supplies a useful opposing test. Evaluate its complete
modal relation on a proposed concentrating family. A universal proof would supply the existing
regularity endpoint. A counterexample to that sufficient bound would narrow that route but
would not, without the reconstruction/stability argument, prove physical blowup. Neither sign
is selected by the ontology in advance.

## 8. RH uses the same methodology with its own source relation

[proved-derived; source-inspected] `RH/CriticalChart.lean` and `RH/DeBruijnSeal.lean` identify
Mathlib's RH with `Λstd=0`, where `Λstd=4Λ_DN`. `RH/DescentZeros.lean` proves nonnegativity by
the Dobner route. `RH/FosterClassHeatFlow.lean` discharges the entire-flow principal-value
zero-dynamics port. A structure declaration in `PhaseFlowLedger` does not revoke that theorem.

[proved-derived; formal-checked] MFR2 has returned the folded source construction, its
Gaussian remainder, integral derivatives and zero-count receivers. After applying the full theta reflection, standard

```text
H_t(z) = Σ_(n≥1) ∫₀^∞ exp(tu²) φ_n(u) cos(zu) du,
φ_n(u) = (2π²n⁴exp(9u)-3πn²exp(5u)) exp(-πn²exp(4u)).
```

For `u≥0`, `|t|≤T`, `|Im z|≤R`, the integrand's norm is at most

```text
2π² n⁴ exp(-πn²/2) · exp(Tu²+(R+9)u-πexp(4u)/2).
```

The first factor is summable and the second integrable. Splitting another Gaussian factor
gives a cutoff bound `C_(T,R) exp(-π(N+1)²/4)` for the tail `n>N`. Thus the folded representation
has compact-uniform convergence at every real time. This does not contradict
`FlowedExplicitFormula.not_integrable_flowedTerm`: those are individual whole-line event
integrals, and reflection was applied here to the assembled source before its new decomposition.
The standard kernel is documented in [Rodgers–Tao](https://arxiv.org/abs/1801.05914).

[counterexample] The complex zero velocity `2Σ 1/(z_j-z_k)` is not ordinary Euclidean Coulomb
descent away from the real axis: the Euclidean gradient conjugates the denominator.
`z²+1-2t` moves its imaginary roots inward. The September 3 flow-reading prose's unqualified
complex gradient assertion is corrected by this example; the actual complex ODE remains valid.

[interpretation] The next RH question is which source relation controls the full signed
interaction, with the reflected source and its tail now available in the needed direction.
The existing written shorting construction
`research/papers/source/mathematics/theorems/conditioned-effective-tension.typ` identifies
`S=D-C* A⁻¹ C` as the source's remaining form after old-interior relaxation, under its strict
old-gap/domain hypotheses. Its positivity is a candidate arithmetic target, not a consequence
of calling the system passive. `RH/GlobalWeilFinishLine.lean` retains the additional global
explicit-formula, convergence and complete-separator obligations. A zero old gap requires
the appropriate range/kernel shorting law, not division by zero.

## 9. Construction order

[definition] Brandon's subsequent instruction activates this strategy as the standing goal.
The roadmap carries the next construction; phase entries below specify required returns rather
than asserting they have already been produced. MFR1 and MFR2 have independent mathematical owners;
neither is a prerequisite to the other's first lemma.

| Phase | Required return | Failure that changes the next attempt |
|---|---|---|
| **MFR0 — strategy** | This source-grounded design, scope correction, exact scale/clock derivations and retained counterexamples | A missing owner or invalid calculation must be repaired in the design |
| **MFR1 — fluid rescaling and endpoint** | Compose `OpenPeriodicSolutionOn` with the moving scalar/matrix chart and physical clock; derive the actual normalized PDE, period/pressure transport, inverse-domain law, and sufficient finite-time divergence receiver | An omitted Jacobian, zero fibre, boundary current, or uncontrolled clock falsifies the proposed transport; no new wrapper may conceal the missing law |
| **MFR2 — folded RH source** | Extend the existing kernel/event owners with the half-line all-time expansion, compact-uniform remainder, then justified derivative/zero-count receivers | A failed integrable majorant or missing reflection/limit interchange narrows the decomposition; the whole-line divergence theorem remains standing |
| **MFR3 — locating admissible fluid conditions** | Use MFR1 to derive source-specific exclusions and surviving modulated families; instantiate the actual pressure/triad and coherence-defect relation before numerical search | Energy/viscosity/critical-norm conflict or wrong periodicity rejects the family with the violated equation retained |
| **MFR4 — residual and stability** | One specified family, approximate profile and complete residual, quantitative linear/nonlinear control, then an exact solution and physical endpoint if the stability threshold closes | Return the actual unstable mode, tail, pressure coupling or residual term; repair the family at that relation |
| **MFR5 — arithmetic sign** | Use MFR2 to derive a source-specific positive form or a separating negative direction; compose a returned positivity theorem with the complete Weil or Foster passage | An unsigned cross term, unresolved range condition, or absent global limit is the next analytic task |

[definition] MFR1 returned the varying scalar length/amplitude chart with a moving centre.
MFR2 returned its folded source, uniform remainder, derivatives and retained zero-count passage.
MFR3 is the current construction. The later ansatz and sign phases are adaptive
research: their models and estimates are determined by the preceding source returns. They do
not authorize an unbounded simulation, a new general search subsystem, or a claimed solution
assembled from assumed stability/positivity fields.

[proved-derived; formal-checked] MFR3's first return excludes a nonzero globally stationary
exponential profile using actual periodicity and pressure; binds the energy exponent condition
to an actual unforced solution; constructs a decaying shear with zero coherence defect; and
returns a complete finite coherent coefficient population. Its absent output coefficient has a
nonzero nonlinear source, and its third-component coherence inequality requires `kappa>=1`.

[proved-derived; formal-checked] MFR3's continuation reconstructs the smooth coherent initial
field and its actual nonlinear source, including initial-time Fourier continuity and a positive
interior time in an actual local solution where the projected nonlinear component is nonzero.
The actual moving-frame energy law now retains local pressure, viscous, frame and boundary flux.

[proved-derived; formal-checked] The replacement positive algebraic axis now has an actual
smooth strain, Cartesian residual/pressure laws and a first radial pressure correction with a
genuine derivative at the zero transport axis. The affine-radial profile has no smooth pressure
completion; matching its first swirl correction leaves a strictly positive quadratic coefficient.

[proved-derived; formal-checked] The actual reciprocal axis now conjugates the linear swirl
operator to dilation transport. Its differentiated zero-axis relation retains both the resonant
source condition and the free homogeneous coefficient. The explicit compatibility polynomial
has a kernel-checked interior positive root and a corresponding positive amplitude.
A smooth positive perturbation of the
axis changes its 30th derivative while preserving lower derivatives and its relative tail.

[established-bounded; computational-witness] In the explicit reflection class at
`alpha=3/2,beta=1,p=5/2`, the first resonant row gives a degree-14 polynomial in squared swirl
strength. Its unique positive root closes the retained finite pressure/swirl rows through mode
15. The mode-15 pressure relation determines the previous free swirl coefficient and retains
the new axial coefficient. Independently, the 30th-axis-coefficient perturbation closes all
retained rows through mode 14. The resonance record states exact Taylor budgets and receipts.

[proved-derived; formal-checked] The scalar critical inverse now preserves the admitted
source-series radius, returns the exact resonant projection and retains its homogeneous fibre.
Its real restriction composes with the actual fluid axis. Axial transport constructs the mode-15
homogeneous profile. The explicit mode-28 sensitivity polynomial is positive throughout the
amplitude bracket. Actual angular momentum has a finite incoming-history bound and a source
threshold for a compact complete past.

[established-bounded; computational-witness] Linearizing the actual source in the retained
axial coefficient gives the complete next swirl residual `R(X)z^4`, with all other retained
linearized rows zero. Its positive slope makes that coefficient effective at the next affine
row. The full constant forcing of that row has not yet returned.

[open] MFR3 remains in progress. Return that constant forcing and the nonlinear source bounds
needed for radial convergence, keeping subsequent compatibility conditions and free fibres.
Construct the actual periodic exterior and profile time current that carry the circulation:
a globally sublinear stationary axisymmetric completion with the current nonzero swirl is
excluded by the stated backward-history argument. Viscosity and stability remain part of the
surviving-family construction. The complete return is unfinished.

## 10. Return into the wider framework and verification

[interpretation] A successful mathematical operation becomes reusable material when its source,
chart, hypotheses, full defect, successor and reconstruction can participate in another problem.
A biological or learned system can reuse the frame, residual or continuation method after its
own constitutive mapping is supplied. This is how the mathematical framework can improve the
construction of learning systems, while those systems can assist the next investigation.
The source-specific PDE or arithmetic inequality is the part that does not transfer for free.

[project-postulate] Treating information as physical makes locality, admissible transport,
storage, boundary flux and chronology productive questions for research. Physical instantiations
retain calibrated units and constitutive laws. The objective is a growing body of explanations
and executable methods whose derivations and unsuccessful alternatives remain recoverable.
Preserve candidate ancestry and the equation that rejected it in existing research records and
Provenance, not merely a terminal proof or a scalar success score.

[established-bounded; computational-witness] MFR0's exact symbolic check returned the normalized
PDE chain-rule coefficients with `b=ell/a`, the Riccati/reciprocal clock identities, all five
exponential scale factors and their finite clock integral, and the complex logarithmic-flow
identity on `H=z²+1−2t`. This checks the displayed algebra, not PDE existence or the analytic
estimates.

[definition] MFR0 verification is source/derivation review and focused documentation inspection.
No Lean source or imports changed in MFR0. Each later formal phase builds its affected owner
and checks the actual assumptions; each numerical phase validates residual, truncation and
stability bounds appropriate to its receiver. A finite simulation is never a continuum limit.
HNP's concurrent runtime changes and receipts remain owned by that campaign.
