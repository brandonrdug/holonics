# Changing constitution and receivers share one defect calculus

**Date:** September 8, 2026, local time. **Inspection base:** `f6e9679d`.
**Return:** shared addressed receiver-defect and constitutive-pullback laws, instantiated by
changing-scale mechanical response and the existing nonlinear Galerkin fluid source.

## Authority and scope

[project-postulate] Brandon's latest correction makes the continuation a unification of patterns
already studied in specific instances. His exact wording is: “What you're describing is
unification and formalization of elementary patterns, no?” He then authorizes the first proposed
continuation. Source: local Codex root log
`~/.codex/sessions/2026/09/08/rollout-2026-09-08T16-00-58-01a08340-d28a-7350-836c-37918f573f77.jsonl`,
line 633, timestamp `2026-09-09T00:26:59.657Z` (September 8 in the operator's timezone).
The raw private log remains local.

[definition] This continues the [framework synthesis](2026-09-08_FORMAL_HOLONICS_IS_A_FRAMEWORK_OF_INTERACTING_TRANSPORT.md).
The constructions reuse addressed passages, receiver transformers, generator equivariance,
coupled incidence, constraint/prestress mechanics and the actual finite Navier–Stokes source.
It is a shared mathematical return with two instantiations, not four newly founded programmes.
The [framework guide](../../docs/FORMAL_FRAMEWORK.md) presents its meaning; the roadmap and
construction state retain their scheduling and position roles. The native AC1 session remains
separate; this review edits no Rust/CUDA implementation or model.

## The shared receiver difference

[definition] `Transport/ChangingReceiver.lean` defines

```text
defect(entering, returned, U; w) = returned(w) - U(entering(w)).
```

For an existing `AddressedPassage P : X <- Occurrence -> Y`, `passageDefect` applies the before
chart to `P.source` and the after chart to `P.target`. Both charts can change, the occurrence
population can be plural, and a proposed coarse operation need not be linear or invertible.
The existing `ReceiverTransformer` supplies the actual-range existence criterion, including the
full fibre. Its classical existence proof is not an executable decoder.

[proved-derived; formal-checked] Let P and Q join at the retained middle occurrence, with
charts q0, q1, q2 and proposed coarse operations U and V. `passageDefect_comp` proves

```text
r(Q ∘ P) = r(Q) + V(q1(target P)) - V(U(q0(source P))).
```

The middle equality is the actual pullback witness. For additive V,
`passageDefect_comp_additive` gives `r(Q ∘ P) = r(Q) + V(r(P))`.
`norm_passageDefect_comp_le` takes a later norm receiver under an explicit bound on V's finite
response. The signed, correlated return exists before that scalar bound.

[proved-derived; formal-checked] `changing_history_exact` permits different fine and coarse
carrier types at every natural-number cut, different charts at every cut and different local
transports. Commuting local squares and matched initial states imply matched received states
through the supplied complete histories. `word_defect_zero` recovers the existing fixed-chart
ordered-word theorem directly from generator equivariance. No new recurrence executor is defined.

[proved-derived; formal-checked] `opposite_translations_cancel` retains the same parameter d
through joined translations by d and -d. Each local defect may be nonzero; their composite defect
is zero for every d. This illustrates why a joint occurrence family should be composed before
independent magnitude bounds erase cancellations. It neither guarantees a cancellation for a
particular native error nor makes unknown causes exact.

## Moving receivers and constitutive geometry

[definition] For a differentiable real-linear receiver Q(t), fine rate F and proposed coarse
rate G, the differential-cut defect is

```text
r(x) = Qdot(x) + Q(F(x)) - G(Q(x)).
```

[proved-derived; formal-checked] `moving_receiver_rate` binds this expression to an actual
trajectory and differentiable chart:

```text
d/dt [Q(t)x(t)] = G(Q(t)x(t)) + r(x(t)).
```

The proof composes Mathlib's derivative of continuous-linear-map evaluation. The derivative of
the chart is retained; a receiver need not stay fixed while its source evolves.

[proved-derived; formal-checked] `Physics/ConstitutiveModulation.lean` now joins this same law to
the constitutive pullback. `potential_strain_first_variation` returns the actual derivative of a
potential through a strain chart. `stress_strain_rate_return` treats stress as a moving receiver
of strain rate and proves

```text
d/dt [stress(c(t))(cRate(t))]
  = stiffness(cVelocity)(cVelocity) + stress(c(t))(cAcceleration).
```

Its hypotheses supply the strain derivative, derivative of strain rate and actual derivative of
stress at the stated cut. When strainRate is the first strain derivative on the relevant
neighbourhood and stress is the potential differential, this is the material plus
geometric/prestress second variation. The pointwise theorem does not invent those neighbourhood
identifications. The existing exact finite `Bᵀ M B x` change remains standing.

## Mechanical instantiation

[definition] `Physics/ConformationResponse.lean` supplies a declared dimensionless transverse
strain chart with parameters a and k:

```text
c(x) = a + x²,       E(x) = k/2 (a+x²)²,
response(x) = 2 k x (a+x²).
```

The restoring direction in its finite update is the negative energy-gradient response. This is
a reduced mechanical constitutive model, not a calibrated protein, complete folded molecule or
new biological law. The existing `Rigidity` controls motivated recovery of the prestress term.

[proved-derived; formal-checked] Exact differentiation gives

```text
E''(x) = k(2x)² + 2k(a+x²).
```

At x=0 the strain's first derivative and the energy-gradient response vanish, while stiffness is
positive for positive k and a. The strain there is a, not zero. In
`Physics/MechanicalReceiver.lean`, `conformation_stiffness_joins_coupled_response` identifies the
first term with the existing `coupledResponse` for B=2x, M=k, tested on unit displacement. The
second term is the geometric/prestress contribution. This explicitly joins the existing owners.

[proved-derived; formal-checked] The declared finite Euler update

```text
T(x) = x - h response(x)
```

descends exactly through squared extension y=x² to
`U(y)=y(1-2hk(a+y))²`. The carrying displacement is an existing `BoundaryHolon`. With receiver
scales s and s' and s nonzero, the exact changing-chart operation is

```text
q_s(x) = s x²,       U_(s,s')(y) = s' U(y/s).
```

`updateHolon_defect_zero` returns the shared addressed defect at zero, and
`changing_mechanical_history_exact` applies the common history theorem to changing h, k, a and
nonzero scale at every cut. These are exact identities for the declared discrete step, not a
claim that Euler stepping equals the continuous flow.

[counterexample; formal-checked] `oriented_response_reopens_extension` exhibits the scope of that
compression: positive and negative nonzero configurations share squared extension while their
oriented responses differ. No transformer from squared extension to the full oriented response
exists under the declared positive-parameter hypotheses.

[counterexample; formal-checked] `exact_coarse_step_can_increase_energy` uses h=k=a=x=1.
Fine and coarse updates still agree, but energy changes from 2 to 50. Exact representation,
quotient descent, local positive stiffness and finite energy decrease are different statements.

## Nonlinear-fluid instantiation

[definition] `Physics/FluidReceiverClosure.lean` uses the existing
`NavierStokesFiniteGalerkinLocalPicard.finiteGalerkinNavierStokesVectorField` on its declared
finite Fourier carrier and aperture. The quadratic operator B is the actual finite
advective–Leray interaction. The theorem does not relabel an arbitrary polynomial as a fluid.
The existing finite local existence and source bounds retain their original scopes.

[definition] The identity is stated on the full finite complex coefficient carrier. A real-fluid
realization additionally retains conjugate symmetry, incompressibility, nonnegative viscosity
and an aperture covering its admitted convolution. The existing source definitions and their
physical-mode bridge keep those hypotheses; this theorem does not remove them.

[definition] Given a continuous real-linear receiver Q and an explicit lift J, put
`r=J(Qx)` and `z=x-r`. The proposed coarse rate is `G(y)=Q F(Jy)`.
If `Q.comp J=id`, `q_hiddenState_eq_zero` proves Qz=0. This is a section chosen for the declared
coarse comparison; z is retained and the section is not a recovered unique microscopic cause.

[proved-derived; formal-checked] The complete receiver defect of the actual Galerkin field is

```text
rateDefect = Qdot(x) + Q(Lz - B(z,r) - B(r,z) - B(z,z)),
```

where L is the existing diagonal viscous Stokes rate. Both mixed terms and the unresolved–unresolved
term survive. `moving_galerkin_receiver_equation` composes this identity with the shared moving
receiver theorem under actual chart/trajectory derivative hypotheses. Even at an identity
receiver/lift cut, `full_receiver_retains_chart_motion` retains Qdot(x).

[proved-derived; formal-checked] `norm_fluid_rateDefect_le` composes the existing finite
interaction cost C with the declared receiver norm:

```text
||rateDefect|| <= ||Qdot(x)|| + ||Q|| [ ||Lz|| + C(2||r||+||z||)||z|| ].
```

C is the existing actual carrier/aperture-dependent Galerkin interaction bound. The signed
three-term source remains primary. This supplies quantitative finite receiver control, with no
uniform continuum limit or prescribed cutoff implied by it.

[open] This is a full finite-carrier receiver equation with explicit feedback, not an autonomous
closure theorem for Qx alone. Eliminating z still owes its continuing generator or memory law,
and continuum/Galerkin-limit convergence requires its existing separate analytic obligations.
The theorem identifies exactly the contribution those further constructions must preserve.

## Native consequence and verification

[definition] The shared return supports three distinctions relevant to AC1: compose the actual
joint source before bounding its receiver; retain chart/constitutive change through the producing
maps; and establish the admitted future receiver after a morphology change. The mechanical
energy control also shows why correct local return and exact coarse representation do not supply
a finite stability theorem by themselves.

[definition] A declared finite numerical model law T and a reference unrounded law Tref are two
maps. Their discrepancy may be retained at a comparison receiver without turning a coefficient
which T defines exactly into an uncertain coefficient of T. The defect calculus does not mandate
one numerical realization or erase genuine source uncertainty. This distinction prevents the
formal synthesis from imposing an unnecessary enclosure law on the parallel native construction.

[established-bounded; process-audit] The primary complete check
`bash tools/lean_check.sh ElementaryHolonics` returned exit 0 with 9,960 build jobs. The focused
changing-receiver, constitutive-pullback and mechanical/fluid instance checks returned before
that integration. The final `bash tools/lean_check.sh` returned exit 0 with 3,985 jobs,
including the subsequently added quantitative fluid bound. The new declarations print only
subsets of the usual `propext`, `Classical.choice`, `Quot.sound`; `changing_history_exact` prints
no axioms. `git diff --check` passed. The
[verification receipt](2026-09-08_constitutive_unification/verification.txt) retains commands,
scopes and exact new-owner axiom output. Toolchain/dependency manifests are unchanged. No native
or unchanged-paper check was run for this formal change; the parallel session owns its native
work. No source, caches, user files or prior evidence were removed.
