# Reflected surface currents and fractal volume towers

**Date:** 2026-09-22. **Status:** research proposal with three bounded Lean returns; its external-majorant framing and numerical-plate description are superseded by [the exterior Holon correction](2026-09-22_THE_ESTIMATE_IS_A_RECEIVER_FACE_OF_THE_EXTERIOR_HOLON.md). These conditional constructions do not prove RH, Hodge, BSD or Navier–Stokes. **Source:** Brandon's request for surfaces and volumes induced by gyroparallelograms, integration by reflection, fractal continuation, and the microscopic/macroscopic ↔ local/global relation. This deposit is for Claude's iteration; it does not reorder the active construction campaign.

## One Holon and its dimensioned faces

Use the foundational port Holon H=(K,∂ₐ;Π;𝒟;𝓔;G;π): complex and incidence, flow/effort ports, power-neutral interconnection, constitution, generators, and scale restrictions. A state is a point on this law. An oriented k-cell is carried by a generator, paired with a coholon, and joined to other Holons at ports. Area and volume are readings of the same object, not new primitive objects.

For a parameterized two-cell X(u,v), the oriented blade B=∂ᵤX∧∂ᵥX and positive area element dA=√det((DX)ᵀG DX) du dv are distinct. More generally, the squared metric volume of v₁∧⋯∧vₖ is det(⟨vᵢ,vⱼ⟩_G), provided G is positive on their span. Sweeping a k-face through a transverse parameter yields (k+1)-volume with the Jacobian and side boundary retained. A gyroparallelogram supplies four vertices and ordered transports; it becomes an area element only after a tangent chart, metric and incidence/orientation map are supplied. Its two routes may differ by holonomy.

Existing exact footholds are Geometry/Gyrogroup.lean (completion), Millennium/HolonicInteractionExterior.lean (exterior-square minors and declared determinant-one volume), Geometry/ExteriorBoundary.lean (chain/cochain Stokes), research/experiments/contact_receiver_faces/ (exact rational oriented torus facets and area vectors), and Foundation/FractalPacking.lean (ordered rational restriction words). The general induced exterior metric and source-specific integration map remain a missing join. The July 18 hyperarea/sweep record already states the coarea principle.

## Three typed reflections

1. The RH same-height involution J(s)=1−conj(s) pairs zeros of the actual flowed completed-zeta source; the functional-equation map s↦1−s is distinct. RH/ConjugationEntire.lean owns the former symmetry.
2. Interior elimination returns a boundary effort/flow relation through a Schur complement Λ_DN for a specified linear Dirichlet problem. Sources and nonlinear hidden fibres retain volume defects. The exact diffusion engine uses C+τL with positive capacity, so its exit rows are sub-stochastic rather than bare harmonic measure.
3. Image sums and Poisson/theta reflection relate scales for their declared heat/lattice sources. A fractal-packing image sum is still a proposal; finite Cantor addresses do not ensure convergence.

None of these involutions gives positivity of an arbitrary cross term by symmetry alone.

## RH: a zero-current surface before an all-height bound

Let F_τ(s)=heatE(−τ,ξ,s), with coordinates (σ,t,τ). On the zero-free locus, the phase one-form a=(2π)⁻¹ Im(F⁻¹dF) is closed. Its circulation counts winding; distributionally da is the codimension-two zero current with multiplicity. An oriented two-surface S reads zero intersections by ∫_S da, and a three-region reads their boundary passage. RH/Winding.lean, RH/RectangleArgumentPrinciple.lean, RH/WeightedArgumentPrinciple.lean and RH/SimpleZeroCurve.lean own finite/local pieces. The distributional three-dimensional current and surface integration join are not yet formalized.

The new theorem in RH/FiniteZeroCurrent.lean separates the finite Foster comb into the same-height reflected partner and a surplus S_R, then proves for a locally simple zero:

  ||logDeriv g(z₀) − [1/(z₀−Jz₀)+S_R(z₀)]||
    ≤ 2 (|z₀−1/2|+δ/2) tailInvSq_Fτ(R).

It assumes distinct multiplicity-one partner membership in the chosen finite divisor, local factorization and disc inclusion. The actual anti-linear symmetry has not yet been joined to that divisor membership. RH/TransverseCurrentBound.lean supplies a pointwise normal-velocity inequality under ordered-root and tail hypotheses; the missing analytic content is a source-specific nonnegative or controlled surplus over an exhausted receiving family.

A genuine area law requires more than discrete zero points. For a *separately constructed* measurable positive gap field d(τ,η) on a height interval I of length L, let A(τ)=∫_I d(τ,η)dη. Assume differentiability under the integral, compatible root identity, no lost branch flux and d_τ≤−(1+a)/d almost everywhere with a≥0. Cauchy–Schwarz yields A′≤−(1+a)L²/A and hence A(T)²+2(1+a)L²T≤A(0)². The swept volume is ∫₀ᵀA(τ)dτ, with side and branching flux retained. This is a conditional derivation, not a theorem about ξ: its zeros are discrete and do not automatically provide a gap field at every height. A finite family of simple strands can instead use explicit receiver weights and a weighted transverse measure. The reflected-quartet heat-polynomial experiment has off-line zeros under the same local reflection/heat structure, so Stokes and winding alone cannot provide the sign.

**Experiment:** take the certified Euler–Maclaurin ζ jets in research/experiments/analytic_receiving_basins/, triangulate exact source squares, hatch interval-certified Re F and Im F level families, retain unresolved faces, and sweep only where continuation and multiplicity certificates hold. Measure reflected surplus and Foster tail on each admitted cell; failure of a uniform sign is an informative falsifier.

## Hodge: exterior periods and the correct cycle dimension

For a smooth projective complex n-fold, a codimension-p algebraic cycle has real dimension 2n−2p; its Poincaré dual is a degree-2p rational (p,p) class. A closed 2p-form has periods on *real 2p-cycles*. These complementary orientation readings must not be identified.

Foundation/HodgeReceiver.lean proves finite exact/coexact/harmonic splitting and harmonic/cohomology correspondence. Its new harmonic_transport_of_laplacian_intertwining theorem transports harmonic representatives under an equivalence that intertwines the declared Laplacians. Its new exact shear counterexample fixes the exact axis and cohomology class yet sends a harmonic vector outside the harmonic subspace: a cochain map alone does not transport preferred representatives. Millennium/HodgeOfficialReceiver.lean still owns the global analytification, decomposition and cycle-class interfaces. Finite area positivity cannot prove cycle-class surjectivity onto H²ᵖ(X,Q)∩Hᵖ,ᵖ.

**Next formal square:** define exterior-2p transport and period pairing under a chain map that preserves boundary, de Rham differential and a transported metric. Prove that fundamental class → Poincaré dual → harmonic representative agrees with cycle class → harmonic representative. Retain the rational Hodge cokernel without manufacturing a complement. Hodge–Riemann positivity needs an ample polarization and primitive/sign hypotheses; Millennium/PositiveForm.lean already supplies an effective class with negative self-square in an indefinite intersection form.

**Experiment:** hatch actual exterior-basis coefficients in a finite cochain complex including the proved shear, and show the harmonic representative move while its class pairing remains fixed. A purported global example requires an actual variety, cycle and period source.

## Euler and Navier–Stokes: flux two-form over a three-volume

For Lamb-current component c=Cᵢ, define Fᵢ=c u−ν∇c and βᵢ=ι_Fᵢ vol₃. On a smooth oriented cell,

  ∂ₜ(c vol₃)+dβᵢ=Sᵢ vol₃,
  d/dt ∫_Ω c vol₃ + ∫_∂Ω βᵢ = ∫_Ω Sᵢ vol₃.

The signed source includes stretching, pressure, mixed diffusion and forcing. Millennium/NavierStokesLambCurrentCell.lean formalizes the real-source balance on the unit cube on an open smooth slab. The new smoothSolutionOn_twoCell_sharedFace_gluing proves *conditional algebraic* cancellation of a common trace with opposite face orientations. It takes the two local balances as hypotheses. A physical translated-cell theorem still needs solution translation and translated-cube change of variables. Setting ν=0 yields the Euler specialization; complex u=a+ib requires the true split nonlinear terms and its indefinite Hermitian-energy cross term, so real-source positivity cannot be copied.

A gyroparallelogram can parameterize an oriented face, βᵢ contracts its area blade, and adjacent face fluxes cancel only under common trace and opposite orientation. Linear interior elimination uses the declared Λ_DN operator; nonlinear unresolved Galerkin stress is retained as an interior defect in Physics/FluidReceiverClosure.lean. The exact finite experiment research/experiments/mfr_lamb_current/ witnesses a generated Fourier mode outside the resolved cube.

The terminal tower is exact in Millennium/NavierStokesTerminalShellControl.lean: if canonical derivative shell masses mⱼ admit nonnegative Mⱼ with mⱼ≤Mⱼ and ΣMⱼ<∞, terminal control follows. The PDE has not produced Mⱼ. A proposed obligation is mⱼ≤C(Aⱼ+Vⱼ), with nonnegative face and volume readings and summable Σ(Aⱼ+Vⱼ). Signed boundary balance cannot substitute: NavierStokesCriticalCancellationObstruction.lean exhibits canceling dyadic returns with nonsummable absolute mass. The terminal trace is not included in the existing smooth-slab theorem.

**Experiment:** tile the finite Lamb leakage source with oriented faces, compute tangential hatch families and βᵢ contractions, compare joined boundary flux with direct volume source, then refine dyadically. Record signed flux and absolute/coercive mass separately.

## BSD: regulator as covolume, period as another receiver

Millennium/LocalFactor.lean and TraceSequence.lean own exact local factor and trace relations, not the global BSD leading term. On the Mordell–Weil free lattice with positive-definite Néron–Tate height pairing G and a basis P,

  Reg(E)=det(PᵀGP)=covol_G(P)².

Torsion remains separate. The real period Ω_E is an integral of a differential over a real cycle, a different receiver; Millennium/FamilyPeriod.lean has a source-specific period transformation. A common exterior-volume language organizes these operands but does not prove analytic continuation, rank, Sha, Tamagawa or the leading-coefficient equality.

## Microscopic/macroscopic and local/global as a descent cube

The two phrases share one categorical question: do restriction and gluing commute, and what defect is retained? They are independent coordinates. Grain restriction may lose internal modes within one region; spatial gluing can fail across a shared face at one grain; longitudinal generator transport adds time. The proposed cube has transverse towers, longitudinal tubes and spatial port joins. Its faces commute only under incidence, trace and constitutive hypotheses. Curvature, holonomy, hidden modes and incompatible boundaries are typed defects.

Foundation/FractalPacking.lean proves exact finite addressed similarity and separation, not an infinite analytic limit. Self-similar infinite structures can be central to this scale strategy, while global theorems in general do not logically require fractals. Here the actual limit obligations are compatible restrictions, controlled multiplicity/branching, domination or tightness, and summable defects.

## Figures and next joins

The four CeTZ/Fletcher vector figures are in research/papers/source/papers/categorical-holonics/figures/volume-flux-classes.typ; rendered SVG/PNG pages are research/papers/rendered/holon-volume-flux-{1,2,3,4}. Their cross-hatches are *oriented integration-coordinate families* with a displayed source form or metric. Projected crossings are not contact vertices.

Three replacement source-qualified plates are in research/papers/source/papers/categorical-holonics/figures/source-hatches.typ: rational subdivision for the exact Euler–Maclaurin ζ jet and certified receiving square, the exact rational Hodge shear, and symbolic real/imaginary normal flux from a divergence-free complex trigonometric generator. The earlier sampled numerical contour packets were deleted after Brandon's correction. The proposed certified ζ-jet contour hatch remains a distinct experiment.

Formal returns this session: RH/FiniteZeroCurrent.lean (finite reflected-current split and bounded local source join), Foundation/HodgeReceiver.lean (Laplacian-intertwined transport and exact shear obstruction), and Millennium/NavierStokesLambCurrentCell.lean (conditional shared-face cancellation). Each file passed a focused Lean compile. No conjecture endpoint follows.

Open joins, in order of specificity: (1) bind actual flowed-ξ reflection to its selected Foster divisor and bound surplus/tails uniformly while retaining multiple-zero events; (2) construct the exterior metric, integral and holonomy defect for actual gyrofaces, compatible with port power (issue #30); (3) bind Hodge period and cycle-class/PD interfaces with polarization; (4) derive physical translated-cell balances and a coercive terminal shell majorant; (5) connect BSD regulator and real period through one actual curve source; (6) pass an addressed fractal tower to an infinite current only with convergence and defect estimates.

Relevant tracked issues: [#30](https://github.com/brandonrdug/holonics/issues/30) requests the covariant port-Hamiltonian storage/flux connection; [#20](https://github.com/brandonrdug/holonics/issues/20) tracks per-eigenvalue Hodge-spectrum refinement; [#62](https://github.com/brandonrdug/holonics/issues/62) holds the remaining formal machine and relative-completeness joins. These issues are adjacent work containers, not evidence that the conjecture endpoints have been discharged.
