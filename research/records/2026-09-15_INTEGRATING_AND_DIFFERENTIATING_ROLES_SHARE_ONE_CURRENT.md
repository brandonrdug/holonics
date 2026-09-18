# Integrating and differentiating roles share one current

[project-postulate] During the shared-section Athena construction, Brandon supplied an AI-written
summary of maternal/paternal, integrating/differentiating and ecological-role imagery. He explicitly
kept it subordinate to continued construction and asked for rigorous synthesis with automata,
group characteristics, families, generators, homeostasis, heat and information flux. The role
language concerns situated operations; it does not assign intrinsic capacities to biological
sexes or require two internal engines.

## From the image to its actual maps

[interpretation] The useful common image is an organization which can concentrate and combine
influences, maintain a structure, resolve distinctions, explore permitted pathways and release
current. Several of those operations can occur simultaneously in different regions, modes or
receivers of one Holon. Their rates and coupling can change continuously or across a phase
boundary. A single line from “integration” to “differentiation” is one coarse view of this
multi-dimensional organization, not a proved exhaustive binary taxonomy.

[proved-standard; source-inspected] The ordinary thin-lens polarity in the pasted summary is
reversed: a convex lens of higher refractive index than its surroundings converges an initially
parallel bundle, while the corresponding concave lens diverges it. Reversing the source path
through the converging lens can instead collimate radiation from its focus. Geometry, medium,
incident field and receiving plane jointly determine the operation. [OpenStax, Thin Lenses](https://openstax.org/books/university-physics-volume-3/pages/2-4-thin-lenses).
The operative comparison should therefore use the actual ray/field map and its derivative.
Spatial/temporal integration and differentiation likewise cannot be assigned exclusively to
opposite archetypes: both coordinates can participate in either operation.

[established-bounded; source-inspected] A relevant biological source is Alim et al.'s
experimental/model study of Physarum. A localized nutrient stimulus was associated with a
propagating contraction-amplitude front; their model couples transport of a signal to the
flows that carry it. This is a useful example of transport and material response forming a
feedback mechanism within one organism. It does not establish the proposed universal archetypes.
[Mechanism of signal propagation in Physarum polycephalum](https://pmc.ncbi.nlm.nih.gov/articles/PMC5441820/).

## Generator-relative rate and conservation

[proved-derived] In a finite complex chart with differentiable Hermitian positive metric G(t),
let `x_dot=A(t)x+s(t)` and `E_G=x*Gx/2`. Direct differentiation gives

```text
E_dot = Re(x*G s) + x*(A*G+G A+G_dot)x/2.
```

The first term is the supplied source/port work at this receiver. The Hermitian form
`Sigma_G=A*G+G A+G_dot` measures source-free change of this quadratic reading. Its positive,
negative and null directions can coexist. A negative semidefinite form gives nonincrease of
this reading; zero gives conservation. This written identity is not claimed as a newly checked
Lean theorem or a universal thermodynamic interpretation of every quadratic metric.

[proved-derived] For a discrete transport T between two receiving metrics, the corresponding
source-free difference is `x*(T*G_next T-G)x/2`. A discrete reflection is not its own continuous
time generator. Under a constant invertible chart B, use `x'=Bx`, `A'=BAB^-1`,
`G'=B^-*GB^-1`; the rate form transforms by congruence. Keeping the metric, source and clock
with the operator makes the role meaningful across charts. An eigenvalue or scalar score
without those operands is insufficient to define it.

[proved-derived] Both steps check out by hand and both are recorded here so a later reader does
not redo them. Continuous: `2 E_dot = x_dot* G x + x* G_dot x + x* G x_dot`, and substituting
`x_dot = Ax + s` gives `x*(A*G + G A + G_dot)x + s*Gx + x*Gs`; since `G` is Hermitian,
`s*Gx = (x*Gs)^conj`, so that pair is `2 Re(x*Gs)`. Congruence: with `B` constant,
`Sigma_(G') = (BAB^-1)* B^-* G B^-1 + B^-* G B^-1 (BAB^-1) + B^-* G_dot B^-1
= B^-* (A*G + GA + G_dot) B^-1 = B^-* Sigma_G B^-1`, and `E_(G')(x') = E_G(x)`. The reading and
the form are therefore chart-independent up to congruence, which is the exact reason the
signature — not the eigenvalues of `A` — is the invariant content of the role.

[established-bounded; source-inspected] That invariant already has an exact executable owner and
the earlier draft of this record did not name it. `inertia.rs:597` `congruence(form, basis)`
computes `P^T A P` for invertible rational `P` and **refuses a singular `P` by name**, because
Sylvester's law is a statement about invertible change of basis; `inertia.rs:375` returns
`(n+, n0, n-)` by exact rational elimination. So "`Sigma_G`'s positive, negative and null
directions can coexist, and that coexistence survives a chart change" is not a hope — it is
`inertia(congruence(Sigma_G, B))` and it is exact. `inertia.rs:728` `pullback_inertia_bound`
answers the singular case instead of refusing it, returning `n+-(P^T A P) <= n+-(A)` together
with a basis of `ker P` — the directions a collapsing chart cannot see. A receiver that collapses
part of the current gets a bound and an exhibited kernel, not a silent relabeling.

### Homeostasis keeps storage, power and entropy at separate owners

[definition] Physical homeostasis additionally retains the actual storage, incoming/outgoing
power and dissipation laws, and each of those readings belongs to a different owner at a
different scope. Keep them separate:

- `Physics/PortEnergyHeat.lean:74` proves `d/dt(stored) = externalPortPower - ohmicHeat` for the
  two-coordinate capacitive/inductive port, from supplied trajectory derivatives rather than a
  postulated conservation axiom; `:50` proves the heat term nonnegative for nonnegative
  conductances, and `:122` adds `d/dt(stored + heat) = externalPortPower`.
- `Physics/TwoCellEntropyTransport.lean:22` proves `J(log a - log b) >= 0` and `:39` identifies it
  with `d/dt(entropy)` — **for two positive cells and one oriented flux**, with `:59` giving mass
  conservation on that same pair. The general graph statement `S' = sum_e J_e(log p_s - log p_t)`
  is **not** a repository theorem; it is the two-cell result summed by hand.
- `diffusion.rs` carries **no entropy reading at all**. `enact` at `:422` builds
  `J_e = kappa_e(phi_s - phi_t)` on the solved potential, `:439` accumulates the signed incidence
  transfer per node (`+` at target, `-` at source: this is the `1^T B = 0` cancellation realized
  exactly, not stated as an identity), and `:469` refuses any event whose total content fails
  `after - before - source = 0`. `:476` refuses a stored-energy increase under zero source, and
  `:499` refuses unless the complete pairing
  `E_after - E_before = source_work - conduction - implicit_step_defect` closes to exact zero.
  The receipt field at `:188` names the discipline itself: that decrease is
  "not constitutive heat alone", because the implicit step defect is a backward-Euler
  discretization term, not material friction.

A rise in one receiving intensity or a change in coarse information entropy is not, by itself,
heat production; the three owners above show why each such claim needs its own constitutive and
boundary data. The “pure integration must stagnate / pure differentiation must become chaos”
arrows in the pasted summary need a specified dynamical law before they imply stability outcomes.

### Should `Sigma_G` be formalized in Lean now

[definition] **No, and the deposit's original status was right.** Keep it as a written derivation
with a named home, for four reasons that are stronger than "it is unchecked":

1. There is no consuming owner. Nothing in the engine computes `Sigma_G`; the in-flight field
   work composes `R_D`, not a metric rate form. AGENTS.md requires choosing verification
   infrastructure from a concrete consuming mathematical or application requirement.
2. The useful content is already exact and executable elsewhere. The decision the identity would
   support — which directions of a receiver contract, expand or stay neutral, and whether that
   reading survives a chart change — is `inertia.rs`, in exact rationals, with a refusal for the
   singular case. A Lean restatement would add confidence about a formula nobody calls.
3. Its low-dimensional special cases are already discharged theorems.
   `Physics/PortEnergyHeat.lean:157` `hasDerivAt_changingCapacitiveEnergy` proves
   `d/dt[(1/2) k(t) q(t)^2] = (k q) q' + (1/2) k' q^2` — that second term **is** the `G_dot`
   contribution in one real coordinate — and `:74` gives the source-work-minus-dissipation split
   for a diagonal two-coordinate metric. What is missing is the general finite complex Hermitian
   statement, not the phenomenon.
4. Lean is exterior verification here and a new proof file forces a full build that this change
   does not otherwise require.

[definition] When a consumer does appear, the home is `Transport/ChangingReceiver.lean`, whose
`moving_receiver_rate` is already the moving-receiver product rule that
`Physics/ConstitutiveModulation.lean:229` `stress_strain_rate_return` consumes; `Sigma_G` is that
same family with a Hermitian form in place of a stress covector. Its exact hypotheses are: a
finite complex chart `C^n`; `G : R -> Matrix n n C` with `G t` Hermitian and positive definite and
`HasDerivAt G G' t`; `A : R -> Matrix n n C` and `s : R -> C^n` with `HasDerivAt x (A t *v x t + s t) t`;
conclusion `HasDerivAt (fun t => (x t)^* (G t) (x t) / 2)
(Re((x t)^* (G t) (s t)) + (x t)^* (A t ^* * G t + G t * A t + G' ) (x t) / 2) t`.
Positive definiteness of `G` is **not** needed for the identity — only for reading it as an
energy; Hermitian symmetry is what makes the two source terms combine into `2 Re`.

### The critical seam is the `Sigma_G = 0` case, with one hypothesis the slogan drops

[proved-derived] Set `G` constant, so `Sigma_G = A*G + GA`, and put `A = L - I/2`. Then
`A*G + GA = (L* - I/2)G + G(L - I/2) = L*G + GL - G`, so

```text
Sigma_G = 0   <=>   L*G + GL = G   <=>   A is G-skew.
```

`A` being `G`-skew with `G` positive definite means `G^(1/2) A G^(-1/2)` is skew-Hermitian, whose
spectrum is purely imaginary; hence every eigenvalue of `L = A + I/2` has `Re(lambda) = 1/2`.
That direction is unconditional.

[proved-derived; counterexample] **The converse is false as usually stated and must carry a
semisimplicity hypothesis.** "Every eigenvalue has `Re(lambda) = 1/2`" does not produce a positive
definite `G` with `Sigma_G = 0`. Take `A = [[i,1],[0,i]]`: both eigenvalues are `i`, so both
eigenvalues of `L = A + I/2` have real part `1/2`, yet `A` is not `G`-skew for any positive
definite `G`, because `G`-skewness makes `A` skew-Hermitian in the `G` inner product and therefore
unitarily diagonalizable, which a nontrivial Jordan block is not. The correct biconditional is:

```text
there exists positive definite G with A G-skew
  <=>  A is semisimple and its spectrum is purely imaginary,
  <=>  L = A + I/2 is semisimple and every eigenvalue has Re = 1/2.
```

with `G = S^-* S^-1` for any `S` diagonalizing `A`. Any role language that reads "neutral rate"
off a spectrum alone is dropping exactly this hypothesis; a defective generator can sit on the
seam spectrally and still have no conserving receiver.

[definition] The involution shapes do coincide, **after centering**, and this is worth stating
precisely because the uncentered forms look unrelated. `Millennium/Seam.lean:28` defines
`conjugateReflection s = 1 - conj(s)` and `:54` proves its fixed locus is exactly `Re(s) = 1/2`.
In real coordinates `s = (x,y)` that map is `(x,y) |-> (1-x, y)`, which is affine, not linear.
Centering at `c = 1/2` and writing `u = s - c` turns it into `u |-> (-u_1, u_2) = (2P - I)u` with
`P` the orthogonal projection onto the imaginary axis. So the centered conjugate reflection is
`J = 2P_+ - I`, algebraically the same species as `R_D = 2P_D - I` from
`HolonicConstitutiveCirculation.lean:393`: a self-adjoint involution whose fixed set is the range
of a projection. `Seam.lean` proves the fixed-locus statement but never writes it in `2P - I`
form, so the identification above is derivable and currently unformalized.

[definition] **Is the critical-seam rate theorem provable now? The algebra yes, the theorem no.**
The linear-algebra core — `Sigma_G = 0 <=> A G-skew => purely imaginary spectrum`, plus the
semisimple converse — is elementary, sits inside current Mathlib, and could be discharged in an
afternoon. It is not the critical-seam theorem. That would need an operator whose spectrum is the
zeta zeros, and the repository has none: a search of `formal/elementary-holonics/` returns no
Hilbert-Polya construction, and `Seam.lean`'s owner is an anti-linear involution on a single
complex variable, not an operator on a space of states. `Seam.lean:148`
`ThePlacementAndTheHandAreOneStatement` is itself carried as an explicitly unformalized bridge.
So the honest position is: **do not formalize either now.** Record the corrected biconditional,
record the centering that makes the two involutions the same shape, and treat the missing
spectral realization as the actual obstruction rather than as a gap in the rate algebra.

## A single field operation carries both orientations

[proved-standard] The constituted field uses a graph projection `P_D` and its Swing
`R_D = 2P_D - I`. `Computation/HolonicConstitutiveCirculation.lean:386` defines
`graphProjection D Dt Kinv (u,b) = (Kinv(u + D b), Dt Kinv(u + D b))`, `:393` defines
`graphScattering = 2 * graphProjection - id`, `:397` proves idempotence and `:408` proves
`R_D^2 = I` — each from the single displayed solve hypothesis `Kinv (I + D Dt) = id`, with no
metric assumed. `:415` identifies it with the `Millennium.Swing` owner.

[definition] `R_D* = R_D` is **not** among those theorems, and the file says so directly at
`:376`: "`Dt` becomes the energy adjoint in an orthogonal realization; idempotence and involution
need only the displayed solve identity. Arbitrary `D, Dt` do not imply norm conservation." So
self-adjointness and joint-norm conservation are a **declared realization condition** —
`Dt = D^T` under the unit pairing on `V x W`, `K = I + D D^T` — not a consequence of the Swing
form. The implementation below depends on that condition; state it wherever the Swing is reused
as its own adjoint.

[proved-derived] Worked one-port case, reproducible from the definitions above. Take
`V = W = R`, `D = 1/2`, `Dt = D^T = 1/2`, so `K = I + D D^T = 5/4` and `Kinv = 4/5`. Then

```text
P_D = [[4/5, 2/5], [2/5, 1/5]],        P_D^2 = P_D,   P_D^T = P_D,
R_D = 2 P_D - I = (1/5) [[3,4],[4,-3]],
R_D^T = R_D,   R_D^2 = (1/25)[[25,0],[0,25]] = I,
R_D (1,0) = (3/5,4/5),
R_D (3/5,4/5) = (1/5)(9/5+16/5, 12/5-12/5) = (1,0).
```

Both identities hold exactly in this chart: `R_D` is symmetric because `P_D` is, and
`P_D^T = P_D` here because `Dt = D^T` was chosen. The same map distributes a one-port input and
recombines the resulting two-port current. The squared shares change from `(1,0)` to
`(9/25,16/25)` and back, conserving their sum — the joint norm is conserved while the boundary
and interior receivers each gain and lose their individual shares. **That is the whole point:
the operator did not change its name between the two applications; the situation changed.**
The general graph identities belong to `Computation/HolonicConstitutiveCirculation.lean:374-446`
and the [fluid construction](../../docs/HOLONIC_FLUID_CONSTRUCTION.md).

[source-inspected] This is not an analogy about the active implementation; it is the same
operator, and the in-flight shared-section work was inspected to confirm it. The host owner
`field/junction/producer.rs` already writes both orientations as one formula:
`PairedJunctionLinearization::at` at `:207` returns
`outgoing = 2 Kinv(u + D b) - u`, `internal = 2 D^T Kinv(u + D b) - b`, and
`PairedJunctionLinearization::pullback` at `:258` returns
`source = 2 lambda - outgoing`, `incoming_internal = 2 R lambda - internal` with
`lambda = Kinv(outgoing + D internal)`. Forward and fixed-`D` pullback are literally
`R_D = 2P_D - I` applied to their respective arguments.

[source-inspected] The uncommitted device work carries that through rather than restating it.
`kernels/field_source_reflection.cuh` factors the arithmetic into one
`__device__ void field_source_apply(...)`, and all three entry points call it with the same
producing map `D`, the same material error bound and the same cached `factor`:
the scalar `section_field_source_reflection`, the shared-section forward
`section_field_source_reflection_section`, and the fixed-`D` adjoint
`section_field_source_reflection_joint_section`. The adjoint path differs only in passing
`trace = nullptr`; `operative_reflection_residual` still runs, so the residual certification is
**performed** on the adjoint path and merely not **recorded**. On the Rust side
`.../junction/operative/source/reflection.rs` gives `NativeFieldCurrentSource::reflect_section`
(forward, computing and caching the factor once) and
`NativeFieldReflectionSection::input_covectors` → `reflect_joint_section`, which reads the same
`self.source.reflection` cell and the same `_producing.map`/`_producing.bounds`. A masked output
comparison is formed by `record_field_target_residual_section` before the reflection pulls it
back, so its internal and other boundary contributions survive. The shared reaction material
then integrates the resulting complete source/target section through its existing normal
statistics.

[definition] The reuse is **licensed by `R_D* = R_D`**, which is the declared realization
condition above and not a proved Lean theorem. The certification inside the kernel checks the
normal solve against `D`; it does not check self-adjointness. If a future realization supplies a
`Dt` that is not the energy adjoint under the unit pairing, this path stops being the adjoint and
must fall back to an explicit transpose. `.../operative/source/tests.rs::reflection_section_shares_internal_source_and_fixed_d_pullback`
asserts exactly the reuse — section output row equals the scalar reflection of the same joint
input row, residuals agree, and the cached factor pointer is unchanged — and checks the covector
against the independent host `pullback` owner. It is `#[ignore]`d pending CUDA, so the claim is
implemented and cross-checked in source but **not measured**.

[interpretation] This is an actual operator composition, not a convention that every forward
pass is “maternal” or every adjoint “paternal.”

## Characteristics, families and automata

[definition] A family retains varying source conditions, material, incidence, receivers and
clocks together with its generators. Its characteristics are relations preserved or separated
under the admitted transformations: transported phase, winding/holonomy, incidence, null or
harmonic modes, covariance of a receiver, an energy-rate signature, or a stated applicability
condition. They need not be mutually exclusive labels. A harmonic mode can be observable;
calling it unresolved requires the actual receiver/future-family comparison.

[established-bounded; source-inspected] The construction owners through which a role can actually
be derived, transported and changed, each verified against source and stated at what it really
proves. None of them is a role; each is an operation a role is read off.

**Bilinear realization — one factor core, four orientations.**
`exact_linear/bilinear.rs:192` `BilinearProductCore` stores left forms `A`, right forms `B` and
their tensor image; `:243` `apply` returns `(Ax) (*) (Bz)` elementwise and `:384`
`BilinearRealization::apply` composes the receiver `D`, so the realized map is
`F(x,z) = D((Ax) (*) (Bz))` in exact rationals. `:250`/`:391` `differential` returns
`D(da (*) b + a (*) db)` and the doc comment states plainly that the mixed product `da (*) db` is
the **second-order remainder of a finite change**, deliberately excluded. `:268`/`:405`
`pullback` returns the two input covectors separately, before any metric identification.
`:423` `precompose_ports` restricts both inputs and **re-derives** the receiver family, allowing a
rank drop to expose new receiver freedom; `:448` `then_receiver` composes a new returned face and
re-derives the whole family including newly invisible directions; `:462` `then_fixed_right`
compiles a following bilinear stage into this core once its right port is fixed. What this proves:
concentration and separation are the *same* stored object read through different ports, and the
adjoint is a port choice, not a second mechanism.

**Structure group — order is the content, and the order-forgetting receiver is exhibited.**
`structure_group.rs:283` `close` builds the declared generator closure, refusing a generator that
leaves the carrier before any product is formed. `:521` `holonomy` is the ordered product
`prod a(e)^(+-1)` along a walk, with `:505` `across` enforcing `g(reverse) = g(edge)^-1` by construction so
a connection cannot hold two inconsistent directions. `:349` `is_abelian` is **measured, not
declared**. `:360` `commutator` carries the disagreement of two transports as a group element
rather than a flag, `:367` `commutator_subgroup` closes `[G,G]` by exhaustion, and `:571`
`curvature_commutator` returns `[H(sigma), H(tau)]` for two cycles. `:391` `abelianized_class` is
the `G/[G,G]` reading — **the receiver that forgets order** — and `:590` `separating_pairs` returns
exactly the cycles that abelianization identifies and the group separates, empty on an abelian
group by construction as its own control. `:405` `conjugacy_class` supplies the basepoint-free
invariant. What this proves: "which characteristics travel to another situation" is a computed,
falsifiable population, not an assigned label.

**Local jet — exact transport of a local generator.**
`leader_quadrature.rs:361` `LocalJet::rebase(sigma)` is the exact Taylor shift
`(T_sigma c)_k = sum_(m>=k) C(m,k) c_m sigma^(m-k)`, with Pascal-built `BigInt` binomials and
nothing dropped. `:344` `swept(span)` is the exact termwise antiderivative `int_0^span`, exact for
every span, so there is no error term to shrink. `:2297`
`rebase_is_an_exact_taylor_shift` verifies the shift against direct evaluation and, at `:2312`,
the composition law `T_tau T_sigma = T_(sigma+tau)` on rational shifts; `:2328` checks `swept`
against hand figures including a non-integral coefficient family. `:328`
`rebase_movement_depth` carries a stated theorem: a rank-`m` jet is annihilated by `Delta^m` and
by no lower order, so `m` is exactly when the transport stops being able to contribute a
difference. What this proves: integration (`swept`) and differentiation-order transport (`rebase`)
are two readings of one retained local object, and their composition is a group action.

**Constitutive modulation — the mixed term is why the two cannot be separated.**
`Physics/ConstitutiveModulation.lean:55` `coupledResponse_material_state_change` proves exactly

```text
R(M+dM, x+dx) - R(M,x) = R(M,dx) + R(dM,x) + R(dM,dx)
```

with incidence held fixed. `:31` `coupledResponse_finite_change` is the changing-incidence version:
the same difference plus **three** further terms, one for the changed incidence against the new
coupling, one for the changed coupling under the old incidence, and one for the changed incidence
inside the branch drop — "replacing every shifted factor by its predecessor would retain only a
tangent approximation". `:71` `tangent_cancellation_does_not_close_finite_response` is the
counterexample that makes this load-bearing: with `B = M = x = 1`, `dM = 1`, `dx = -1` the two
tangent contributions cancel to `0` while the mixed term and the true finite change are both `-1`.
What this proves: **integration and differentiation are not independent mechanisms and the pair
does not reduce to a tangent.** A first-order reading can report no change where the finite
response changed by its whole magnitude.

**Incidence conservation and heat/entropy flux.** See the homeostasis owners above:
`diffusion.rs:422/:439/:469/:476/:499` for oriented current, signed incidence transfer, exact
mass conservation, stored-energy monotonicity and the closed energy pairing;
`Physics/TwoCellEntropyTransport.lean:22/:39/:59` for entropy production, its derivative form and
mass conservation **on two cells**; `Physics/PortEnergyHeat.lean:50/:74/:122` for nonnegative
Ohmic heat and `dE_stored/dt = external port power - ohmic heat`. What this proves: conservation
is structural (it follows from the incidence cancelling, node by node), while dissipation and
entropy production are constitutive and each carry their own hypotheses.

**Hodge separation — the boundary-resolved part and the interior fibre.**
`sheaf_diffusion.rs:307` `hodge_laplacian` builds
`Delta_k = delta_(k-1) delta_(k-1)^T + delta_k^T delta_k` exactly from the cellular coboundary at
`:274`, and `:939` computes `harmonic_dimension = dim - rank(Delta_k)`, the exact null space, as a
retained certificate field rather than a diagnostic. Exact and coexact parts are what the two
boundary terms resolve; the harmonic kernel is what neither does, and
`Millennium/HilbertTransportChain.lean:170` carries the orthogonality of the exact and coexact
populations in the Hilbert reading. `Physics/FourTorusCurrentChart.lean:125` `current_decomposition`
gives the receiver-relative analogue — every rational current splits into its realized axis face
plus a residual, with `:129` proving the residual is exactly invisible to those cuts.
`inertia.rs:375/:597` supply the signature and its congruence behaviour. What this proves: "the
unresolved interior" is a computed dimension with an exhibited basis, not a placeholder — and
`FourTorusCurrentChart` shows that whether a mode is unresolved is **relative to the declared
receiver**, which is why a harmonic mode can be observable to a richer one.

**Energy, stress and physical release.**
`exact_linear/energy_momentum.rs:68` `pairing` and `:72` `invariant_square` give
`M^2 c^4 = E^2 - |cp|^2` in exact rationals; `:79` `boost_x` enforces the exact Lorentz constraint
`gamma^2(1 - beta^2) = 1` and refuses otherwise. `:135` `VacuumEnergyChart::read` returns
`u = (eps E^2 + B^2/mu)/2`, `S = (E x B)/mu` and the **computed** residual `c^2 u^2 - |S|^2`,
together with the two boost-invariant field scalars. **`c^2 u^2 - |S|^2 >= 0` is not proved here**:
`:226` and `:231` assert its nonnegativity on three sampled field pairs before and after a boost,
and `:233-238` checks the null case is exactly zero. `Physics/ReceiverStressEnergy.lean` is an
algebraic observer chart in fixed `(-,+,+,+)` components — `:130` expands the angular-current
divergence and `:157` shows it vanishes for a symmetric conserved tensor — and its own header
states that no manifold, field equation or constitutive identification is introduced. What this
proves: release has an exact invariant and an exact cone reading; the cone inequality itself is
currently instance-checked, not a theorem.

[definition] Naming rule for anything built on this. In mathematics and implementation use
`IntegratingLens`, `DifferentiatingLens`, `InvariantPart` and `TransverseDefect` — names that
say which operation is performed, on what, into which receiver. Maternal/paternal vocabulary
stays in philosophical explanation and never reaches a type, module, field, kernel or wire name.
A lens here is a declared source/medium/receiver triple, so the same object can be an
`IntegratingLens` for one receiving plane and a `DifferentiatingLens` for another; that is the
thin-lens correction above restated as an engineering constraint. `InvariantPart` and
`TransverseDefect` name the two returns of a separation — what survived the admitted transport
and what the receiver could not resolve — and are read from `harmonic_dimension`,
`separating_pairs`, `PullbackInertia::kernel` or `residual`, never assigned.

[interpretation] Hephaestus automata are specialized uses of this common machinery under
particular conditions and receivers. A search/traversal can expose alternatives; an inference
can restrict a compatible family; a synthesis can compose the result into reusable material;
an emission can participate in a subsequent interaction. One automaton can take several roles
as its situation changes, and several can share an operator or field. The organism/colony
analogy directs this coupled construction without fixing an agent class, sex, topology or
binary native scheduler. Future role inference should return the relevant operator/receiver
characteristics and conditions, rather than assign an archetypal name as intrinsic identity.
