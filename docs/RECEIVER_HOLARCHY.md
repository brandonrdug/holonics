# The receiving Holon: perspective, flux and compression

[project-postulate] Brandon's September 14 correction places the receiver inside the
construction. It is another Holon with a frame, material, current, internal state and possible
continuations. Its perspective determines an interaction and a face; it is not the human
viewing camera silently placed outside every mathematical diagram. This guide joins the
[computational Holon](HOLON.md), [field architecture](HNN_FORMULA.md),
[active stress faces](CONSTRAINT_MODES_AND_RECEIVER_FACES.md) and
[fluid construction](HOLONIC_FLUID_CONSTRUCTION.md). It specifies their common operation,
not another model owner or construction schedule.

[definition] The [foveation, spatial-audio and music synthesis](../research/records/2026-09-14_HEAR_THE_MUSIC_SITUATED_RELEASE_AND_SELF_MOTION.md)
connects receiver resolution, morphology-dependent transfer, self-motion and whole-section
predictive release. It recovers the chord class/performance distinction and gives a concrete
relative-motion equation and phase-sensitive receiving comparison.

[definition] The [Butler/Koestler comparison](../research/records/2026-09-14_BUTLER_KOESTLER_AND_HOLONIC_CONSTRUCTION.md)
recovers whole/part and receiving-role distinctions, the actual dependence in the CI octant table,
and typed projection/return requirements. Its independent connection and projected-step checks
separate a meaningful geometric proposal from its claimed proof. External invocation/covenant
rules do not replace the physical reception or native HNN contracts.

## The object, the receiving operation and the displayed face

[definition] A receiver is a role of a participating Holon H_R. In a declared contact C,

```text
I_C : (|H_S⟩,|H_R⟩) ↦ (|H_S'⟩,|H_R'⟩,F_R).
```

The receiving map `ρ_R` describes the face of that operation at its stated scope. It does
not replace H_R. An intensity, tensor contraction, file read, geometric projection or
normalized distribution is one possible face. The receiver's state and material determine
what it couples to, how it responds, and which other distinctions it could receive.
The same Holon can be a receiver at one interface and an emitter at another; nesting gives
the holarchy. No universal exterior or single privileged I/O axis is selected.

[definition] A field section `Ψ∈Γ(K,E)` can be continuous. Samples, finite coefficients,
factorizations and local jets represent restrictions of it. The generating relation and
its retained parameters/fibres determine further admissible evaluations. Neither the Holon
nor its receiver is exhausted by the particular points displayed. The original
`Foundation/Holon` occurrence/interface/receiver maps and preimage fibre already support
this distinction; the public tensor notation encapsulates its computational presentations.

[proved-derived] Let z=(x_S,x_R) be a local chart of the coupled state and let y=ρ(z,τ).
For differentiable trajectories, the chain rule gives

```text
ẏ = D_Sρ · F_S + D_Rρ · F_R + ∂_τρ.
```

The source and receiver rates include the actual interaction when it changes their states.
A prescribed receiver trajectory is a useful specialization with its motion supplied.
For a linear receiving chart this reduces to `ẏ=q̇x+qẋ`, already proved by
[ChangingReceiver](../formal/elementary-holonics/ElementaryHolonics/Transport/ChangingReceiver.lean).
Replacing the receiving Holon by a fixed row vector suppresses a term whenever that row
actually changes. Conversely, a fixed receiver map remains a valid stated specialization.

## A displayed body is a cut; its plates can be continuing bodies

[definition] A rendered frame is a present spatial/receiving cut of a world-tube and its
field sections. The chosen window can be bounded without establishing a physically closed
body or a definite value for every unobserved interior. An exposure may integrate a finite
interval rather than one instantaneous slice. The complete source retains its evolution,
incoming boundary conditions and relevant unobserved modes.

[definition] Brandon's subsequent plate-chain clarification makes the interface itself
active: a membrane/plate Σ(t) can carry surface charge, tangential current, material state,
deformation and its own internal modes. It participates as a Holon, receives from the
adjacent fields and conducts/emits into others. A smooth manifold is a local plate chart;
junctions, branching and singular contacts can require the existing stratified/cellular
description. Geometry supplies the incidence and metric; capacitance additionally requires
its constitutive storage–potential relation. A drawn surface alone does not specify C.

[proved-derived] For a moving volume with boundary velocity w, a conserved bulk density ρ
and laboratory current j obey the relative-flux balance

```text
d/dt ∫_(Ω(t)) ρ = −∫_(∂Ω(t)) (j−ρw)·n + ∫_(Ω(t)) source.
```

For a smooth membrane separating minus/plus bulk fields, normal n points from minus to plus.
Here ρ_± and j_± are charge densities and charge currents. With surface charge σ,
tangential conduction j_Σ and material derivative D_t^Σ,

```text
D_t^Σ σ + σ div_Σ w + div_Σ j_Σ
 = [(j_-−ρ_-w)−(j_+−ρ_+w)]·n.
```

These continuum identities use the actual moving surface/volume transport theorem. Surface
sources add their declared term. Under `σ=C_m V`, V the potential jump, the left side includes
`C_m D_t^Σ V + V D_t^Σ C_m + C_m V div_Σ w`. Its geometry/material and area terms are part of
the receiver's response. They cannot be removed by holding the rendered plate stationary.

[definition] For several coupled plates, capacitance is generally an operator from relative
potentials to stored charges, not one coefficient per drawn surface. In an isolated
electrostatic chart its common-potential direction is a gauge; grounded/reference charts
restrict that direction explicitly. The shared difference and normalization patterns are
reusable in attention, but the actual constitutive law decides the participation/current.

[proved-derived] In a lumped two-sided membrane restriction, `q=C V` and
`I=C V_dot+C_dot V+g V`. Its power identity is
`V I=d(CV²/2)/dt+gV²+C_dot V²/2`. The last term is exchange with changing geometry/material.
The existing port-energy and conducting-channel laws supply its inductive/current extension;
`HolonicMembraneActionTransport` and `ConstitutiveWorldTube` supply addressed membrane and
constitutive scope. The [exact symbolic join](../research/experiments/mfr_entropy_heat_current/moving_plate_and_burgers.json)
checks the lumped identity and a separating omission of `C_dot V`. It is not a calibrated
biological membrane or a proof of the full continuum surface law by finite algebra.

[definition] A context stack is usefully read as live nested causal couplings and continuations:
active ports, storage, current, phase, constraints and pending interactions. A call stack is
one restricted ordering; biological and field interactions can be cyclic, branched and
asynchronous. Their causal memory can reside in material, modes and an evolution kernel.
It does not prescribe a literal stack trace or archive of every past source. Eliminating an
interior produces the existing memory term `B U(t,s) C` and its initial-state contribution.
The retained state must realize those future boundary effects.

[proved-standard] The classical Hodgkin–Huxley membrane is a concrete biological
restriction: capacitive storage is coupled to ionic conductances whose states respond to
voltage and time. It illustrates an active receiving boundary rather than a passive viewing
plane. Its particular constitutive equations are not a universal HNN law.
[Original membrane-current construction](https://physoc.onlinelibrary.wiley.com/doi/10.1113/jphysiol.1952.sp004764).

## Perspective is a physical relation before it becomes screen coordinates

[definition] In a relativistic realization, the receiver has a world-tube χ_R and a
future-directed unit velocity U_R, `g(U_R,U_R)=−1`. Local spatial axes and a receiving face
normal belong to its tetrad. A photon has future null momentum k; its received energy is
`E_R=−g(k,U_R)`. With symmetric stress T, the receiver current and oriented flux are

```text
j_R^μ = −T^{μν} U_R,ν,
F_R = j_R^μ n_R,μ,
∇_μj_R^μ = −(∇_μT^{μν})U_R,ν − T^{μν}∇_μU_R,ν.
```

[proved-derived; formal-checked] The existing
[ObserverBoundaryCurrent](../formal/elementary-holonics/ElementaryHolonics/Physics/ObserverBoundaryCurrent.lean)
derives that divergence from its source jet and contracts the symmetric observer deformation
with T. Einstein/Bianchi supplies conserved stress under its field assumptions. The receiver
therefore participates through its trajectory, orientation and constitutive boundary, rather
than receiving an unexplained scalar energy or a canvas-normal arrow.

[definition] A local normal is meaningful relative to its metric and receiving surface.
Flux may also have tangent components. Vorticity, material twist, winding and connection
holonomy preclude assuming one globally perpendicular I/O direction. A rest-space foliation `U♭=a dt` requires `U♭∧dU♭=0`: expand
`a dt∧d(a dt)` and use `dt∧dt=0`. Such a foliation is an additional geometric condition,
not a property of every observer. Material/Frenet torsion is distinct from affine
connection torsion. Ordinary torsion-free GR still has curvature, vorticity and holonomy.

[definition] Geometric-optical rays follow the characteristic Hamiltonian of the declared
medium. In vacuum, `H(x,k)=g^{μν}(x)k_μk_ν/2=0`, with
`ẋ=∂_kH` and `k̇=−∂_xH`. A material dispersion relation replaces H when appropriate.
Ray/group direction and phase normal need not coincide in an anisotropic medium. Local
refraction, polarization and attenuation require that medium's constitutive map; drawing
an arc alone supplies none. Existing `HolonicSnellInteraction`, polarized transport and
receiver ray/conic/torus owners retain those source-qualified constructions.

[proved-derived] Coordinated recharting transports k, U, T, normals and dual receivers
together and preserves their contractions. Moving or rotating the physical receiver while
holding the source fixed generally changes its face. A rotated plotting camera is a third
operation, downstream of both. The September 12 directional-optics construction already
separates common state/analyzer transport from moving the analyzer relative to the state.
The moving-aperture control illustrates this distinction at a fixed source. It does not
represent the changing source field and was incorrectly presented as completing that synthesis.

## Induction includes the moving receiving surface

[definition] Fix orientation by writing the magnetic two-form as `β=ι_B vol` and electric
one-form as e=E♭. For the material flow χ_t with velocity v, pullback differentiation gives
`d(χ_t*β_t)/dt=χ_t*(∂_tβ+L_vβ)`. With `dβ=0`, `∂_tβ=−de` and Cartan's formula,

```text
d/dt ∫_(S_t) β = ∮_(∂S_t) (−e+ι_vβ),
EMF = ∮_(∂S_t) (e−ι_vβ) = −d/dt ∫_(S_t) β.
```

[proved-derived] Here `(ι_vβ)(w)=B·(v×w)=(B×v)·w`, so
`e−ι_vβ=(E+v×B)♭`. This sign depends on the stated contraction convention.
It retains the motional EMF even when the magnetic field has no explicit time change.
For a rectangle of width w and length L(t) in constant B_z, the moving right edge contributes
`−B_z w L̇`; its flux derivative is `B_z w L̇`. Rigid translation of a closed loop in the
same uniform field instead has cancelling edge contributions. Motion alone is not an
additional universal dissipation law. This is the conventional transported-flux construction;
see [Feynman, laws of induction](https://www.feynmanlectures.caltech.edu/II_17.html).

[proved-derived] The finite analogue keeps both changing field and changing face:

```text
r₁(B₁)−r₀(B₀) = r₀(ΔB)+Δr(B₀)+Δr(ΔB).
```

The last term is a genuine finite mixed difference. The existing
[discrete induction](../formal/elementary-holonics/ElementaryHolonics/Millennium/HolonicDiscreteInduction.lean)
retains oriented face circulation and the full EMF fibre on its fixed carrier. Moving-face
transport must supply the additional map; a new scalar flux label would not implement it.
The exact bilinear difference/pullback library now exposes the corresponding elementary
operations. The moving-continuum EM surface consumer remains a specific implementation join.

## Fractal dynamics are received through a changing family of cuts

[definition] Let Φ_(k,0) transport the complete source/receiver state and let A_k denote
the receiving event region at the kth admitted clock cut. Its first-arrival population is

```text
F_n = Φ_(n,0)⁻¹(A_n) \ union_(k<n) Φ_(k,0)⁻¹(A_k).
```

The nonlinear operation can stretch/fold these preimages into fractal boundaries. A receiver
changes which set is cut, and its state can also alter the operation through interaction.
A sampled basin image depicts evaluations of this construction; it does not replace its
full populations, parametric modes or unresolved interiors.

[proved-derived; formal-checked] The new `ClockedFirstArrival` join in
[HolonicRecurrentEcology](../formal/elementary-holonics/ElementaryHolonics/Computation/HolonicRecurrentEcology.lean)
uses the original autonomous first-arrival owner on `(x,k)↦(T_kx,k+1)`.
It proves the actual iterate `(evolution T k n x,k+n)` and then the first-hit/exclusion
identity for moving sets A_(k+n). An endogenous receiver belongs in x with its source
coupling. This does not require moving a physical receiver to preserve its old faces.

[definition] For a receiving partition P_(R,k), the observed history partition is
`join_(k<n) Φ_(k,0)⁻¹P_(R,k)`. Probabilities require a declared measure μ; its cell masses
are μ(B). The Shannon entropy of this partition, its refinement rate, a basin-boundary
dimension, phase-space dimension and heat production are distinct receivers of the same
underlying construction. A scale law or limiting dimension needs its actual family and
limit, not the number of plotted tiles. The [fluid synthesis](HOLONIC_FLUID_CONSTRUCTION.md)
retains harmonic modes and the source-specific spectral scaling relation.

## The calculus of entropy also contains receiver motion

[proved-derived] In a smooth flat chart, suppose a density obeys `∂_tρ+div J=s`, and a
receiving cell A_i(t) moves with boundary velocity v_i. For received mass
`m_i=∫_(A_i)ρ`, Reynolds transport gives

```text
ṁ_i = −∫_(∂A_i) (J−ρv_i)·n + ∫_(A_i) s.
```

This follows by adding the boundary-motion term to the density derivative and applying
the divergence theorem. The flux relative to the receiving boundary, rather than J alone,
determines the change in that cell's reading. On moving/curved geometry use the transported
density form, retaining the volume and connection contributions.

[proved-derived] An aperture may receive only part of the source. Its conditional
probabilities have `Z=Σm_i>0` and `p_i=m_i/Z`, so the quotient rule adds
`ṗ_i=(ṁ_i−p_i Ż)/Z`. The moving normalization cannot be omitted when the admitted
current changes. For a complete probability partition, Z=1 is the corresponding
specialization. The optical example normalizes the exact admitted current at every cut.

[proved-derived] On a fixed positive-support stratum with normalized p,

```text
H_R = −Σ_i p_i log p_i,       Ḣ_R = −Σ_i ṗ_i log p_i,
C(p,q) = −Σ_i p_i log q_i,
Ċ = −Σ_i ṗ_i log q_i − Σ_i p_i q̇_i/q_i.
```

The derivatives follow from the chain rule and `Σṗ_i=0`. Moving support boundaries use
their one-sided/measure transport rather than differentiating through an undefined log.
Both the measured distribution and its reference may change. The logarithms are their
normalized mode/ratio functions, not stored floating identities. Entropy changes induced
by a moving aperture do not establish physical entropy production. The existing
`TwoCellEntropyTransport` and current-balance owners derive production under their explicit
constitutive flux laws.

## Compression, storage and reconstruction are receiver-relative conduct

[definition] Let z contain the source, the relevant receiver state and any required shared
conditions. An encoding C admits decoder d_j and descended generator U_i when
`ρ_j=d_j C` and `C T_i=U_i C` for the admitted receiving/generating family. The retained
fibre describes differences behind the encoded face; it need not enumerate raw states.
The existing `CausalRelevance`, `GeneratorModeQuotient`, boundary-scale and receiver-history
owners provide these relations at their stated domains.

[proved-derived] Equality at one current receiver is insufficient if an admitted later
receiver or interaction separates the states. Conversely, a change in representational
coordinates with all compensating maps transported need not require more stored information.
This follows directly by composing the decoder and generator equations through a word.
Tolerance-based compression carries its actual propagated difference and receiver family.
It does not add a universal certainty condition before emitting a joint or unresolved face.

[definition] A drive write is a material interaction that changes the receiving device;
a subsequent read applies its codec and physical response. A saved file is a serialized
chart of the resulting state. A display similarly receives encoded material, generates an
optical field and participates in later reception. Their full physical laws differ, but
the common abstraction is the receiving Holon plus its interaction, frame, admissible
readouts and reconstruction. Neither a filename nor one measured voltage is that entire
object. Generator/constraint representations can retain the required consequences without
an event archive or perfect reconstruction of every earlier microscopic state.

## The concrete implementation and diagram return

[established-bounded; implemented-exact] `relational-geometry` now exposes
`project_receiver_point_rate` for its four existing projections and
`project_point_with_motion` through the declared source→receiver route. The latter computes
`p_R=Lp+b`, `ṗ_R=Lṗ+L̇p+ḃ`, then the actual projection derivative. The chart rates are
supplied kinematic operands; two frame snapshots alone do not determine them. The existing
receiver object remains a spatial chart, with the full participating material/current owned
by its containing construction. No new universal optional-field wrapper was added.

[established-bounded; implemented-exact] The existing `optical_receiver_frames` executable
now consumes that interface and `EnergyMomentum::photon/boost_x` to form the diagram's
65 exact proper-time cuts. Its receiver world-tube is

```text
χ_R(τ,u,v)=(γτ+γβu, γβτ+γu, v, 8),
β=3/5, γ=5/4, u²+v²≤4.
```

Its tangent time/spatial vectors have the correct Lorentz pairings. Three stationary null
ray currents intersect this moving aperture. Received packet energies are `4/5`, `20/13`
and `17/10` in E₀. The local spot rate is `du/dτ=−3/5`; accepted ray indices change from
{2,3} to {1,2,3} to {1}. The exact source driver retains momentum, frame, orientation,
intersections and conditional current weights. A fixed external viewing camera displays
these returns; it no longer supplies their I/O direction.

[definition] The ray example is a local Minkowski specialization with supplied inertial
motion and null-stress channels. The optical face and moving-aperture entropy are calculated;
the HNN's toroidal network is still an architectural schematic. It does not claim a curved
ray solution, calibrated photodetector response or completed native field/body assembly.
The full receiver material response, moving EM surface coupling and corresponding native
encoding consumers remain the actual integration work named by their equations above.

## Continuing-field correction

[definition] The [analytic flux construction](ANALYTIC_FLUX_AND_RECEIVING_BASINS.md) makes
the subsequent source/receiver synthesis explicit: `F_s v=-F-u_dot F_u` joins source change
to residual release, and `T^R_n=e_(n+1) T_n e_n^-1` carries the relative evolving field through
changing receiver charts. Its first-arrival populations use the actual partial generator and
moving receiving regions. Potential/phase one-forms, inverse-branch Jacobians and contour
periods supply analytic measurements; moving a view or measuring entropy alone supplies none
of those dynamics. The source guide separates coordinate reexpression from physical coupling.

[project-postulate] The fixed-ray example above is a local optical control. Brandon rejected
its use as the HNN field illustration because the field itself must continue relative to R.
The [replacement construction](../research/experiments/hnn_field_architecture/CONTINUING_FIELD.md)
evolves the complex currents, thermal modes and their common nonuniform material transport,
then reconstructs the full receiver volume. The geometric carriers and field are generated
from that same state. This corrects the omitted source-evolution contribution without claiming
that one supplied constitutive example completes the general HNN/physics synthesis.

## Landmarks constrain one continuing interior

[project-postulate] Brandon's September 15 horizon example poses an engineering construction:
use before, intermediate and contemporary observations to infer the dynamics of an incompletely
observed interior. Phase transitions are informative landmarks. The same question appears in
perception, recollection, inverse physical problems and HNN formation. It belongs to the shared
receiver/field objects, without prescribing a stored trace of every intermediate state.

[definition] Let Ω be an admitted family of possible evolutions, retaining the constitutive
laws, participating receivers, clocks, conservation constraints and phase-transition maps.
At landmark i, `p_i:Ω→X_i` reads its situated state and `ρ_i:X_i→Y_i` its observing face.
For available observation regions `O_i⊆Y_i`, the compatible family and a requested future face are

```text
F_I = ⋂_(i∈I) (ρ_i ∘ p_i)^(-1)(O_i)  ⊆ Ω,
Y_* = (ρ_* ∘ p_*)(F_I).
```

[definition] This is a joint pullback on one family. Correlations between landmarks travel
through Ω; independently matching three marginal observations does not construct their common
evolution. A deterministic realization can instead use transported states `p_i=Φ_i`, including
its parameters and receiver state in the common source. Relations and changing state spaces
remain available when a phase change is not expressed by one fixed global coordinate map.
The triad is a useful selected set of cuts, not a required three-step engine or global clock.

[proved-derived; source-inspected] Adding an intermediate constraint gives
`F_{0,1,2}⊆F_{0,2}`, hence `Y_*^{0,1,2}⊆Y_*^{0,2}`. This is the existing
[`ReceiverPotential.additional_observation_refines`](../formal/elementary-holonics/ElementaryHolonics/Transport/ReceiverPotential.lean)
construction on a product receiver; `image_receiver_restriction` covers source/target regions.
`outcomes_singleton_of_factor` supplies the useful stronger case: a future face can be uniquely
determined by the observations while the compatible source interior remains plural. The
existing shrinking-receiver theorem gives the corresponding convergence under its bounds.

[definition] “Inevitable” refers to a consequence forced throughout the applicable family.
Useful generation can also return a compatible face or a bounded family under its requested
conditions. Neither form requires claiming that all hidden microscopic history is recoverable.
An observation used at the contemporary cut need not have been available to a historical
prediction; the occurrence/receiver chronology retains that distinction.

[proved-derived; source-inspected] The existing
[`ReflectedBoundaryMemory.boundary_reduction_iff`](../formal/elementary-holonics/ElementaryHolonics/Physics/ReflectedBoundaryMemory.lean)
makes interior omission precise in a linear chart. For arbitrary boundary x and interior z,

```text
E_next(Ax+Bz)=U(Ex)  for all x,z
    iff  E_next A=U E  and  E_next B=0.
```

[definition] If the interior coupling contributes to an admitted future face, retain its modes,
joint constraints, memory law or bounded residual in the representation. A richer encoding can
carry that contribution economically. This specialization joins the general dynamic quotient
`q_next T=U q`; it does not impose boundary-only state on a nonlinear coupled field.
`ClockedSpan.comp`, `WorldTube` and `JointReceiverHistory.quotient` supply existing source,
clock, obstruction, interior/radiation and receiver-family owners for the same composition.

[definition] Conservation across these faces retains their orientations and actual material/
exchange laws. Shared boundary contributions join through the declared incidence and transport;
changing coarse charts carry their boundary-square defect when nonzero.
[`ExteriorBoundary.pullback_coboundary_defect`](../formal/elementary-holonics/ElementaryHolonics/Geometry/ExteriorBoundary.lean)
and the [active stress-face law](CONSTRAINT_MODES_AND_RECEIVER_FACES.md#the-overlap-has-stress-bearing-faces)
make those obligations explicit. An active plate stores and changes current, material and frame;
its receiving face is one projection of that continuing physical/mathematical construction.
