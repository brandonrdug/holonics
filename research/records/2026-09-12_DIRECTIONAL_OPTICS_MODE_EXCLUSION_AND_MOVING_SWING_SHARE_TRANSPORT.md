# Directional optics, mode exclusion and moving Swing share transport

[project-postulate] Brandon's September 12 message connects directional bra-ket notation,
polarization, Pauli exclusion, moving fluid boundaries, frame-dependent invariants and physical
emulation with the generator/information programme. Direct source:
`msg_01a0964a-d841-76d3-80ec-cde52f9339c3`, `2026-09-12T15:44:42.561Z`, line 644 of
`/home/b/.codex/sessions/2026/09/12/rollout-2026-09-12T07-07-56-01a095f2-3f4f-7012-a914-f4fb5c419fa5.jsonl`.
The clarification is that a contemporary invariant or held boundary can itself vary along the
physical development, and a changed frame can transfer where that variation is represented.

## Source reading and access

[established-bounded; source-inspected] The requested references were retrieved at the following
scopes. Publisher access failures were not treated as permission to bypass access controls;
public author preprints and indexed publisher abstracts supplied the indicated alternatives.

| Requested reference | Identified content and read scope |
|---|---|
| [Goldberg et al., Quantum concepts in optical polarization](https://opg.optica.org/aop/abstract.cfm?uri=aop-13-1-1) | Publisher abstract and public [author preprint, §§2–3 and polarization measures](https://arxiv.org/html/2011.03979v1): Jones/coherency/Stokes maps, SU(2)/SL(2,C), Fock sectors and higher moments. |
| [Kim, Björk and Kim, Experimental characterization of quantum polarization of three-photon states](https://arxiv.org/html/1706.07755v1) | Theory and analysis of prepared states distinguished by first-, second- and third-order polarization moments. |
| [ZeroTheHero's answer](https://physics.stackexchange.com/a/397741) | Read the requested answer, including its double-arrow and diagonal-arrow density decomposition, coherent ket and Malus calculation. It is an answer to question 397451; 397741 identifies the answer. |
| [Maták, Unitarity, the optical theorem, and the Pauli exclusion principle](https://arxiv.org/html/2509.26612v3) | Read v3, revised April 30, 2026; the earlier v1 title was The Pauli exclusion principle from the optical theorem. The cancellation concerns interference terms in a fermionic scattering model. |
| [Li, The S-matrix conjecture](https://arxiv.org/html/2608.29750v1) | Abstract, main theorem and proof structure: nonnegative matrix inverse/Frobenius bounds from Hadamard-transform optics. This S-matrix is not the unitary scattering S-matrix. The full external Lean proof was not imported or rechecked here. |
| [Gavassino, Life on a closed timelike curve](https://arxiv.org/html/2405.18640v1) | Abstract, Gödel-type setup, entropy orientation and memory-return discussion. The paper assumes a particular CTC geometry; it does not construct a CTC from a fluid neck. |

[established-bounded; source-inspected] Titles and abstract-level content for the five references
Brandon could not access:

| Reference | Title and abstract-level return |
|---|---|
| [Fabre–Treps, RMP 92, 035005 (2020)](https://journals.aps.org/rmp/abstract/10.1103/RevModPhys.92.035005) | **Modes and states in quantum optics.** Multimode state descriptions, changing mode decompositions, invariant properties, minimal mode populations and optical-network applications. A different subsystem decomposition can change the entanglement description; this is not entanglement removal by local unitaries at a fixed bipartition. |
| [Fano, RMP 29, 74 (1957)](https://journals.aps.org/rmp/abstract/10.1103/RevModPhys.29.74) | **Description of States in Quantum Mechanics by Density Matrix and Operator Techniques.** Title, author and publication verified; the retrieved publisher page exposes no abstract. No abstract was invented. |
| [Ramos, J. Mod. Opt. 52, 2093–2103 (2005)](https://www.tandfonline.com/doi/abs/10.1080/09500340500147208) | **Mixture of two-mode unpolarized and pure quantum light states: quantum polarization and application in quantum communication.** The publisher's indexed abstract relates purity and polarization for mixed two-mode states and discusses amplification and quantum-key-distribution applications. Direct page fetching failed. |
| [Bhandari, Physics Reports 281, 1–64 (1997)](https://www.sciencedirect.com/science/article/pii/S0370157396000294) | **Polarization of light and topological phases.** The indexed publisher abstract covers geometric/topological phase, unitary/nonunitary optical transport and the relation of SU(2) to SO(3). Direct page fetching failed. |
| [Deb–Kjærgaard, Science 374, 972–975 (2021)](https://www.science.org/doi/10.1126/science.abh3470) | **Observation of Pauli blocking in light scattering from quantum degenerate fermions.** The [public abstract/preprint](https://arxiv.org/abs/2103.02319) reports suppressed scattering and increased transmission from restricted final-state availability in a degenerate Fermi gas. |

## Directional kets, rays and receivers

[definition] Choose a local transverse frame F. Its two independent polarization axes are
`|↔⟩_F` and `|↕⟩_F`. Define

`|↗⟩_F = (|↔⟩_F + |↕⟩_F)/√2`,
`|↖⟩_F = (-|↔⟩_F + |↕⟩_F)/√2`,
`|θ,φ⟩_F = cos θ |↔⟩_F + exp(iφ) sin θ |↕⟩_F`.

The arrows are declared directional polarization charts. A reversed real vector gives the same
one-ray projector, while relative phase between coherent components remains observable. Opposite
arrow glyphs therefore do not automatically denote orthogonal quantum states. These transverse
axes are also distinct from a photon's propagation direction and helicity. The code introduces
scoped arrow notation over the existing `JonesSection` and an explicit `inFrame` map.

[proved-derived; formal-checked] `Physics/DirectionalPolarization.lean` reuses the existing
`FiniteCoherentPathFamily.analyze` covector and proves the relative-angle Malus law,
`|⟨α|θ⟩|² = cos²(θ−α)`, and the rotated orthonormal-pair mixture identity. In particular,

`ρ_mix = (|↔⟩⟨↔|+|↕⟩⟨↕|)/2 = (|↗⟩⟨↗|+|↖⟩⟨↖|)/2 = I/2`.

This differs from `ρ_coh=|↗⟩⟨↗|`: both return 1/2 at the horizontal analyzer, but the normalized
diagonal analyzer returns 1/2 and 1 respectively. The finite checked density separator retains
the off-diagonal coherence. The source answer's notation is thereby used as actual algebra,
rather than another semantic direction label.

[proved-standard] For multiphoton fields, a single first-moment Stokes vector need not determine
the polarization state. The supplied three-photon experiment distinguishes states with matching
lower moments through third-order coherence. This supplies a physical example of a receiver
quotient that loses a future analyzer distinction; a qubit's two-by-two density description must
not silently be substituted for every photon-number sector.

## The spherical and hyperbolic connection

[definition] Our conventional Stokes normalization is

`ρ = 1/2 [[S0+S1, S2−iS3], [S2+iS3, S0−S1]]`,

so S0 is the trace and S1 the H/V contrast. The review uses a different factor/permutation in
its circular-basis convention; comparisons require that explicit rechart.

[proved-derived; formal-checked] The new owner proves

`4 det ρ = S0²−S1²−S2²−S3²`,

and determinant preservation under `ρ ↦ GρG†` for `det G=1`. Positivity of a physical coherency
matrix places its Stokes vector in the corresponding forward cone. Pure Jones/one-photon
polarization rays lie on the null
boundary. The determinant identity itself is algebraic and is checked without asserting that
every real Stokes tuple is an admitted physical state.

[proved-standard] SU(2) polarization transformations rotate the Poincaré sphere. The positive
Hermitian unimodular sector of SL(2,C) supplies hyperbolic boosts in the Stokes representation;
diattenuators additionally carry their common attenuation. This is a concrete spherical/
hyperbolic representation bridge. Identifying that internal Stokes cone with a particular
spacetime causal cone additionally requires the physical field/tetrad and propagation map.

[proved-derived; formal-checked] The same owner now defines the alternating Jones pairing
`[u,v]=u_H v_V−u_V v_H` and proves `[Gu,Gv]=det(G)[u,v]`. The four-ray receiver

`χ(a,b;c,d) = [a,c][b,d] / ([a,d][b,c])`

is invariant under a common invertible frame and independent nonzero rescalings of the rays,
with both denominator pairings required nonzero. This directly rejoins optical directions and
the projective cross-ratio underlying Swing. It is a scoped ray receiver: individual path
amplitudes/phases can remain relevant to a coherent interference experiment. Physical evolution
can change χ(t); frame covariance at each time does not imply temporal constancy.

## Exclusion without an absolute container

[proved-derived; formal-checked] The repository already had finite occupation, creation/
annihilation and canonical anticommutation relations in `HolonicFermionicOccupation`, together
with a finite Fermi–Hubbard Hamiltonian. The new extension forms

`c†(v)=Σ_i v_i c†_i`

and proves `{c†(u),c†(v)}=0` and `c†(v)²=0` for every complex superposed mode. The repeated
one-particle state is excluded independently of which basis presents it. Spatial coordinates
can label a particular mode chart; they are not required by this algebra. For two-mode spinors,
the double-creation vacuum amplitude is the alternating pairing above.

[definition] A mode includes the relevant motional and internal state. Different preparation
occurrences can prepare the same mode; distinct historical origins are not a way to evade
exclusion. Conversely, agreeing in one position/intensity receiver does not make two full modes
equal. The earlier August 26 paragraph treating differing receiver histories as automatically
different excluded-state labels is corrected at its source. No measured location or privileged
observer is required to state an operator relation; the preparation/analyzer map determines how
the relation is tested. An unresolved position does not remove the field's mode algebra.

[proved-standard] Maták's v3 scattering calculation retains fermionic exchange interference in
the optical theorem `2 Im T_ii = Σ_f |T_fi|²`. A contribution that appears to populate an already
occupied momentum/spin mode cancels against the crossed contribution in the complete rate.
The individual terms must remain until that combination is formed. The paper establishes this
compatibility within its fermionic model; it does not derive antisymmetry from discreteness
alone. Photons also have discrete detections and admit multiple occupation, so the exchange
character is part of the physical source law.

[proved-derived; formal-checked] `Physics/FermionicModeReceiver.lean` adds the thermal receiver
over the two allowed occupations. With grand-canonical weights 1 and `exp[β(μ−ε)]`,

`n = 1/(1+exp[β(ε−μ)]) = sigmoid[β(μ−ε)]`,    `vacancy = 1−n`.

It reuses the existing normalized-exponential/sigmoid owner and proves common energy-reference
shift invariance. Exclusion supplies the two-state carrier; the thermal model supplies its
weights. This is a direct physical instance of the prior inference/normalization theorem.
The optical scattering experiment reads the reduced availability of final fermion states.
Interacting many-body states do not automatically factor into independent thermal modes.

## Swing with moving constitutive boundaries

[definition] A contemporary constitutive relation is a family `e_t=R_t j_t`, or its nonlinear/
frequency-dependent analogue. In a hydraulic chart e is a pressure/effort difference and j a
volume-flow current; resistance depends on the domain, material and boundary conditions. The
Ohmic relation describes an admitted regime rather than the complete law of an arbitrary river.
Storage/inertial response can instead require a complex impedance or a memory operator.

[proved-derived] Even the scalar specialization gives the exact finite difference

`Δe = R Δj + ΔR j + ΔR Δj`.

The existing checked `ConstitutiveModulation.coupledResponse_material_state_change` proves the
corresponding mixed-term law for `Bᵀ M B x`, and its full finite-change theorem also varies both
incidence factors. The moving-receiver derivative is `d(q_t x_t)/dt = q̇_t x_t+q_t ẋ_t`.
Thus the current, constitutive material, incidence and receiver can all evolve in the same
construction. Fixed-current and fixed-boundary descriptions are different conditioned charts
of the relation; neither makes all other observers' physical measurements constant.

[proved-derived; formal-checked] The polarized transport owner now admits different frames
at the source and target:

`T'_t = G_(t+1) T_t G_t^(-1)`,    `T'_t(G_t x)=G_(t+1)(T_t x)`.

`Transport.ChangingReceiver.changing_history_exact` already carries the corresponding indexed
square `q_(t+1)T_t=U_tq_t` through an actual changing-carrier trajectory. Its differential owner
retains chart velocity. This is the formal content needed by the Swing clarification; the old
fixed-board Swing remains its particular specialization.

[proved-standard] Schrödinger and Heisenberg pictures give a useful quantum instance: evolution
can be carried by the density state or by observables while their trace pairing agrees. For
`y=G(t)x` and `ẋ=A(t)x`, the transformed generator is
`A'=ĠG^(-1)+GAG^(-1)`. Keeping only the conjugated A loses frame motion. Changing the Hamiltonian
or medium physically changes the source law as well. In fluid coordinates the material derivative
`∂_t v+(v·∇)v` already distinguishes acceleration along flow from an Eulerian partial derivative.

## The neck, paired cones and the physical source question

[interpretation] A pinching neck gives a useful model of a changing interaction boundary: two
regions share a shrinking passage and their outward interface orientations are opposed. The
appropriate first physical map is the moving fluid surface, its traction jump and capillary
energy, with mass/momentum/heat transport. Young–Laplace pressure involves both principal
curvatures. Concavity and convexity are oriented local descriptions; an arbitrary partition can
also have saddle curvature, so a global convex-particle/concave-container classification is not
assumed. The [axisymmetric source construction](https://arxiv.org/abs/physics/0110081) derives
neck evolution from Navier–Stokes with a free surface.

[conditional] In the usual capillary similarity regimes, radius scales respectively like
`(σ/ρ)^(1/3)(t*−t)^(2/3)` or `(σ/μ)(t*−t)`, with regime-dependent coefficients and matching.
These are distinct balances of capillarity, inertia and viscosity. A proposed cone-only
description is insufficient if the same geometric receiver fails to distinguish these returned
rates. Interface storage and surface energy must also enter any paired-flux cancellation.
The concrete continuation question is which neck/interior modes affect the retained boundary
response and its remainder, using the existing fluid/memory and constitutive owners.

[definition] The spatial neck tangent cones, an optical Stokes cone and a Lorentzian light cone
have different defining quadratic/constitutive data. To identify a proposed neck boundary as
null, exhibit the physical metric/characteristic law and show the relevant tangent is null.
To identify a CTC, additionally exhibit timelike closed transport. Gavassino's supplied source
assumes a Gödel-type CTC and obtains a particular recurrent thermodynamic account; the drawing
of two tip-to-tip cones does not supply that geometry. The quantum recurrence result remains
useful to compare closed versus open transport without imposing exact historical recurrence
on ordinary inference or fluid evolution.

[definition] A geometric cross-ratio can have a logarithmic receiver, with its sign/complex phase
and branch retained. It becomes a cross-entropy or relative-entropy expression only through an
actual probability/density and likelihood-ratio map. Likewise, a wire's sudden failure needs
electrothermal/material dynamics; the name “pop” for the sixth position derivative does not
identify a rupture mechanism. The finite constitutive defect and phase-transition source are
the constructive objects to calculate.

## Fermi-gas emulation, quantum information and the previous theorem

[established-bounded; source-inspected] [Van Houcke et al., Feynman diagrams versus Fermi-gas
Feynman emulator](https://arxiv.org/html/1110.3747) compares a resummed diagrammatic computation
with measured density/pressure in ultracold lithium-6 near the unitary-gas regime. The continuum
unitary gas is a specific interacting source; it is not identical to our existing finite Hubbard
chart. Agreement of the reported normal-state equation of state is the demonstrated receiver
scope. It does not establish every microscopic state or efficient emulation of arbitrary systems.

[definition] An emulator is a physical or computational realization of a requested generator/
receiver family. With representation E, target dynamics T, apparatus dynamics U and decoder D,
the exact task has `E_(t+1)T_t=U_tE_t` and `D_tE_t=ρ_t`; bounded defects use the existing
`ChangingReceiver` composition and simulation-certificate budgets. The emulator need not
reproduce microscopic constituents or every source history. The implemented action, admitted
source family, clock, decoder and measured error/work establish its scope. This is the same
kind of representation question in CPU architecture emulation and Holonic Encoding, with
different physical and computational source maps.

[proved-standard] The previous finite inference functional has a noncommutative counterpart:
`D(ρ||σ)=Tr[ρ(logρ−logσ)]`. Quantum channels contract this distinguishability. Exact sufficiency
for a declared state pair is characterized by recovery, with support conditions; approximate
versions retain quantitative recovery defects. See the primary
[recovery/sufficiency paper](https://arxiv.org/html/1509.07127). Recovery here concerns that
declared quantum information, not a unique microscopic preparation history.

[proved-derived] For finite density matrices, β>0 and a Gibbs reference `σ=exp(−βH)/Z`,
`logσ=−βH−log Z` gives

`Fβ(ρ)−Fβ(σ)=β^(-1)D(ρ||σ)`,    `Fβ(ρ)=Tr(ρH)−β^(-1)S(ρ)`.

Indeed `D=-S(ρ)+β Tr(ρH)+log Z` and `Fβ(σ)=−β^(-1)log Z`. No commutation of ρ and H is required.
Full-rank σ and the usual zero-eigenvalue convention for ρ give the stated finite domain. This
algebraic derivation is not claimed as a new Lean matrix-log theorem. The
[primary free-energy source](https://arxiv.org/html/1702.08473) also treats objects `(ρ,H)` with
changing Hamiltonians. Our preceding scalar/KL proof is the commuting candidate chart, and
the current density/phase construction makes explicit which additional information a quantum
receiver retains.

## Actual returned operators and checks

[established-bounded; implemented-exact; computational-witness] The new
`crates/holonic-engine/examples/optical_receiver_frames.rs` uses `ExactRatMatrix` and the existing
`SymbolicSurprisal`/`RatioFamily` owners. Its complete
[receipt](2026-09-12_optical_frame_receipts/receiver-frames.json) returns:

- Mixed/coherent H readings both 1/2 and diagonal readings 1/2 versus 1.
- Joint state/analyzer rotation covariance, and 9/25 transmission when the state alone rotates.
- A unimodular Jones core with Stokes trace 17/8 and contrast 15/8, preserving quadratic value 1.
- Harmonic four-ray cross-ratio −1 before and after the common frame transform.
- The two-ended moving-frame return `(10,3/2)` through the transformed operation.
- Repeated creation of mode `(3/5,4/5)` vanishing, and exchanged orthogonal-mode amplitudes +1/−1.
- Thermal occupied/vacant weights 2/3 and 1/3 for logit ln 2.

[established-bounded; implemented-exact] The supplied nonnegative-matrix paper additionally
gives a decoder-conditioning application. For the order-three mask `S=11ᵀ−I`, the public exact
inverse returns diagonal −1/2 and off-diagonal 1/2, with `||S^(-1)||_F²=9/4`, attaining the
stated order-three bound. Under a declared zero-mean isotropic unit-noise covariance this equals the
decoded squared-noise expectation, since covariance transports as `A^(-1)ΣA^(-T)`. The general
paper claims `||A^(-1)||_F≥2n/(n+1)||A||_max^(-1)` under its stated hypotheses. Its full new
proof remains external; our exact application verifies this particular matrix.

[established-bounded; process-audit] `bash tools/lean_check.sh ElementaryHolonics.Framework.Physics`
passes under Lean 4.33.0, including DirectionalPolarization, FermionicModeReceiver, superposed
CAR and the two-frame transport extension. Early complex-algebra/notation drafts failed and
were repaired before the final build. The
[terminal receipt](2026-09-12_optical_frame_receipts/formal-terminal.txt) records completion.
`cargo run -p holonic-engine --example optical_receiver_frames --no-default-features -- .local/scratch/2026-09-12-optical-receiver-frames.json`
completes all assertions. Rustfmt and `git diff --check` pass. This is exact exterior execution;
no calibrated physical apparatus, native model cultivation or backend parity is claimed.

[definition] These returned source/receiver laws become mathematical material for Hephaestus
requests: directional analyzers, phase-sensitive mode families, changing-frame operations,
exclusion-compatible compositions and decoder costs. They extend the shared generator/encoding
programme. A general quantum/GR, fluid pinch-off or CTC realization is not a new prerequisite to
using these already constructed relations.
