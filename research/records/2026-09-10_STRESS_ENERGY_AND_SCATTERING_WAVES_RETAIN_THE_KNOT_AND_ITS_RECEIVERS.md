# Stress-energy and scattering waves retain the knot and its receivers

## Scope and recovered owners

[definition] Brandon requested actual coupling of the receiver/friction/world-tube work to fluid dynamics, Einstein stress-energy, rotational momentum, mass-energy, quantum mechanics, force sectors, tensile dark-sector questions, capacitive circuitry/lightning and Feynman diagrams. He requested Lean work and evolving prime knots, unknots and chains. This is an exterior mathematical/physical construction and presentation return. Native AC cultivation remains paused.

[definition; source-inspected] The recovered assembly uses these existing owners:

| Relation | Owner | Scope retained |
|---|---|---|
| Fluid rotational momentum | `NavierStokesLambCurrentEvolution` | Actual NS source, pressure, diffusion, forcing and velocity–vorticity current |
| Swirl/angular history | `NavierStokesSwirlCirculation`, `NavierStokesViscousSwirlBalance` | Actual trajectory and viscous angular return |
| Einstein/fluid conservation | `NavierStokesCurvedTransport.EinsteinFluidDynamics` | Field equation, Bianchi identity, metric compatibility, nonzero coupling |
| Lorentz/mass shell | `HolonicCurvedArcEinstein`, `HolonicMassShellFace` | Typed frames, flat vacuum, mass shell; supplied physical calibration |
| Maxwell wave transport | `HolonicMaxwellPropagation` | Typed curls, speed and wave-preserving receiver |
| Storage and capacitance | `Physics/CoupledIncidence`, `HolonicMeasuredParametron` | Oriented storage and nonzero charge/voltage comparison |
| Complex nonlinear return | `Physics/FluidReceiverClosure`, September 8 complex-fluid record | Imaginary field and its nonlinear feedback survive folding |
| Quantum and force sectors | `Computation/HolonicQuantumTransport`, `HolonicFourForceSectorCarrier`, `HolonicGaugeCovariance` | Finite evolution, representations, ordered holonomy and gauge covariance |
| Entropy | `Physics/InformationDifference`, `HolonicMembraneActionTransport` | Full distribution and source fibre precede scalar cross-entropy |
| Dark-sector inference | `HolonicFieldTheoryPassage`, `HolonicCosmologicalInference` | Dust/vacuum distinction, opposite exchange, retained inference fibre |

## Constitutive coupling

[conditional] In signature (-,+,+,+), with a metric-compatible connection, natural units c=1 and specified constitutive matter, Einstein's equation is G + Λg = 8πG T_total. The total tensor retains fluid, electromagnetic and other sectors. A perfect fluid has Tᵐⁿ=(e+p)uᵐuⁿ+p gᵐⁿ, u·u=-1; shear and heat transport add their actual tensors. Covariant conservation follows from the field equation and Bianchi identity. This is the existing `EinsteinFluidDynamics` interface; the current flat vacuum example does not instantiate a nonzero matter geometry. [Tong, General Relativity](https://www.damtp.cam.ac.uk/user/tong/gr/gr.pdf).

[conditional] Maxwell and matter exchange opposite Lorentz-force divergences under a consistent field convention. A resistive conducting-fluid reduction gives ρDₜu=-∇p+∇·τ+j×B+f, j=σ(E+u×B), τ=2μD. Ohmic and viscous heat are |j|²/σ and 2μD:D. With constant material coefficients and the low-frequency reduction, Bₜ=∇×(u×B)+ηΔB, ∇·B=0. Ideal flux freezing requires the ideal constitutive law; resistive reconnection is an admitted different event. [Tong, electromagnetism](https://www.damtp.cam.ac.uk/user/tong/em/el4.pdf).

[interpretation] Capacitive surface storage is obtained from the actual electric field/medium boundary problem, descending field energy to a quadratic port form. Charge, current and emf are surface/path integrals. Moving boundaries, induction, dielectric memory and unresolved modes remain potential obstructions to a static scalar C. Lightning extends this same interface with ionization, changing conductivity and leader incidence. Existing leader/quadrature and RELAMPAGO material recover that path/receiver question; this return does not turn a path score into physical lightning.

## New formal returns

[proved-derived; formal-checked] `Physics/PortEnergyHeat.lean` composes quadratic storage with supplied coordinate derivatives. For E=½(Cx₁²+L⁻¹x₂²), e=∇E and ẋ=s-Ge, it derives Ė=e·s-e·Ge. Nonnegative diagonal conductances make the dissipative return nonnegative. A heat receiver accumulating that constitutive rate gives d(E+Q)/dt=e·s. The chain rule proves the balance; the heat law stays an explicit assumption. Example coordinates voltage and flux have conjugates charge and current, so the derivative/source coefficients require corresponding units.

[proved-derived; formal-checked] `Physics/ScatteringWaveHeat.lean` proves complex two-port power preservation for R(a,b)=[[a,-b],[b,a]] when a²+b²=1. With P=|z₁|²+|z₂|², it derives P(Rz)=P(z), d²P+(1-d²)P=P, and nonnegative retained heat for 0≤d≤1. Cyclic shift and diffusive heat passage are verified separately in the exact generator; the Lean result does not assert a continuum limit or a thermal quantum reservoir.

[proved-derived; formal-checked] `Physics/ReceiverStressEnergy.lean` constructs rest perfect-fluid components and lowers both observer indices correctly. Its angular derivative-jet identity is

    ∂λ J^(λμν) = T^(μν) − T^(νμ) + x^μ f^ν − x^ν f^μ,
    J^(λμν) = x^μ T^(λν) − x^ν T^(λμ),  ∂λ T^(λν)=f^ν.

Symmetric stress and zero divergence give zero angular return. This is finite inertial component algebra; curved global charges need the appropriate symmetry/connection/boundary, and spin adds its current. The positive rest branch E=m₀c² is derived through `HolonicMassShellFace.massShell_iff`, with zero spatial momentum, nonnegative energy/mass and c>0. The older `dustFaceReading` comment was corrected: its algebraic density-weighted Lorentz diagonal is not a physical dust stress-energy contraction.

## A separating tension receiver

[proved-derived; formal-checked] For T=diag(e,p₁,p₂,p₃), the rational Lorentz pair u=(5/3,4/3,0,0), n=(4/3,5/3,0,0) has norms -1,+1 and zero pairing. The new owner derives T(u,u)=(25e+16p₁)/9 and T(u,n)=20(e+p₁)/9. Dust gives 25e/9,20e/9; vacuum pⱼ=-e gives e,0. The active diagonal combination e+Σpⱼ is e for dust, -2e for vacuum and zero for one axial tension p₁=-e,p₂=p₃=0.

[interpretation] Brandon's tensile question becomes a proposal for a complete source tensor and its exchange. The existing dust/vacuum and cosmological inference owners already preserve these differences. A proposed tensile dark contribution must return compatible lensing, expansion and clustering faces. The boost supplies a first exact separator: a proposal identifying dust and vacuum tensors fails it.

[proved-standard] Dark matter is inferred from dynamical/lensing effects and structure formation; dark energy concerns accelerated expansion and its stress/equation of state. Their underlying physical nature remains unresolved. Vacuum negative pressure alone does not identify dark matter with tension or establish common microphysics. [PDG dark matter](https://pdg.lbl.gov/2025/reviews/rpp2025-rev-dark-matter.pdf), [PDG dark energy](https://pdg.lbl.gov/2025/reviews/rpp2025-rev-dark-energy.pdf).

## Exact material flow and wave passage

[proved-derived; implemented-exact] The material perturbation and Eulerian source are

    Fₜ(x,y,z) = (x+tz/2, y+t²x/4+t³z/8, z),  det DFₜ=1,
    Uₜ(X,Y,Z) = (Z/2, tX/2+t²Z/8, 0),
    fₜ=(0,X/2+tZ/2,0), P=0, curl U=(-t²/8,1/2,t/2).

Polynomial differentiation verifies Uₜ+(U·∇)U=νΔU-∇P+f, ΔU=0, div U=0, and dFₜ/dt=Uₜ∘Fₜ. These holomorphic identities hold on C³; the pictured carrier lies on its invariant real slice. The inverse is z=Z, x=X-tZ/2, y=Y-t²X/4. Spatial affinity transports every triangular face exactly. The family is an ambient isotopy for real t: intersections and knot type cannot change. This is a declared forced whole-space polynomial source with a local receiver aperture, not an unforced finite-energy NS solution or freely reacting elastic knot.

[definition] Each material station carries two complex directional ports. One step scatters with R(3/5,4/5), attenuates by d=15/16, and travels one actual incident edge. These rational scattering magnitudes correspond to a power-normalized impedance ratio 4 with an oriented output convention. Attenuation is a declared material parameter. Heat receives (1-d²)P locally and passes its existing content to self with weight 1/2 and each cycle neighbor with weight 1/4. The displayed clock step is 1/24. This finite transmission lattice is its own exact source; it is not a hidden approximate NS solve.

[proved-derived; implemented-exact] Initial stimulus is Ψ⁺₀=1, Ψ⁻₀=i, zero elsewhere. Every step checks Σ(|Ψ⁺|²+|Ψ⁻|²)+ΣQ=2, nonnegative heat and the finite incidence cone. Repeated local scattering gives interference and counterpropagation; heat diffuses along the same cycle. No randomness seeds the stimulus. Separated chain components do not exchange amplitudes merely because they are linked; the contact-driven exchange is the earlier plate 10–11 construction.

[definition] The image is a declared joint receiver of U+iℓ curl U plus the pushed-forward wave tangent, with ℓ=1 in the braid lane-length chart. This preserves the distinction between velocity and vorticity units. The unchanged coherent primary law reads P=(a²,b²,(a+b)²), C=P/(κ+ΣP), at fixed aperture. Cross-entropy uses positive normalized receiver channels with bounded rational logarithms. Brightness/entropy supplies neither a force nor a knot classification.

## Knots, quantum completion and diagram composition

[established-bounded; implemented-exact] `knot_geometry.py` builds rational annular closed braids. Exact nonincident segment intersections, projected crossing parameters, angular cell population and observed over/under signs are checked against the braid. The unknot is a planar convex polygon with spanning disk; the trefoil is the closure of σ₁³; the figure-eight is the closure of (σ₁σ₂⁻¹)². Their projected crossings are 0,3,4. Prime classification and Alexander polynomials are standard external identifications of those diagrams, not newly proved Lean knot classification. [Knot Atlas](https://katlas.org/wiki/4_1).

[definition] Rational transverse sections form a triangular closed tube. Its actual face intersections, including adjacent joints and coplanar cases, and oriented incidence are checked. An edge-clearance fraction alone would not check joints. The affine time map preserves the complete mesh. Triangular faces and their vertex source remain the geometry, rather than a smooth spline substituted for them.

[proved-derived] Attenuation has the exact unitary completion V=[[15,-√31],[√31,15]]/16. The environment retains the complementary amplitude norm; √31 follows from 16²-15². A classical power or finite quantum-channel reading can use this map, but interpreting the environment as thermodynamic heat requires its reservoir energy law.

[conditional] A QED exchange attaches fermion lines, photon propagator and -ieγᵐ vertices with momentum, spin and integration rules. A graph crossing is not a literal electron trajectory or knot contact. The exact inverse identity G=G₀+G₀ΣG follows from G⁻¹=G₀⁻¹-Σ where inverses exist. Iteration requires convergence or a formal-series chart. [Tong, QFT](https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf).

[definition] The shared addressed base does not erase sector representations, actions or source: U(1), electroweak SU(2)ₗ×U(1)ᵧ, SU(3), and frame/Spin gravity remain attached to the existing four-force carrier. A real Lorentzian source from complex fields is derived from a real action with conjugate channels retained. Taking the real part of the holomorphic fluid alone is not that construction.

[interpretation] ETP's comparison discipline is productive here: identify operations and substitution/composition laws, then derive an intertwiner or a separating receiver. A shared graph silhouette is weaker, while differing application labels do not prevent exact energy, boundary and transport relations from being reused. The new Lean owners are concrete reusable returns of this programme.

## Verification

[definition] Final artifact/check receipts are recorded below after execution. Python is exterior exact construction/rendering apparatus. Lean remains separate verification and never enters cultivation or inference.

[definition] `knot_differences.py` supplies two additional receivers. The impulse image subtracts the unexcited bulk current exactly, leaving (Ψ⁺+Ψ⁻)DFₜv. The heat image contracts stored heat and its outgoing edge heat flow, divided by the declared initial energy per station 2/N. This normalization is derived from the source energy and actual station count. A black patch in the difference frame is a zero/occluded receiver return, not deletion of the underlying knot. The complete carrier and parent current remain attached.

[established-bounded; implemented-exact] Exact logarithm-series denominators made entropy clipping expensive. The optional `log_display_bits=20` enclosure places each log measurement at a dyadic center and adds 2⁻²⁰ to its existing series error before reference weighting. The source/current packet is unchanged. `verify_stress_waves.py` checks this separation and the recorded bound; this is an exterior receiver approximation with explicit radius, not a native floating-point current.

[established-bounded; formal-checked; implemented-exact] Final return:

- `bash tools/lean_check.sh ElementaryHolonics.Framework.Physics` completed successfully after integration of all three new owners. No `sorry` or new axiom declaration was introduced. This is the declared Physics import closure, not a claim about all research roots or native execution.
- `uv run --with sympy python research/experiments/receiver_engraving/knot_waves.py` returned all four carriers and 28 joint/entropy/monochrome packets. `knot_differences.py` added six source-relative impulse/heat packets.
- `uv run --with sympy python research/experiments/receiver_engraving/verify_stress_waves.py` checked all 34 packets against the actual fluid map, directional states, transported current, heat, mesh receipts and logarithm enclosure. `triangle_embedding.py` returned its explicit positive/negative geometry checks.
- Closed embedded meshes: unknot V=72,F=144; trefoil V=432,F=864; figure-eight V=864,F=1728; three-component chain V=432,F=864. Every component is orientable and has Euler characteristic zero. The mesh source and receipts retain all actual vertices and faces.
- `typst compile --root research/papers/source research/papers/source/papers/hnn-information-chemistry/main.typ research/papers/rendered/hnn-information-chemistry.pdf` returned 18 numbered plates, with no overflow continuation. Changed plates were rendered with Poppler and inspected; function/subscript, divergence notation, graph-label spacing and QED labels were corrected.
- `uv run --with cairosvg --with pillow python research/experiments/receiver_engraving/animate_knots.py` returned trefoil, figure-eight and chain APNGs. All five decoded frames match their rendered RGB frames exactly. Playback pauses and resets are presentation only; no interpolated physical states are inserted.

[definition] [Current PDF](../papers/rendered/hnn-information-chemistry.pdf), [Typst source](../papers/source/papers/hnn-information-chemistry/main.typ), [trefoil animation](../papers/rendered/receiver-engraving/trefoil_3_1-motion.png), [figure-eight animation](../papers/rendered/receiver-engraving/figure_eight_4_1-motion.png), [chain animation](../papers/rendered/receiver-engraving/chain-motion.png). The earlier atlas and unrelated local research were preserved. This return changes no native cultivation/inference operation.
