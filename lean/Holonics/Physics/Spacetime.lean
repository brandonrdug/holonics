import Holonics.Physics.Spacetime.StressEnergy
import Holonics.Physics.Spacetime.Einstein
import Holonics.Physics.Spacetime.Boost
import Holonics.Physics.Spacetime.Wigner
import Holonics.Physics.Spacetime.NonClosedClock

/-!
# Physics.Spacetime: stress–energy, Einstein, observers and the Lorentz scope on aeons

[definition] Rebuild step 6, K4 (#75; restructure plan §3.6 at `13f8c734`; null-cone record
2026-09-24 §1–§2). The spacetime instance reads the K3 fluid and thermal cells as a stress–energy
source, states Einstein's equation as a residual with its conservation return, derives the
Bianchi identity from `∂∂ = 0` on cell complexes, and states the Lorentz transformation on aeon
clocks. Rust owner `holonics::physics::spacetime`.

- `Spacetime/StressEnergy`: the source map from a constituted cell (the K3 Newtonian stress,
  internal energy and heat flux) to the owner's `ReceiverStressEnergy.Tensor`; its perfect-fluid
  face; a boosted observer reads the transported tensor `Λ⁻¹TΛ⁻ᵀ`; the trace reversal
  `Ric = κ(T − ½(tr T)η)` and the Newtonian coupling `R₀₀ = 4πGρ` at `κ = 8πG`; the observer
  current whose deformation term is the fluid's pressure work and viscous heat
  (`ObserverBoundaryCurrent`); conservation belongs to a receiver.
- `Spacetime/Einstein`: the discrete Bianchi identity on the grid chart
  (`Physics/Fluid/Cells.boundary_boundary`) and on a Holarchy's complex, where each shared face
  cancels once (`Holarchy/View`), consuming the one owner of the residual `𝓡 = G + Λg − κT` and its
  conservation return `κ∇·T = −∇·𝓡`, `Fluid/NavierStokesCurvedTransport`.
- `Spacetime/Boost`: the boost as the Doppler ratio `(u, v) ↦ (ku, k⁻¹v)`, composition by products,
  velocity addition through the landmark owner's Doppler chart, time dilation as the clock reading
  `t_R = ⟨ω_R | γ⟩` and as the owner's aeon rate of one inertial clock per receiver, the boost as a
  clock transport, the twin.
- `Spacetime/Wigner`: the Thomas–Wigner rotation of a loop of boosts, exactly, as the oriented angle
  defect of the velocity triangle, whose angles are read from its vertices.
- `Spacetime/NonClosedClock`: Sagnac and the gravitational redshift as the production time of the
  owner's Hodge split (`Aeon/Production/HodgeTime`) on a cycle bounding a cell; the redshift as the
  owner's rate of two static clocks.

[open] Owed in #62: a nontrivial continuum Einstein realization (Lorentzian metric, connection,
curvature and a fluid-plus-thermal constitution); the weak static limit `R₀₀ = ∇²Φ`; the Regge
construction of the discrete Einstein side (`G` the boundary of the moment of rotation of a
simplicial metric); the hyperbolic Gauss–Bonnet identification of the Wigner defect with the
velocity triangle's area, the non-perpendicular composition and the join to the gyration reading
`Geometry/HolonicCurvedArcEinstein.gyrationCurvatureReturn`; a frame-dragging clock of a stationary
spacetime (only Sagnac's first-order case is stated); the relativistic (finite-speed) heat law of
the thermal port.
-/
