import Holonics.Physics.Fluid.Cells
import Holonics.Physics.Fluid.ControlVolume
import Holonics.Physics.Fluid.ComplexFluid
import Holonics.Physics.Fluid.Singularity
import Holonics.Physics.Fluid.Body
import Holonics.Physics.Fluid.LiftUp

/-!
# Physics.Fluid: the fluid instance of the Holon law

[definition] Rebuild step 6, K3 (#74; restructure plan §3.5 and §3.7 at `13f8c734`). The fluid
instance keeps its constitutive equations, its clocks, its heat and entropy returns and its
participating receiver. Its modules:

* `Fluid/Cells` — cubical cells of the grid chart, `∂² = 0`, the Swing as a chain map with its
  hand `(−1)^k`, and the reflect-and-join of a square and a cube, whose shared face cancels exactly
  once through `Holarchy/View.shared_face_cancels` (battle test 1);
* `Fluid/ControlVolume` — per-face returns of mass flux, momentum flux and traction, the joined
  balance and the joined box's full-volume return, Newtonian stress with its viscous heat handed
  to the thermal port (`Thermal/ViscousPort.cell_port_join`), and the coholon reading of velocity,
  vorticity, pressure, circulation and the Lamb cross-current (battle test 3; the time advance and
  the pressure solve are open);
* `Fluid/ComplexFluid` — the complex-bilinear fluid law and its Hermitian energy exchange, kept
  distinct from the Fourier chart of a real field (battle test 4);
* `Fluid/Singularity` — planar point-singularity flows as one-parameter Möbius navigators,
  classified by site kind, with the potential carried as the log of an undivided ratio with its
  winding (egg record §4);
* `Fluid/Body` — a closed dividing streamline, a loop whose lifts are continued by path lifting,
  balances its windings and, winding once around every site, forces zero net strength
  (Gauss/Rankine necessity); the half-body counterexample; and the block-membrane form joined to
  relative completeness;
* `Fluid/LiftUp` — the lift-up of a streamwise-constant mode of uniform shear: every mode decays
  at `ν k²`, while the boost's largest reading `|S|/2 − ν k²` bounds the response and no smaller
  exponent does (`Geometry/Motion.numerical_abscissa`); the exact response is a free-fall shear
  riding a uniform decay, with a witness of transient amplification.

The Rust instance is `holonics::physics::fluid`.
-/
