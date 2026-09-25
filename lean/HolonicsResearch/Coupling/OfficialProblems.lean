import HolonicsResearch.Geometry.PoincareConjecture
import HolonicsResearch.Zeta.Seam
import HolonicsResearch.Hodge.HodgeConjecture
import HolonicsResearch.EllipticCurve.BirchSwinnertonDyer
import Holonics.Fluid.NavierStokes
import HolonicsResearch.Gauge.YangMills
import HolonicsResearch.Computation.PVersusNP

/-!
# The seven Millennium problem objects

This import face makes the actual statement carriers available together:

* the solved Poincaré proposition, without a local kernel proof;
* the Riemann-hypothesis proposition already supplied through mathlib by `Seam`;
* the Hodge cycle-class/rational-Hodge-subspace interface;
* the repository's present BSD proposition, whose documented gap from the complete official ledger
  remains open;
* all four official Navier–Stokes alternatives;
* the compact-simple continuum Yang–Mills/mass-gap interface; and
* fixed-encoding polynomial-time classes `P` and `NP`.

Importing this module asserts none of the open conclusions. It prevents nearby finite models and
documentation rows from silently standing in for the named mathematical objects.
-/
