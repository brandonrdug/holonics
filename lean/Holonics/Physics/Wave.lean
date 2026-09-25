import Holonics.Physics.Wave.Interference
import Holonics.Physics.Wave.Telegrapher
import Holonics.Physics.Wave.Energy
import Holonics.Physics.Wave.Radiation

/-!
# The wave instance of the Holon law

[definition] Rebuild step 6, K3 (#74), battle test 2; ELEMENTARY_OBJECTS operator contract,
"Physical instances" (`wave propagate/interfere`). Rust owner `holonics::physics::wave`.

- `Wave/Interference`: coherent amplitudes join before the intensity is read,
  `|Σu|² = Σ|u|² + 2 Re Σ_(j<k) ū_j u_k`; reading intensities first loses the cross terms.
- `Wave/Telegrapher`: the telegrapher's constitution on a chain of LC cells under a staggered
  clock; the causal cone of one cell per tick, attained, and independent of the leakage, which
  only damps the front by `2C/(2C + hG)` per tick.
- `Wave/Energy`: the same field on a supplied incidence: the exact energy balance of a tick and
  the Courant bound under which the staggered energy is a norm on the state `(V, I₀)`.
- `Wave/Radiation`: a stationary configuration emits nothing; the radiated field is the
  propagated change of the source.
-/
