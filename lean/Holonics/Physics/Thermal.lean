import Holonics.Physics.Thermal.Exchange
import Holonics.Physics.Thermal.ViscousPort
import Holonics.Physics.Thermal.Schnakenberg
import Holonics.Physics.Thermal.ChainAxes

/-!
# The thermal instance of the Holon law

[definition] Rebuild step 6, K3 (#74), battle test 5, and issue #5; ELEMENTARY_OBJECTS operator
contract, "Physical instances" (`thermal exchange/diffuse/entropy_production`). Rust owner
`holonics::physics::thermal`.

- `Thermal/Exchange`: two cells under the caloric law `U = CT` with a Fourier contact: the first
  law of a tick, the exact production rate `κ(T₁ − T₂)²/(T₁T₂) ≥ 0`, and the tick's entropy
  enclosed by two rational Clausius readings, nonnegative under the tick condition.
- `Thermal/ViscousPort`: the fluid's viscous-work port: the fluid control volume produces the
  admitted work (`ViscousWork.ofFluid`, `cell_port_join`), which enters internal energy through
  the exchange's update, with production `W/T ≥ 0`.
- `Thermal/Schnakenberg`: production across a neck, `Σ (J₊ − J₋) log(J₊/J₋) ≥ 0`, carried as
  exact pairs with a rational sign certificate, zero exactly when balanced; the two-cell exchange
  is a one-junction neck; a cut's production is at most the epoch production.
- `Thermal/ChainAxes`: the time and entropy axes along an oriented chain (#5): an open chain has
  no stationary arrow; a stationary ring carries one current, and its production is that current
  times the cycle affinity, bounded by the least forward flow (the neck); the entropy clock is a
  helix whose carry sits at the carry section, so entropy is the turn times the signed epochs
  plus a bounded state term.

The retired `holonics-cuda` diffusion receipt: its energy balance is carried by
`Thermal/Exchange.first_law` (two cells); many-cell diffusion is owed (#62).
-/
