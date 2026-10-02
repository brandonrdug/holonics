# The lattice floor leaves `K u²/32` uncertified

**Date.** October 2. **Issues.** #73, #63. **Grade.** [proved-derived; formal-checked] for §1
(`HNN/ExecutedComparison` §13); [agent-inferred] for §2's trace. No run. **Parked**: the main line's
read of the kinetic chain's moves m5 to m7 found every refused rung `OwnNotBelow`, not `Guards`. So
the stall is the guard, and this branch waits.

## 1. The law

Every adopted move moves at least one lattice coordinate, so its step is at least `c = u/(2U)`. Along
a ray of slope `−q` and curvature at most `K`, the certified decrease of a step `η` is
`η q − ½ K η² D`.
- **No floor step is certified below the floor's slope** (`floor_certifies_nothing`): with
  `q ≤ ½ K c D`, every `η ≥ c` certifies nothing.
- **What that leaves** (`floor_lost_le`, `floor_lost_lattice`): a free step would certify
  `q²/(2KD) ≤ K c² D/8`, which is `K u²/32` at `D = U²`. The unit move's scale cancels.
- **The finest lattice the comparison reads** (`lattice_needed_iff`): `u = 2^(−L)` leaves at most a
  grain `g` uncertified exactly when `K ≤ 32 g 4^L`. Refining past the least such `L` changes nothing
  the comparison can read at `g`. Each refinement costs one bit per entry
  (`remainder_rat_bits_bounded`), and the re-base owner exists (`Constitution::rebased`; the
  declared schedule never calls it).

## 2. The trace of `K`, `u` and `U`

- **`u`**: the source port's lattice, `L = ⌈log₂(2 L_R X)⌉` (`field::lattice_exponent`). `L_R = 16`
  comes from the declared tolerance `1/16` bit, which is declared and is the root of every scale
  (PR #150). `X` is the population, a declared bound read from the data. The declared schedule never
  re-bases it.
- **`K`**: the executed comparison's curvature along the move. The ladder does not form it; it
  re-reads. The deposit's certificate bounds the same quantity as `s κ² b`. Here `s = ½` is derived
  (`ln 2/2` is tight, #150). `κ²` is derived from `‖R‖₂²`, the admittance ratios (declared constitutive
  values) and the certified amplitude growth `(1 + ω)` over the passage's re-entries.
- **`U`**: the unit move's largest entry, `‖M⁻¹Aᵀc‖∞`. It is derived from the state, with
  `|p − q| ≤ 1`, counts at most `X`, and `H′ ⪰ (1 − 1/(2L_R)) I`. It cancels in `K u²/32`.

The grain `g` at which the comparison is read is the open input: `N/L_R` bits over `N` readings
under the declared grain, or `1/L(N)` per reading under #150's derived one.
