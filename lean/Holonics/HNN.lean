import Holonics.HNN.Propagation
import Holonics.HNN.Word
import Holonics.HNN.Moment
import Holonics.HNN.Normal
import Holonics.HNN.LatticeDeposit
import Holonics.HNN.LatticeWord
import Holonics.HNN.Ratio
import Holonics.HNN.Retention
import Holonics.HNN.Keys

/-!
# The HNN law

[definition] Rebuild step 4 (#73), campaign 1: the laws of `docs/plans/THE_REBUILD.md`, "Step 4
design: the HNN law", table (b) rows 1–7, stated before their Rust owners in `holonics::hnn`.

| Module | Design item | Rust consumer |
|---|---|---|
| `HNN/Word` | 1. the ring's element and the tick's global power | `hnn::propagation` |
| `HNN/Propagation` | 2. the junction Swing, the transit, the causal cone and diamond | `hnn::{propagation, word}` |
| `HNN/Moment` | 3. selective stepping, the phase-binned moment, its adjoint and capacity | `hnn::moment` |
| `HNN/Normal` | 4. the normal constitution and deposition, per locus | `hnn::constitution` |
| `HNN/LatticeDeposit` | 4. deposition on a declared carrier lattice with a carried remainder | `hnn::constitution::{Lattice, NormalLaw}` |
| `HNN/LatticeWord` | Decision 24: transients and inverse charts on declared lattices, certified residuals | `hnn::{word, propagation, constitution}` |
| `HNN/Ratio` | 5. the Holon ratio at the receiver's face, and the carried power | `hnn::ratio` |
| `HNN/Retention` | 6. retention as the collapse onto what the admitted future distinguishes | `hnn::{retention, pending}` |
| `HNN/Keys` | 7. keys by loop closure, and selective stepping | `hnn::keys` |
-/
