import Holonics.HNN.Propagation
import Holonics.HNN.Word
import Holonics.HNN.Moment
import Holonics.HNN.Normal
import Holonics.HNN.LatticeDeposit
import Holonics.HNN.LatticeWord
import Holonics.HNN.Ratio
import Holonics.HNN.TargetFace
import Holonics.HNN.StandingRead
import Holonics.HNN.IndexedOpen
import Holonics.HNN.RegionCounts
import Holonics.HNN.Retention
import Holonics.HNN.Keys
import Holonics.HNN.Ring
import Holonics.HNN.Contact
import Holonics.HNN.ContactBreak
import Holonics.HNN.BornFace
import Holonics.HNN.ModeQuotient

/-!
# The HNN law

[definition] Rebuild step 4 (#73), campaign 1: the laws of `docs/plans/THE_REBUILD.md`, "Step 4
design: the HNN law", table (b) rows 1–8, stated before their Rust owners in `holonics::hnn`.

| Module | Design item | Rust consumer |
|---|---|---|
| `HNN/Word` | 1. the ring's element and the tick's global power | `hnn::propagation` |
| `HNN/Propagation` | 2. the junction scattering, the transit, the causal cone and diamond | `hnn::{propagation, word}` |
| `HNN/Moment` | 3. selective stepping, the phase-binned moment, its adjoint and capacity | `hnn::moment` |
| `HNN/Normal` | 4. the normal constitution and deposition, per locus | `hnn::constitution` |
| `HNN/LatticeDeposit` | 4. deposition on a declared carrier lattice with a carried remainder | `hnn::constitution::{Lattice, NormalLaw}` |
| `HNN/LatticeWord` | Decision 24: transients and inverse charts on declared lattices, certified residuals | `hnn::{word, propagation, constitution}` |
| `HNN/Ratio` | 5. the Holon ratio at the receiver's face, and the carried power | `hnn::ratio` |
| `HNN/TargetFace` | Decision 26: the target's code face, the margin rule, the receiving locus's exogenous normal law | `hnn::{ratio, constitution}` |
| `HNN/StandingRead` | Decision 26: the face reads the receiving parametron's bound harmonic coordinate | `hnn::receiving` |
| `HNN/IndexedOpen` | Decision 26: the source opens on its indexed, normalized counts | `hnn::moment` |
| `HNN/RegionCounts` | Decision 27: the receiving face is the grain of the receiving parametron's region class masses, corrected by the wave | `hnn::receiving` (target owner); KT baseline `hnn::reference` |
| `HNN/Retention` | 6. retention as the collapse onto what the admitted future distinguishes | `hnn::{retention, pending}` |
| `HNN/Keys` | 7. keys by loop closure, and selective stepping | `hnn::keys` |
| `HNN/Ring` | campaign 2, item 8: the ring's mode tick keeps `Q = diag(K, C)`, its denominator, its executed balance with pump and port work, the two-port reference change, crossings as epoch ticks, the pump and the sheets | `hnn::ring` |
| `HNN/Contact` | campaign 2, item 8: the contact's transfer and site kind by its stiffness's sign, the boost's certified solve or singular direction, the signed-storage balance, the lock address from the measured winding pair | `hnn::contact`, `hnn::propagation` |
| `HNN/ContactBreak` | campaign 2, item 8: the released storage `R = E_a + W_a − D_a − E_a′`, the advance `R ≥ J`, Griffith's closed-port case, the parted face's typed gluing defect | `hnn::contact`, `hnn::field` |
| `HNN/BornFace` | Decision 33: the wave read by the Born rule, a finitely correlated receiver on the receiving ring's register: the normalized digit split and dyadic cell face, the reception keeping a density, the density as the retained quotient, the absorbed unitary tick, the interference zero no nonnegative receiver makes, the exact covector and the Fisher-scored step | `hnn::born` |
| `HNN/ModeQuotient` | Campaign 3, first construction: a loaded ring's modes descend to their future quotient: the pump's cycle factors through its period (`cycle_mul_add`), so the period lift reads exactly the admitted future (`periodic_lift_exact`); one chart for every phase releases at most the phase family's kernel, which lies in it (`shared_chart_le_phase_kernel`, `phase_kernel_le_lift`); the descended ring returns the same wave for every drive (`descended_run`, `descended_run_reads`); a pair silent at the loaded port on its state and its tick stores nothing (`released_pair_storage_null`); the learning covector factors through the chart (`descended_costate`, `descended_gain`, `gain_fibre_invariant`) exactly when each gain family's variation vanishes on the release (`solved_pairing_null_iff`), which capacity and dissipation always do and stiffness and pump do under a half-turn pump cycle (`half_turn_separates`) but not at a standing pump's threshold (`standing_pump_threshold_reads_release`), so a learning aeon admits the variations as receivers (`learning_chart_le_kernel`); and the descended block ticks with its descended storage form and the full ring's balance (`descended_form`, `descended_balance`) | `hnn::modes` |

[definition] The receiving parametron's storage is the receiving tree, the shift navigator's
landmarks: its laws are `Compression/Landmark/Context` (its Rust owner
`compression::landmark::context`, which `hnn::receiving` reads). `HNN/RegionCounts` stays here: it
is the receiving face's region table, its grain read and the wave's combined face, and the tree
reads its KT count laws.
-/
