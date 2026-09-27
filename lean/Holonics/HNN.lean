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
import Holonics.HNN.LandmarkTree
import Holonics.HNN.LandmarkAddress
import Holonics.HNN.LandmarkCarrier
import Holonics.HNN.Retention
import Holonics.HNN.Keys
import Holonics.HNN.Ring
import Holonics.HNN.Contact
import Holonics.HNN.ContactBreak
import Holonics.HNN.BornFace
import Holonics.HNN.LocalWeighing
import Holonics.HNN.ConvergenceFounding
import Holonics.HNN.LandmarkCompaction

/-!
# The HNN law

[definition] Rebuild step 4 (#73), campaign 1: the laws of `docs/plans/THE_REBUILD.md`, "Step 4
design: the HNN law", table (b) rows 1–8, stated before their Rust owners in `holonics::hnn`.

| Module | Design item | Rust consumer |
|---|---|---|
| `HNN/Word` | 1. the ring's element and the tick's global power | `hnn::propagation` |
| `HNN/Propagation` | 2. the junction Swing, the transit, the causal cone and diamond | `hnn::{propagation, word}` |
| `HNN/Moment` | 3. selective stepping, the phase-binned moment, its adjoint and capacity | `hnn::moment` |
| `HNN/Normal` | 4. the normal constitution and deposition, per locus | `hnn::constitution` |
| `HNN/LatticeDeposit` | 4. deposition on a declared carrier lattice with a carried remainder | `hnn::constitution::{Lattice, NormalLaw}` |
| `HNN/LatticeWord` | Decision 24: transients and inverse charts on declared lattices, certified residuals | `hnn::{word, propagation, constitution}` |
| `HNN/Ratio` | 5. the Holon ratio at the receiver's face, and the carried power | `hnn::ratio` |
| `HNN/TargetFace` | Decision 26: the target's code face, the margin rule, the receiving locus's exogenous normal law | `hnn::{ratio, constitution}` |
| `HNN/StandingRead` | Decision 26: the face reads the receiving parametron's bound harmonic coordinate | `hnn::receiving` |
| `HNN/IndexedOpen` | Decision 26: the source opens on its indexed, normalized counts | `hnn::moment` |
| `HNN/RegionCounts` | Decision 27: the receiving face is the grain of the receiving parametron's region class masses, corrected by the wave | `hnn::receiving` (target owner); KT baseline `hnn::reference` |
| `HNN/LandmarkTree` | Decision 28: the receiving face compresses landmarks, context-tree weighting over typed addresses (Decision 27 is its depth-one case) | `hnn::landmark` |
| `HNN/LandmarkAddress` | Campaign 2, item 13: the receiving letters, typed bundles restricted by whole bundles, their finite partitions and injective codes, the enlarged tree keeping the cell-only branch | `hnn::{landmark, receiving}` |
| `HNN/LandmarkCarrier` | Campaign 2, item 14: the tree's carriers rebase past their width with an enclosed released remainder | `hnn::landmark` |
| `HNN/Retention` | 6. retention as the collapse onto what the admitted future distinguishes | `hnn::{retention, pending}` |
| `HNN/Keys` | 7. keys by loop closure, and selective stepping | `hnn::keys` |
| `HNN/Ring` | campaign 2, item 8: the ring's mode tick keeps `Q = diag(K, C)`, its denominator, its executed balance with pump and port work, the two-port reference change, crossings as epoch ticks, the pump and the sheets | `hnn::ring` |
| `HNN/Contact` | campaign 2, item 8: the contact's transfer and site kind by its stiffness's sign, the boost's certified solve or singular direction, the signed-storage balance, the lock address from the measured winding pair | `hnn::contact`, `hnn::propagation` |
| `HNN/ContactBreak` | campaign 2, item 8: the released storage `R = E_a + W_a − D_a − E_a′`, the advance `R ≥ J`, Griffith's closed-port case, the parted face's typed gluing defect | `hnn::contact`, `hnn::field` |
| `HNN/BornFace` | Decision 33: the wave read by the Born rule, a finitely correlated receiver on the receiving ring's register: the normalized digit split and dyadic cell face, the reception keeping a density, the density as the retained quotient, the absorbed unitary tick, the interference zero no nonnegative receiver makes, the exact covector and the Fisher-scored step | `hnn::born` |
| `HNN/LocalWeighing` | Decision 34: weighing is local: the forward mixture over faces (its telescope, dominance, Bayes-then-kernel step and executed chart), the static two-face prior and the fixed share with its switch price, the tree over own weights (node-local mixing: normalized, Kraft-complete, each landmark paying at most `−log₂` of its prior weight) and the stop-weight mixture per digit tree | `hnn::landmark::{Landmarks::local, LocalLaw, StopMixture, JoinTree}`, `hnn::receiving::Mixture::switching` |
| `HNN/ConvergenceFounding` | Decision 36: a landmark is founded where paths converge, at its second arrival: the stopped path normalized under any stopping rule decided before the symbol (a complete prequential code), the tree with absent children (the Kraft form of its prior over pruned trees and its dominance), the stopped step (`β` still at the stop), Decision 28's tree as the case found at the first arrival, and the convergence standing whose root weight is the product of the stopped faces | retired; realization at `d137e8a6` |
| `HNN/LandmarkCompaction` | Decision 37: the tree is stored at the faces where paths part: a unary chain with its bottom is one node at the summed rung (`chain_ratio`, `chain_ratio_dyadic`: `E − W = ∏ (1 − w_i)(E − X)`, `∏ (1 − w_i) = 2^(−S)`, founded at `2^S − 1`), a chain ending at the declared depth is one KT node (`leaf_chain_is_one_node`), a split's closed-form ratios and the pass-through of an upper part with no rung (`chain_split`, `chain_split_pass`), the compacted tree (parting nodes and leaves; a unary root folds into its chain, and the root is kept only while nothing has arrived) is Decision 28's tree code for code, weight, face and prequential code exactly in `ℚ` at any rungs `j_d ≥ 0`, a forced depth's rung `0` (`compacted_is_decision_28`), and it keeps at most `2n − 1` nodes over `n ≥ 1` arrivals at any depth (`compacted_node_bound`) | `hnn::landmark` compacted storage |
-/
