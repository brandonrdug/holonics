import Holonics.Compression.Landmark.Context.Tree
import Holonics.Compression.Landmark.Context.Standing
import Holonics.Compression.Landmark.Context.Address
import Holonics.Compression.Landmark.Context.Carrier
import Holonics.Compression.Landmark.Context.LocalWeighing
import Holonics.Compression.Landmark.Context.Population
import Holonics.Compression.Landmark.Context.Dormancy
import Holonics.Compression.Landmark.Context.Composition
import Holonics.Compression.Landmark.Context.Evolution
import Holonics.Compression.Landmark.Context.Merge
import Holonics.Compression.Landmark.Context.ConvergenceFounding
import Holonics.Compression.Landmark.Context.Compaction
import Holonics.Compression.Landmark.Context.Capacity
import Holonics.Compression.Landmark.Context.Epoch

/-!
# The receiving tree: the shift navigator's landmarks

[definition; agent-inferred] The unity audit of September 27 (`research/records/2026-09-27_THE_
HOLARCHY_AND_ITS_AEONS_ARE_THE_TOP_THE_DECISIONS_DISSOLVE_INTO_THEIR_OWNERS_AND_LEARNING_IS_
PROTOTYPED_WHERE_A_HOLARCHY_MADE_THE_TERRAIN.md`, §2, Order item 2). A source read cell by cell is
a passage of the **shift navigator**: each tick pushes its letter onto the address. A node of the
receiving tree is a **context**, the face where every path ending in that context converges, which
is the elementary objects' definition of a landmark: the same object the sibling owners locate for
other navigators (site kinds, fixed points, identities, primitive cycles). The HNN reads the tree
as the receiving parametron's storage (Rust `hnn::receiving` over `compression::landmark::context`).
The computational object is the helical pair interaction's receiving tree; of the winding guide's
six general objects it touches the **tower thread** (context depth as restriction), **faces and
placement** (the digit faces) and the **helix** (the register's carry); the pair, the cell holonomy
and the tube stay attached.

The joins to the framework ([proved-derived; formal-checked]):
- **Standing** (`Context/Standing`): for a tree source over a pruned tree `S`, the address at the
  declared depth is a `Foundation/Standing.StandingLaw` on the shift navigator's words
  (`address_standing`), and so is the leaf-context map when `S`'s leaves are closed under the shift
  (`leaf_standing`; not otherwise, `unclosed_leaf_is_not_a_standing`). The tree's weight is the
  stop prior's mixture over these candidate standings, each pruned tree's likelihood its tree
  source's (`tree_source_likelihood`, `mixture_over_leaf_standings`), and its dominance bound
  (`Tree.own_kraft_and_dominance`) is the code cost of choosing among them.
- **Epoch** (`Context/Epoch`): a node's section is certified, its arrivals are the epoch index of
  its ticks (`Aeon/Clock/Epoch.epochOf`; `arrivals_are_epochs`), and its register, the capped one
  included, is a function of that epoch history, whose total never passes the epoch index
  (`node_register_on_epochs`, `capped_register_on_epochs`).

| Module | Law | Rust consumer |
|---|---|---|
| `Context/Tree` | context-tree weighting over typed addresses: KT masses, the opened-path face and its step, the Kraft form and dominance over pruned trees under any stop prior and any node law, the digit emission and its lattice chart, the cochain, the deposition join, founding and release, the receiver's two-face mixture | `compression::landmark::context::{Landmarks, IdealLandmarks, StopPrior, Beta}`, `hnn::receiving::Mixture` |
| `Context/Standing` | each pruned tree is a candidate standing on the shift navigator's words; the tree is their mixture | the module doc of `compression::landmark::context` |
| `Context/Address` | the receiving letters: typed bundles restricted by whole bundles, their finite partitions and injective codes, the enlarged tree keeping the cell-only branch | `compression::landmark::context::{Letter, Bundle, LetterFamily}`, `hnn::receiving::LetterReader` |
| `Context/Carrier` | the tree's carriers rebase past their width with an enclosed released remainder | `compression::landmark::context::Beta` |
| `Context/LocalWeighing` | weighing is local: the forward mixture over faces, the two-face prior and the fixed share, node-local mixing over own weights, the stop-weight mixture per digit tree | `compression::landmark::context::{StopMixture, JoinTree, FaceJoins}`, `receiver::population::Dormancy` (the fixed share; `Mixture::switching` retired September 28) |
| `Context/Population` | the egg population: the static mixture with death (nonnegative faces; a family at zero likelihood keeps weight zero, the population codes within its prior of every living family), survivor filtering as uniform Bayes (`log₂ \|K\| − log₂ #S`), a product key space's survivors, and death as an exchange (the dead mass is the survivors' gain) | `receiver::population::{Population, Survivors, KeyFamily, DeathReceipt}` |
| `Context/Dormancy` | the population's dormancy: the forward mixture with nonnegative faces, keys filtered only where their layers sound (`log₂ \|K\| − log₂ #S_σ` plus the activity path's code), independent layers, and the fixed share's path code (a switch pays `j` bits at `α = 2^(−j)`) | `receiver::population::{Dormancy, DormantFamily}` |
| `Context/Composition` | composition at ports: a keystone's keys weigh the family that reads its port (`P_(A⊳B)(x \| past) = Σ_a P_A(a \| past) P_B(x \| past, a)`), the composed face a face where the constituents' are (nonnegative, summing to one, positive where a weighted key's is), its telescope, and the chain rule along the surviving keys (`code(A⊳B) = log₂ \|κ\| − log₂ #S + code(B \| A)`) | `receiver::population::{Composed, Keystone, PortPath, PortedEmitters, Unheld}` |
| `Context/Evolution` | the evolved prior across aeons (the Dirichlet face of the retained selection counts at the survival pseudo-count, KT's `½` until a death, mixed with the description prior at a declared `λ`: a prior, keeping the declared mass, at most `−log₂ λ` over the face and `−log₂(1 − λ)` over the description, and the aeon's code at most the selected family's plus `−log₂ π`), and species collapse relative to the admitted future (one member a species at the summed weight changes no face and no code over it, and splits exactly) | `receiver::population::{Selections, Tally, Population::evolved, Population::collapse, Population::split}` |
| `Context/Merge` | merges as species of cells: a merged cell's face reconstructs its members' by the declared expansion, the code-length pair (a merge lowers the complete code exactly when `W′/W > 2^d`; `P·W < P′·W′` for masses), the restaurant description at `α = ½` (seatings a face at every step, a merge of blocks of `a` and `b` multiplying it by `2·(a + b − 1)!/((a − 1)!(b − 1)!)`), the segmentation lattice's mass a probability law, the merged encoding square or a separator, and a release exactly when the merged cells are future-equivalent (changing no admitted code) | `receiver::population::merge::{Blocks, learn_hazard_partition}`, `receiver::population::HazardPartition` |
| `Context/ConvergenceFounding` | founding at the second arrival (retired as a realization, measured at `d137e8a6`): the stopped path under any stopping rule, the tree with absent children, and the first-arrival tree as its case (`first_arrival_is_the_full_tree`) | none (the law of absent children and stopping rules) |
| `Context/Compaction` | the tree stored where paths part: a unary chain is one node at its summed rung, the compacted tree is the full tree code for code (`compacted_is_the_full_tree`) under any node law, with at most `2n − 1` nodes | `compression::landmark::context::Landmarks` (its arena) |
| `Context/Capacity` | a landmark's register has a capacity: the capped register is a node law, its carry only lowers the register, `c = ∞` and every unreached ceiling are KT's | `compression::landmark::context::Capacity` |
| `Context/Epoch` | a node's arrivals are the epochs of its section; the register, capped or not, is read on them | `compression::landmark::context::Capacity` (the deposit's count register) |

`HNN/RegionCounts` (the receiving face's region table, grain read and combined face) stays with
the HNN; `Context/Tree` reads its KT count laws.
-/
