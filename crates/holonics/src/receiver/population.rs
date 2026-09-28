//! **The egg population: a receiver's Bayesian mixture over declared navigator families**
//! (`docs/ELEMENTARY_OBJECTS.md`, "The egg: a generator read as a whole";
//! `docs/RECEIVER_HOLARCHY.md`, "Probability is a receiver geometry"; rebuild step 4 item 4, #73).
//!
//! [definition; agent-inferred] **A population is a receiver's mixture over candidate eggs.** Each
//! candidate is a declared navigator family `f` ([`Family`]): its declared description `ℓ_f` bits,
//! its own predictive face `P_f(· | past)` on the declared cell alphabet, its deposit, and its
//! decoder's readout (its surviving keys, or its standing). No new object enters: the population
//! is the receiver's mixture and a family is a navigator family with its initial configuration
//! (the egg's genome) left to be located. The prior is Kraft's, `2^(−ℓ_f)`, normalized over the
//! declared families by their declared total mass `M = Σ_f 2^(−ℓ_f) ≤ 1` ([`Population::mass`];
//! the unused mass `1 − M` is reserved beside it): `π_f = 2^(−ℓ_f)/M`, over the founded mass once a
//! family is born (below, "Birth from reserved mass").
//!
//! [proved-derived; formal-checked] **Selection is Bayes, and Bayes is the discrete replicator.**
//! A received cell `x` reweighs the families by their faces of it,
//! `w_f′ = w_f P_f(x)/Σ_g w_g P_g(x)` (Lean `Computation/HolonicAdjointNormalization.
//! {bayes_eq_face, bayes_eq_discrete_replicator}`), and the population's face is
//! `q(x) = Σ_f w_f P_f(x)` ([`Population::face`]). **A family dies exactly at zero likelihood**
//! (`replicator_eq_zero_iff`): a positive but poor face only lowers its weight; a family whose face
//! gives the received cell zero dies, its mass passes to the survivors (below, "Death is an
//! exchange"), and it is never read again. The population's product of
//! faces telescopes to its families' likelihoods (Lean
//! `Compression/Landmark/Context/Population.population_mixture`, the static mixture with death):
//!
//! ```text
//! ∏_(t<n) q_t(x_t) = W = Σ_f π_f L_f,    L_f = ∏_(t<n) P_f(x_t | past)
//! −log₂ W ≤ −log₂ π_f − log₂ L_f          every family f alive at n
//! ```
//!
//! so the population's code ([`Population::code`]) is read once from its families' likelihoods and
//! never from carried weights: no chart drift enters it.
//!
//! [proved-derived; formal-checked] **A deterministic family is survivor filtering**
//! ([`Survivors`]; Lean `Population.survivor_code`). A finite key space `K` of emitters, each key
//! emitting one class a tick (the terrain's own navigators keyed by it), under the uniform prior:
//! the survivors `S_t` are the keys whose emissions agree with every cell before `t`; the family's
//! face of class `c` is the fraction of survivors emitting `c`, exact; and its likelihood
//! telescopes to `L = #S_n/|K|`, so its code is `log₂ |K| − log₂ #S_n`, the key description less
//! the surviving fibre (the key description itself when one key survives; the gauge orbit's
//! `log₂` less when a gauge fibre survives). A **factorized** key space `K = Π_i K_i` whose emission
//! is the mixed-radix tuple of the factors' emissions keeps a product of survivor sets, so its face
//! is the product of the factors' faces and its code the sum of theirs
//! (`Population.survivors_product`; [`KeyFamily`]).
//!
//! [definition; agent-inferred] **Why the population does not reuse the context tree's joins**
//! (`compression::landmark::context::{JoinTree, FaceJoins}`): the joins carry each two-face ratio
//! `β` on the tree's lattice and admit only digit faces inside the open unit interval. A
//! deterministic family's face is zero on the classes no survivor emits, and its death (zero
//! likelihood) is the replicator's law, which a positive carried ratio cannot reach. So the
//! population carries no weights at all: each family carries its own likelihood (exact for
//! survivors, `#S/|K|`; the tree's product of executed dyadic faces enclosed by
//! `compression::landmark::context::PassageCode`'s outward bounds), and the population's code, its
//! posteriors and its face are read from them through the telescope, each an exact enclosure
//! ([`Population::receipt`]). The bounds are kept at [`PRECISION`] significant bits, rounded
//! outward at every operation, and the codes are rounded out on the enclosure grid
//! (`ratio::algebraic::LOG_OCTAVES`).
//!
//! [definition; agent-inferred] **The owner.** The population is the receiver's: a receiver reads a
//! passage and weighs the navigator families it admits by their faces of it, so its owner is
//! `receiver::population`, beside `receiver::standing` (a standing is what one family retains; a
//! population is what the receiver retains over its families: each family's retained state and its
//! likelihood, never a record of the cells). The families it declares ([`families`]) read their
//! key spaces from the terrain's own declarations (`holarchy::terrain::MoireFamily`, the field's
//! ring for a rotor crib) and the receiving tree from `compression::landmark::context`.
//!
//! [proved-derived; formal-checked] **Dormancy** ([`dormancy`]; Lean
//! `Compression/Landmark/Context/Dormancy`). A static family of fixed keys cannot follow an aeon
//! switch: on the dormant-grating terrain every grating key dies at the first cell the silent layer
//! changes. The dormant family ([`DormantFamily`]) reads each ring as a layer that is active or
//! dormant: a dormant layer is silent while its ring's clock keeps winding, so its key is retained
//! through the aeon, filtered only where the layer sounds (`layer_survivors`), and each layer's
//! activity switches between cells under the fixed share at `α = 2^(−j)` (`LocalWeighing.shareKernel`,
//! independent layers `Dormancy.productKernel`). The exact mixture codes within
//! `log₂ |K| − log₂ #S_σ` plus the activity path's fixed-share code over its transitions between
//! received cells, for every path `σ` (`dormant_survivor_code`), and a switch costs `j` bits, the
//! `log₂` of its positions when `n ≤ 2^j` (`share_path_code_le`). The executed family codes within
//! that bound plus its certified drift `3 · r · 2^(−62)` bits, `r` its roundings counted
//! ([established-bounded]; [`Dormancy::drift`], the `dormancy` module's "The executed chart").
//! Death is reserved for keys contradicted while active.
//!
//! [proved-derived; formal-checked] **Death is an exchange, never a deletion** (Brandon, September
//! 27: "the death is felt by whatever killed it"; Lean `Population.death_is_an_exchange`, a
//! corollary of `sum_replicator`). A family dies exactly at zero likelihood; its mass `w_f` passes to
//! the survivors: the population's mass is conserved, and the survivors' total gain is the dead
//! mass. Bayes fixes only that total. [definition] **The per-survivor attribution**: survivor `g`
//! receives `w_f w′_g` of dead family `f`'s mass (`w′_g = c_g P_g(x)/Σ_(h alive) c_h P_h(x)`, Bayes'
//! normalization stated as the transfer), and under it each dead family's shares sum to `w_f`
//! (`death_is_an_exchange`'s dead-family clause). The reception returns a [`DeathReceipt`]: the
//! killing cell and the class that arrived, the dead family's last face (a death is not a deposit,
//! so the dead family keeps the state it died in), the exhausted factor, the dying mass and the
//! shares (enclosed, and exact when every living likelihood is), and its seed. Within a key family a
//! key's death is the same exchange: the face of the arrived class is the surviving fraction, and the
//! dying fraction passes to the survivors in proportion.
//!
//! [definition; agent-inferred] **A death keeps the seed** (Brandon, September 27: "faces that are
//! irrelevant can become relevant"). A dead key family's seed is the keys it held when it died; they
//! stay in its declared key space ([`Survivors::seeded`]), and [`Population::refound`] re-founds
//! them at a later cell, their clocks wound to it, charged half the reserved mass (the declared prior
//! share of a re-founding, so births never exhaust the reserve), never the relearning of the key
//! space. A newborn seed that dies returns the seed to its family, which can be re-founded again. A
//! composed egg's seed is its keystone's surviving keys: their ports wind without the cells, so it is
//! re-founded with each conditioned family re-founded from its own seed or declared anew on the path
//! read from the cell ([`Composed`]'s `reseed`).
//!
//! [definition; agent-inferred] **Birth from reserved mass.** The declared families take
//! `M = Σ_f 2^(−ℓ_f)`; the unused `1 − M` is reserved. A family founded at cell `t_g`
//! ([`Population::found`]) draws its mass `2^(−ℓ_g)` from it and abstained before its birth (it
//! predicted with the population's own face), so it inherits the population's likelihood `W_(t_g)`:
//!
//! ```text
//! W_n = [Σ_f 2^(−ℓ_f) L_f + Σ_g m_g W_(t_g) L_g[t_g, n)] / M_n,     M_n = M + Σ_g m_g
//! −log₂ W_n ≤ −log₂(m_g/M_n) + (−log₂ W_(t_g)) − log₂ L_g[t_g, n)     every newborn g
//! ```
//!
//! so the population's code does not move at a birth and the newborn pays its charge once. The
//! trigger ([`Founding`]) is the population's residual: at the receiver's section every
//! `section_period` cells, when the code paid since the previous section passes a founding's charge (the opening
//! section only opens the reading), the most recently dead family's seed is re-founded (with
//! `reseed`), else the next declared candidate. The prior of every founding is declared, never tuned
//! on the cells. [open] Owed (#62): the specialists' telescope of the abstaining newborn in Lean.
//!
//! [proved-derived; measured] **The parity class locates one word, not one rate** ([`families`]
//! module header): its survivors are one species wider than a gauge orbit.
//!
//! [proved-derived; formal-checked] **Eggs compose at ports** ([`composition`]; Lean
//! `Compression/Landmark/Context/Composition`). A keystone ([`Keystone`]) exposes its state at a
//! port, and a family built on the port path through one of its keys reads it; the composed family
//! ([`Composed`]) is the mixture over the keystone's keys, `P_(A⊳B)(x | past) = Σ_a P_A(a | past)
//! P_B(x | past, a)`, its face a face wherever the constituents' are, its product the keystone's
//! prior mixture of the conditioned likelihoods, and under the uniform prior its code the chain
//! rule along the surviving keys, `code(A⊳B) = (log₂ |K_A| − log₂ #S_A) + code(B | A)`. A
//! deterministic keystone is survivor filtered by the family that reads it. A keystone's value is
//! the joint code without it against with it; without it a stateless reader meets its unheld port
//! ([`Unheld`]). The arithmetic eggs ([`arithmetic`]: the record clock, the carry egg, the counter,
//! the sieve) are the first composition.
//!
//! [proved-derived; formal-checked] **The curated source's readers and the boundary egg**
//! ([`families`], [`boundary`]; Lean `Composition.{stagedFace_nonneg, stagedFace_sum_one,
//! staged_chain_rule, staged_code}`; campaign 5). On a curated stream the receiving tree is a family
//! over its cells (bytes and section letters) or over its typed ticks, each cell bundled with its
//! part's channel read once at the section ([`TreeFamily::sectioned`],
//! `compression::landmark::context::sections`). The part clock ([`PartClock`]) is a keystone of one
//! key read from the coded past (bytes since the section letter, sentence closes among them, the last
//! byte's class), and the boundary egg ([`BoundaryEgg`]) factors each cell's face through its stage:
//! the hazard law ([`Hazard`], a KT face per cell of a declared partition of the port) times the byte
//! tree's face within the bytes or the letter tree's face of the letter. Its code is the hazard's
//! plus the conditioned faces', by the chain rule at every tick, and its byte tree read alone is its
//! unheld port, so the part clock's value is exact.
//!
//! [proved-derived; formal-checked] **The admitted receivers** ([`admitted`]; HNN_FORMULA's source
//! contract, item 7; Lean `Composition.{stagedFace_nonneg, stagedFace_sum_one, staged_chain_rule,
//! staged_code}` at a tick's own stage map). The curated source's declared incidence places a
//! response's request, and a later human part's response, on a port the reading part is located
//! on (`compression::landmark::context::spans`: the longest suffix of the part that recurs in the
//! target's span, and the span's byte after it). The admitted egg ([`AdmittedEgg`]) factors the
//! boundary egg's face through a copy stage, a KT face per cell of a declared partition (the
//! located length's and the inner egg's odds' dyadic classes) of whether the located byte comes
//! next; the later human's stage is a receipt only, never the family's face. Its inner egg read
//! alone is the port unheld, and the incidence is coded where it arrives and charged beside the
//! cells.
//!
//! [definition; agent-inferred] **Identity** ([`evolution`]). A family's identity across aeons is
//! its declaration ([`Family::declaration`]: the generator family's kind, declared integers and the
//! declarations it is built on) and its description ([`Identity`]), never its label: a seed
//! re-founded, or the same declaration in a new aeon, carries it.
//!
//! [proved-derived; formal-checked] **The evolved prior** ([`evolution`]; Lean
//! `Compression/Landmark/Context/Evolution`). Across aeons the receiver retains, for each identity,
//! the aeons it was declared, selected and died in ([`Selections`], [`Tally`]), and nothing else. At
//! an aeon's opening ([`Population::evolved`]) the declared families' prior is
//! `π(f) = λ D(f) + (1 − λ) 2^(−ℓ_f)/M`, `D(f) = (s_f + σ_f)/Σ_g (s_g + σ_g)` the Dirichlet face of
//! the selections at the survival pseudo-count `σ_f = (2(a_f − d_f) + 1)/(2(2a_f + 1))` (KT's `½`
//! until a death), at the static total mass `M` (the reserve unchanged), and the aeon's code is at
//! most the selected family's code plus `−log₂ π(f)` in an aeon without births
//! (`evolved_aeon_code`). A birth renormalizes the declared priors to `m_f/M_n`, so once births have
//! founded the mass `M_n` the bound gains `log₂(M_n/M)` ([`evolution`]; its Lean owed with the
//! newborn's telescope, #62). A family is founded at a declared rational mass with
//! [`Population::found_with`].
//!
//! [proved-derived; formal-checked] **Species collapse** ([`species`]; Lean `Evolution.{species_face,
//! species_collapse_code, species_split}`). Surviving keys whose conditioned faces agree for every
//! admitted receiver over the declared admitted future ([`AdmittedFuture`]: the next `h` ticks or
//! every tick; the exact check is the key space's own [`Emitters::signature`]) are one species: one
//! member at the summed posterior ([`Population::collapse`]), which changes no code for the admitted
//! future, the receipt ([`Collapse`]) keeping every member's seed; a collapsed family refuses a cell
//! past its admitted future, and [`Population::split`] restores every member of a surviving species
//! at its share, so a wider future can collapse again. A composed egg collapses within each keystone
//! key's conditioned family and merges the keystone keys whose conditioned families are certain with
//! one signature.
//!
//! [proved-derived; formal-checked] **Merges are species of cells** ([`merge`]; Lean
//! `Compression/Landmark/Context/Merge`). A partition's cells merge by the same quotient as keys: a
//! **release** when the merged cells' faces agree at every admitted reading (no code changes,
//! `release_merge_iff_future_equivalent`), or a **priced merge** that pools counts and is accepted
//! exactly when it lowers the complete code, the description's restaurant mass at `α = ½` times the
//! likelihood (`merge_cost_mass_iff`, `restaurant_merge_ratio`), decided by integer bounds. Every
//! member keeps its counts, so a merged block splits exactly. The boundary egg's hazard reads a
//! partition learned this way on the development cells ([`learn_hazard_partition`]: the last-byte
//! classes, then the ports' shared counts, each adopted where its complete code falls).
//!
//! [definition; agent-inferred] **Maintenance work** ([`Work`], [`Act`]). Beside a family's
//! description and code its receipt reports the work it has spent, as exact counts of what it
//! executed: a key family's emissions read against received cells, a dormant family's states read
//! and kernel shares, a tree's deposits and held nodes, a composed egg's keystone keys weighed and its
//! constituents' work, a carry egg's digit products, and a sieve's window decided once by face (its
//! gratings' maintenance). No family here is pumped against dissipation (every ring is a lossless
//! exact clock), so no pump work is claimed: the counts are the computation the families actually
//! execute.
//!
//! [definition; agent-inferred] **A partition's reading** ([`Population::receive_partitioned`],
//! [`PartReading`]). A receipt is a field of readings over a partition: the passage's cells declared
//! into parts (a product record's operand, mark, trailing, middle and leading cells), and on each
//! part the population's code (`Σ_(t ∈ part) −log₂ q_t(x_t)`, read as the population's code after
//! each cell less its code before) and each family's code (`−log₂` of its faces' product over the
//! part). The population keeps only each part's sums while reading, never the cells: a receipt, not
//! a record.
//!
//! [definition] The computational object is the helical pair interaction, read here as a
//! receiver's population of candidate eggs through aeons. Of the winding guide's six general objects
//! this owner touches four: the **helix** (a grating's key is its ring's rate and phase, a clock with
//! carry, read at its half-turn sheet, which keeps winding while its layer is silent; a rotor key's
//! stage steps with the field's carry), the **tube** (the passage, one cell a tick, and an aeon's span
//! at one activity), **faces and placement** (each family's face on the receiver's cell alphabet,
//! and the population's face, exact or enclosed) and the **tower thread** (the tree family's
//! restrictions of the address). The **pair** (a moiré's pairs lock, which a grating key names but
//! no family reads) and the **cell holonomy** (none is claimed) stay attached.
//!
//! | Lean | Rust |
//! |---|---|
//! | `Computation/HolonicAdjointNormalization.{bayes_eq_face, bayes_eq_discrete_replicator, replicator_eq_zero_iff}` | [`Population::receive`] (a family's weight moves by its face; zero face, death) |
//! | `Compression/Landmark/Context/LocalWeighing.static_mixture` (positive faces) | the telescope's positive case |
//! | `Compression/Landmark/Context/Population.population_mixture` (the static mixture with death) | [`Population::code`], [`Population::receipt`] |
//! | `Compression/Landmark/Context/Population.survivor_code` | [`Survivors`] |
//! | `Compression/Landmark/Context/Population.survivors_product` | [`KeyFamily`]'s factors |
//! | `Compression/Landmark/Context/Population.{seqLik_escaped_survivor, escaped_fibre_is_mode}` | [`ChaseFamily`] (the escaped face), [`selected_fibre`] |
//! | `Compression/Landmark/Context/Population.death_is_an_exchange` | [`DeathReceipt`] (the exchange of [`Population::receive`]) |
//! | `Compression/Landmark/Context/Dormancy.{forward_dominance_nonneg, dormant_survivor_code, layer_survivors, productKernel_stochastic, productKernel_path}` | [`Dormancy`], [`DormantFamily`] |
//! | `Compression/Landmark/Context/Dormancy.{share_path_code, stay_code_le, share_path_code_le}` | the declared rate `α = 2^(−j)` of [`Dormancy::new`] |
//! | owed (#62): the abstaining newborn's telescope | [`Population::found`], [`Population::refound`] |
//! | `Compression/Landmark/Context/Composition.{composedFace_received, composedFace_nonneg, composedFace_sum_one, composedFace_pos, composed_telescope}` | [`Composed`] (its face and its likelihood) |
//! | `Compression/Landmark/Context/Composition.{chain_rule, chain_rule_of_species}` | [`Composed`]'s code over a keystone's keys; [`PortedEmitters`] under `KeyFamily` (a deterministic reader: `log₂ \|K_A\| − log₂ #S`) |
//! | `Compression/Landmark/Context/Evolution.{survivalPseudo_zero_deaths, survivalPseudo_death_lt, dirichletFace_isPrior, kt_face, dirichletFace_no_deaths, descriptionPrior_isPrior, evolved_isPrior, masses_total}` | [`Tally::pseudo`], [`Selections::face`], [`Selections::prior`], [`Population::evolved`] |
//! | `Compression/Landmark/Context/Evolution.{evolved_code_le_face, evolved_code_le_description, evolved_aeon_code}` | the evolved population's code against its selected family's |
//! | `Compression/Landmark/Context/Evolution.{speciesWeight_isPrior, species_mixture, species_face, species_collapse_code, species_split}` | [`Population::collapse`], [`Population::split`], [`Collapse`] |
//! | `Compression/Landmark/Context/Composition.{stagedFace_nonneg, stagedFace_sum_one, staged_chain_rule, staged_code}` | [`BoundaryEgg`] (its staged face and its code by stage, [`BoundaryReadout`]) |
//! | `Compression/Landmark/Context/Tree.{ktFace, ktFace_pos, ktFace_sum}` (over `{byte, letter}`) | [`Hazard`] |
//! | `Compression/Landmark/Context/Composition.{stagedFace_nonneg, stagedFace_sum_one}` at each tick's `σ_t`, `{staged_chain_rule, staged_code}` at `σ = id` | [`AdmittedEgg`] (the copy stage over the inner egg, [`StageReadout`]) |
//! | `Compression/Landmark/Context/Tree.{ktFace, ktFace_pos, ktFace_sum}` (over `{miss, copy}`, the pointer's sides) | [`CopyStage`], [`PointerReadout`] |
//! | `Compression/Landmark/Context/Merge.{merge_cost_iff, merge_cost_mass_iff, merge_cost_nat}` | [`Blocks::price`] (accepted exactly when `P·W < P′·W′`) |
//! | `Compression/Landmark/Context/Merge.{restaurant_found, restaurant_join, restaurant_step_sum, restaurant_merge_ratio, restaurant_merge_ratio_ge_two}` | [`restaurant_ratio`], [`Blocks::description_bits`] |
//! | `Compression/Landmark/Context/Merge.{expand_merge, expansion_sum, mergedFace_isPrior}` | [`Blocks`] (a block's pooled counts; every member's seed, [`Blocks::split`]) |
//! | `Compression/Landmark/Context/Merge.{release_merge_iff_future_equivalent, release_merge_code}` | [`Blocks::species`] (the release reading) |
//! | `Compression/Landmark/Context/Merge.{segmentation_mass, parse_given_sum, parse_code, segmentation_code_le}`, `{square_iff_no_separator, encoding_square_or_separator, merged_square_of_compatible}` | owed consumers: word merges over segmentation lattices and the merged encoding's square (campaign 5) |

pub mod admitted;
pub mod arithmetic;
pub use checkpoint::{
    AdmittedMemberManifest, PopulationCheckpointError, PopulationMemberManifest, TreeMemberManifest,
};
pub mod boundary;
pub mod chase;
pub mod chaser;
pub mod checkpoint;
pub mod composition;
pub mod dormancy;
pub mod evolution;
pub mod families;
pub mod family_release;
pub mod health;
pub mod merge;
pub mod provenance;
pub mod releasing;
pub mod sampling;
pub mod species;
pub mod text_release;

#[cfg(test)]
mod composition_tests;
#[cfg(test)]
mod evolution_tests;
#[cfg(test)]
mod family_release_tests;
#[cfg(test)]
mod future_branch_tests;
#[cfg(test)]
mod health_tests;
#[cfg(test)]
mod provenance_tests;
#[cfg(test)]
mod releasing_tests;
#[cfg(test)]
mod sampling_tests;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod text_release_tests;

pub use admitted::{
    AdmittedEgg, AdmittedReadout, CopyCell, CopyLaw, CopyStage, PointerReadout, Relation,
    RelationKind, StageReadout, odds_class,
};
pub use arithmetic::{CarryEgg, Counter, RecordClock, Sieve, SieveFace};
pub use boundary::{
    BYTE_VALUES, BoundaryEgg, BoundaryReadout, Hazard, HazardCell, HazardComparison,
    HazardPartition, HazardRest, LastByte, PartClock, PartPort, byte_index, dyadic_class,
};
pub use chase::{ChaseFamily, selected_fibre};
pub use chaser::{MachineChaser, MachineDeclaration, MachineReceipt, Release};
pub use composition::{
    Composed, Conditioned, Keystone, Port, PortPath, PortReader, PortedEmitters, Unheld,
};
pub use dormancy::{Dormancy, DormantFamily, Layered, Weight};
pub use evolution::{Declaration, Identity, Selections, Tally};
pub use families::{GratingParity, GratingSheet, RotorKeys, TreeFamily};
pub use family_release::{FamilyReleaseError, select_family_class};
pub use health::{
    PopulationReceivingFaceHealth, PopulationReceivingFaceHealthError,
    population_receiving_face_health,
};
pub use merge::{
    Blocks, Item, KtTables, MergeReceipt, PartitionReceipt, Price, learn_hazard_partition,
    restaurant_ratio,
};
pub use provenance::{FaceContribution, MissingProducerTerm};
pub use releasing::{PopulationRelease, ReleaseRefusal};
pub use sampling::{CertifiedClass, CrossingBounds, SamplingError, select_class};
pub use species::{
    AdmittedFuture, Collapse, FactorSpecies, KeystoneMember, KeystoneSpecies, Seed, Species,
};
pub use text_release::{
    TextAppend, TextDecoder, TextRelease, TextReleaseError, TextSeparator, verify_scored_text_path,
};

use std::collections::BTreeMap;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use rayon::prelude::*;
use thiserror::Error;

use crate::compression::landmark::context::{
    ContextError, Landmarks, PassageCode, ProductBound, ratio_code_length,
};
use crate::hnn::HnnError;
use crate::holarchy::terrain::TerrainError;
use crate::holon::contact::menu::MenuError;
use crate::ratio::Rat;
use crate::ratio::algebraic::{
    ExactInterval, ExactValueError, LOG_OCTAVES, interval_difference, interval_sum,
};

/// Every refusal of a population. Bad input is a typed return, never a panic.
#[derive(Debug, Error, PartialEq)]
pub enum PopulationError {
    #[error("{what}: {reason}")]
    Declaration {
        what: &'static str,
        reason: &'static str,
    },
    #[error("cell {cell} lies outside the declared alphabet of {alphabet}")]
    CellOutside { cell: usize, alphabet: usize },
    /// A key space past the declared enumeration: survivor filtering is refused, and its keys are
    /// owed to the named Bombe (the construction that locates them by loop closure).
    #[error(
        "the key space of {key_space} keys passes the declared enumeration of {admitted}: survivor filtering is refused; its keys are the Bombe's ({bombe})"
    )]
    Bombe {
        key_space: BigUint,
        admitted: BigUint,
        bombe: &'static str,
    },
    #[error(
        "every family's likelihood reached zero by cell {cell}: no declared family made the passage"
    )]
    Extinct { cell: usize },
    #[error("family {label} does not expose a contemporary standing for future branching")]
    FutureBranchUnsupported { label: String },
    #[error("a population with a live founding closure cannot be branched")]
    FutureBranchFounding,
    #[error(transparent)]
    Context(#[from] ContextError),
    #[error(transparent)]
    Exact(#[from] ExactValueError),
    #[error(transparent)]
    Menu(#[from] MenuError),
    /// Boxed: a terrain's refusals are wide.
    #[error(transparent)]
    Terrain(Box<TerrainError>),
    /// Boxed: the HNN's refusals are wide.
    #[error(transparent)]
    Hnn(Box<HnnError>),
}

impl From<TerrainError> for PopulationError {
    fn from(error: TerrainError) -> Self {
        Self::Terrain(Box::new(error))
    }
}

impl From<HnnError> for PopulationError {
    fn from(error: HnnError) -> Self {
        Self::Hnn(Box::new(error))
    }
}

pub(crate) fn refuse(what: &'static str, reason: &'static str) -> PopulationError {
    PopulationError::Declaration { what, reason }
}

// -------------------------------------------------------------------------------------------
// the family

/// [definition] **A family's likelihood** `L_f = ∏_(t<n) P_f(x_t | past)`: exact (a survivor
/// family's `#S/|K|`), or enclosed by a passage's product bounds (the tree's executed dyadic faces,
/// `PassageCode`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Likelihood {
    Exact(Rat),
    Enclosed(PassageCode),
}

impl Likelihood {
    /// **The family's code alone** `−log₂ L_f`, enclosed; `None` at zero likelihood (a dead
    /// family's code is unbounded).
    pub fn code(&self) -> Result<Option<ExactInterval>, PopulationError> {
        match self {
            Likelihood::Exact(value) if value.is_zero() => Ok(None),
            Likelihood::Exact(value) => Ok(Some(ratio_code_length(
                value.numer().magnitude(),
                value.denom().magnitude(),
            )?)),
            Likelihood::Enclosed(passage) => Ok(Some(passage.bits()?)),
        }
    }

    /// Whether the likelihood is exactly zero.
    pub fn is_zero(&self) -> bool {
        matches!(self, Likelihood::Exact(value) if value.is_zero())
    }

    /// The likelihood's lower or upper bound.
    fn bound(&self, up: bool) -> Bound {
        match self {
            Likelihood::Exact(value) => Bound::of_rat(value, up),
            Likelihood::Enclosed(passage) => {
                let (numerator, denominator, exponent) = passage.bounds();
                let side = usize::from(up);
                // L ∈ [N_lower/(D_upper 2^E), N_upper/(D_lower 2^E)].
                let (n, d) = (numerator[side], denominator[1 - side]);
                Bound::of_product_bounds(n, d, exponent, up)
            }
        }
    }
}

/// [definition] **A key family's readout** (its decoder): each factor's key space `|K_i|` (one
/// factor for a joint key space) and each factor's surviving keys, each key its coordinates in the
/// family's declared layout ([`Emitters::coordinates`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KeyReadout {
    pub spaces: Vec<u64>,
    pub survivors: Vec<Vec<Vec<u64>>>,
    /// Each factor's survivors' executed posteriors (a dormant family's; empty for a static one,
    /// whose survivors are uniform).
    pub masses: Vec<Vec<Rat>>,
    /// Each factor's layers' executed posterior of dormancy (a dormant family's; empty otherwise).
    pub dormant: Vec<Vec<Rat>>,
}

impl KeyReadout {
    /// `|K| = Π_i |K_i|`.
    pub fn space(&self) -> BigUint {
        self.spaces.iter().map(|&s| BigUint::from(s)).product()
    }

    /// `#S = Π_i #S_i`.
    pub fn count(&self) -> BigUint {
        self.survivors
            .iter()
            .map(|keys| BigUint::from(keys.len()))
            .product()
    }
}

/// [definition] **A family's readout**: a key family's surviving keys, a tree family's standing, a
/// boundary egg's code by stage and channel, or the admitted receivers' (their inner egg's, their
/// copy stages' and their incidence's code).
#[derive(Clone, Debug, PartialEq)]
pub enum Readout<'a> {
    Keys(KeyReadout),
    Standing(&'a Landmarks),
    Boundary(Box<BoundaryReadout>),
    Admitted(Box<AdmittedReadout>),
}

/// [definition] **A declared navigator family** (module header): a candidate egg read by the
/// receiver.
pub trait Family: Send {
    /// Canonical contemporary checkpoint bytes for owners with a declared native codec.
    /// Unsupported family owners return `None`; the population codec refuses them.
    fn tree_checkpoint(&self) -> Option<Vec<u8>> {
        None
    }
    /// Cell ticks already received by a tree owner that exposes the tree-only checkpoint.
    fn tree_received_cells(&self) -> Option<u64> {
        None
    }
    /// Canonical contemporary checkpoint for the admitted request/response receiver, when owned.
    fn admitted_checkpoint(
        &self,
    ) -> Option<Result<Vec<u8>, crate::receiver::population::admitted::AdmittedStageCheckpointError>>
    {
        None
    }
    /// Cell ticks already received by the admitted egg's inner boundary receiver.
    fn admitted_received_cells(&self) -> Option<u64> {
        None
    }
    /// An ephemeral continuation at this family's contemporary standing. Implementations must
    /// copy only the state needed to continue admitted futures; they must not reconstruct by replay.
    fn branch_future(&self) -> Option<Box<dyn Family>> {
        None
    }
    /// The family's declaration, for a receipt.
    fn label(&self) -> String;
    /// The declared cell alphabet.
    fn alphabet(&self) -> usize;
    /// `ℓ_f`: the declaration's description in bits (its prior is `2^(−ℓ_f)` before normalizing).
    fn description(&self) -> u64;
    /// `P_f(· | past)`: the family's face on the alphabet before the next cell, exact.
    fn face(&self) -> Result<Vec<Rat>, PopulationError>;
    /// **Receive one cell**: `P_f(x | past)` read before the deposit, then the deposit.
    fn receive(&mut self, cell: usize) -> Result<Rat, PopulationError>;
    /// `L_f`: the product of the faces received so far.
    fn likelihood(&self) -> Likelihood;
    /// The decoder's readout.
    fn readout(&self) -> Readout<'_>;
    /// **Whether the family admits a passage** before anything moves: a declared refusal (a cell
    /// outside the alphabet, a passage past a declared population) is read here, so a population
    /// refuses a cell before any family receives it.
    fn admits(&self, cells: &[usize]) -> Result<(), PopulationError> {
        let alphabet = self.alphabet();
        match cells.iter().find(|&&cell| cell >= alphabet) {
            Some(&cell) => Err(PopulationError::CellOutside { cell, alphabet }),
            None => Ok(()),
        }
    }
    /// Whether this family actually owns planned request/response incidence. An unrelated family
    /// may share the population's alphabet but cannot make a requested relation effective.
    fn owns_planned_relation(&self) -> bool {
        false
    }
    /// Validate a receiver incidence planned before its target part arrives. Families that do
    /// not own admitted request/response incidence ignore this operation.
    fn validate_planned_relation(&self, _relation: Relation) -> Result<(), PopulationError> {
        Ok(())
    }
    /// Commit a relation after every living family has validated it. This operation is infallible
    /// so a later family cannot reject after an earlier one has already changed its standing.
    fn commit_planned_relation(&mut self, _relation: Relation) {}
    /// The factor whose every key the killing cell contradicted, once the family has died there.
    fn exhausted(&self) -> Option<usize> {
        None
    }
    /// **The family re-founded from its seed** at cell `at` (module header, "A death keeps the
    /// seed"): the keys it held when it died, under the uniform prior over them, its clocks wound to
    /// `at`; none when its clocks cannot wind without the cells.
    fn reseed(&self, _at: usize) -> Option<Box<dyn Family>> {
        None
    }
    /// **The certified drift** in bits between the family's executed code and its ideal law's
    /// bound (zero for a family whose faces are its law's own).
    fn drift(&self) -> Rat {
        Rat::zero()
    }
    /// **The family's declaration** (module header, "Identity"): its generator family's kind and
    /// declared integers, never its label.
    fn declaration(&self) -> Declaration;
    /// **The family's identity across aeons**: its declaration and its description.
    fn identity(&self) -> Identity {
        Identity {
            declaration: self.declaration(),
            description: self.description(),
        }
    }
    /// **The work the family has spent** (module header, "Maintenance work"): exact counts of what
    /// it executed, by act.
    fn work(&self) -> Work {
        Work::default()
    }
    /// **Collapse the family's surviving keys into species** relative to the admitted future
    /// (module header, "Species collapse"): none when the family declares no exact check.
    fn collapse(&mut self, _future: AdmittedFuture) -> Result<Option<Collapse>, PopulationError> {
        Ok(None)
    }
    /// **Split the species a collapse merged** from its receipt: every member of a surviving
    /// species returns with its share.
    fn split(&mut self, _collapse: &Collapse) -> Result<(), PopulationError> {
        Err(refuse(
            "a species split",
            "the family collapsed its keys into the receipt's species",
        ))
    }
    /// **The family's certain signature** over the admitted future: per factor, the signature
    /// every held key shares, when each factor's keys share one (the family then gives face one on
    /// one class at every admitted tick of every admitted passage it survives); none otherwise.
    fn certain(&self, _future: AdmittedFuture) -> Option<Vec<Vec<usize>>> {
        None
    }
    /// **The family's seed**: the keys it holds, per factor with each key's members, its clock's
    /// reading and its admitted future's end (a key family's).
    fn seed(&self) -> Option<Seed> {
        None
    }
    /// **Hold exactly a seed's keys** (a species member restored at a split), the clock reading the
    /// seed's tick.
    fn restrict(&mut self, _seed: &Seed) -> Result<(), PopulationError> {
        Err(refuse(
            "a species member's restoration",
            "the family holds keys of a declared key space",
        ))
    }
}

/// **A cell's mixed-radix digits** over the declared radices, the first least significant.
pub(crate) fn mixed_radix(radices: impl Iterator<Item = usize>, mut cell: usize) -> Vec<usize> {
    radices
        .map(|radix| {
            let digit = cell % radix;
            cell /= radix;
            digit
        })
        .collect()
}

// -------------------------------------------------------------------------------------------
// the deterministic key family

/// [definition] **A declared finite key space of deterministic emitters** (module header, "A
/// deterministic family"): key `k < |K|` emits one class a tick; the emitters' navigators advance
/// together past each received cell.
pub trait Emitters: Send {
    /// The emitted classes' alphabet.
    fn alphabet(&self) -> usize;
    /// `|K|`.
    fn keys(&self) -> u64;
    /// The class key `k` emits at the current tick.
    fn emit(&self, key: u64) -> usize;
    /// Advance every key's navigator one tick past the received cell.
    fn advance(&mut self, cell: usize) -> Result<(), PopulationError>;
    /// Key `k`'s coordinates in the family's declared layout.
    fn coordinates(&self, key: u64) -> Vec<u64>;
    /// **The emitters again, their clocks reading `tick`** (a seed re-founded at a later cell),
    /// when their clocks wind without the cells (a moiré's rings do; a rotor crib's field steps by
    /// its cells, so it has none).
    fn fork_at(&self, _tick: u64) -> Option<Box<dyn Emitters>> {
        None
    }
    /// **The key space's declaration** (module header, "Identity").
    fn declaration(&self) -> Declaration;
    /// **The class key `k` emits `ticks` ticks after the current one**, read without the cells,
    /// when its clock winds without them.
    fn ahead(&self, _key: u64, _ticks: u64) -> Option<usize> {
        None
    }
    /// **A declared period of key `k`'s emission**: `e_k(t + P) = e_k(t)` at every tick.
    fn period(&self, _key: u64) -> Option<u64> {
        None
    }
    /// **Key `k`'s signature over the admitted future** (module header, "Species collapse"): two
    /// keys with equal signatures emit one class at every admitted tick of every admitted passage.
    /// Over `h` ticks it is the word of the next `h` classes; over the whole future the word of one
    /// least period from the current tick (two periodic words agree forever exactly when their least
    /// periods and one period's words agree). None when the emitters declare no exact check.
    fn signature(&self, key: u64, future: AdmittedFuture) -> Option<Vec<usize>> {
        match future {
            AdmittedFuture::Ticks(ticks) => (0..ticks).map(|t| self.ahead(key, t)).collect(),
            AdmittedFuture::Whole => {
                let period = self.period(key)?;
                let word: Vec<usize> = (0..period)
                    .map(|t| self.ahead(key, t))
                    .collect::<Option<_>>()?;
                let least = (1..=period).find(|&d| {
                    period % d == 0
                        && (d..period).all(|t| word[t as usize] == word[(t - d) as usize])
                })?;
                Some(word[..least as usize].to_vec())
            }
        }
    }
}

/// [definition] **Survivor filtering** (module header): the uniform prior over a declared key
/// space, conditioned on the received cells. The survivors are held as key indices; before the
/// first cell every key survives and none is held. Once collapsed into species (module header,
/// "Species collapse") each held key is its species' representative and carries its members.
pub struct Survivors {
    emitters: Box<dyn Emitters>,
    held: Option<Vec<u64>>,
    /// Each held key's members, once collapsed; none: one member each.
    members: Option<Vec<u64>>,
    count: u64,
    space: u64,
    /// The clock's reading: the ticks the emitters stand at.
    tick: u64,
    /// The tick the admitted future of a collapse ends at (none: every future tick).
    until: Option<u64>,
    /// The emissions read against received cells.
    reads: u64,
}

impl Survivors {
    /// **Declare survivor filtering** over the emitters' key space; refused at an empty key space,
    /// and past the declared enumeration `admitted`, naming the Bombe that owns the larger key
    /// space.
    pub fn new(
        emitters: Box<dyn Emitters>,
        admitted: u64,
        bombe: &'static str,
    ) -> Result<Self, PopulationError> {
        let keys = emitters.keys();
        if keys == 0 || emitters.alphabet() == 0 {
            return Err(refuse(
                "survivor filtering",
                "its key space and its alphabet each hold at least one member",
            ));
        }
        if keys > admitted {
            return Err(PopulationError::Bombe {
                key_space: BigUint::from(keys),
                admitted: BigUint::from(admitted),
                bombe,
            });
        }
        Ok(Self {
            emitters,
            held: None,
            members: None,
            count: keys,
            space: keys,
            tick: 0,
            until: None,
            reads: 0,
        })
    }

    /// **Survivor filtering over a seed** (module header, "A death keeps the seed"): the uniform
    /// prior over the declared keys `seed` of the emitters' key space; refused at an empty seed or a
    /// key outside the space.
    pub fn seeded(emitters: Box<dyn Emitters>, seed: Vec<u64>) -> Result<Self, PopulationError> {
        let seed: Vec<(u64, u64)> = seed.into_iter().map(|key| (key, 1)).collect();
        Self::of_species(emitters, &seed, 0, None)
    }

    /// Survivor filtering over declared keys, each with its members, the clock reading `tick`
    /// and the admitted future ending at `until`; the prior uniform over the members.
    fn of_species(
        emitters: Box<dyn Emitters>,
        seed: &[(u64, u64)],
        tick: u64,
        until: Option<u64>,
    ) -> Result<Self, PopulationError> {
        let keys = emitters.keys();
        if seed.is_empty()
            || seed
                .iter()
                .any(|&(key, members)| key >= keys || members == 0)
            || seed.windows(2).any(|pair| pair[0].0 >= pair[1].0)
        {
            return Err(refuse(
                "a seed's survivor filtering",
                "its seed holds ascending keys of the declared key space, each with a member",
            ));
        }
        let count = seed.iter().map(|&(_, members)| members).sum();
        let members = seed
            .iter()
            .any(|&(_, members)| members > 1)
            .then(|| seed.iter().map(|&(_, members)| members).collect());
        Ok(Self {
            emitters,
            held: Some(seed.iter().map(|&(key, _)| key).collect()),
            members,
            count,
            space: count,
            tick,
            until,
            reads: 0,
        })
    }

    /// The prior's support: `|K|`, or a seed's size.
    pub fn space(&self) -> u64 {
        self.space
    }

    /// `#S`, the survivors (the members of every held species).
    pub fn count(&self) -> u64 {
        self.count
    }

    /// `|K|`.
    pub fn keys(&self) -> u64 {
        self.emitters.keys()
    }

    /// The emitters.
    pub fn emitters(&self) -> &dyn Emitters {
        self.emitters.as_ref()
    }

    /// The clock's reading.
    pub fn tick(&self) -> u64 {
        self.tick
    }

    /// The tick the admitted future of a collapse ends at, if one is declared.
    pub fn until(&self) -> Option<u64> {
        self.until
    }

    /// The surviving keys' indices (each a species' representative once collapsed), ascending.
    pub fn survivors(&self) -> Vec<u64> {
        match &self.held {
            Some(held) => held.clone(),
            None => (0..self.emitters.keys()).collect(),
        }
    }

    /// **Each held key's members**, in the order of [`Survivors::survivors`] (one each until a
    /// collapse).
    pub fn members(&self) -> Vec<u64> {
        match &self.members {
            Some(members) => members.clone(),
            None => vec![1; self.held_len()],
        }
    }

    /// The held keys.
    fn held_len(&self) -> usize {
        match &self.held {
            Some(held) => held.len(),
            None => self.emitters.keys() as usize,
        }
    }

    /// **Each class's surviving members** at the current tick.
    pub fn counts(&self) -> Vec<u64> {
        let mut counts = vec![0u64; self.emitters.alphabet()];
        let mut tally = |key: u64, members: u64| {
            let class = self.emitters.emit(key);
            if let Some(count) = counts.get_mut(class) {
                *count += members;
            }
        };
        match (&self.held, &self.members) {
            (Some(held), Some(members)) => held
                .iter()
                .zip(members)
                .for_each(|(&key, &members)| tally(key, members)),
            (Some(held), None) => held.iter().for_each(|&key| tally(key, 1)),
            (None, _) => (0..self.emitters.keys()).for_each(|key| tally(key, 1)),
        }
        counts
    }

    /// **The family's face**: each class's surviving members over the survivors, exact; all zero
    /// once no key survives.
    pub fn face(&self) -> Vec<Rat> {
        let total = BigInt::from(self.count);
        self.counts()
            .into_iter()
            .map(|count| {
                if self.count == 0 {
                    Rat::zero()
                } else {
                    Rat::new(BigInt::from(count), total.clone())
                }
            })
            .collect()
    }

    /// **The survivors that emit `cell`** at the current tick, ascending: the filter a deposit would
    /// commit, read without moving anything.
    pub fn filter(&self, cell: usize) -> Vec<u64> {
        let emitters = &self.emitters;
        match &self.held {
            Some(held) => held
                .iter()
                .copied()
                .filter(|&key| emitters.emit(key) == cell)
                .collect(),
            None => (0..emitters.keys())
                .filter(|&key| emitters.emit(key) == cell)
                .collect(),
        }
    }

    /// **Commit a filter** read by [`Survivors::filter`] at `cell`: the survivors become exactly
    /// `kept` (an ascending part of the held keys, each keeping its members), and every emitter
    /// advances past the cell.
    fn commit(&mut self, kept: Vec<u64>, cell: usize) -> Result<(), PopulationError> {
        if let (Some(held), Some(members)) = (&self.held, &self.members) {
            let mut next = kept.iter().peekable();
            let kept_members: Vec<u64> = held
                .iter()
                .zip(members)
                .filter_map(|(key, &members)| next.next_if_eq(&key).map(|_| members))
                .collect();
            self.count = kept_members.iter().sum();
            self.members = Some(kept_members);
        } else {
            self.count = kept.len() as u64;
        }
        self.held = Some(kept);
        self.tick += 1;
        self.emitters.advance(cell)
    }

    /// **Receive one cell**: the fraction of survivors emitting it, read before the deposit; then
    /// the survivors keep exactly the keys that emitted it, and every emitter advances. [definition;
    /// agent-inferred] **A death is not a deposit**: when no survivor emits the cell the face is
    /// zero and nothing moves, so the factor keeps the state it died in, and its last face (what it
    /// predicted against what arrived) stays readable for the death's receipt.
    pub fn receive(&mut self, cell: usize) -> Result<Rat, PopulationError> {
        let alphabet = self.emitters.alphabet();
        if cell >= alphabet {
            return Err(PopulationError::CellOutside { cell, alphabet });
        }
        self.reads += self.held_len() as u64;
        let kept = self.filter(cell);
        if kept.is_empty() {
            return Ok(Rat::zero());
        }
        let before = self.count;
        self.commit(kept, cell)?;
        Ok(Rat::new(BigInt::from(self.count), BigInt::from(before)))
    }

    /// `#S/|K|` (a seed's `#S/#seed`), exact.
    pub fn likelihood(&self) -> Rat {
        Rat::new(BigInt::from(self.count), BigInt::from(self.space))
    }

    /// Whether the admitted future admits `cells` more cells.
    fn admits(&self, cells: usize) -> Result<(), PopulationError> {
        match self.until {
            Some(end) if self.tick + cells as u64 > end => Err(refuse(
                "a collapsed key family's passage",
                "it stays within the admitted future its species were collapsed over (split them from their receipt first)",
            )),
            _ => Ok(()),
        }
    }
}

/// [definition] **A key family** (module header): survivor filtering over a key space of one
/// factor, or over a factorized one whose cell is the mixed-radix tuple of its factors' classes
/// (the first factor least significant).
pub struct KeyFamily {
    label: String,
    description: u64,
    factors: Vec<Survivors>,
    exhausted: Option<usize>,
}

impl KeyFamily {
    /// The family of the declared factors; refused without a factor.
    pub fn new(
        label: String,
        description: u64,
        factors: Vec<Survivors>,
    ) -> Result<Self, PopulationError> {
        if factors.is_empty() {
            return Err(refuse("a key family", "it holds at least one factor"));
        }
        Ok(Self {
            label,
            description,
            factors,
            exhausted: None,
        })
    }

    /// The factors.
    pub fn factors(&self) -> &[Survivors] {
        &self.factors
    }

    /// Each factor's digit of a cell.
    fn digits(&self, cell: usize) -> Vec<usize> {
        mixed_radix(
            self.factors.iter().map(|factor| factor.emitters.alphabet()),
            cell,
        )
    }
}

impl Family for KeyFamily {
    fn label(&self) -> String {
        self.label.clone()
    }

    fn alphabet(&self) -> usize {
        self.factors
            .iter()
            .map(|factor| factor.emitters.alphabet())
            .product()
    }

    fn description(&self) -> u64 {
        self.description
    }

    fn face(&self) -> Result<Vec<Rat>, PopulationError> {
        let faces: Vec<Vec<Rat>> = self.factors.iter().map(Survivors::face).collect();
        Ok((0..self.alphabet())
            .map(|cell| {
                self.digits(cell)
                    .iter()
                    .zip(&faces)
                    .map(|(&digit, face)| face[digit].clone())
                    .product()
            })
            .collect())
    }

    fn receive(&mut self, cell: usize) -> Result<Rat, PopulationError> {
        let alphabet = self.alphabet();
        if cell >= alphabet {
            return Err(PopulationError::CellOutside { cell, alphabet });
        }
        // Every factor's filter is read before any commits: a death moves no factor, though its
        // reads were spent.
        let digits = self.digits(cell);
        for factor in &mut self.factors {
            factor.reads += factor.held_len() as u64;
        }
        let kept: Vec<Vec<u64>> = self
            .factors
            .iter()
            .zip(&digits)
            .map(|(factor, &digit)| factor.filter(digit))
            .collect();
        if let Some(factor) = kept.iter().position(Vec::is_empty) {
            self.exhausted = Some(factor);
            return Ok(Rat::zero());
        }
        let mut face = Rat::one();
        for ((factor, keys), digit) in self.factors.iter_mut().zip(kept).zip(digits) {
            let before = factor.count;
            factor.commit(keys, digit)?;
            face *= Rat::new(BigInt::from(factor.count), BigInt::from(before));
        }
        Ok(face)
    }

    fn exhausted(&self) -> Option<usize> {
        self.exhausted
    }

    /// The seed re-founded at `at`: each factor's held keys with their members, the admitted
    /// future of a collapse kept; none once that future has ended (split the species first).
    fn reseed(&self, at: usize) -> Option<Box<dyn Family>> {
        let at = at as u64;
        let factors = self
            .factors
            .iter()
            .map(|factor| {
                if factor.until.is_some_and(|end| at >= end) {
                    return None;
                }
                let seed: Vec<(u64, u64)> = factor
                    .survivors()
                    .into_iter()
                    .zip(factor.members())
                    .collect();
                Survivors::of_species(factor.emitters.fork_at(at)?, &seed, at, factor.until).ok()
            })
            .collect::<Option<Vec<Survivors>>>()?;
        Some(Box::new(KeyFamily {
            label: format!("{} (re-founded from its seed)", self.label),
            description: self.description,
            factors,
            exhausted: None,
        }))
    }

    fn admits(&self, cells: &[usize]) -> Result<(), PopulationError> {
        let alphabet = self.alphabet();
        if let Some(&cell) = cells.iter().find(|&&cell| cell >= alphabet) {
            return Err(PopulationError::CellOutside { cell, alphabet });
        }
        self.factors
            .iter()
            .try_for_each(|factor| factor.admits(cells.len()))
    }

    fn declaration(&self) -> Declaration {
        Declaration::new("key family", Vec::new()).with(
            self.factors
                .iter()
                .map(|factor| factor.emitters.declaration())
                .collect(),
        )
    }

    /// Each factor's emissions read against received cells.
    fn work(&self) -> Work {
        let mut work = Work::default();
        for factor in &self.factors {
            work.add(Act::Read, factor.reads);
        }
        work
    }

    fn collapse(&mut self, future: AdmittedFuture) -> Result<Option<Collapse>, PopulationError> {
        species::collapse_keys(self, future).map(Some)
    }

    fn split(&mut self, collapse: &Collapse) -> Result<(), PopulationError> {
        species::split_keys(self, collapse)
    }

    fn certain(&self, future: AdmittedFuture) -> Option<Vec<Vec<usize>>> {
        self.factors
            .iter()
            .map(|factor| {
                let mut keys = factor.survivors().into_iter();
                let first = factor.emitters.signature(keys.next()?, future)?;
                keys.all(|key| factor.emitters.signature(key, future).as_ref() == Some(&first))
                    .then_some(first)
            })
            .collect()
    }

    fn seed(&self) -> Option<Seed> {
        Some(Seed {
            keys: self
                .factors
                .iter()
                .map(|factor| {
                    factor
                        .survivors()
                        .into_iter()
                        .zip(factor.members())
                        .collect()
                })
                .collect(),
            tick: self.factors[0].tick,
            until: self
                .factors
                .iter()
                .fold(None, |end, factor| species::earliest(end, factor.until)),
        })
    }

    fn restrict(&mut self, seed: &Seed) -> Result<(), PopulationError> {
        if seed.keys.len() != self.factors.len()
            || seed.keys.iter().zip(&self.factors).any(|(keys, factor)| {
                keys.iter()
                    .any(|&(key, members)| key >= factor.keys() || members == 0)
            })
        {
            return Err(refuse(
                "a species member's restoration",
                "its seed names keys of every factor's key space",
            ));
        }
        let factors = std::mem::take(&mut self.factors);
        let mut restored = Vec::with_capacity(factors.len());
        for (factor, keys) in factors.into_iter().zip(&seed.keys) {
            restored.push(Survivors::of_species(
                factor.emitters,
                keys,
                seed.tick,
                seed.until,
            )?);
        }
        self.factors = restored;
        Ok(())
    }

    fn likelihood(&self) -> Likelihood {
        Likelihood::Exact(self.factors.iter().map(Survivors::likelihood).product())
    }

    fn readout(&self) -> Readout<'_> {
        Readout::Keys(KeyReadout {
            spaces: self.factors.iter().map(Survivors::space).collect(),
            survivors: self
                .factors
                .iter()
                .map(|factor| {
                    factor
                        .survivors()
                        .into_iter()
                        .map(|key| factor.emitters.coordinates(key))
                        .collect()
                })
                .collect(),
            masses: if self.factors.iter().any(|factor| factor.members.is_some()) {
                self.factors
                    .iter()
                    .map(|factor| {
                        factor
                            .members()
                            .into_iter()
                            .map(|members| {
                                Rat::new(BigInt::from(members), BigInt::from(factor.count))
                            })
                            .collect()
                    })
                    .collect()
            } else {
                Vec::new()
            },
            dormant: Vec::new(),
        })
    }
}

// -------------------------------------------------------------------------------------------
// the work a family spends

/// [definition; agent-inferred] **An act a family executes** (module header, "Maintenance work").
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Act {
    /// A key's emission read against a received cell (survivor filtering).
    Read,
    /// A dormancy state (a key and one activity of its layers) read against a received cell.
    State,
    /// One share of the dormancy kernel: a layer's stay or switch on one key's activity.
    Share,
    /// A cell deposited into a receiving tree along its address.
    Deposit,
    /// A node a receiving tree holds: the storage it maintains.
    Node,
    /// A keystone key weighed at a received cell: its conditioned family read, its weight moved.
    Weigh,
    /// A record's digit product formed by convolution and carry (the carry egg).
    Product,
    /// An integer of a sieve's window decided by a face: the gratings maintained over the window.
    Decide(SieveFace),
    /// A stage counted in a cell of a declared partition (the boundary egg's hazard law).
    Count,
}

/// [definition; agent-inferred] **A family's work** (module header, "Maintenance work"): exact
/// counts of what it executed, by act; never a scalar price.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Work {
    pub acts: BTreeMap<Act, u64>,
}

impl Work {
    /// Count `count` more of an act.
    pub fn add(&mut self, act: Act, count: u64) {
        if count > 0 {
            *self.acts.entry(act).or_insert(0) += count;
        }
    }

    /// Count another work's acts too.
    pub fn absorb(&mut self, other: &Work) {
        for (&act, &count) in &other.acts {
            self.add(act, count);
        }
    }

    /// The count of one act.
    pub fn of(&self, act: Act) -> u64 {
        self.acts.get(&act).copied().unwrap_or(0)
    }
}

// -------------------------------------------------------------------------------------------
// the population

/// [definition; agent-inferred] **The kept precision** `P = 2·O` significant bits (`O` the enclosure
/// grid's octaves, `ratio::algebraic::LOG_OCTAVES`): a bound kept at `P` bits moves by a relative
/// `2^(1−P)` at most, so its `log₂` by less than `3·2^(−P)` (`log₂ e < 3/2`), and a reading of at most
/// `2^(O − 2)` kept operations stays within `2^(−O)` of the exact one, the grid the codes are
/// rounded out on.
pub const PRECISION: u64 = 2 * LOG_OCTAVES as u64;

/// A nonnegative bound `m · 2^e`, its mantissa kept at [`PRECISION`] significant bits, rounded
/// down (a lower bound) or up (an upper bound) at every operation.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Bound {
    mantissa: BigUint,
    exponent: i64,
}

impl Bound {
    fn zero() -> Self {
        Self {
            mantissa: BigUint::zero(),
            exponent: 0,
        }
    }

    fn is_zero(&self) -> bool {
        self.mantissa.is_zero()
    }

    /// `m 2^e` kept at `P` bits, rounded up when `up` and a dropped bit is set.
    fn kept(mantissa: BigUint, exponent: i64, up: bool) -> Self {
        let bits = mantissa.bits();
        if bits <= PRECISION {
            return Self { mantissa, exponent };
        }
        let shift = bits - PRECISION;
        let dropped = mantissa.trailing_zeros().is_some_and(|zeros| zeros < shift);
        let mut kept = &mantissa >> shift as usize;
        if up && dropped {
            kept += 1u32;
        }
        Self {
            mantissa: kept,
            exponent: exponent + shift as i64,
        }
    }

    /// `n/d` kept at `P` bits (`d > 0`).
    fn of_ratio(numerator: &BigUint, denominator: &BigUint, up: bool) -> Self {
        if numerator.is_zero() {
            return Self::zero();
        }
        let shift = (PRECISION + 1 + denominator.bits()).saturating_sub(numerator.bits());
        let scaled = numerator << shift as usize;
        let (quotient, remainder) = (&scaled / denominator, &scaled % denominator);
        let quotient = if up && !remainder.is_zero() {
            quotient + 1u32
        } else {
            quotient
        };
        Self::kept(quotient, -(shift as i64), up)
    }

    /// A nonnegative rational kept at `P` bits.
    fn of_rat(value: &Rat, up: bool) -> Self {
        Self::of_ratio(value.numer().magnitude(), value.denom().magnitude(), up)
    }

    /// `N/(D 2^E)` from a passage's product bounds.
    fn of_product_bounds(
        numerator: ProductBound,
        denominator: ProductBound,
        exponent: u64,
        up: bool,
    ) -> Self {
        let mut bound = Self::of_ratio(
            &BigUint::from(numerator.mantissa),
            &BigUint::from(denominator.mantissa),
            up,
        );
        bound.exponent += numerator.exponent as i64 - denominator.exponent as i64 - exponent as i64;
        bound
    }

    fn times(&self, other: &Bound, up: bool) -> Self {
        Self::kept(
            &self.mantissa * &other.mantissa,
            self.exponent + other.exponent,
            up,
        )
    }

    fn plus(&self, other: &Bound, up: bool) -> Self {
        if self.is_zero() {
            return other.clone();
        }
        if other.is_zero() {
            return self.clone();
        }
        let exponent = self.exponent.min(other.exponent);
        let align = |b: &Bound| &b.mantissa << (b.exponent - exponent) as usize;
        Self::kept(align(self) + align(other), exponent, up)
    }

    /// `self/other` (`other > 0`).
    fn over(&self, other: &Bound, up: bool) -> Self {
        let mut bound = Self::of_ratio(&self.mantissa, &other.mantissa, up);
        if !bound.is_zero() {
            bound.exponent += self.exponent - other.exponent;
        }
        bound
    }

    /// `−log₂(m 2^e)`, enclosed (`m > 0`).
    fn code(&self) -> Result<ExactInterval, PopulationError> {
        let log = ratio_code_length(&self.mantissa, &BigUint::one())?;
        let shift = Rat::from_integer(BigInt::from(self.exponent));
        Ok(ExactInterval {
            lower: &log.lower - &shift,
            upper: &log.upper - &shift,
        })
    }

    /// The bound as an exact rational, on the grid `2^(−P)` (rounded down, or up when `up`).
    fn to_rat(&self, up: bool) -> Rat {
        let grid = -(PRECISION as i64);
        if self.exponent >= grid {
            let value = BigInt::from(self.mantissa.clone());
            return if self.exponent >= 0 {
                Rat::from_integer(value << self.exponent as usize)
            } else {
                Rat::new(value, BigInt::one() << (-self.exponent) as usize)
            };
        }
        let shift = (grid - self.exponent) as usize;
        let mut floor = &self.mantissa >> shift;
        if up
            && self
                .mantissa
                .trailing_zeros()
                .is_some_and(|zeros| (zeros as usize) < shift)
        {
            floor += 1u32;
        }
        Rat::new(BigInt::from(floor), BigInt::one() << PRECISION as usize)
    }
}

/// `[lower, upper]` of `−log₂ x` from `x`'s bounds `[x_lower, x_upper]` (`x_lower > 0`), rounded
/// out on the enclosure grid.
fn code_between(lower: &Bound, upper: &Bound) -> Result<ExactInterval, PopulationError> {
    let enclosure = ExactInterval::new(upper.code()?.lower, lower.code()?.upper)?;
    Ok(interval_sum(
        &ExactInterval::point(Rat::zero()),
        &enclosure,
    )?)
}

/// `−log₂ w` of a mass `w ≤ 1` from its bounds: never negative.
fn mass_code(lower: &Bound, upper: &Bound) -> Result<ExactInterval, PopulationError> {
    let code = code_between(lower, upper)?;
    Ok(ExactInterval::new(
        code.lower.max(Rat::zero()),
        code.upper.max(Rat::zero()),
    )?)
}

/// [definition] **A family's posterior**: exactly zero (the family died at zero likelihood), or
/// `−log₂ w_f` enclosed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Posterior {
    Dead,
    Bits(ExactInterval),
}

/// [definition] **One family's receipt** ([`Population::receipt`]): its declaration and description
/// `ℓ_f`, its normalized prior `π_f` over the founded mass, the cell it was founded at (`0` for a
/// declared family), the cell it died at (zero likelihood), its code alone `−log₂ L_f` from its
/// founding and charged `−log₂ c_f` (none once dead; `c_f = π_f L_f`, a newborn's times the
/// population's likelihood at its birth), its posterior, its keys' readout, and its certified drift.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FamilyReceipt {
    pub label: String,
    /// The family's identity across aeons: its declaration and description.
    pub identity: Identity,
    pub description: u64,
    pub prior: Rat,
    pub born: usize,
    pub died: Option<usize>,
    pub code: Option<ExactInterval>,
    pub charged: Option<ExactInterval>,
    pub posterior: Posterior,
    pub keys: Option<KeyReadout>,
    pub drift: Rat,
    /// The work the family has spent (module header, "Maintenance work").
    pub work: Work,
}

/// [definition] **A death's exchange, exactly** (when every living family's likelihood is exact):
/// the dying mass `w_f` and each survivor's attributed share `w_f w′_g`, which sum to `w_f`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Exchange {
    pub mass: Rat,
    pub shares: Vec<(usize, Rat)>,
}

/// [definition; agent-inferred] **A death's receipt** (module header, "Death is an exchange"): the
/// family, the factor whose every key the cell contradicted (a key family's), the killing cell's
/// position and the class that arrived, the dead family's last face (what it predicted against what
/// arrived), the dying mass `−log₂ w_f` and each survivor `g`'s received share
/// `−log₂(w_f w′_g)`, `w′_g = c_g P_g(x)/Σ_(h alive) c_h P_h(x)` (Bayes' normalization, stated as
/// the transfer: [definition] the per-survivor attribution, since Bayes fixes only the survivors'
/// total gain), each enclosed, and the same exactly when every living family's likelihood is;
/// and its seed, the keys it held when it died (a key family's), which stay in its declared key
/// space and can be re-founded.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeathReceipt {
    pub family: usize,
    pub label: String,
    pub factor: Option<usize>,
    pub cell: usize,
    pub arrived: usize,
    pub face: Vec<Rat>,
    pub mass: ExactInterval,
    pub shares: Vec<(usize, ExactInterval)>,
    pub exact: Option<Exchange>,
    pub seed: Option<KeyReadout>,
}

/// [definition; agent-inferred] **A birth's receipt** (module header, "Birth from reserved
/// mass"): the newborn, the cell it was founded at, its declared description `ℓ_g`, its mass drawn
/// from the reserved mass (`2^(−ℓ_g)` for a declared candidate, half the reserved mass for a seed
/// re-founded) and its charge `−log₂` of that mass, the reserved mass left, the population's code
/// before the birth `−log₂ W_(t_g)` (the newborn's own before its birth: it abstained), the section's
/// residual that triggered it, if a trigger did, and the dead family whose seed it re-founds.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BirthReceipt {
    pub family: usize,
    pub label: String,
    pub cell: usize,
    pub description: u64,
    pub mass: Rat,
    pub charge: ExactInterval,
    pub reserved: Rat,
    pub inherited: ExactInterval,
    pub residual: Option<ExactInterval>,
    pub seed: Option<usize>,
}

/// [definition] **A reception's receipts**: the deaths and births the received cells caused, in
/// cell order. The population keeps none of them: a dead member keeps the state it died in, a
/// newborn its founding; the receipts are the reception's return.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Reception {
    pub deaths: Vec<DeathReceipt>,
    pub births: Vec<BirthReceipt>,
}

impl Reception {
    fn extend(&mut self, other: Reception) {
        self.deaths.extend(other.deaths);
        self.births.extend(other.births);
    }
}

/// [definition; agent-inferred] **One part's reading** (module header, "A partition's reading"):
/// the part's cells, the population's code on them (the sum of `−log₂ q_t(x_t)` over the part,
/// each the population's code after the cell less its code before, enclosed), and each family's
/// code on them (`−log₂` of its faces' product over the part, enclosed; none once the family died).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartReading {
    pub cells: usize,
    pub population: ExactInterval,
    pub families: Vec<Option<ExactInterval>>,
}

/// [definition] **The population's receipt**: the cells received, the declared total mass `M` and
/// the founded mass `M_n` (`M` plus every newborn's), the population's code `−log₂ W` (exact
/// enclosure), each family's receipt, and the family the population selects: the one whose
/// posterior is decided above one half (`−log₂ w_f < 1`), if any.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PopulationReceipt {
    pub cells: usize,
    pub mass: Rat,
    pub founded: Rat,
    pub code: ExactInterval,
    pub families: Vec<FamilyReceipt>,
    pub selected: Option<usize>,
}

/// [definition] **A founding candidate**: its declared description `ℓ_g` and its declaration, built
/// at the cell of its birth (its clocks wound to that cell).
pub struct Candidate {
    pub description: u64,
    pub found: FoundFamily,
}

/// A candidate's declaration, built at the cell of its birth.
pub type FoundFamily = Box<dyn FnMut(usize) -> Result<Box<dyn Family>, PopulationError> + Send>;

/// [definition; agent-inferred] **The founding trigger** (module header, "Birth from reserved
/// mass"): the receiver's section every `section_period` cells; at a section whose residual (the code the
/// population paid since the last section) passes a founding's charge, it is founded from the
/// reserved mass: with `reseed`, first the most recently dead family's seed (half the reserved
/// mass), then the next declared candidate (its description). The opening section only opens the
/// reading: it pays the declared families' own key location.
pub struct Founding {
    pub section_period: usize,
    pub candidates: Vec<Candidate>,
    pub reseed: bool,
}

struct Member {
    family: Box<dyn Family>,
    mass: Rat,
    prior: Rat,
    born: usize,
    inherited: Option<(Bound, Bound)>,
    died: Option<usize>,
    reseeded: bool,
    origin: Option<usize>,
}

/// [definition; agent-inferred] **The population** (module header): the declared families with
/// their Kraft masses, normalized over the founded mass, each carrying its own likelihood; a newborn
/// also carries the population's likelihood at its birth.
pub struct Population {
    members: Vec<Member>,
    alphabet: usize,
    mass: Rat,
    founded: Rat,
    cells: usize,
    founding: Option<Founding>,
    section: Option<ExactInterval>,
}

/// The mass `2^(−ℓ)` of a description of `ℓ` bits.
fn kraft(description: u64) -> Result<Rat, PopulationError> {
    let bits = usize::try_from(description)
        .map_err(|_| refuse("a family's description", "it fits the address space"))?;
    Ok(Rat::new(BigInt::one(), BigInt::one() << bits))
}

impl Population {
    /// **Declare the population** over its families: one alphabet, and descriptions whose Kraft sum
    /// `M = Σ_f 2^(−ℓ_f)` is at most one (a prefix code's lengths); the prior is `2^(−ℓ_f)/M`, and
    /// `1 − M` is reserved.
    pub fn new(families: Vec<Box<dyn Family>>) -> Result<Self, PopulationError> {
        let masses = families
            .iter()
            .map(|family| kraft(family.description()))
            .collect::<Result<Vec<Rat>, _>>()?;
        if masses.iter().sum::<Rat>() > Rat::one() {
            return Err(refuse(
                "a population's descriptions",
                "their Kraft sum passes one: they are no prefix code's lengths",
            ));
        }
        Self::with_masses(families, masses)
    }

    /// **Declare the population at declared masses** `m_f` (the evolved prior's, module header of
    /// [`evolution`]): positive rationals summing to at most one; the prior is `m_f/M`,
    /// `M = Σ_f m_f`, and `1 − M` is reserved.
    pub fn with_masses(
        families: Vec<Box<dyn Family>>,
        masses: Vec<Rat>,
    ) -> Result<Self, PopulationError> {
        let Some(first) = families.first() else {
            return Err(refuse("a population", "it declares at least one family"));
        };
        let alphabet = first.alphabet();
        if alphabet == 0 || families.iter().any(|family| family.alphabet() != alphabet) {
            return Err(refuse(
                "a population",
                "its families read one declared cell alphabet",
            ));
        }
        if masses.len() != families.len() || masses.iter().any(|mass| !mass.is_positive()) {
            return Err(refuse(
                "a population's masses",
                "one positive mass is declared for every family",
            ));
        }
        let mass: Rat = masses.iter().sum();
        if mass > Rat::one() {
            return Err(refuse("a population's masses", "they sum to at most one"));
        }
        let members = families
            .into_iter()
            .zip(masses)
            .map(|(family, weight)| Member {
                family,
                prior: &weight / &mass,
                mass: weight,
                born: 0,
                inherited: None,
                died: None,
                reseeded: false,
                origin: None,
            })
            .collect();
        Ok(Self {
            members,
            alphabet,
            founded: mass.clone(),
            mass,
            cells: 0,
            founding: None,
            section: None,
        })
    }

    /// **Declare the founding trigger** (module header, "Birth from reserved mass"); refused at an
    /// empty section, or when the candidates' masses pass the reserved mass.
    pub fn with_founding(mut self, founding: Founding) -> Result<Self, PopulationError> {
        if founding.section_period == 0 {
            return Err(refuse(
                "a founding trigger",
                "its section holds at least one cell",
            ));
        }
        let masses = founding
            .candidates
            .iter()
            .map(|candidate| kraft(candidate.description))
            .collect::<Result<Vec<Rat>, _>>()?;
        if masses.iter().sum::<Rat>() > self.reserved() {
            return Err(refuse(
                "a founding trigger",
                "its candidates' masses fit within the reserved mass",
            ));
        }
        self.founding = Some(founding);
        Ok(self)
    }

    /// The declared cell alphabet.
    pub fn alphabet(&self) -> usize {
        self.alphabet
    }

    /// Plan an admitted request/response incidence before receiving its target part. Validation
    /// runs across all living families before any family is mutated; unrelated families ignore it.
    pub fn plan_relation(&mut self, relation: Relation) -> Result<(), PopulationError> {
        if !self
            .members
            .iter()
            .any(|member| member.died.is_none() && member.family.owns_planned_relation())
        {
            return Err(refuse(
                "a planned admitted relation",
                "at least one living family owns the request/response incidence",
            ));
        }
        for member in &self.members {
            if member.died.is_none() {
                member.family.validate_planned_relation(relation)?;
            }
        }
        for member in &mut self.members {
            if member.died.is_none() {
                member.family.commit_planned_relation(relation);
            }
        }
        Ok(())
    }

    /// **The declared total mass** `M = Σ_f 2^(−ℓ_f)` of the declared families.
    pub fn mass(&self) -> &Rat {
        &self.mass
    }

    /// **The founded mass** `M_n`: `M` and every newborn's `2^(−ℓ_g)`.
    pub fn founded(&self) -> &Rat {
        &self.founded
    }

    /// **The reserved mass** `1 − M_n`, from which a birth draws.
    pub fn reserved(&self) -> Rat {
        Rat::one() - &self.founded
    }

    /// The cells received.
    pub fn cells(&self) -> usize {
        self.cells
    }

    /// Make an ephemeral branch from the current standing. The exact current face and receipt are
    /// preserved by continuing family-owned state, likelihoods, masses, clocks and counters as-is.
    /// Unsupported owners and populations with a non-cloneable founding closure return refusals.
    pub fn branch_future(&self) -> Result<Self, PopulationError> {
        if self.founding.is_some() {
            return Err(PopulationError::FutureBranchFounding);
        }
        let mut members = Vec::with_capacity(self.members.len());
        for member in &self.members {
            let Some(family) = member.family.branch_future() else {
                return Err(PopulationError::FutureBranchUnsupported {
                    label: member.family.label(),
                });
            };
            members.push(Member {
                family,
                mass: member.mass.clone(),
                prior: member.prior.clone(),
                born: member.born,
                inherited: member.inherited.clone(),
                died: member.died,
                reseeded: member.reseeded,
                origin: member.origin,
            });
        }
        Ok(Self {
            members,
            alphabet: self.alphabet,
            mass: self.mass.clone(),
            founded: self.founded.clone(),
            cells: self.cells,
            founding: None,
            section: self.section.clone(),
        })
    }

    /// The families, in their declared order, newborns after.
    pub fn families(&self) -> impl Iterator<Item = &dyn Family> {
        self.members.iter().map(|member| member.family.as_ref())
    }

    /// Family `f`'s normalized prior `π_f = 2^(−ℓ_f)/M_n`.
    pub fn prior(&self, family: usize) -> Option<&Rat> {
        self.members.get(family).map(|member| &member.prior)
    }

    /// The cell family `f` died at, if it died.
    pub fn died(&self, family: usize) -> Option<usize> {
        self.members.get(family).and_then(|member| member.died)
    }

    /// The cell family `f` was founded at (`0` for a declared family).
    pub fn born(&self, family: usize) -> Option<usize> {
        self.members.get(family).map(|member| member.born)
    }

    fn check(&self, cell: usize) -> Result<(), PopulationError> {
        if cell >= self.alphabet {
            return Err(PopulationError::CellOutside {
                cell,
                alphabet: self.alphabet,
            });
        }
        Ok(())
    }

    /// **Admission before anything moves**: every cell lies in the alphabet and every living
    /// family admits the passage, so a refusal changes nothing.
    fn admit(&self, cells: &[usize]) -> Result<(), PopulationError> {
        for &cell in cells {
            self.check(cell)?;
        }
        for member in &self.members {
            if member.died.is_none() {
                member.family.admits(cells)?;
            }
        }
        Ok(())
    }

    /// Each member's `c_f` bounds `(lower, upper)`: `π_f L_f`, a newborn's times the population's
    /// likelihood at its birth; zero once dead.
    fn charged_bounds(&self) -> Vec<(Bound, Bound)> {
        self.members
            .iter()
            .map(|member| {
                if member.died.is_some() {
                    return (Bound::zero(), Bound::zero());
                }
                Self::charged(member, &member.family.likelihood())
            })
            .collect()
    }

    /// One member's `c_f` bounds at a likelihood.
    fn charged(member: &Member, likelihood: &Likelihood) -> (Bound, Bound) {
        let (mut lower, mut upper) = (
            Bound::of_rat(&member.prior, false).times(&likelihood.bound(false), false),
            Bound::of_rat(&member.prior, true).times(&likelihood.bound(true), true),
        );
        if let Some((inherited_lower, inherited_upper)) = &member.inherited {
            lower = lower.times(inherited_lower, false);
            upper = upper.times(inherited_upper, true);
        }
        (lower, upper)
    }

    /// `W`'s bounds over the declared members.
    fn total(bounds: &[(Bound, Bound)], members: impl Iterator<Item = usize>) -> (Bound, Bound) {
        members.fold((Bound::zero(), Bound::zero()), |(lower, upper), f| {
            (
                lower.plus(&bounds[f].0, false),
                upper.plus(&bounds[f].1, true),
            )
        })
    }

    /// **Receive one cell** (module header): every living family's face of it is read and
    /// deposited, each after every family has admitted the cell; a family whose face gives it zero
    /// dies, keeping the state it died in, and its mass passes to the survivors (the receipt).
    /// Refused, with nothing moved, at a cell some family refuses and at a cell every living family
    /// gives zero.
    pub fn receive(&mut self, cell: usize) -> Result<Reception, PopulationError> {
        self.admit(&[cell])?;
        self.receive_admitted(cell)
    }

    /// One admitted cell: the families read it together on the host's cores, each writing only its
    /// own state (the hardware law), then the deaths are exchanged and the founding read.
    fn receive_admitted(&mut self, cell: usize) -> Result<Reception, PopulationError> {
        Ok(self.receive_faces(cell)?.0)
    }

    /// One admitted cell ([`Population::receive_admitted`]), returning beside the reception each
    /// member's face of the cell (none for a member already dead).
    fn receive_faces(
        &mut self,
        cell: usize,
    ) -> Result<(Reception, Vec<Option<Rat>>), PopulationError> {
        let position = self.cells;
        let read: Vec<Option<(Likelihood, Rat)>> = self
            .members
            .par_iter_mut()
            .map(|member| {
                if member.died.is_some() {
                    return Ok(None);
                }
                let before = member.family.likelihood();
                let face = member.family.receive(cell)?;
                if face.is_negative() || face > Rat::one() {
                    return Err(refuse(
                        "a family's face of a cell",
                        "it lies in the unit interval",
                    ));
                }
                Ok(Some((before, face)))
            })
            .collect::<Result<_, PopulationError>>()?;
        let dying: Vec<usize> = read
            .iter()
            .enumerate()
            .filter_map(|(f, entry)| entry.as_ref().filter(|(_, face)| face.is_zero()).map(|_| f))
            .collect();
        if read.iter().flatten().all(|(_, face)| face.is_zero()) {
            return Err(PopulationError::Extinct { cell: position });
        }
        let faces = read
            .iter()
            .map(|entry| entry.as_ref().map(|(_, face)| face.clone()))
            .collect();
        let mut reception = Reception::default();
        if !dying.is_empty() {
            reception.deaths = self.exchange(position, cell, &read, &dying)?;
            for &f in &dying {
                self.members[f].died = Some(position);
                // A re-founded seed that dies returns the seed to the family it came from.
                if let Some(origin) = self.members[f].origin {
                    self.members[origin].reseeded = false;
                }
            }
        }
        self.cells += 1;
        if let Some(birth) = self.found_at_section()? {
            reception.births.push(birth);
        }
        Ok((reception, faces))
    }

    /// **Death is an exchange** (module header): each dying family's mass `w_f` before the cell and
    /// each survivor's received share `w_f w′_g`, enclosed, and exactly when every living family's
    /// likelihood is exact.
    fn exchange(
        &self,
        position: usize,
        cell: usize,
        read: &[Option<(Likelihood, Rat)>],
        dying: &[usize],
    ) -> Result<Vec<DeathReceipt>, PopulationError> {
        let living: Vec<usize> = (0..read.len()).filter(|&f| read[f].is_some()).collect();
        let survivors: Vec<usize> = living
            .iter()
            .copied()
            .filter(|f| !dying.contains(f))
            .collect();
        let before: Vec<(Bound, Bound)> = (0..read.len())
            .map(|f| match &read[f] {
                Some((likelihood, _)) => Self::charged(&self.members[f], likelihood),
                None => (Bound::zero(), Bound::zero()),
            })
            .collect();
        let after: Vec<(Bound, Bound)> = (0..read.len())
            .map(|f| match &read[f] {
                Some((_, face)) if !face.is_zero() => (
                    before[f].0.times(&Bound::of_rat(face, false), false),
                    before[f].1.times(&Bound::of_rat(face, true), true),
                ),
                _ => (Bound::zero(), Bound::zero()),
            })
            .collect();
        let (whole_lower, whole_upper) = Self::total(&before, living.iter().copied());
        let (kept_lower, kept_upper) = Self::total(&after, survivors.iter().copied());
        let weight = |part: &(Bound, Bound), lower: &Bound, upper: &Bound| {
            (part.0.over(upper, false), part.1.over(lower, true))
        };
        let exact = living.iter().all(|&f| {
            self.members[f].inherited.is_none()
                && matches!(&read[f], Some((Likelihood::Exact(_), _)))
        });
        let exact_charged = |f: usize| -> Rat {
            match &read[f] {
                Some((Likelihood::Exact(value), _)) => &self.members[f].prior * value,
                _ => Rat::zero(),
            }
        };
        let (exact_whole, exact_kept) = if exact {
            (
                living.iter().map(|&f| exact_charged(f)).sum::<Rat>(),
                survivors
                    .iter()
                    .map(|&g| exact_charged(g) * &read[g].as_ref().expect("a survivor").1)
                    .sum::<Rat>(),
            )
        } else {
            (Rat::zero(), Rat::zero())
        };
        dying
            .iter()
            .map(|&f| {
                let mass = weight(&before[f], &whole_lower, &whole_upper);
                let shares = survivors
                    .iter()
                    .map(|&g| {
                        let received = weight(&after[g], &kept_lower, &kept_upper);
                        Ok((
                            g,
                            mass_code(
                                &mass.0.times(&received.0, false),
                                &mass.1.times(&received.1, true),
                            )?,
                        ))
                    })
                    .collect::<Result<Vec<_>, PopulationError>>()?;
                let exchange = exact.then(|| {
                    let mass = exact_charged(f) / &exact_whole;
                    let shares = survivors
                        .iter()
                        .map(|&g| {
                            let received = exact_charged(g)
                                * &read[g].as_ref().expect("a survivor").1
                                / &exact_kept;
                            (g, &mass * received)
                        })
                        .collect();
                    Exchange { mass, shares }
                });
                let member = &self.members[f];
                Ok(DeathReceipt {
                    family: f,
                    label: member.family.label(),
                    factor: member.family.exhausted(),
                    cell: position,
                    arrived: cell,
                    face: member.family.face()?,
                    mass: mass_code(&mass.0, &mass.1)?,
                    shares,
                    exact: exchange,
                    seed: match member.family.readout() {
                        Readout::Keys(keys) => Some(keys),
                        _ => None,
                    },
                })
            })
            .collect()
    }

    /// **Receive a passage**: admitted whole before any cell moves, then received cell by cell.
    pub fn receive_passage(&mut self, cells: &[usize]) -> Result<Reception, PopulationError> {
        self.admit(cells)?;
        let mut reception = Reception::default();
        for &cell in cells {
            // A newborn's admission of the rest is read at each of its cells.
            if self.members.iter().any(|member| member.born > 0) {
                self.admit(&[cell])?;
            }
            reception.extend(self.receive_admitted(cell)?);
        }
        Ok(reception)
    }

    /// **Receive a passage read over a declared partition of its cells** (module header, "A
    /// partition's reading"): cell `t` belongs to part `parts[t] < count`. Admitted whole before any
    /// cell moves, then received cell by cell exactly as [`Population::receive_passage`] receives
    /// it; returns the reception and each part's reading.
    pub fn receive_partitioned(
        &mut self,
        cells: &[usize],
        parts: &[usize],
        count: usize,
    ) -> Result<(Reception, Vec<PartReading>), PopulationError> {
        if parts.len() != cells.len() || parts.iter().any(|&part| part >= count) {
            return Err(refuse(
                "a partition of a passage",
                "it names one declared part for every cell",
            ));
        }
        self.admit(cells)?;
        let mut codes = vec![vec![PassageCode::new(); self.members.len()]; count];
        let mut population = vec![ExactInterval::point(Rat::zero()); count];
        let mut sizes = vec![0usize; count];
        let mut reception = Reception::default();
        let mut before = self.code()?;
        for (&cell, &part) in cells.iter().zip(parts) {
            if self.members.iter().any(|member| member.born > 0) {
                self.admit(&[cell])?;
            }
            let (received, faces) = self.receive_faces(cell)?;
            reception.extend(received);
            for row in &mut codes {
                row.resize(self.members.len(), PassageCode::new());
            }
            for (family, face) in faces.iter().enumerate() {
                if let Some(face) = face
                    && face.is_positive()
                {
                    codes[part][family].face(face)?;
                }
            }
            let after = self.code()?;
            population[part] =
                interval_sum(&population[part], &interval_difference(&after, &before)?)?;
            before = after;
            sizes[part] += 1;
        }
        let readings = codes
            .into_iter()
            .zip(population)
            .zip(sizes)
            .map(|((row, population), cells)| {
                let families = row
                    .iter()
                    .zip(&self.members)
                    .map(|(code, member)| match member.died {
                        Some(_) => Ok(None),
                        None => Ok(Some(code.bits()?)),
                    })
                    .collect::<Result<Vec<_>, PopulationError>>()?;
                Ok(PartReading {
                    cells,
                    population,
                    families,
                })
            })
            .collect::<Result<Vec<_>, PopulationError>>()?;
        Ok((reception, readings))
    }

    /// **Found a family from the reserved mass** (module header, "Birth from reserved mass"): its
    /// mass `2^(−ℓ_g)` must fit in `1 − M_n`; it abstained before this cell, so it inherits the
    /// population's likelihood `W_(t_g)`, and the priors renormalize over the founded mass. The
    /// population's code does not move at a birth.
    pub fn found(
        &mut self,
        family: Box<dyn Family>,
        residual: Option<ExactInterval>,
    ) -> Result<BirthReceipt, PopulationError> {
        let mass = kraft(family.description())?;
        self.found_from(family, mass, residual, None)
    }

    /// **Found a family at a declared rational mass** from the reserved mass (module header,
    /// "Birth from reserved mass"; the evolved prior's birth mass, module header of [`evolution`]):
    /// refused unless the mass is positive and fits in `1 − M_n`.
    pub fn found_with(
        &mut self,
        family: Box<dyn Family>,
        mass: Rat,
        residual: Option<ExactInterval>,
    ) -> Result<BirthReceipt, PopulationError> {
        self.found_from(family, mass, residual, None)
    }

    /// **Re-found a dead family from its seed** (module header, "A death keeps the seed"): the keys
    /// it held when it died, wound to this cell, charged half the reserved mass (the declared prior
    /// share of a re-founding), never the relearning of its key space. Refused unless the family is
    /// a declared or founded family (not itself a seed's newborn) that is dead with its seed not
    /// alive in a newborn, its clocks wind without the cells, and its species are split first where
    /// a re-founding cannot keep them (a composed egg's keystone species, and any species, its own
    /// or a conditioned family's, whose admitted future has ended at this cell). When the newborn
    /// dies, the seed returns to the dead family and can be re-founded again.
    pub fn refound(
        &mut self,
        dead: usize,
        residual: Option<ExactInterval>,
    ) -> Result<BirthReceipt, PopulationError> {
        let Some(member) = self.members.get(dead) else {
            return Err(refuse("a re-founding", "it names a declared family"));
        };
        if member.died.is_none() || member.reseeded || member.origin.is_some() {
            return Err(refuse(
                "a re-founding",
                "it names a dead family whose seed has not been re-founded",
            ));
        }
        let Some(newborn) = member.family.reseed(self.cells) else {
            return Err(refuse(
                "a re-founding",
                "the dead family's clocks wind without the cells, and its species are split first (a composed egg's keystone species, and any species whose admitted future has ended)",
            ));
        };
        let mass = self.reserved() / Rat::from_integer(BigInt::from(2u32));
        let receipt = self.found_from(newborn, mass, residual, Some(dead))?;
        self.members[dead].reseeded = true;
        Ok(receipt)
    }

    fn found_from(
        &mut self,
        family: Box<dyn Family>,
        mass: Rat,
        residual: Option<ExactInterval>,
        seed: Option<usize>,
    ) -> Result<BirthReceipt, PopulationError> {
        if family.alphabet() != self.alphabet {
            return Err(refuse(
                "a newborn family",
                "it reads the population's cell alphabet",
            ));
        }
        if !mass.is_positive() || mass > self.reserved() {
            return Err(refuse(
                "a newborn family",
                "its mass is positive and fits within the reserved mass",
            ));
        }
        let bounds = self.charged_bounds();
        let (lower, upper) = Self::total(&bounds, 0..bounds.len());
        if lower.is_zero() {
            return Err(PopulationError::Extinct { cell: self.cells });
        }
        let inherited = code_between(&lower, &upper)?;
        self.founded += &mass;
        for member in &mut self.members {
            member.prior = &member.mass / &self.founded;
        }
        let label = family.label();
        let description = family.description();
        self.members.push(Member {
            family,
            prior: &mass / &self.founded,
            mass: mass.clone(),
            born: self.cells,
            inherited: Some((lower, upper)),
            died: None,
            reseeded: false,
            origin: seed,
        });
        Ok(BirthReceipt {
            family: self.members.len() - 1,
            label,
            cell: self.cells,
            description,
            charge: ratio_code_length(mass.numer().magnitude(), mass.denom().magnitude())?,
            mass,
            reserved: self.reserved(),
            inherited,
            residual,
            seed,
        })
    }

    /// The founding trigger at a section (module header, "Birth from reserved mass").
    fn found_at_section(&mut self) -> Result<Option<BirthReceipt>, PopulationError> {
        let Some(period) = self
            .founding
            .as_ref()
            .map(|founding| founding.section_period)
        else {
            return Ok(None);
        };
        if self.cells % period != 0 {
            return Ok(None);
        }
        let code = self.code()?;
        let residual = match &self.section {
            Some(previous) => interval_difference(&code, previous)?,
            None => code.clone(),
        };
        let opening = self.section.is_none();
        self.section = Some(code);
        if opening {
            // The opening section pays the declared families' own key location: no residual yet.
            return Ok(None);
        }
        if self
            .founding
            .as_ref()
            .is_some_and(|founding| founding.reseed)
        {
            let dead = (0..self.members.len())
                .filter(|&f| {
                    let member = &self.members[f];
                    member.died.is_some()
                        && !member.reseeded
                        && member.origin.is_none()
                        && member.family.reseed(self.cells).is_some()
                })
                .max_by_key(|&f| self.members[f].died);
            if let Some(dead) = dead {
                let mass = self.reserved() / Rat::from_integer(BigInt::from(2u32));
                let charge = ratio_code_length(mass.numer().magnitude(), mass.denom().magnitude())?;
                if residual.lower > charge.upper {
                    return Ok(Some(self.refound(dead, Some(residual))?));
                }
            }
        }
        let reserved = self.reserved();
        let founding = self.founding.as_mut().expect("a declared founding");
        let Some(next) = founding.candidates.first() else {
            return Ok(None);
        };
        if residual.lower <= Rat::from_integer(BigInt::from(next.description))
            || kraft(next.description)? > reserved
        {
            return Ok(None);
        }
        let mut candidate = founding.candidates.remove(0);
        let family = (candidate.found)(self.cells)?;
        if family.description() != candidate.description {
            return Err(refuse(
                "a founding candidate",
                "its family carries its declared description",
            ));
        }
        Ok(Some(self.found(family, Some(residual))?))
    }

    /// **The population's code** `−log₂ W = −log₂ Σ_f c_f`, an exact enclosure (module header: the
    /// telescope). Refused when every family is dead.
    pub fn code(&self) -> Result<ExactInterval, PopulationError> {
        let bounds = self.charged_bounds();
        let (lower, upper) = Self::total(&bounds, 0..bounds.len());
        if lower.is_zero() {
            return Err(PopulationError::Extinct { cell: self.cells });
        }
        code_between(&lower, &upper)
    }

    /// **The posterior of a set of families** `−log₂ Σ_(f ∈ set) w_f`, enclosed; `Dead` when every
    /// family of the set is dead.
    pub fn posterior_of(&self, set: &[usize]) -> Result<Posterior, PopulationError> {
        if set.iter().any(|&f| f >= self.members.len()) {
            return Err(refuse("a set of families", "it names declared families"));
        }
        let bounds = self.charged_bounds();
        let (part_lower, part_upper) = Self::total(&bounds, set.iter().copied());
        if part_upper.is_zero() {
            return Ok(Posterior::Dead);
        }
        // Every family outside the set is dead: the set's posterior is exactly one.
        if (0..self.members.len()).all(|f| set.contains(&f) || self.members[f].died.is_some()) {
            return Ok(Posterior::Bits(ExactInterval::point(Rat::zero())));
        }
        let (lower, upper) = Self::total(&bounds, 0..bounds.len());
        if lower.is_zero() {
            return Err(PopulationError::Extinct { cell: self.cells });
        }
        if part_lower.is_zero() {
            return Err(refuse(
                "a posterior's enclosure",
                "a living family's likelihood bound kept at the precision is positive",
            ));
        }
        // −log₂ w ∈ [code(part_upper) − code(W_lower), code(part_lower) − code(W_upper)].
        let (part, whole) = (
            ExactInterval::new(part_upper.code()?.lower, part_lower.code()?.upper)?,
            ExactInterval::new(upper.code()?.lower, lower.code()?.upper)?,
        );
        // A posterior is at most one: its code is never negative.
        let enclosure = ExactInterval::new(
            (&part.lower - &whole.upper).max(Rat::zero()),
            (&part.upper - &whole.lower).max(Rat::zero()),
        )?;
        Ok(Posterior::Bits(interval_sum(
            &ExactInterval::point(Rat::zero()),
            &enclosure,
        )?))
    }

    /// **The population's face** `q(c) = Σ_f w_f P_f(c)` before the next cell, each class enclosed
    /// on the grid `2^(−P)` (the weights' bounds are read from the likelihoods: module header).
    pub fn face(&self) -> Result<Vec<ExactInterval>, PopulationError> {
        let bounds = self.charged_bounds();
        let (lower, upper) = Self::total(&bounds, 0..bounds.len());
        if lower.is_zero() {
            return Err(PopulationError::Extinct { cell: self.cells });
        }
        let mut sums = vec![(Bound::zero(), Bound::zero()); self.alphabet];
        for (member, (charged_lower, charged_upper)) in self.members.iter().zip(&bounds) {
            if member.died.is_some() {
                continue;
            }
            let (weight_lower, weight_upper) = (
                charged_lower.over(&upper, false),
                charged_upper.over(&lower, true),
            );
            for (sum, face) in sums.iter_mut().zip(member.family.face()?) {
                let (face_lower, face_upper) =
                    (Bound::of_rat(&face, false), Bound::of_rat(&face, true));
                sum.0 = sum.0.plus(&weight_lower.times(&face_lower, false), false);
                sum.1 = sum.1.plus(&weight_upper.times(&face_upper, true), true);
            }
        }
        sums.into_iter()
            .map(|(lower, upper)| {
                let upper = upper.to_rat(true).min(Rat::one());
                Ok(ExactInterval::new(lower.to_rat(false), upper)?)
            })
            .collect()
    }

    /// **The population's receipt** (module header).
    pub fn receipt(&self) -> Result<PopulationReceipt, PopulationError> {
        let code = self.code()?;
        let bounds = self.charged_bounds();
        let mut families = Vec::with_capacity(self.members.len());
        let mut selected = None;
        for (index, (member, (lower, upper))) in self.members.iter().zip(&bounds).enumerate() {
            let alive = member.died.is_none();
            let posterior = self.posterior_of(&[index])?;
            if let Posterior::Bits(bits) = &posterior
                && bits.upper < Rat::one()
            {
                selected = Some(index);
            }
            families.push(FamilyReceipt {
                label: member.family.label(),
                identity: member.family.identity(),
                description: member.family.description(),
                prior: member.prior.clone(),
                born: member.born,
                died: member.died,
                code: if alive {
                    member.family.likelihood().code()?
                } else {
                    None
                },
                charged: if alive && !lower.is_zero() {
                    Some(code_between(lower, upper)?)
                } else {
                    None
                },
                posterior,
                keys: match member.family.readout() {
                    Readout::Keys(keys) => Some(keys),
                    _ => None,
                },
                drift: member.family.drift(),
                work: member.family.work(),
            });
        }
        Ok(PopulationReceipt {
            cells: self.cells,
            mass: self.mass.clone(),
            founded: self.founded.clone(),
            code,
            families,
            selected,
        })
    }

    /// **Collapse a living family's surviving keys into species** relative to the admitted future
    /// (module header, "Species collapse"): the population's code, its face over the admitted
    /// future and every posterior are unchanged; the receipt keeps every member's seed. Refused at
    /// a dead family and at a family that declares no exact check.
    pub fn collapse(
        &mut self,
        family: usize,
        future: AdmittedFuture,
    ) -> Result<Collapse, PopulationError> {
        let Some(member) = self.members.get_mut(family) else {
            return Err(refuse("a species collapse", "it names a declared family"));
        };
        if member.died.is_some() {
            return Err(refuse("a species collapse", "it names a living family"));
        }
        member.family.collapse(future)?.ok_or_else(|| {
            refuse(
                "a species collapse",
                "the family declares an exact check over the admitted future",
            )
        })
    }

    /// **Split the species a collapse merged** (module header, "Species collapse"): every member
    /// of a surviving species returns with its share, so a wider admitted future can collapse
    /// again. The population's code does not move.
    pub fn split(&mut self, family: usize, collapse: &Collapse) -> Result<(), PopulationError> {
        let Some(member) = self.members.get_mut(family) else {
            return Err(refuse("a species split", "it names a declared family"));
        };
        member.family.split(collapse)
    }

    /// Family `f`'s identity.
    pub fn identity(&self, family: usize) -> Option<Identity> {
        self.members
            .get(family)
            .map(|member| member.family.identity())
    }

    /// Family `f`'s readout.
    pub fn readout(&self, family: usize) -> Option<Readout<'_>> {
        self.members
            .get(family)
            .map(|member| member.family.readout())
    }
}
