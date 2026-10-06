//! **The execution port resident on the card** (`holonics::hnn::ExecutionPort` for a device;
//! design (c), "Realization on the card"; the lattice word and the hardware-surfaces rule; #76).
//!
//! [definition] [`Resident`] implements the port with its resident ([`Mounted`]) on a [`Card`]. It
//! returns, method by method, the **same** `InteractionReturn`s as the host reference
//! (`holonics::hnn::Reference`), the parity target: every word runs on the card, and the host keeps
//! what the port plan assigns it, read exactly from the card's integer records.
//!
//! | On the card | On the host |
//! |---|---|
//! | the moment and its ingest (`hnn_moment_ingest`, [`ResidentMoment`]); a pending ratio's counts frozen at its cut ([`MomentSnapshot`]) | the lift point `λ`, the receiving parametron's active suffix address (`hnn::receiving::ActiveAddress`, shifted at every ingested cell) and the host's mirror of the moment (the pending ratio's operand, which the deposit's samples and the state's bits read), checked equal at every ingest |
//! | the published constitution's loci at their lattices, the moved words scattered at each publication (`hnn::publication`) | the constitution `Θ`, the normal laws' prox steps, the receiving parametron's landmark tree and its deposit with its certificates (the landmark tree), the budgeted carry and its remainders, the budget (`Constitution::deposited`), and the operators `I − ½K`, `m_a` formed from it |
//! | the keyed charts, their rounded Newton–Schulz steps and exact certificates (`hnn::store`) | each refinement's decisions from the certificates (warm, cold, fallback, target), the cold start's transpose and the exact fallback |
//! | the word's open (`E_g M_g[c]`, the pair port), its ticks, its receiving read (`hnn_pair_weights`, `hnn_word_forward`) | the faces in `ℚ(θ)`, each tick's balance, the release (`hnn::readout`) |
//! | the receiving parametron's landmark tree mirrored, stored at the faces where paths part (`hnn::tree::CardTree`, campaign 2, the storage where paths part): each window's splits at every phase's causal address in cell order (the known targets' deposits applied and undone on the card), and each deposit's opened-path update with its splits, foundings and label runs | the class faces from the splits and their grain exponents (`hnn::receiving::faces_of_splits`), added to the card's wave at the grain (`ReceivingPhases::combine`); after every deposit the mirror's counts and the masses, `β`, stop weights, depth words and label ends of every node the deposit's walks opened or it founded, its joins and its held labels, checked against the host's tree (`CardTree::agrees_at`) |
//! | each declared ring resonator's ticks inside `hnn_word_forward`, its returned wave reaching the next junction; its state/input adjoint inside `hnn_word_reverse` (the loaded resonator) | the resonators' local operands and certified charts (`ResonatorOperands::at_cut`), formed once per publication (`publication::Loci::resonator_operands`); their balances and bounds read from the live word's record; gain contractions and deposition at the same producing operands |
//! | in the GPU suite's parity tests only ([`Resident::with_normal_mirror`]; off the exposure's path, where it replaced no host owner): each normal law's prox step a deposit takes once at its locus (`hnn_outer_update` for `ΔH` and `ΔW`, `hnn_budgeted_split` for their carries, the reaches `X̂f` by `hnn_lattice_read` through the host's successor chart; campaign 2), read against the host's successor (`crate::hnn::lattice::normal_deposit_on_card`), every step counted carried, declined by reason or skipped | the successor constitution (`Constitution::deposited`, the owner of `Θ`), the chart of `H′`, and the steps the card's words cannot carry (a sample off the dyadics, such as `R`'s covector on `(1/W)ℤ`) |
//! | the word's return (`hnn_word_reverse`) | the compare phase under the hardware law (`reference::compare_phase`: the tree at the grain beside the population's score, the Holon ratio and its covector), the return's source through `Rᵀ` (the covector lives on `(1/W)ℤ`), the composition onto the loci (`reference::compose`) |
//! | | keys, the collapse, the first law's ledger, the handles, every refusal's reason |
//!
//! [definition; agent-inferred] **The tree read moved to the card** (campaign 2; the hardware-surfaces rule; the
//! #76 debt of campaign 1, whose host read took 1,720 µs a window against the card's word at 2,110
//! µs). The mirror is uploaded at the mount, moved by the same steps as the host's tree at every
//! deposit, and read at every compare, release and re-read; the host completes the class faces
//! from the card's splits, and the tree's transfers, reads and updates are timed apart
//! (`WallTimes::{tree_transfer, tree_read, tree_deposit}`). The host's tree stays the owner: its
//! deposit keeps the certificates, and the collapse keeps it whole (the mirror is uploaded again
//! should it ever move).
//!
//! [definition] **The current stays on the card between methods** (the hardware law): the
//! moment's counts, the published loci, the kept charts, and a refine's word (its record and its
//! operands) until its compare reads its return. What crosses the bus per window is counted in
//! [`Traffic`].
//!
//! [definition] **The host's bookkeeping is the reference's** (`holonics::hnn::reference`): the
//! pending capacity, the kept read at its commit, the arrived operand of the first law, the aeon's
//! clock law (the carry-out, keys only between `close_aeon` and the next ingest), the budget stop,
//! each receipt's work, and the state's bits (the kept charts' bits read from the host's mirror of
//! the card's store). The exposure is the reference's protocol over this port
//! (`holonics::hnn::reference::expose`).

use std::cell::Cell;
use std::collections::BTreeMap;
use std::rc::Rc;
use std::time::Instant;

use holonics::aeon::{ClockLift, EnclosedLedger};
use holonics::compression::cost::ceil_log2;
use holonics::compression::landmark::context::{
    LandmarkDeclaration, Landmarks, Letter, code_length,
};
use holonics::hnn::constitution::{
    CAMPAIGN_ONE_BUDGET, Carrier, DepositReading, LandmarkStep, LinearLocus, gamma_length,
};
use holonics::hnn::keys::{self, KeyLocation};
use holonics::hnn::encoding::Encoded;
use holonics::hnn::moment::{Ingested, SourceCapacity};
use holonics::hnn::pending::Against;
use holonics::hnn::port::{
    Census, Deposit, ExecutionPort, Handle, MomentId, PendingId, PortReceipt, Pullback,
    ReceiptDetail, StagedId, Transpose, port_receipt, release_width, resonance_reading,
    source_order, stepped, wrote_all,
};
use holonics::hnn::propagation::path_attenuation;
use holonics::hnn::ratio::{HolonRatio, PhaseRatio};
use holonics::hnn::receiving::faces_of_splits;
use holonics::hnn::reference::{
    BudgetStop, ChartTally, ComparePhase, Cut, Declared, ExposedResident, Exposure, Reception,
    WallTimes, carry_bits, compare_phase, compose, expose, expose_from, window_code_length,
};
use holonics::hnn::retention::{Diamond, aeon_readings, collapse, contained, retained, separator};
use holonics::hnn::{
    Absorption, ActiveAddress, AeonBoundary, ChartKey, ChartReading, Constitution,
    ConstitutionRead, Current, Faces, Field, HnnError, Locus, PendingRatio, ReceivingPhases,
    ReceptionCarry, SourceMoment,
};
use holonics::navigator::Clock;
use holonics::ratio::Rat;
use holonics::ratio::algebraic::ExactInterval;
use holonics::ratio::work::ExactWork;
use holonics::receiver::reception::{Component, InteractionReturn, SourceOrder};
use holonics::receiver::release::{DecisionRule, LawfulOptions, ReleaseReturn, release};
use num_bigint::{BigInt, BigUint};
use num_traits::One;

use crate::hnn::DeviceError;
use crate::hnn::card::{Card, Layout};
use crate::hnn::carry::{CardCarry, CardOpening};
use crate::hnn::execute::{ResidentWord, SourceOpen, WordPlan};
use crate::hnn::lattice::{NormalMirror, normal_deposit_on_card};
use crate::hnn::moment::{MomentSnapshot, ResidentMoment};
use crate::hnn::publication::{ContactOperator, Loci, Publication};
use crate::hnn::readout::{self, Executed};
use crate::hnn::store::{ChartStore, Pair};
use crate::hnn::tree::{CardTree, TreeTimes};

fn device(error: DeviceError) -> HnnError {
    error.into_hnn()
}

/// [definition; agent-inferred, October 5] **A failed open is discarded, never consumed.** One
/// open's ingest: the card's, then the host mirror's, checked equal. On a refusal the two do not
/// hold one checked state: the card's ingest commits nothing past a refused occurrence and is
/// invalid after any failure past its launch (`ResidentMoment::is_valid`), while the host's commits
/// the occurrences admitted before the refused one (`Field::step_occurrence` is atomic per
/// occurrence). So the port's caller drops the open on every error returned here, and its handle
/// then reads `HnnError::UnknownHandle`.
fn ingest_open(
    open: &mut MomentSlot<'_>,
    field: &Field,
    current: &mut Current,
    cells: &Encoded,
) -> Result<Ingested, HnnError> {
    let carded = if cells.is_empty() {
        Ingested {
            cells: 0,
            carry_out: false,
        }
    } else {
        open.card.ingest(cells).map_err(device)?
    };
    let ingested = open.host.ingest(field, current, cells)?;
    if carded != ingested || open.card.lift() != current.lift() {
        return Err(HnnError::Realization {
            what: "the card's ingest against the host's moment",
        });
    }
    Ok(ingested)
}

/// **Every open moment but `except` re-keyed to the lift point's phases.** A moment whose re-key
/// fails holds an unchecked device write (`ResidentMoment::rekey`), so it is dropped with the
/// failed opens and the first failure is returned.
fn rekey_moments(
    moments: &mut BTreeMap<MomentId, MomentSlot<'_>>,
    field: &Field,
    current: &Current,
    except: Option<MomentId>,
) -> Result<(), HnnError> {
    let mut failed = Vec::new();
    for (id, moment) in moments.iter_mut() {
        if Some(*id) != except
            && let Err(error) = moment.card.rekey(field, current)
        {
            failed.push((*id, device(error)));
        }
    }
    let mut first = None;
    for (id, error) in failed {
        moments.remove(&id);
        first.get_or_insert(error);
    }
    first.map_or(Ok(()), Err)
}

// -------------------------------------------------------------------------------------------
// the traffic

/// [definition] **What crossed the bus, by phase** (octets, both directions), since the mount: an
/// exterior reading of the realization, beside the wall time; no law reads it.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Traffic {
    /// Every word's plan, operands, record and certificates (refine, compare, deposit, release,
    /// close), and the charts the store moved or read.
    pub words: u64,
    /// The returns' carried reads and records.
    pub returns: u64,
    /// The publications' words (whole at the mount, the moved words after).
    pub publications: u64,
    /// The ingests' cells and receipts.
    pub ingest: u64,
    /// The words run and the returns run.
    pub word_count: u64,
    pub return_count: u64,
}

// -------------------------------------------------------------------------------------------
// the resident

/// A moment on both sides: the host's mirror and the card's resident moment.
struct MomentSlot<'c> {
    host: SourceMoment,
    card: ResidentMoment<'c>,
}

/// [definition] **A word executed on the card, kept for its return**: its resident buffers and
/// record, the contacts' operators its balance read, and its charts' readings.
struct ExecutedWord<'c> {
    word: ResidentWord<'c>,
    operators: Vec<Rc<ContactOperator>>,
    readings: Vec<ChartReading>,
}

/// The refine's read kept for its compare, tagged with its commit (the reference's kept read).
struct KeptRead<'c> {
    commit: u64,
    word: ExecutedWord<'c>,
    faces: Faces,
}

struct PendingSlot<'c> {
    ratio: PendingRatio,
    emitted: Vec<Vec<Rat>>,
    moment: MomentSnapshot<'c>,
    kept: Option<KeptRead<'c>>,
    /// The opening the refine's word opened on (the reference's), so a compare that reads again
    /// opens on the same change.
    opening: CardOpening<'c>,
}

impl PendingSlot<'_> {
    fn bits(&self) -> u64 {
        self.ratio.bits()
            + self
                .emitted
                .iter()
                .flatten()
                .map(|x| x.numer().bits() + x.denom().bits())
                .sum::<u64>()
            + self.opening.bits()
    }
}

/// The first law's arrived operand (the reference's `Arrived`), with its counts on the card.
struct Arrived<'c> {
    ratio: PendingRatio,
    targets: Vec<usize>,
    moment: MomentSnapshot<'c>,
    /// The opening the compared word opened on, so the successor's re-read opens on it too.
    opening: CardOpening<'c>,
}

impl Arrived<'_> {
    fn bits(&self) -> u64 {
        self.ratio.bits()
            + self.opening.bits()
            + self
                .targets
                .iter()
                .map(|target| BigInt::from(*target).bits() + 1)
                .sum::<u64>()
    }
}

#[derive(Clone, Debug)]
struct AeonState {
    awaiting: bool,
    keys_admitted: bool,
    opening: Vec<BigInt>,
    cells: u64,
    closed: u64,
}

/// [definition] **The resident of the device port** (module header): the host's bookkeeping and
/// the card's current.
pub struct Mounted<'c> {
    field: Field,
    current: Current,
    address: ActiveAddress,
    constitution: Constitution,
    moments: BTreeMap<MomentId, MomentSlot<'c>>,
    pending: BTreeMap<PendingId, PendingSlot<'c>>,
    staged: BTreeMap<StagedId, Deposit>,
    next: u64,
    admitted: Vec<ReceivingPhases>,
    parametric: ClockLift,
    aeon: AeonState,
    ledger: EnclosedLedger,
    arrived: Option<Arrived<'c>>,
    released_bits: u64,
    stop: Option<BudgetStop>,
    tally: ChartTally,
    wall: WallTimes,
    publication: Rc<Publication<'c>>,
    store: ChartStore<'c>,
    /// The port's traffic reading, shared with the port so it outlives the resident.
    traffic: Rc<Cell<Traffic>>,
    /// The word's and the return's layouts as last derived, shared with the port.
    layouts: Rc<Cell<Option<(Layout, Layout)>>>,
    /// The receiving parametron's landmark tree mirrored on the card (campaign 2), at the first
    /// admitted receiver's ring, moved by every deposit's steps as the host's tree is.
    tree: Option<(usize, CardTree<'c>)>,
    /// The tree's wall time by part, shared with the port.
    tree_times: Rc<Cell<TreeTimes>>,
    /// [definition; the reception carry §2.6] The one carried change the next reception opens on
    /// under a declared reception carry (`crate::hnn::carry`): its words on the card and the
    /// reference's carry mirrored on the host. `None` at rest and at the mount.
    carried: Option<Rc<CardCarry<'c>>>,
}

impl<'c> Mounted<'c> {
    pub fn field(&self) -> &Field {
        &self.field
    }

    /// The receiving parametron's active suffix address (the reference's `Resident::address`).
    pub fn address(&self) -> &ActiveAddress {
        &self.address
    }

    /// What crossed the bus through this resident's port (exterior; [`Traffic`]).
    pub fn traffic(&self) -> Traffic {
        self.traffic.get()
    }

    /// Count what crossed the bus.
    fn count(&self, update: impl FnOnce(&mut Traffic)) {
        let mut traffic = self.traffic.get();
        update(&mut traffic);
        self.traffic.set(traffic);
    }

    fn fresh(&mut self) -> u64 {
        self.next += 1;
        self.next
    }

    /// Share the tree's wall time by part with the port (exterior).
    fn publish_tree_times(&self) {
        if let Some((_, tree)) = &self.tree {
            self.tree_times.set(tree.times());
        }
    }

    fn forget_kept_reads(&mut self) {
        for slot in self.pending.values_mut() {
            slot.kept = None;
        }
    }

    /// The exact bits of the resident's state, as the reference counts them (the kept charts' bits
    /// read from the host's mirror of the card's store).
    fn bits(&self) -> u64 {
        let lift: u64 = self
            .current
            .lift()
            .iter()
            .map(|x| x.bits() + 1)
            .sum::<u64>()
            + self.address.bits(self.field.alphabet());
        let moments: u64 = self
            .moments
            .values()
            .map(|moment| moment.host.dense_bits())
            .sum();
        let pending: u64 = self.pending.values().map(PendingSlot::bits).sum();
        let staged: u64 = self.staged.values().map(Deposit::bits).sum();
        let arrived = self.arrived.as_ref().map_or(0, Arrived::bits);
        let carried = self
            .carried
            .as_ref()
            .map_or(0, |carry| carry_bits(&carry.host));
        lift + moments
            + carried
            + pending
            + staged
            + arrived
            + self.constitution.exact_bits()
            + self.store.bits()
    }

    /// **Execute a word on the card** at a publication (module header): the operators formed, the
    /// charts refined on the card, the word's open, ticks and read in one launch, and the wave's
    /// faces read on the host (the tree part is added at compare, `PendingRatio::against`).
    fn execute(
        &mut self,
        ratio: &PendingRatio,
        moment: &MomentSnapshot<'c>,
        publication: &Rc<Publication<'c>>,
        card: &'c Card,
        opening: &CardOpening<'c>,
    ) -> Result<(ExecutedWord<'c>, Faces), HnnError> {
        let field = &self.field;
        let current = ratio.current(field)?;
        // The normalized open (it reads no held cell), read from the pending ratio's copy of the
        // moment.
        let opens = SourceOpen::of(field, ratio.moment())?;
        // The host's declared resonator operands and charts at this publication, formed once per
        // publication (`Loci::resonator_operands`); ring/contact chart refinement remains resident
        // below.
        let resonators = publication.loci.resonator_operands(field)?;
        let plan = WordPlan::form(
            field,
            &current,
            publication,
            ratio.phases(),
            moment,
            &opens,
            &resonators,
        )?;
        // A received opening's carry table and its words on the card (the reception carry).
        let (plan, carried) = opening.plan(plan, &publication.loci)?;
        let loci = &publication.loci;
        let mut operators = Vec::with_capacity(plan.contacts.len());
        for (a, contact) in plan.contacts.iter().enumerate() {
            operators.push(loci.contact_operator(
                a,
                &contact.carry,
                &contact.conductance,
                field.step(),
            )?);
        }
        let mut pairs: Vec<Pair<'_>> = loci
            .rings
            .iter()
            .enumerate()
            .map(|(g, ring)| Pair {
                key: ChartKey::Ring(g),
                matrix: &ring.operator,
                words: &ring.operator_words,
            })
            .collect();
        for (a, operator) in operators.iter().enumerate() {
            pairs.push(Pair {
                key: ChartKey::Contact {
                    contact: a,
                    carry: plan.contacts[a].carry.clone(),
                },
                matrix: &operator.operator,
                words: &operator.words,
            });
        }
        let refined = self.store.refine(&pairs)?;
        drop(pairs);
        let (word, launches) = ResidentWord::forward(
            card,
            plan,
            Rc::clone(publication),
            moment,
            &self.store,
            &refined,
            carried,
        )?;
        self.layouts.set(Some(launches.layouts()));
        let mut word = word;
        let (octets, store) = (word.octets as u64, self.store.octets as u64);
        self.count(|traffic| {
            traffic.words += octets + store;
            traffic.word_count += 1;
        });
        self.store.octets = 0;
        word.octets = 0;
        let faces = readout::faces(&word.plan, &word.record)?;
        Ok((
            ExecutedWord {
                word,
                operators,
                readings: refined.readings,
            },
            faces,
        ))
    }

    /// **The arrived targets' code length at a publication**: a word on the card at the arrived
    /// ratio's operands, its wave's faces with the tree of the constitution the publication
    /// publishes (a deposit's successor, or the resident's own) at the targets' addresses, compared
    /// with the targets; and the charts' readings.
    fn arrived_code_length(
        &mut self,
        publication: &Rc<Publication<'c>>,
        successor: Option<&Constitution>,
        card: &'c Card,
    ) -> Result<(ExactInterval, Vec<ChartReading>), HnnError> {
        let arrived = self.arrived.take().ok_or(HnnError::Shape {
            what: "the arrived targets a staged deposit was compared on",
            expected: 1,
            found: 0,
        })?;
        let read = self.execute(
            &arrived.ratio,
            &arrived.moment,
            publication,
            card,
            &arrived.opening,
        );
        let constitution = successor.unwrap_or(&self.constitution);
        let tree = self.tree.as_mut();
        let result = read.and_then(|(word, wave)| {
            let (against, _, _) =
                tree_against(tree, constitution, &arrived.ratio, &wave, &arrived.targets)?;
            let scored = arrived
                .ratio
                .scored(constitution, &against, &arrived.targets)?;
            Ok((window_code_length(&scored.model)?, word.readings))
        });
        self.arrived = Some(arrived);
        result
    }
}

impl ExposedResident for Mounted<'_> {
    fn admitted(&self) -> &[ReceivingPhases] {
        &self.admitted
    }
    fn constitution(&self) -> &Constitution {
        &self.constitution
    }
    fn stopped(&self) -> Option<&BudgetStop> {
        self.stop.as_ref()
    }
    fn moment(&self, id: &MomentId) -> Option<&SourceMoment> {
        self.moments.get(id).map(|moment| &moment.host)
    }
    fn current(&self) -> &Current {
        &self.current
    }
    fn state_bits(&self) -> u64 {
        self.bits()
    }
    fn state_bits_without_collapse(&self) -> u64 {
        self.bits() + self.released_bits
    }
    fn tally(&self) -> &ChartTally {
        &self.tally
    }
    fn wall(&self) -> &WallTimes {
        &self.wall
    }
    fn carried(&self) -> Option<&ReceptionCarry> {
        self.carried.as_ref().map(|carry| &carry.host)
    }
}

// -------------------------------------------------------------------------------------------
// the port

/// [definition] **The device's execution port**: a card, with the declared pending capacity,
/// constitution budget, and an exposure's deadline if one is set (the reference's
/// declarations, so the two describe the same field).
pub struct Resident<'c> {
    card: &'c Card,
    pending_capacity: usize,
    budget: u64,
    deadline: Option<u64>,
    /// How a reception's word opens (the reference's [`Reception`]): the carry at `A = 0` unless
    /// declared.
    reception: Reception,
    /// The normal-law mirror's tally when the mirror runs (the GPU suite's parity tests,
    /// [`Resident::with_normal_mirror`]); `None` on the exposure's path, which does not run it.
    normal_mirror: Option<Rc<Cell<NormalMirror>>>,
    traffic: Rc<Cell<Traffic>>,
    layouts: Rc<Cell<Option<(Layout, Layout)>>>,
    tree_times: Rc<Cell<TreeTimes>>,
}

impl<'c> Resident<'c> {
    /// Campaign 1's declarations on a card: `B_Θ = 2^33` and a pending capacity of 64 (the
    /// reference's), every locus's step certified at its deposit.
    pub fn campaign_one(card: &'c Card) -> Self {
        Self::new(card, 64, CAMPAIGN_ONE_BUDGET)
    }

    pub fn new(card: &'c Card, pending_capacity: usize, budget: u64) -> Self {
        Self {
            card,
            pending_capacity,
            budget,
            deadline: None,
            reception: Reception::Carry(Absorption::Nothing),
            normal_mirror: None,
            traffic: Rc::new(Cell::new(Traffic::default())),
            layouts: Rc::new(Cell::new(None)),
            tree_times: Rc::new(Cell::new(TreeTimes::default())),
        }
    }

    /// **The word's and the return's realizations** as the port last derived them from the card's
    /// census (`hnn_word_forward`, `hnn_word_reverse`: one block, its threads striding each stage's
    /// rows), `None` before the first word.
    pub fn word_layouts(&self) -> Option<(Layout, Layout)> {
        self.layouts.get()
    }

    /// What crossed the bus through this port since it was made, over every resident it mounted
    /// (exterior; [`Traffic`]).
    pub fn traffic(&self) -> Traffic {
        self.traffic.get()
    }

    /// The landmark tree's wall time by part on the last mounted resident (exterior; [`TreeTimes`]).
    pub fn tree_times(&self) -> TreeTimes {
        self.tree_times.get()
    }

    /// **Run the normal-law mirror in every deposit** (the GPU suite's parity test; campaign 2's
    /// review moved it off the exposure's path, where it replaced no host owner): each normal law's
    /// prox step a deposit takes once at its locus is formed on the card and read against the host's
    /// successor (`crate::hnn::lattice::normal_deposit_on_card`), and its tally
    /// ([`Resident::normal_mirror`]) counts the steps carried, declined by reason and skipped.
    pub fn with_normal_mirror(self) -> Self {
        Self {
            normal_mirror: Some(Rc::new(Cell::new(NormalMirror::default()))),
            ..self
        }
    }

    /// The normal-law mirror's tally since the port was made, when it runs.
    pub fn normal_mirror(&self) -> Option<NormalMirror> {
        self.normal_mirror.as_ref().map(|tally| tally.get())
    }

    /// [definition; agent-inferred, October 3] **The reception's opening**
    /// (`Reference::with_reception`): the carry at `A = 0` unless declared, as the host's (the
    /// reception carry §8). Each reception's word opens on the change at the last crossing of the
    /// previous word read, written by its refine and kept on the card (`crate::hnn::carry`);
    /// [`Reception::Rest`] declares the `A = I` limit.
    pub fn with_reception(self, reception: Reception) -> Self {
        Self { reception, ..self }
    }

    /// The declared reception.
    pub fn reception(&self) -> Reception {
        self.reception
    }

    /// [definition; the reception carry §2.4] **Mount on a declared constitution with a
    /// reception's carried end restored** (`Reference::mount_carried`): the carry uploaded to the
    /// card, so the next reception's word opens on it as the reference's does. Refused where the
    /// carry has another field's shape, lies off the transients' lattice, or this port receives at
    /// rest. Like the reference's, it is the narrower remount: the card's store holds no kept chart,
    /// so the next word is the uninterrupted chain's only where every kept chart is its operator's
    /// cold chart (October 5; the whole continuation carries the kept charts in the passage).
    pub fn mount_carried(
        &self,
        field: &Field,
        current: &Current,
        constitution: Constitution,
        carry: ReceptionCarry,
    ) -> Result<Mounted<'c>, HnnError> {
        if !matches!(self.reception, Reception::Carry(_)) || !carry.fits(field) {
            return Err(HnnError::ContinuingState {
                what: "a carried end mounted at rest or of another field's shape",
            });
        }
        let mut resident = self.mount_with(field, current, constitution)?;
        resident.carried = Some(Rc::new(CardCarry::restored(self.card, field, carry)?));
        Ok(resident)
    }

    /// An exposure's deadline in windows (`Reference::with_deadline`).
    pub fn with_deadline(self, windows: u64) -> Self {
        Self {
            deadline: Some(windows),
            ..self
        }
    }

    /// **Campaign 1's exposure on the card**: the reference's protocol
    /// (`holonics::hnn::reference::expose`) over this port.
    pub fn expose(&self, field: &Field, cut: &Cut) -> Result<Exposure, HnnError> {
        expose(
            self,
            &Declared {
                budget: self.budget,
                pending_capacity: self.pending_capacity,
                deadline: self.deadline,
                refining: false,
            },
            field,
            cut,
        )
    }

    /// Run the shared exposure from a caller-declared constitution. This is the resident-card
    /// counterpart to `Reference::expose_with`, used to compare a loaded resonator source against
    /// the same cut and prequential protocol.
    pub fn expose_with(
        &self,
        field: &Field,
        cut: &Cut,
        constitution: Constitution,
    ) -> Result<Exposure, HnnError> {
        let current = Current::at_rest(field);
        let resident = self.mount_with(field, &current, constitution)?;
        expose_from(
            self,
            &Declared {
                budget: self.budget,
                pending_capacity: self.pending_capacity,
                deadline: self.deadline,
                refining: false,
            },
            field,
            cut,
            resident,
        )
    }

    /// **Mount on a declared constitution** (the reference's `mount_with`): the Holarchy's gluing
    /// certified, the admitted family declared, and the constitution's loci published on the card
    /// with an empty chart store.
    pub fn mount_with(
        &self,
        field: &Field,
        current: &Current,
        constitution: Constitution,
    ) -> Result<Mounted<'c>, HnnError> {
        let parametric = field.holarchy(&constitution)?.parametric();
        if parametric != field.parametric() {
            return Err(HnnError::Shape {
                what: "the Holarchy's parametric orientation against the field's joint clock lift",
                expected: field.rings().len(),
                found: parametric.navigators(),
            });
        }
        let lattice = *field.word_lattice().ok_or(HnnError::Realization {
            what: "a field whose word runs on no declared lattice (the card carries lattice words)",
        })?;
        let admitted = field
            .receivers()
            .iter()
            .map(|receiver| ReceivingPhases::declare(field, &constitution, current, receiver))
            .collect::<Result<Vec<_>, _>>()?;
        let publication = Publication::publish(self.card, Loci::of(field, &constitution)?, None)?;
        // The receiving parametron's tree mirrored on the card, with room for a window's overlay
        // and a re-read's (`A − 1` deposits past the population).
        let tree = match admitted.first() {
            Some(phases) => match constitution.landmarks(phases.ring()) {
                Some(tree) => Some((
                    phases.ring(),
                    CardTree::mirror(self.card, tree, phases.aperture().max(2) - 1)
                        .map_err(device)?,
                )),
                None => None,
            },
            None => None,
        };
        let octets = publication.octets as u64;
        let traffic = Rc::clone(&self.traffic);
        traffic.set(Traffic {
            publications: traffic.get().publications + octets,
            ..traffic.get()
        });
        Ok(Mounted {
            field: field.clone(),
            current: current.clone(),
            address: ActiveAddress::of_field(field, current, &constitution)?,
            constitution,
            moments: BTreeMap::new(),
            pending: BTreeMap::new(),
            staged: BTreeMap::new(),
            next: 0,
            admitted,
            parametric,
            aeon: AeonState {
                awaiting: false,
                keys_admitted: false,
                opening: current.lift().to_vec(),
                cells: 0,
                closed: 0,
            },
            ledger: EnclosedLedger::new(),
            arrived: None,
            released_bits: 0,
            stop: None,
            tally: ChartTally::new(field),
            wall: WallTimes::default(),
            publication: Rc::new(publication),
            store: ChartStore::new(self.card, &lattice)?,
            traffic,
            layouts: Rc::clone(&self.layouts),
            tree,
            tree_times: Rc::clone(&self.tree_times),
            carried: None,
        })
    }
}

/// **The tree part of a window's faces** (the landmark tree; `PendingRatio::against`): on the card's
/// mirror when it holds the receiving ring's tree, its splits in cell order (the known targets'
/// deposits applied and undone on the card) completed into class faces on the host
/// (`hnn::receiving::faces_of_splits`) and added to the wave's faces at the grain; otherwise the host's
/// read. Returns the faces, the read's wall time and the transfers' apart.
fn tree_against(
    tree: Option<&mut (usize, CardTree<'_>)>,
    constitution: &Constitution,
    ratio: &PendingRatio,
    wave: &Faces,
    known: &[usize],
) -> Result<(Against, std::time::Duration, std::time::Duration), HnnError> {
    let start = Instant::now();
    let phases = ratio.phases();
    let Some((ring, tree)) = tree.filter(|(ring, _)| *ring == phases.ring()) else {
        let against = ratio.against(constitution, wave, known)?;
        return Ok((against, start.elapsed(), std::time::Duration::ZERO));
    };
    let declaration: &LandmarkDeclaration = constitution
        .landmarks(*ring)
        .ok_or(HnnError::MissingReceivingMap { ring: *ring })?
        .declaration();
    let before = tree.times().transfer;
    let addresses = ratio.addresses(known)?;
    let splits = tree.window_splits(&addresses, known).map_err(device)?;
    let completing = Instant::now();
    let trees = faces_of_splits(declaration, &splits, phases.grain())?;
    let complete = completing.elapsed();
    let combining = Instant::now();
    let faces = phases.combine(wave, &trees)?;
    tree.completed(complete, combining.elapsed());
    let transfer = tree.times().transfer - before;
    Ok((
        Against { faces, trees },
        start.elapsed() - transfer,
        transfer,
    ))
}

fn zero_ticks(field: &Field) -> Vec<u64> {
    vec![0u64; field.rings().len()]
}

/// A compare's readings: the ratio, the pullback, the deposit, the receipt, the source order, the
/// phases, the wall time and the window's code length.
type Compared<'c> = (
    HolonRatio,
    Pullback,
    Deposit,
    PortReceipt,
    SourceOrder,
    ReceivingPhases,
    WallTimes,
    ExactInterval,
);

impl<'c> Resident<'c> {
    /// **The compare of a pending ratio taken out of the resident** (the reference's compare, the
    /// word's return on the card): its kept read at the published commit, or a word read again.
    fn compared(
        &self,
        resident: &mut Mounted<'c>,
        slot: &PendingSlot<'c>,
        kept: Option<KeptRead<'c>>,
        target: &Encoded,
        field: &Field,
    ) -> Result<Compared<'c>, HnnError> {
        let classes: Vec<usize> = target.classes_read().collect();
        let targets = classes.as_slice();
        let commit = resident.constitution.commit();
        let ratio = &slot.ratio;
        let phases = ratio.phases().clone();
        let mut wall = WallTimes::default();
        let (mut word, faces) = match kept.filter(|kept| kept.commit == commit) {
            Some(KeptRead { word, faces, .. }) => (word, faces),
            None => {
                let start = Instant::now();
                let publication = Rc::clone(&resident.publication);
                let (word, faces) = resident.execute(
                    ratio,
                    &slot.moment,
                    &publication,
                    self.card,
                    &slot.opening,
                )?;
                resident.tally.read(&word.readings);
                wall.compare_read = start.elapsed();
                (word, faces)
            }
        };
        // The tree part of the combined face at each phase's causal address (the landmark tree): the
        // splits read on the card's mirror of the published tree, the class faces completed on the
        // host.
        let (against, read, transfer) = tree_against(
            resident.tree.as_mut(),
            &resident.constitution,
            ratio,
            &faces,
            targets,
        )?;
        wall.tree_read = read;
        wall.tree_transfer = transfer;
        resident.publish_tree_times();
        let start = Instant::now();
        let residual: Vec<Vec<Rat>> = faces
            .logits
            .iter()
            .zip(&slot.emitted)
            .map(|(now, then)| now.iter().zip(then).map(|(a, b)| a - b).collect())
            .collect();
        // The receiver's scored face: its population over the tree's and the combined face (ruling
        // A, THE_REBUILD U1), received phase by phase, scored on the host as the reference scores
        // it; beside it the tree's executed face alone, the tree at the grain, the Holon ratio and its
        // covector, under the hardware law (`reference::compare_phase`).
        let ComparePhase {
            tree_grain,
            scored,
            holon,
            covector,
        } = compare_phase(field, &resident.constitution, ratio, against, target)?;
        resident.constitution.receiving_map(phases.ring()).ok_or(
            HnnError::MissingReceivingMap {
                ring: phases.ring(),
            },
        )?;
        wall.holon = start.elapsed();
        let start = Instant::now();
        let publication = Rc::clone(&word.word.publication);
        let map = &publication.loci.maps[phases.ring()]
            .as_ref()
            .ok_or(HnnError::MissingReceivingMap {
                ring: phases.ring(),
            })?
            .matrix;
        let source = readout::source(
            field,
            &word.word.plan,
            &word.word.record,
            &covector,
            map,
            &ratio.anchor()[phases.ring()],
        )?;
        let reverse = word.word.reverse(&source.carried)?;
        let octets = word.word.octets as u64;
        resident.count(|traffic| {
            traffic.returns += octets;
            traffic.return_count += 1;
        });
        word.word.octets = 0;
        let back = readout::word_return(
            &word.word.plan,
            &publication.loci,
            &word.word.record,
            &reverse,
            source,
        );
        wall.pull_back = start.elapsed();
        let start = Instant::now();
        let (pullback, deposit) = compose(
            field,
            &resident.constitution,
            ratio,
            &slot.opening.host(),
            &back,
            targets,
            &scored.steps,
        )?;
        wall.compose = start.elapsed();
        let code_length = window_code_length(&scored.model)?;
        let order = source_order(field, ratio.anchor(), ratio.moment().cells());
        let mut work = ExactWork::nothing();
        wrote_all(&mut work, covector.logits().iter().flatten());
        wrote_all(&mut work, back.opening.iter().flatten());
        let detail = ReceiptDetail::Compare {
            code_length: code_length.clone(),
            excess: holon.excess(),
            windings: holon.phases().iter().map(PhaseRatio::winding).collect(),
            residual,
            reached: deposit.loci(),
            released: back.released.clone(),
            tree: scored.tree,
            tree_grain,
            model: scored.model,
        };
        let steps = phases.junction_steps() as u64;
        let ticks = vec![steps; field.rings().len()];
        let mut receipt = port_receipt(&ticks, field.step(), work, detail)?;
        receipt.unresolved = holon
            .faces()
            .faces
            .iter()
            .map(|face| face.fibres())
            .collect();
        Ok((
            holon,
            pullback,
            deposit,
            receipt,
            order,
            phases,
            wall,
            code_length,
        ))
    }
}

impl<'c> ExecutionPort for Resident<'c> {
    type Resident = Mounted<'c>;

    fn census(&self) -> Census {
        Census {
            pending_capacity: self.pending_capacity,
            budget: self.budget,
            arithmetic: "exact integers on the card: ℤ/2^128 ring words under the l1 certificate, \
                         lattice coordinates in signed 64-bit words, the nearest-point split with its \
                         remainder carried; ℚ and ℚ(θ) on the host; every refusal reported",
        }
    }

    fn mount(&self, field: &Field, current: &Current) -> Result<Mounted<'c>, HnnError> {
        let constitution = Constitution::initial(field, self.budget)?;
        self.mount_with(field, current, constitution)
    }

    fn read(
        &self,
        resident: &Mounted<'c>,
    ) -> Result<(Field, Current, Vec<(Handle, u64)>), HnnError> {
        let mut handles: Vec<(Handle, u64)> = resident
            .moments
            .iter()
            .map(|(id, moment)| (Handle::Moment(*id), moment.host.dense_bits()))
            .collect();
        handles.extend(
            resident
                .pending
                .iter()
                .map(|(id, slot)| (Handle::Pending(*id), slot.bits())),
        );
        handles.extend(
            resident
                .staged
                .iter()
                .map(|(id, deposit)| (Handle::Staged(*id), deposit.bits())),
        );
        Ok((resident.field.clone(), resident.current.clone(), handles))
    }

    fn ingest(
        &self,
        resident: &mut Mounted<'c>,
        moment: Option<&MomentId>,
        cells: &Encoded,
    ) -> Result<
        (
            MomentId,
            InteractionReturn<Ingested, (), (), Vec<ReceivingPhases>, PortReceipt>,
        ),
        HnnError,
    > {
        if resident.aeon.awaiting {
            return Err(HnnError::AeonAwaitingClose);
        }
        let field = resident.field.clone();
        field.admit(cells)?;
        // The card steps a ring by the admitted encoding's advance plus the carry: an identity by
        // the lock's fit, a located passage by its classes' digits at their exact width, mounted by
        // the native owner (`ResidentMoment::ingest`; #76).
        let codes: Vec<usize> = cells.classes_read().collect();
        // [definition; agent-inferred, October 6] **The capacity preflight, before anything moves**
        // (`hnn::moment`, "The checked reading"): a nonempty passage's clock family must have a
        // certificate this field admits (`Field::capacity_for`: a located passage on a field whose
        // population is below the located `n*` is refused here), and a continuing moment must read
        // its capacity at its current state. A refusal leaves the lift, the moments, the address and
        // the aeon as the call found them.
        if !cells.is_empty() {
            field.capacity_for(cells)?;
        }
        let id = match moment {
            Some(id) if resident.moments.contains_key(id) => {
                SourceCapacity::checked_of(&resident.moments[id].host, &field, &resident.current)?;
                *id
            }
            Some(id) => {
                return Err(HnnError::UnknownHandle {
                    handle: Handle::Moment(*id),
                });
            }
            None => {
                let id = MomentId(resident.fresh());
                let card =
                    ResidentMoment::open(self.card, &field, &resident.current).map_err(device)?;
                resident.moments.insert(
                    id,
                    MomentSlot {
                        host: SourceMoment::open(&field, &resident.current),
                        card,
                    },
                );
                id
            }
        };
        let before = resident.current.lift().to_vec();
        let found = resident.current.clone();
        let start = Instant::now();
        // The cells' 32-bit classes and the lift's and phases' words, and on the located route the
        // located chart, one `u64` digit per ring and class (`8·rings·|A|` octets), counted once the
        // card launched: on its checked receipt, or on a failure past its launch.
        let octets = if codes.is_empty() {
            0
        } else {
            let rings = field.rings().len();
            let located = if cells.located().is_some() {
                8 * rings * field.alphabet()
            } else {
                0
            };
            (4 * codes.len() + 8 * (2 + rings) + located) as u64
        };
        let open = resident
            .moments
            .get_mut(&id)
            .expect("the moment was checked or opened");
        // The card's ingest, resident, and the host's mirror, checked equal. A failed ingest
        // discards its open (`ResidentMoment::is_valid`): it is never read or ingested again.
        let ingested = match ingest_open(open, &field, &mut resident.current, cells) {
            Ok(ingested) => ingested,
            Err(error) => {
                let launched = !open.card.is_valid();
                resident.moments.remove(&id);
                if launched {
                    resident.count(|traffic| traffic.ingest += octets);
                }
                return Err(error);
            }
        };
        // [definition; agent-inferred, October 6] The receipt's capacity is the host mirror's checked
        // reading against its producing partition and the reached lift point, as the reference's
        // (`SourceCapacity::checked_of`). The preflight admitted the clock family and the moment's
        // state, so a refusal here is a reached state outside the certificate: the whole open, card
        // and host, is discarded (the failed-open disposition), and the host lift returns to where
        // the call found it (no other moment's card has been re-keyed yet). The card launched and
        // returned, so its traffic is counted either way.
        let capacity = SourceCapacity::checked_of(&open.host, &field, &resident.current);
        resident.count(|traffic| traffic.ingest += octets);
        let capacity = match capacity {
            Ok(capacity) => capacity,
            Err(error) => {
                resident.moments.remove(&id);
                resident.current = found;
                return Err(error);
            }
        };
        // The receiving parametron's active suffix address receives the cells the moment took,
        // and its contact letters' site kinds refresh after the ingest, as the reference's.
        for &code in &codes[..ingested.cells] {
            resident.address.receive(code)?;
        }
        let opening = if ingested.carry_out {
            resident.current.lift()
        } else {
            &resident.aeon.opening
        };
        if !resident
            .address
            .reader()
            .agrees(&field, &resident.current, opening)
        {
            return Err(HnnError::Shape {
                what: "the address register's clock against the lift point",
                expected: field.rings().len(),
                found: 0,
            });
        }
        resident.address.refresh(&field, &resident.constitution)?;
        // Every other open moment steps from the one lift point: its card's phases follow it.
        if ingested.cells > 0 && resident.moments.len() > 1 {
            rekey_moments(&mut resident.moments, &field, &resident.current, Some(id))?;
        }
        let open = &resident.moments[&id];
        resident.wall.ingest += start.elapsed();
        if ingested.cells > 0 {
            resident.aeon.keys_admitted = false;
        }
        resident.aeon.cells += ingested.cells as u64;
        if ingested.carry_out {
            resident.aeon.awaiting = true;
        }
        let ticks: Vec<u64> = resident
            .current
            .lift()
            .iter()
            .zip(&before)
            .map(|(after, before)| {
                u64::try_from(after - before).expect("a lift only advances at ingest")
            })
            .collect();
        let n = open.host.cells();
        let detail = ReceiptDetail::Ingest {
            cells: ingested.cells as u64,
            moment_bits: open.host.dense_bits(),
            capacity,
            source_bits: n * ceil_log2(&BigUint::from(field.alphabet())),
            carry_out: ingested.carry_out,
        };
        let mut work = ExactWork::nothing();
        holonics::hnn::port::resident(&mut work, open.host.dense_bits());
        stepped(&mut work, ingested.cells as u64);
        let order = source_order(&field, resident.current.lift(), n);
        Ok((
            id,
            InteractionReturn {
                forward: Component::Present(ingested),
                pullback: Component::Absent("ingestion produces no covector"),
                deposit: Component::Absent("ingestion deposits nothing"),
                order: Component::Present(order),
                phases: Component::Absent("nothing is read at ingest"),
                receipt: port_receipt(&ticks, &Rat::one(), work, detail)?,
            },
        ))
    }

    fn locate_keys(
        &self,
        resident: &mut Mounted<'c>,
        crib: &Encoded,
        offset: usize,
    ) -> Result<
        InteractionReturn<KeyLocation, (), Vec<Option<Clock>>, Vec<ReceivingPhases>, PortReceipt>,
        HnnError,
    > {
        if !resident.aeon.keys_admitted {
            return Err(HnnError::KeysNotAdmitted);
        }
        let field = resident.field.clone();
        field.admit(crib)?;
        if crib.len() as u64 > resident.aeon.closed {
            return Err(HnnError::Shape {
                what: "a closing crib's cells against the closed aeon's",
                expected: usize::try_from(resident.aeon.closed).unwrap_or(usize::MAX),
                found: crib.len(),
            });
        }
        let location = keys::locate_closing(&field, &resident.current, crib, offset)?;
        let jumps = location.rekey(&field, &mut resident.current)?;
        resident.address.synchronize(&field, &resident.current)?;
        // Re-keying moves only the lift's phase classes: every resident moment steps from them.
        rekey_moments(&mut resident.moments, &field, &resident.current, None)?;
        resident.aeon.opening = resident.current.lift().to_vec();
        let published = location
            .rings
            .iter()
            .map(|ring| match ring.carried {
                Some(_) => field
                    .ring(ring.ring)
                    .clock_at(&resident.current.lift()[ring.ring])
                    .map(Some),
                None => Ok(None),
            })
            .collect::<Result<Vec<_>, HnnError>>()?;
        let detail = ReceiptDetail::Keys {
            fibres: location.rings.iter().map(|ring| ring.fibre.len()).collect(),
            orbits: location.rings.iter().map(|ring| ring.orbits).collect(),
            fell_back: location.rings.iter().map(|ring| ring.fell_back).collect(),
            failing_loops: location
                .rings
                .iter()
                .map(|ring| ring.failing_loop.clone())
                .collect(),
            candidates: location.rings.iter().map(|ring| ring.seeds).collect(),
            work: location.rings.iter().map(|ring| ring.work).collect(),
            jumps,
        };
        let mut work = ExactWork::nothing();
        for ring in &location.rings {
            holonics::hnn::port::added(&mut work, ring.work);
        }
        let order = source_order(&field, resident.current.lift(), crib.len() as u64);
        Ok(InteractionReturn {
            forward: Component::Present(location),
            pullback: Component::Absent("key location is discrete; the key covector is a reading"),
            deposit: Component::Present(published),
            order: Component::Present(order),
            phases: Component::Absent("nothing is read when keys are located"),
            receipt: port_receipt(&zero_ticks(&field), &Rat::one(), work, detail)?,
        })
    }

    fn refine(
        &self,
        resident: &mut Mounted<'c>,
        moment: &MomentId,
        phases: &ReceivingPhases,
    ) -> Result<
        (
            PendingId,
            InteractionReturn<Faces, (), (), Vec<ReceivingPhases>, PortReceipt>,
        ),
        HnnError,
    > {
        if resident.pending.len() >= self.pending_capacity {
            return Err(HnnError::PendingCapacity {
                capacity: self.pending_capacity,
            });
        }
        // One chain in refine order under the carry, as the reference's (the reception carry §8).
        let opening = match self.reception {
            Reception::Rest => CardOpening::Rest,
            Reception::Carry(absorption) => match &resident.carried {
                Some(carry) => CardOpening::Received {
                    carry: Rc::clone(carry),
                    absorption,
                },
                None => CardOpening::Rest,
            },
        };
        let source = resident
            .moments
            .get(moment)
            .ok_or(HnnError::UnknownHandle {
                handle: Handle::Moment(*moment),
            })?;
        let ratio = PendingRatio::produce(
            &resident.current,
            &source.host,
            &resident.address,
            phases,
            resident.constitution.commit(),
        )?;
        let snapshot = source.card.snapshot().map_err(device)?;
        let start = Instant::now();
        let publication = Rc::clone(&resident.publication);
        let (word, faces) =
            resident.execute(&ratio, &snapshot, &publication, self.card, &opening)?;
        let read = start.elapsed();
        let ended = match self.reception {
            Reception::Rest => None,
            Reception::Carry(absorption) => Some(Rc::new(CardCarry::ended(
                &word.word,
                opening.ticks(),
                absorption,
            )?)),
        };
        let start = Instant::now();
        let field = &resident.field;
        let executed = Executed {
            contacts: word
                .operators
                .iter()
                .map(|operator| (&operator.words, &operator.norm))
                .collect(),
            readings: &word.readings,
        };
        let released = readout::released(
            &word.word.plan,
            &publication.loci,
            &word.word.record,
            &executed,
        )?;
        resident.tally.read(&released.charts);
        // Loaded resonators ran inside this word. The release reads their actual state and
        // balance from that same record; no separate forward evaluation follows it.
        let path = path_attenuation(
            field,
            ratio.anchor(),
            phases.ring(),
            phases.last_epoch(),
            phases.grain(),
        )?;
        let reached: Vec<Locus> = Diamond::opened(field, phases, &opening.host().support(field))
            .retained(field)
            .into_iter()
            .filter(|locus| !resident.constitution.released().contains(locus))
            .collect();
        let mut work = ExactWork::nothing();
        wrote_all(&mut work, faces.logits.iter().flatten());
        stepped(&mut work, released.ticks as u64);
        let ticks = vec![released.ticks as u64; field.rings().len()];
        let mut receipt = port_receipt(
            &ticks,
            field.step(),
            work,
            ReceiptDetail::Refine {
                reached,
                released_power: released.power.clone(),
                peak_bits: released.peak_bits,
                path,
                charts: released.charts.clone(),
                remainders: released.remainders.clone(),
                last: released.last.clone(),
                resonators: released.resonators.clone(),
                // Under `A = 0` the word's motion carries from its last crossing (record B §2.4):
                // its balance is read to that crossing, whose change the carry holds.
                word: Box::new(match (&ended, &self.reception) {
                    (Some(carry), Reception::Carry(Absorption::Nothing)) => {
                        holonics::hnn::word::WordBalance::carried(
                            &released,
                            carry.host.change.clone(),
                        )
                    }
                    _ => holonics::hnn::word::WordBalance::of(&released),
                }),
            },
        )?;
        receipt.balances = released.balances;
        receipt.unresolved = faces.faces.iter().map(|face| face.fibres()).collect();
        let order = source_order(field, ratio.anchor(), ratio.moment().cells());
        let kept = KeptRead {
            commit: resident.constitution.commit(),
            word,
            faces: faces.clone(),
        };
        resident.wall.refine_read += read;
        resident.wall.release += start.elapsed();
        let id = PendingId(resident.fresh());
        resident.pending.insert(
            id,
            PendingSlot {
                ratio,
                emitted: faces.logits.clone(),
                moment: snapshot,
                kept: Some(kept),
                opening,
            },
        );
        // The word ran: its end is the motion the next refine opens on (the reference's).
        if ended.is_some() {
            resident.carried = ended;
        }
        Ok((
            id,
            InteractionReturn {
                forward: Component::Present(faces),
                pullback: Component::Absent(
                    "refine is forward only; its word is kept for the compare at its commit",
                ),
                deposit: Component::Absent("refine publishes only faces"),
                order: Component::Present(order),
                phases: Component::Present(vec![phases.clone()]),
                receipt,
            },
        ))
    }

    fn compare(
        &self,
        resident: &mut Mounted<'c>,
        pending: PendingId,
        target: &Encoded,
    ) -> Result<
        (
            StagedId,
            InteractionReturn<HolonRatio, Pullback, Deposit, Vec<ReceivingPhases>, PortReceipt>,
        ),
        HnnError,
    > {
        let field = resident.field.clone();
        let slot = resident
            .pending
            .get(&pending)
            .ok_or(HnnError::UnknownHandle {
                handle: Handle::Pending(pending),
            })?;
        field.admit(target)?;
        let targets: Vec<usize> = target.classes_read().collect();
        let aperture = slot.ratio.phases().aperture();
        if targets.len() != aperture {
            return Err(HnnError::Shape {
                what: "targets against the aperture",
                expected: aperture,
                found: targets.len(),
            });
        }
        // The slot leaves the resident while it is compared, and returns to it on any refusal
        // (the reference leaves a refused compare's pending ratio open; its kept read is taken
        // either way).
        let mut slot = resident
            .pending
            .remove(&pending)
            .expect("the slot was read");
        let kept = slot.kept.take();
        match self.compared(resident, &slot, kept, target, &field) {
            Ok((holon, pullback, deposit, receipt, order, phases, wall, code_length)) => {
                let PendingSlot {
                    ratio,
                    moment,
                    opening,
                    ..
                } = slot;
                resident.ledger.arrive(code_length, targets.len() as u64);
                resident.wall = add(resident.wall, wall);
                let id = StagedId(resident.fresh());
                resident.staged.insert(id, deposit.clone());
                resident.arrived = Some(Arrived {
                    ratio,
                    targets,
                    moment,
                    opening,
                });
                Ok((
                    id,
                    InteractionReturn {
                        forward: Component::Present(holon),
                        pullback: Component::Present(pullback),
                        deposit: Component::Present(deposit),
                        order: Component::Present(order),
                        phases: Component::Present(vec![phases]),
                        receipt,
                    },
                ))
            }
            Err(refusal) => {
                resident.pending.insert(pending, slot);
                Err(refusal)
            }
        }
    }

    fn deposit(
        &self,
        resident: &mut Mounted<'c>,
        staged: StagedId,
    ) -> Result<
        InteractionReturn<(), (), DepositReading, Vec<ReceivingPhases>, PortReceipt>,
        HnnError,
    > {
        if resident.stop.is_some() {
            return Err(HnnError::DepositsStopped {
                commit: resident.constitution.commit(),
            });
        }
        let slot = resident
            .staged
            .get(&staged)
            .ok_or(HnnError::UnknownHandle {
                handle: Handle::Staged(staged),
            })?;
        let field = resident.field.clone();
        if resident.arrived.is_none() {
            return Err(HnnError::Shape {
                what: "the arrived targets a staged deposit was compared on",
                expected: 1,
                found: 0,
            });
        }
        let start = Instant::now();
        // The budget reads the resident's retention, as the host's (record B §8).
        let retention = retained(&field, &resident.admitted, self.reception.opens());
        let (next, reading) = match resident.constitution.deposited_within(slot, &retention) {
            Ok(published) => published,
            Err(refusal @ HnnError::ConstitutionBudget { .. }) => {
                resident.staged.remove(&staged);
                if let HnnError::ConstitutionBudget {
                    bits,
                    budget,
                    commit,
                    loci,
                } = &refusal
                {
                    resident.stop = Some(BudgetStop {
                        bits: *bits,
                        budget: *budget,
                        commit: *commit,
                        loci: loci.clone(),
                    });
                }
                return Err(refusal);
            }
            Err(refusal) => return Err(refusal),
        };
        let deposited = start.elapsed();
        // The normal laws' prox steps on the card, read against the host's successor (campaign
        // 2), when the mirror runs (the GPU suite's parity tests; not the exposure's path): each
        // linear locus the deposit steps once, its first step at the locus (so nothing was staged
        // before it); a step the card's words cannot carry is declined, and every step is counted.
        let start = Instant::now();
        if let Some(mirror) = &self.normal_mirror {
            let mut tally = mirror.get();
            let mut once: BTreeMap<LinearLocus, usize> = BTreeMap::new();
            for step in slot.linear() {
                *once.entry(step.locus).or_default() += 1;
            }
            for step in slot.linear() {
                if once[&step.locus] != 1 {
                    tally.repeated += 1;
                    continue;
                }
                let locus = step.locus.locus();
                let moved = reading.charts.iter().any(|(at, chart)| {
                    *at == locus
                        && chart
                            .prior
                            .as_ref()
                            .is_some_and(|read| read.to != read.from)
                });
                if moved {
                    tally.moved += 1;
                    continue;
                }
                let (Some(before), Some(after)) = (
                    normal_law(&resident.constitution, step.locus),
                    normal_law(&next, step.locus),
                ) else {
                    tally.lawless += 1;
                    continue;
                };
                let released: Vec<(Carrier, usize, Rat)> = reading
                    .released
                    .iter()
                    .filter(|(at, ..)| *at == locus)
                    .map(|(_, carrier, entry, residual)| (*carrier, *entry, residual.clone()))
                    .collect();
                // The normal law's certified step at the locus (zero where its alignment certified
                // none; the locus's factor families step beside it).
                let certified = reading.linear_step(locus);
                // The receiving map steps in its class metric (the host's
                // `receiving_metric_samples`): the mirror reads the same samples.
                let metric = match step.locus {
                    holonics::hnn::constitution::LinearLocus::Receiving(_) => {
                        holonics::hnn::constitution::receiving_metric_samples(&step.samples)
                    }
                    _ => None,
                };
                tally.count(normal_deposit_on_card(
                    self.card,
                    before,
                    after,
                    metric.as_deref().unwrap_or(&step.samples[..]),
                    &certified,
                    resident.constitution.lattice(locus)?,
                    gamma_length(resident.constitution.clock(locus) + 1),
                    &released,
                )?);
            }
            mirror.set(tally);
        }
        let normal_deposit = start.elapsed();
        let tree_steps: Vec<(Vec<Letter>, usize)> =
            resident.tree.as_ref().map_or_else(Vec::new, |(ring, _)| {
                slot.landmarks()
                    .iter()
                    .filter(|step: &&LandmarkStep| step.ring == *ring)
                    .map(|step| (step.address.clone(), step.class))
                    .collect()
            });
        // The tree and warm charts are physical mirrors. Keep only this call's predecessor until
        // every successor read succeeds; a late carrier refusal must not advance either mirror.
        let chart_before = resident.store.before_trial();
        let trial = (|| {
            // The card's mirror of the tree moved by the deposit's steps, as the host's moved.
            let start = Instant::now();
            if let Some((ring, tree)) = resident.tree.as_mut() {
                let steps = &tree_steps;
                tree.deposit(steps).map_err(device)?;
                // The lockstep: the counts, and the masses, β, stop weights, depth words and label
                // ends of every stored node the deposit's walks opened (read on the predecessor: a
                // later cell's walk only refines an earlier one's chains) and of every node it founded,
                // the joins it stepped, and the labels it held, against the host's successor tree.
                let before =
                    resident
                        .constitution
                        .landmarks(*ring)
                        .ok_or(HnnError::Realization {
                            what: "the host's landmark tree at the predecessor",
                        })?;
                let host = next.landmarks(*ring).ok_or(HnnError::Realization {
                    what: "the host's landmark tree at the successor",
                })?;
                let (mut nodes, mut dyadic) = (Vec::new(), Vec::new());
                for (address, class) in steps {
                    let (touched, cells) = before.touched(address, *class)?;
                    nodes.extend(touched);
                    dyadic.extend(cells);
                }
                let founded = u32::try_from(before.nodes()).unwrap_or(u32::MAX)
                    ..u32::try_from(host.nodes()).unwrap_or(u32::MAX);
                nodes.extend(founded);
                nodes.sort_unstable();
                nodes.dedup();
                dyadic.sort_unstable();
                dyadic.dedup();
                if host.nodes() != tree.nodes()
                    || !tree
                        .agrees_at(host, &nodes, &dyadic, before.held())
                        .map_err(device)?
                {
                    return Err(HnnError::Realization {
                        what: "the card's landmark tree against the host's after a deposit (its counts, a written or founded node's masses, β, stop weight, depth word or label end, a join, or a held label)",
                    });
                }
            }
            let tree_deposit = start.elapsed();
            let start = Instant::now();
            // The successor's loci on the card (the moved words), then the arrived re-read on them.
            let successor = Rc::new(Publication::publish(
                self.card,
                Loci::of(&field, &next)?,
                Some(&resident.publication),
            )?);
            let octets = successor.octets as u64;
            resident.count(|traffic| traffic.publications += octets);
            let (reread, readings) =
                resident.arrived_code_length(&successor, Some(&next), self.card)?;
            let reread_time = start.elapsed();
            // Every fallible step stays inside the trial, as the host's does
            // (`holonics::hnn::reference`): the receipt, then the first law's ledger step on a
            // copy (`EnclosedLedger::deposit` refuses before it moves); the tally is read only after
            // the trial succeeds.
            let mut work = ExactWork::nothing();
            stepped(&mut work, 1);
            holonics::hnn::port::resident(&mut work, reading.bits);
            let receipt = port_receipt(
                &zero_ticks(&field),
                &Rat::one(),
                work,
                ReceiptDetail::Deposit {
                    reading: reading.clone(),
                    reread: reread.clone(),
                },
            )?;
            let mut ledger = resident.ledger.clone();
            ledger.deposit(reread)?;
            Ok::<_, HnnError>((
                successor,
                readings,
                receipt,
                ledger,
                tree_deposit,
                reread_time,
            ))
        })();
        let (successor, readings, receipt, ledger, tree_deposit, reread_time) = match trial {
            Ok(success) => success,
            Err(refusal) => {
                let tree_restore = if let Some((ring, tree)) = resident.tree.as_mut() {
                    match resident.constitution.landmarks(*ring) {
                        Some(before) => tree.upload(&before.arena()).map_err(device),
                        None => Err(HnnError::MissingReceivingMap { ring: *ring }),
                    }
                } else {
                    Ok(())
                };
                let charts_restore = resident.store.restore(chart_before);
                let octets = resident.store.octets as u64;
                resident.count(|traffic| traffic.words += octets);
                resident.store.octets = 0;
                resident.publish_tree_times();
                charts_restore?;
                tree_restore?;
                return Err(refusal);
            }
        };
        resident.tally.read(&readings);
        resident.ledger = ledger;
        resident.staged.remove(&staged);
        resident.constitution = next;
        resident.publication = successor;
        resident.forget_kept_reads();
        resident.wall.deposited += deposited;
        resident.wall.normal_deposit += normal_deposit;
        resident.wall.tree_deposit += tree_deposit;
        resident.wall.reread += reread_time;
        resident.publish_tree_times();
        Ok(InteractionReturn {
            forward: Component::Present(()),
            pullback: Component::Absent("a deposit consumes covectors"),
            deposit: Component::Present(reading),
            order: Component::Absent("a deposit leaves the source order unchanged"),
            phases: Component::Absent("nothing is read by a deposit"),
            receipt,
        })
    }

    fn release(
        &self,
        resident: &mut Mounted<'c>,
        pending: &PendingId,
        decision: &DecisionRule,
    ) -> Result<InteractionReturn<Faces, (), (), Vec<ReceivingPhases>, PortReceipt>, HnnError> {
        let slot = resident
            .pending
            .remove(pending)
            .ok_or(HnnError::UnknownHandle {
                handle: Handle::Pending(*pending),
            })?;
        let publication = Rc::clone(&resident.publication);
        let read = resident.execute(
            &slot.ratio,
            &slot.moment,
            &publication,
            self.card,
            &slot.opening,
        );
        let ratio = slot.ratio.clone();
        resident.pending.insert(*pending, slot);
        let (word, wave) = read?;
        resident.tally.read(&word.readings);
        // No cell of the window is released yet: every phase reads the tree at the window's
        // opening address (`ActiveAddress::phase`), as the reference's release does.
        let faces = tree_against(
            resident.tree.as_mut(),
            &resident.constitution,
            &ratio,
            &wave,
            &[],
        )?
        .0
        .faces;
        let field = &resident.field;
        let phases = ratio.phases().clone();
        let anchors = readout::anchors(&word.word.plan, &word.word.record);
        let width = release_width(&phases, &faces)?;
        let tolerance = Rat::new(BigInt::one(), BigInt::from(phases.grain()));
        let options = LawfulOptions::assemble(&width, tolerance.clone(), None, false)?;
        let decided = release(decision, &options)?;
        let released = matches!(decided, ReleaseReturn::Released { .. });
        let split = if resident
            .constitution
            .ring_resonator(phases.ring())
            .is_some()
        {
            [
                Component::Absent("the loaded resonator has no campaign-3 RIDE/FOUND read"),
                Component::Absent("the loaded resonator has no campaign-3 RIDE/FOUND read"),
            ]
        } else {
            match anchors.last() {
                Some(anchor) => resonance_reading(field.ring(phases.ring()), anchor)?,
                None => [
                    Component::Absent("the window read no anchor"),
                    Component::Absent("the window read no anchor"),
                ],
            }
        };
        let order = source_order(field, ratio.anchor(), ratio.moment().cells());
        let ticks = vec![phases.junction_steps() as u64; field.rings().len()];
        let mut receipt = port_receipt(
            &ticks,
            field.step(),
            ExactWork::nothing(),
            ReceiptDetail::Release {
                width,
                tolerance,
                decision: decided,
                split,
            },
        )?;
        receipt.unresolved = faces.faces.iter().map(|face| face.fibres()).collect();
        Ok(InteractionReturn {
            forward: if released {
                Component::Present(faces)
            } else {
                Component::Absent("the declared rule did not release at this receiver")
            },
            pullback: Component::Absent("release is forward only"),
            deposit: Component::Absent("FOUND is campaign 3's; the RIDE/FOUND split is a reading"),
            order: Component::Present(order),
            phases: Component::Present(vec![phases]),
            receipt,
        })
    }

    fn close_aeon(
        &self,
        resident: &mut Mounted<'c>,
        admitted: &[ReceivingPhases],
    ) -> Result<
        InteractionReturn<
            AeonBoundary,
            Vec<(PendingId, Transpose)>,
            (),
            Vec<ReceivingPhases>,
            PortReceipt,
        >,
        HnnError,
    > {
        if !resident.aeon.awaiting {
            return Err(HnnError::NotAtCarryOut);
        }
        contained(admitted, &resident.admitted)?;
        let before = resident.bits();
        let field = resident.field.clone();
        // As the reference's: the collapse, the carried motion's release with its material, the
        // handles' separators and the first law's re-read are formed before the resident's state
        // moves, so a refusal leaves the aeon awaiting its boundary as it stood.
        let mut constitution = resident.constitution.clone();
        let collapsed = collapse(&field, &mut constitution, admitted, self.reception.opens())?;
        // The descended constitution published on the card at the same commit.
        let descended = Rc::new(Publication::publish(
            self.card,
            Loci::of(&field, &constitution)?,
            Some(&resident.publication),
        )?);
        // The carried motion the released material held leaves with it (the reference's
        // `ReceptionCarry::released`, record B §8).
        let release =
            |opening: &CardOpening<'c>| opening.released(self.card, &field, &collapsed.released);
        let carry = match &resident.carried {
            Some(carry) => match release(&CardOpening::Received {
                carry: Rc::clone(carry),
                absorption: holonics::hnn::Absorption::Nothing,
            })? {
                CardOpening::Received { carry, .. } => Some(carry),
                CardOpening::Rest => None,
            },
            None => None,
        };
        let mut carried = Vec::new();
        let mut refused = Vec::new();
        let mut transposes = Vec::new();
        for (id, slot) in &resident.pending {
            let diamond = Diamond::opened(
                &field,
                slot.ratio.phases(),
                &slot.opening.host().support(&field),
            );
            let separating = separator(&field, &diamond, &collapsed.retained);
            if separating.is_empty() {
                let reads: Vec<Locus> = diamond
                    .retained(&field)
                    .into_iter()
                    .filter(|locus| collapsed.retained.contains(locus))
                    .collect();
                transposes.push((*id, Transpose::Retained(reads)));
                carried.push(*id);
            } else {
                transposes.push((*id, Transpose::Separator(separating.clone())));
                refused.push((*id, separating));
            }
        }
        let refused_staged: Vec<(StagedId, Vec<Locus>)> = resident
            .staged
            .iter()
            .filter_map(|(id, deposit)| {
                let separating: Vec<Locus> = deposit
                    .loci()
                    .into_iter()
                    .filter(|locus| !collapsed.retained.contains(locus))
                    .collect();
                (!separating.is_empty()).then_some((*id, separating))
            })
            .collect();
        let openings: Vec<(PendingId, CardOpening<'c>)> = resident
            .pending
            .iter()
            .filter(|(id, _)| carried.contains(id))
            .map(|(id, slot)| Ok((*id, release(&slot.opening)?)))
            .collect::<Result<_, HnnError>>()?;
        let (mut ledger, mut tally) = (resident.ledger.clone(), resident.tally.clone());
        let arrived_opening = resident
            .arrived
            .as_ref()
            .map(|arrived| release(&arrived.opening))
            .transpose()?;
        if let Some(arrived) = &resident.arrived {
            // As the reference's: seeded on the opening the ledger's reading was read on, before
            // its release.
            let reads = Diamond::opened(
                &field,
                arrived.ratio.phases(),
                &arrived.opening.host().support(&field),
            )
            .retained(&field);
            if collapsed.released.iter().any(|locus| reads.contains(locus)) {
                // The re-read opens on the released opening; the arrived targets are restored
                // as they stood should it be refused.
                let held = resident.arrived.as_mut().map(|arrived| {
                    std::mem::replace(
                        &mut arrived.opening,
                        arrived_opening.clone().expect("formed above"),
                    )
                });
                let read = resident.arrived_code_length(&descended, Some(&constitution), self.card);
                let (reread, readings) = match read {
                    Ok(read) => read,
                    Err(refusal) => {
                        if let (Some(arrived), Some(held)) = (resident.arrived.as_mut(), held) {
                            arrived.opening = held;
                        }
                        return Err(refusal);
                    }
                };
                tally.read(&readings);
                ledger.release(reread)?;
            }
        }
        let first_law = ledger.close();
        // The literal `log₂|A|` a cell, read as the host reads it (the certified binary logarithm of
        // `1/|A|`), so the boundary's parity holds at any `|A|`, a power of two or not.
        let literal = first_law.against_literal(&code_length(&Rat::new(
            BigInt::one(),
            BigInt::from(field.alphabet()),
        ))?);
        let opening = resident.aeon.opening.clone();
        let carry_out = resident.current.lift().to_vec();
        let (readings, epochs, closing) =
            aeon_readings(&resident.parametric, &opening, &carry_out)?;
        // Published together.
        resident.constitution = constitution;
        // The collapse keeps the tree whole (`hnn::retention`); the mirror is uploaded again should
        // it ever move.
        if let Some((ring, tree)) = resident.tree.as_mut()
            && resident.constitution.landmarks(*ring).map(Landmarks::nodes) != Some(tree.nodes())
            && let Some(host) = resident.constitution.landmarks(*ring)
        {
            tree.upload(&host.arena()).map_err(device)?;
        }
        let octets = descended.octets as u64;
        resident.count(|traffic| traffic.publications += octets);
        resident.publication = Rc::clone(&descended);
        resident.carried = carry;
        resident.forget_kept_reads();
        for (id, _) in &refused {
            resident.pending.remove(id);
        }
        for (id, opening) in openings {
            if let Some(slot) = resident.pending.get_mut(&id) {
                slot.opening = opening;
            }
        }
        for (id, _) in &refused_staged {
            resident.staged.remove(id);
        }
        resident.released_bits += collapsed.bits[0].saturating_sub(collapsed.bits[1]);
        resident.ledger = ledger;
        resident.tally = tally;
        if let (Some(arrived), Some(opening)) = (resident.arrived.as_mut(), arrived_opening) {
            arrived.opening = opening;
        }
        let cells = resident.aeon.cells;
        resident.aeon = AeonState {
            awaiting: false,
            keys_admitted: true,
            opening: carry_out.clone(),
            cells: 0,
            closed: cells,
        };
        resident.admitted = admitted.to_vec();
        let after = resident.bits();
        let boundary = AeonBoundary {
            admitted: admitted.to_vec(),
            collapse: collapsed,
            value_kernel: Component::Absent(
                "the value kernel of a frozen aeon is campaign 3's; campaign 1 aeons all learn",
            ),
            opening,
            carry_out,
            readings: readings.clone(),
            epochs,
            closing,
            cells,
            first_law,
            literal,
            view: Component::Absent(
                "the field's Holarchy glues its rings and contacts at their ports, with no glued cell \
                 complex, so no receiver has regions to view or count; owed with the cellular gluing",
            ),
            carried,
            refused,
            refused_staged,
            state_bits: [before, after],
        };
        Ok(InteractionReturn {
            forward: Component::Present(boundary),
            pullback: Component::Present(transposes),
            deposit: Component::Absent("the released loci are the boundary's collapse"),
            order: Component::Present(SourceOrder {
                rings: readings,
                cells,
            }),
            phases: Component::Present(admitted.to_vec()),
            receipt: port_receipt(
                &zero_ticks(&field),
                &Rat::one(),
                ExactWork::nothing(),
                ReceiptDetail::Boundary,
            )?,
        })
    }

    fn discard(
        &self,
        resident: &mut Mounted<'c>,
        handle: Handle,
    ) -> Result<InteractionReturn<(), (), (), Vec<ReceivingPhases>, PortReceipt>, HnnError> {
        let bits = match handle {
            Handle::Moment(id) => resident.moments.remove(&id).map(|m| m.host.dense_bits()),
            // The discarded refinement's word ran, and its refine already carried its end.
            Handle::Pending(id) => resident.pending.remove(&id).map(|slot| slot.bits()),
            Handle::Staged(id) => resident.staged.remove(&id).map(|d| d.bits()),
        }
        .ok_or(HnnError::UnknownHandle { handle })?;
        Ok(InteractionReturn {
            forward: Component::Present(()),
            pullback: Component::Absent("a discard returns nothing"),
            deposit: Component::Absent("a discard deposits nothing"),
            order: Component::Absent("a discard leaves the source order unchanged"),
            phases: Component::Absent("nothing is read by a discard"),
            receipt: port_receipt(
                &zero_ticks(&resident.field),
                &Rat::one(),
                ExactWork::nothing(),
                ReceiptDetail::Discard { bits },
            )?,
        })
    }
}

/// A linear locus's normal law in a constitution.
fn normal_law(
    constitution: &Constitution,
    locus: LinearLocus,
) -> Option<&holonics::hnn::NormalLaw> {
    match locus {
        LinearLocus::SourcePort(g) => constitution.source_law(g),
        LinearLocus::Contrast(g) => Some(constitution.contrast_law(g)),
        LinearLocus::Receiving(g) => constitution.receiving_law(g),
    }
}

/// Two wall readings joined (`WallTimes`'s own sum).
fn add(mut total: WallTimes, more: WallTimes) -> WallTimes {
    total += more;
    total
}
