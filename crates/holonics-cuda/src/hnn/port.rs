//! **The execution port resident on the card** (`holonics::hnn::ExecutionPort` for a device;
//! design (c), "Realization on the card"; Decisions 24 and 25; #76).
//!
//! [definition] [`Resident`] implements the port with its resident ([`Mounted`]) on a [`Card`]. It
//! returns, method by method, the **same** `InteractionReturn`s as the host reference
//! (`holonics::hnn::Reference`), the parity target: every word runs on the card, and the host keeps
//! what the port plan assigns it, read exactly from the card's integer records.
//!
//! | On the card | On the host |
//! |---|---|
//! | the moment and its ingest (`hnn_moment_ingest`, [`ResidentMoment`]); a pending ratio's counts frozen at its cut ([`MomentSnapshot`]) | the lift point `λ`, the receiving parametron's active suffix address (`hnn::receiving::ActiveAddress`, shifted at every ingested cell) and the host's mirror of the moment (the pending ratio's operand, which the deposit's samples and the state's bits read), checked equal at every ingest |
//! | the published constitution's loci at their lattices, the moved words scattered at each publication (`hnn::publication`) | the constitution `Θ`, the normal laws' prox steps, the receiving parametron's landmark tree and its deposit (Decision 28), the budgeted carry and its remainders, the budget (`Constitution::deposited`), and the operators `I − ½K`, `m_a` formed from it |
//! | the keyed charts, their rounded Newton–Schulz steps and exact certificates (`hnn::store`) | each refinement's decisions from the certificates (warm, cold, fallback, target), the cold start's transpose and the exact fallback |
//! | the word's open (`E_g M_g[c]`, the pair port), its ticks, its receiving read (`hnn_pair_weights`, `hnn_word_forward`) | the landmark tree's face read at each phase's causal address at compare and its grain exponents added to the card's logits (Decision 28: the tree stays with the host's constitution, as Decision 27's masses did; the host's tree read per window is timed as `WallTimes::tree_read` beside the card's word), the faces in `ℚ(θ)`, each tick's balance, the release (`hnn::readout`) |
//! | the word's return (`hnn_word_reverse`) | the Holon ratio and its covector, the return's source through `Rᵀ` (the covector lives on `(1/W)ℤ`), the composition onto the loci (`reference::compose`) |
//! | | keys, the collapse, the first law's ledger, the handles, every refusal's reason |
//!
//! [open] **The tree read stays on the host, a #76 debt** (Decision 28; the primary's ruling): the
//! landmark tree's 256-class face at each phase's causal address took 1,720 µs a window on the host
//! (`WallTimes::tree_read`, 5,288,453 µs over the standing cut's 3,074 windows) against the card's
//! word at 2,110 µs a window (the refine read, 6,488,213 µs), not small against it; its card port is
//! owed in #76. The host phases around it (the Holon ratio with the tree-alone and mixture readings,
//! the deposit, the re-read) dominate the wall.
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
use holonics::hnn::constitution::{CAMPAIGN_ONE_BUDGET, DepositReading};
use holonics::hnn::keys::{self, KeyLocation};
use holonics::hnn::landmark::code_length;
use holonics::hnn::moment::Ingested;
use holonics::hnn::port::{
    Census, Deposit, ExecutionPort, Handle, MomentId, PendingId, PortReceipt, Pullback,
    ReceiptDetail, StagedId, Transpose, port_receipt, release_width, resonance_reading,
    source_order, stepped, wrote_all,
};
use holonics::hnn::propagation::path_attenuation;
use holonics::hnn::ratio::{HolonRatio, PhaseRatio, target_phases};
use holonics::hnn::receiving::tree_code_length;
use holonics::hnn::reference::{
    BudgetStop, ChartTally, Cut, Declared, ExposedResident, Exposure, WallTimes, compose, expose,
    window_code_length,
};
use holonics::hnn::retention::{Diamond, aeon_readings, collapse, contained, separator};
use holonics::hnn::{
    ActiveAddress, AeonBoundary, ChartKey, ChartReading, Constitution, ConstitutionRead, Current,
    Faces, Field, HnnError, Locus, PendingRatio, ReceivingPhases, SourceMoment, Steps,
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
use crate::hnn::execute::{ResidentWord, SourceOpen, WordPlan};
use crate::hnn::moment::{MomentSnapshot, ResidentMoment};
use crate::hnn::publication::{ContactOperator, Loci, Publication};
use crate::hnn::readout::{self, Executed};
use crate::hnn::store::{ChartStore, Pair};

fn device(error: DeviceError) -> HnnError {
    error.into_hnn()
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
    }
}

/// The first law's arrived operand (the reference's `Arrived`), with its counts on the card.
struct Arrived<'c> {
    ratio: PendingRatio,
    targets: Vec<usize>,
    moment: MomentSnapshot<'c>,
}

impl Arrived<'_> {
    fn bits(&self) -> u64 {
        self.ratio.bits()
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
        lift + moments
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
    ) -> Result<(ExecutedWord<'c>, Faces), HnnError> {
        let field = &self.field;
        let current = ratio.current(field)?;
        // The indexed normalized open (ruling B), read from the pending ratio's copy of the moment.
        let opens = SourceOpen::of(field, ratio.moment())?;
        let plan = WordPlan::form(field, &current, publication, ratio.phases(), moment, &opens)?;
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
        let read = self.execute(&arrived.ratio, &arrived.moment, publication, card);
        let constitution = successor.unwrap_or(&self.constitution);
        let result = read.and_then(|(word, wave)| {
            let against = arrived
                .ratio
                .against(constitution, &wave, &arrived.targets)?;
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
}

// -------------------------------------------------------------------------------------------
// the port

/// [definition] **The device's execution port**: a card, with the declared pending capacity,
/// steps and constitution budget, and an exposure's deadline if one is set (the reference's
/// declarations, so the two describe the same field).
pub struct Resident<'c> {
    card: &'c Card,
    pending_capacity: usize,
    steps: Steps,
    budget: u64,
    deadline: Option<u64>,
    traffic: Rc<Cell<Traffic>>,
    layouts: Rc<Cell<Option<(Layout, Layout)>>>,
}

/// One-hot exterior cells as their codes (the reference's reading of a cell).
fn codes(cells: &[Vec<(usize, Rat)>], alphabet: usize) -> Result<Vec<usize>, HnnError> {
    cells
        .iter()
        .enumerate()
        .map(|(position, cell)| match cell.as_slice() {
            [(code, value)] if value.is_one() => {
                if *code >= alphabet {
                    Err(HnnError::CellOutside {
                        code: *code,
                        alphabet,
                    })
                } else {
                    Ok(*code)
                }
            }
            _ => Err(HnnError::CellNotOneHot { position }),
        })
        .collect()
}

impl<'c> Resident<'c> {
    /// Campaign 1's declarations on a card: `γ_U = 1`, `η_x = 1/2`, `B_Θ = 2^33`, a pending
    /// capacity of 64 (the reference's).
    pub fn campaign_one(card: &'c Card) -> Self {
        Self::new(card, 64, Steps::campaign_one(), CAMPAIGN_ONE_BUDGET)
    }

    pub fn new(card: &'c Card, pending_capacity: usize, steps: Steps, budget: u64) -> Self {
        Self {
            card,
            pending_capacity,
            steps,
            budget,
            deadline: None,
            traffic: Rc::new(Cell::new(Traffic::default())),
            layouts: Rc::new(Cell::new(None)),
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
                steps: &self.steps,
                budget: self.budget,
                pending_capacity: self.pending_capacity,
                deadline: self.deadline,
            },
            field,
            cut,
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
        let parametric = field.holon(&constitution)?.parametric();
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
        let octets = publication.octets as u64;
        let traffic = Rc::clone(&self.traffic);
        traffic.set(Traffic {
            publications: traffic.get().publications + octets,
            ..traffic.get()
        });
        Ok(Mounted {
            field: field.clone(),
            current: current.clone(),
            address: ActiveAddress::of_field(field),
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
        })
    }
}

fn zero_ticks(field: &Field) -> Vec<u64> {
    vec![0u64; field.rings().len()]
}

/// A compare's readings: the ratio, the pullback, the deposit, the receipt, the source order, the
/// phases, the wall time and the window's code length.
type Compared = (
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
        targets: &[usize],
        field: &Field,
    ) -> Result<Compared, HnnError> {
        let commit = resident.constitution.commit();
        let ratio = &slot.ratio;
        let phases = ratio.phases().clone();
        let mut wall = WallTimes::default();
        let (mut word, faces) = match kept.filter(|kept| kept.commit == commit) {
            Some(KeptRead { word, faces, .. }) => (word, faces),
            None => {
                let start = Instant::now();
                let publication = Rc::clone(&resident.publication);
                let read = resident.execute(ratio, &slot.moment, &publication, self.card)?;
                resident.tally.read(&read.0.readings);
                wall.compare_read = start.elapsed();
                read
            }
        };
        // The tree part of the combined face at each phase's causal address (Decision 28), read
        // on the host from the published constitution's tree.
        let start = Instant::now();
        let against = ratio.against(&resident.constitution, &faces, targets)?;
        wall.tree_read = start.elapsed();
        let start = Instant::now();
        let residual: Vec<Vec<Rat>> = faces
            .logits
            .iter()
            .zip(&slot.emitted)
            .map(|(now, then)| now.iter().zip(then).map(|(a, b)| a - b).collect())
            .collect();
        let tree_grain = against
            .trees
            .iter()
            .zip(targets)
            .map(|(face, &target)| tree_code_length(face, target))
            .collect::<Result<Vec<_>, _>>()?;
        // The receiver's scored face: the mixture of the tree's and the combined face (ruling A),
        // its ratio stepped phase by phase, scored on the host as the reference scores it; beside
        // it the tree's executed face alone.
        let scored = ratio.scored(&resident.constitution, &against, targets)?;
        let anchors = target_phases(field, ratio.anchor(), phases.ring(), targets)?;
        let holon = HolonRatio::compare(against.faces, targets, &anchors)?;
        let covector = holon.covector()?;
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
        let constitution = Constitution::initial(field, self.steps.clone(), self.budget)?;
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
        cells: &[Vec<(usize, Rat)>],
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
        let codes = codes(cells, field.alphabet())?;
        let id = match moment {
            Some(id) if resident.moments.contains_key(id) => *id,
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
        let start = Instant::now();
        if !codes.is_empty() {
            let octets = (4 * codes.len() + 8 * (2 + field.rings().len())) as u64;
            resident.count(|traffic| traffic.ingest += octets);
        }
        let open = resident
            .moments
            .get_mut(&id)
            .expect("the moment was checked or opened");
        // The card's ingest, resident, and the host's mirror, checked equal.
        let carded = if codes.is_empty() {
            Ingested {
                cells: 0,
                carry_out: false,
            }
        } else {
            open.card.ingest(&codes).map_err(device)?
        };
        let ingested = open.host.ingest(&field, &mut resident.current, &codes)?;
        if carded != ingested || open.card.lift() != resident.current.lift() {
            return Err(HnnError::Realization {
                what: "the card's ingest against the host's moment",
            });
        }
        // The receiving parametron's active suffix address receives the cells the moment took.
        for &code in &codes[..ingested.cells] {
            resident.address.receive(code);
        }
        // Every other open moment steps from the one lift point: its card's phases follow it.
        if ingested.cells > 0 && resident.moments.len() > 1 {
            for (other, moment) in resident.moments.iter_mut() {
                if *other != id {
                    moment
                        .card
                        .rekey(&field, &resident.current)
                        .map_err(device)?;
                }
            }
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
        let capacity = field.capacity();
        let detail = ReceiptDetail::Ingest {
            cells: ingested.cells as u64,
            moment_bits: open.host.dense_bits(),
            state_bits: capacity.state_bits(n),
            source_bits: n * ceil_log2(&BigUint::from(field.alphabet())),
            n_star: capacity.n_star(),
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
        crib: &[Vec<(usize, Rat)>],
        offset: usize,
    ) -> Result<
        InteractionReturn<KeyLocation, (), Vec<Option<Clock>>, Vec<ReceivingPhases>, PortReceipt>,
        HnnError,
    > {
        if !resident.aeon.keys_admitted {
            return Err(HnnError::KeysNotAdmitted);
        }
        let field = resident.field.clone();
        let codes = codes(crib, field.alphabet())?;
        if codes.len() as u64 > resident.aeon.closed {
            return Err(HnnError::Shape {
                what: "a closing crib's cells against the closed aeon's",
                expected: usize::try_from(resident.aeon.closed).unwrap_or(usize::MAX),
                found: codes.len(),
            });
        }
        let location = keys::locate_closing(&field, &resident.current, &codes, offset)?;
        let jumps = location.rekey(&field, &mut resident.current)?;
        // Re-keying moves only the lift's phase classes: every resident moment steps from them.
        for moment in resident.moments.values_mut() {
            moment
                .card
                .rekey(&field, &resident.current)
                .map_err(device)?;
        }
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
        let order = source_order(&field, resident.current.lift(), codes.len() as u64);
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
        let (word, faces) = resident.execute(&ratio, &snapshot, &publication, self.card)?;
        let read = start.elapsed();
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
        );
        resident.tally.read(&released.charts);
        let path = path_attenuation(
            field,
            ratio.anchor(),
            phases.ring(),
            phases.last_epoch(),
            phases.grain(),
        )?;
        let reached: Vec<Locus> = Diamond::of(field, phases)
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
            },
        );
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
        target: &[Vec<(usize, Rat)>],
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
        let targets = codes(target, field.alphabet())?;
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
        match self.compared(resident, &slot, kept, &targets, &field) {
            Ok((holon, pullback, deposit, receipt, order, phases, wall, code_length)) => {
                let PendingSlot { ratio, moment, .. } = slot;
                resident.ledger.arrive(code_length, targets.len() as u64);
                resident.wall = add(resident.wall, wall);
                let id = StagedId(resident.fresh());
                resident.staged.insert(id, deposit.clone());
                resident.arrived = Some(Arrived {
                    ratio,
                    targets,
                    moment,
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
        let (next, reading) = match resident.constitution.deposited(slot) {
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
        resident.tally.read(&readings);
        let reread_time = start.elapsed();
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
        resident.ledger.deposit(reread)?;
        resident.staged.remove(&staged);
        resident.constitution = next;
        resident.publication = successor;
        resident.forget_kept_reads();
        resident.wall.deposited += deposited;
        resident.wall.reread += reread_time;
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
        let read = resident.execute(&slot.ratio, &slot.moment, &publication, self.card);
        let ratio = slot.ratio.clone();
        resident.pending.insert(*pending, slot);
        let (word, wave) = read?;
        resident.tally.read(&word.readings);
        // No cell of the window is released yet: every phase reads the tree at the window's
        // opening address (`ActiveAddress::phase`), as the reference's release does.
        let faces = ratio.against(&resident.constitution, &wave, &[])?.faces;
        let field = &resident.field;
        let phases = ratio.phases().clone();
        let anchors = readout::anchors(&word.word.plan, &word.word.record);
        let width = release_width(&phases, &faces)?;
        let tolerance = Rat::new(BigInt::one(), BigInt::from(phases.grain()));
        let options = LawfulOptions::assemble(&width, tolerance.clone(), None, None, false)?;
        let decided = release(decision, &options)?;
        let released = matches!(decided, ReleaseReturn::Released { .. });
        let split = match anchors.last() {
            Some(anchor) => resonance_reading(field.ring(phases.ring()), anchor)?,
            None => [
                Component::Absent("the window read no anchor"),
                Component::Absent("the window read no anchor"),
            ],
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
        resident.forget_kept_reads();
        let collapsed = collapse(&field, &mut resident.constitution, admitted)?;
        // The descended constitution published on the card at the same commit.
        let descended = Rc::new(Publication::publish(
            self.card,
            Loci::of(&field, &resident.constitution)?,
            Some(&resident.publication),
        )?);
        let octets = descended.octets as u64;
        resident.count(|traffic| traffic.publications += octets);
        resident.publication = Rc::clone(&descended);
        let mut carried = Vec::new();
        let mut refused = Vec::new();
        let mut transposes = Vec::new();
        let ids: Vec<PendingId> = resident.pending.keys().copied().collect();
        for id in ids {
            let phases = resident.pending[&id].ratio.phases();
            let separating = separator(&field, phases, &collapsed.retained);
            if separating.is_empty() {
                let reads: Vec<Locus> = Diamond::of(&field, phases)
                    .retained(&field)
                    .into_iter()
                    .filter(|locus| collapsed.retained.contains(locus))
                    .collect();
                transposes.push((id, Transpose::Retained(reads)));
                carried.push(id);
            } else {
                resident.pending.remove(&id);
                transposes.push((id, Transpose::Separator(separating.clone())));
                refused.push((id, separating));
            }
        }
        let mut refused_staged = Vec::new();
        resident.staged.retain(|id, deposit| {
            let separating: Vec<Locus> = deposit
                .loci()
                .into_iter()
                .filter(|locus| !collapsed.retained.contains(locus))
                .collect();
            if separating.is_empty() {
                true
            } else {
                refused_staged.push((*id, separating));
                false
            }
        });
        resident.released_bits += collapsed.bits[0].saturating_sub(collapsed.bits[1]);
        if let Some(arrived) = &resident.arrived {
            let reads = Diamond::of(&field, arrived.ratio.phases()).retained(&field);
            if collapsed.released.iter().any(|locus| reads.contains(locus)) {
                let (reread, readings) =
                    resident.arrived_code_length(&descended, None, self.card)?;
                resident.tally.read(&readings);
                resident.ledger.release(reread)?;
            }
        }
        let first_law = resident.ledger.close();
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
            Handle::Pending(id) => resident.pending.remove(&id).map(|s| s.bits()),
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

/// Two wall readings joined (`WallTimes`'s own sum).
fn add(mut total: WallTimes, more: WallTimes) -> WallTimes {
    total += more;
    total
}
