//! **The published constitution on the card**: every locus a word reads, at its declared lattice.
//!
//! [definition] A word reads the constitution `Θ` only through `holonics::hnn::ConstitutionRead`
//! (the forward face). The device port forms, once per publication (a deposit's successor, a
//! collapse's descent), the dyadic words of every locus the word's kernels read
//! ([`Loci::of`]), each at its locus's **declared lattice** (Decision 22; `Field::lattice`), so the
//! words' scales stay fixed across publications:
//!
//! | Locus | Words | Scale |
//! |---|---|---|
//! | ring `g`'s contrast port `W_c,g` | `2d_g × 2d_g` | `L_Element(g)` |
//! | contact `a`'s storage `C_a = c cᵀ`, stiffness `K_a = b bᵀ` | `k_a × k_a` each | `2 L_Channel(a)` |
//! | source ring `g`'s port `E_g` | `2d_g × |A|` | `L_SourcePort(g)` |
//! | its pair port `(e_ρ, a_ρ, b_ρ)` per offset | `m × 2d_g`, `m × |A|`, `m × |A|` | `L_SourcePort(g)` |
//! | receiving ring `R`'s map | `2|A| × 2d_R` | `L_ReceivingMap(R)` |
//!
//! The host keeps what only the host reads (the element `K_g`, `W_s,g`, the dissipation `D_a`, the
//! exact operators `I − ½K_g` and `m_a` from which the chart store's operator words are read, and
//! the receiving parametron's region class masses, Decision 27, whose count face the host reads at
//! the grain and adds to the card's logits) and a copy of the published words. [definition] **Only
//! the moved words cross the bus.** A successor's words are laid out as its predecessor's (the same
//! loci, shapes and lattices), so the successor is
//! the predecessor copied on the card and the words a deposit moved scattered into it
//! (`hnn_scatter_words`): the port plan's "stepped entries", `(index, word)` per moved entry. A
//! first publication, or one whose layout differs, crosses whole.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::rc::Rc;

use core::ffi::c_void;

use holonics::hnn::propagation::{contact_operator, element_material, gram, ring_operator};
use holonics::hnn::{ClassMasses, ConstitutionRead, Field, HnnError, Locus};
use holonics::ratio::Rat;
use holonics::ratio::linear::ExactRatMatrix;
use num_bigint::BigInt;

use crate::hnn::DeviceError;
use crate::hnn::card::{Card, CardBuffer, copy_layout};
use crate::hnn::dyadic::{DyadicMatrix, refused};

/// The scatter's entry in the image.
pub const SCATTER_ENTRY: &str = "hnn_scatter_words";

/// [definition] **A locus's words in the published buffer**: its offset and its matrix.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Placed {
    pub(crate) offset: usize,
    pub(crate) matrix: DyadicMatrix,
}

/// Ring `g`'s loci: the sheet classes, `K_g`, `W_s,g`, `W_c,g` (placed; `live` when nonzero, the
/// host reading a zero port as no term) and the element's operator `I − ½K_g`.
#[derive(Clone, Debug)]
pub(crate) struct RingLoci {
    pub(crate) element: DyadicMatrix,
    pub(crate) passive: DyadicMatrix,
    pub(crate) contrast: Placed,
    pub(crate) contrast_live: bool,
    pub(crate) operator: ExactRatMatrix,
    pub(crate) operator_words: DyadicMatrix,
}

/// Contact `a`'s loci: its exact forms (the operator per conductance carry reads them), `C_a` and
/// `K_a` placed (each `live` when nonzero) and `D_a` on the host.
#[derive(Clone, Debug)]
pub(crate) struct ContactLoci {
    pub(crate) forms: [ExactRatMatrix; 3],
    pub(crate) storage: Placed,
    pub(crate) storage_live: bool,
    pub(crate) stiffness: Placed,
    pub(crate) stiffness_live: bool,
    pub(crate) dissipation: DyadicMatrix,
}

/// A source ring's pair port at one declared offset (in the field's order): its rank and its three
/// families' placed words, all at the port's lattice.
#[derive(Clone, Debug)]
pub(crate) struct PairLoci {
    pub(crate) rank: usize,
    pub(crate) outputs: Placed,
    pub(crate) current: Placed,
    pub(crate) earlier: Placed,
}

/// A source ring's port `E_g` and its pair ports.
#[derive(Clone, Debug)]
pub(crate) struct SourceLoci {
    pub(crate) ring: usize,
    pub(crate) port: Placed,
    pub(crate) pairs: Vec<PairLoci>,
}

/// [definition] **The contact's operator at one conductance carry** (the chart store's key):
/// `m_a` exact and as words, its conductance `G_a = 2^(n_a) Y_a` and its row norm `‖m_a‖∞`.
#[derive(Clone, Debug)]
pub(crate) struct ContactOperator {
    pub(crate) operator: ExactRatMatrix,
    pub(crate) words: DyadicMatrix,
    pub(crate) norm: Rat,
}

/// [definition] **The loci of one publication**, formed on the host, with the published words.
#[derive(Debug)]
pub(crate) struct Loci {
    pub(crate) rings: Vec<RingLoci>,
    pub(crate) contacts: Vec<ContactLoci>,
    pub(crate) sources: Vec<SourceLoci>,
    /// The receiving map per ring (`None` off the receiving rings).
    pub(crate) maps: Vec<Option<Placed>>,
    /// The receiving parametron's region class masses per ring (Decision 27; `None` off the
    /// receiving rings), kept on the host: the count face's grain read compares `(2C)^L` with
    /// `2^k (2N)^L`, integers past the card's 128-bit carrier, and no kernel reads the masses.
    pub(crate) masses: Vec<Option<ClassMasses>>,
    pub(crate) words: Vec<i64>,
    /// Each placed array's `(offset, length, exponent)`, in order: two publications with equal
    /// layouts differ only in their words.
    layout: Vec<(usize, usize, u32)>,
    operators: RefCell<BTreeMap<(usize, BigInt), Rc<ContactOperator>>>,
}

fn lattice(field: &Field, locus: Locus) -> Result<u32, HnnError> {
    field
        .lattice(locus)
        .map(|lattice| lattice.exponent())
        .ok_or(HnnError::Lattice { locus })
}

/// The words being laid out.
struct Words {
    words: Vec<i64>,
    layout: Vec<(usize, usize, u32)>,
}

impl Words {
    fn place(&mut self, matrix: DyadicMatrix) -> Placed {
        let offset = self.words.len();
        self.words.extend_from_slice(&matrix.words);
        self.layout
            .push((offset, matrix.words.len(), matrix.exponent));
        Placed { offset, matrix }
    }
}

fn vectors(vectors: &[Vec<Rat>], columns: usize) -> Result<ExactRatMatrix, HnnError> {
    Ok(ExactRatMatrix::shaped(
        vectors.len(),
        columns,
        vectors.to_vec(),
    )?)
}

impl Loci {
    /// **Form the loci of a constitution** (see the module header): every array at its locus's
    /// declared lattice, refused when an entry lies off it or passes the word.
    pub(crate) fn of(
        field: &Field,
        constitution: &impl ConstitutionRead,
    ) -> Result<Self, HnnError> {
        let mut words = Words {
            words: Vec::new(),
            layout: Vec::new(),
        };
        let mut rings = Vec::with_capacity(field.rings().len());
        for g in 0..field.rings().len() {
            let el = lattice(field, Locus::Element(g))?;
            let contrast_reading = field.standing_contrast(constitution, g)?;
            let (_, passive, element) = element_material(
                &contrast_reading,
                constitution.passive_factor(g),
                constitution.contrast_port(g),
                constitution.slices(g),
            )?;
            let operator = ring_operator(&element)?;
            let contrast = DyadicMatrix::at(
                constitution.contrast_port(g),
                el,
                "a contrast port entry off its element's lattice or past the word",
            )?;
            let contrast_live = !contrast.is_zero();
            rings.push(RingLoci {
                element: DyadicMatrix::at(
                    &element,
                    2 * el,
                    "an element entry off twice its lattice or past the word",
                )?,
                passive: DyadicMatrix::at(
                    &passive,
                    2 * el,
                    "a passive element entry off twice its lattice or past the word",
                )?,
                contrast: words.place(contrast),
                contrast_live,
                operator_words: DyadicMatrix::of(
                    &operator,
                    "a ring operator entry off the dyadics or past the word",
                )?,
                operator,
            });
        }
        let mut contacts = Vec::with_capacity(field.contacts().len());
        for a in 0..field.contacts().len() {
            let ch = lattice(field, Locus::Channel(a))?;
            let forms = [
                gram(constitution.contact_storage(a))?,
                gram(constitution.contact_stiffness(a))?,
                gram(constitution.contact_dissipation(a))?,
            ];
            let at = |form: &ExactRatMatrix| {
                DyadicMatrix::at(
                    form,
                    2 * ch,
                    "a contact form entry off twice its channel's lattice or past the word",
                )
            };
            let (storage, stiffness, dissipation) =
                (at(&forms[0])?, at(&forms[1])?, at(&forms[2])?);
            let (storage_live, stiffness_live) = (!storage.is_zero(), !stiffness.is_zero());
            contacts.push(ContactLoci {
                storage: words.place(storage),
                storage_live,
                stiffness: words.place(stiffness),
                stiffness_live,
                dissipation,
                forms,
            });
        }
        let mut sources = Vec::with_capacity(field.sources().len());
        for &g in field.sources() {
            let sp = lattice(field, Locus::SourcePort(g))?;
            let port = constitution
                .source_port(g)
                .ok_or(HnnError::MissingSourcePort { ring: g })?;
            let port = words.place(DyadicMatrix::at(
                port,
                sp,
                "a source port entry off its lattice or past the word",
            )?);
            let mut pairs = Vec::with_capacity(field.offsets().len());
            for &offset in field.offsets() {
                let pair = constitution
                    .pair_port(g, offset)
                    .ok_or(HnnError::MissingSourcePort { ring: g })?;
                let what = "a pair port entry off its lattice or past the word";
                let width = field.ring(g).width();
                let alphabet = field.alphabet();
                let outputs = words.place(DyadicMatrix::at(
                    &vectors(pair.outputs(), width)?,
                    sp,
                    what,
                )?);
                let current = words.place(DyadicMatrix::at(
                    &vectors(pair.current_reads(), alphabet)?,
                    sp,
                    what,
                )?);
                let earlier = words.place(DyadicMatrix::at(
                    &vectors(pair.earlier_reads(), alphabet)?,
                    sp,
                    what,
                )?);
                pairs.push(PairLoci {
                    rank: pair.rank(),
                    outputs,
                    current,
                    earlier,
                });
            }
            sources.push(SourceLoci {
                ring: g,
                port,
                pairs,
            });
        }
        let mut maps = vec![None; field.rings().len()];
        for receiver in field.receivers() {
            let ring = receiver.ring;
            if maps[ring].is_some() {
                continue;
            }
            let map = constitution
                .receiving_map(ring)
                .ok_or(HnnError::MissingReceivingMap { ring })?;
            maps[ring] = Some(words.place(DyadicMatrix::at(
                map,
                lattice(field, Locus::ReceivingMap(ring))?,
                "a receiving map entry off its lattice or past the word",
            )?));
        }
        let masses = (0..field.rings().len())
            .map(|ring| constitution.class_masses(ring).cloned())
            .collect();
        Ok(Self {
            rings,
            contacts,
            sources,
            maps,
            masses,
            words: words.words,
            layout: words.layout,
            operators: RefCell::new(BTreeMap::new()),
        })
    }

    /// **Contact `a`'s operator at a conductance** (its chart key's carry), formed once per
    /// publication and carry: `m_a = 1 + (G/2h)(2C + hD + (h²/2)K)` (the host's
    /// `holonics::hnn::propagation::contact_operator`).
    pub(crate) fn contact_operator(
        &self,
        contact: usize,
        carry: &BigInt,
        conductance: &Rat,
        step: &Rat,
    ) -> Result<Rc<ContactOperator>, HnnError> {
        let key = (contact, carry.clone());
        if let Some(found) = self.operators.borrow().get(&key) {
            return Ok(Rc::clone(found));
        }
        let [storage, stiffness, dissipation] = &self.contacts[contact].forms;
        let operator = contact_operator(storage, stiffness, dissipation, conductance, step)?;
        let words = DyadicMatrix::of(
            &operator,
            "a contact operator entry off the dyadics or past the word",
        )?;
        let formed = Rc::new(ContactOperator {
            norm: words.row_norm(),
            words,
            operator,
        });
        self.operators.borrow_mut().insert(key, Rc::clone(&formed));
        Ok(formed)
    }
}

/// [definition] **A publication on the card**: its loci and its words resident.
pub(crate) struct Publication<'c> {
    pub(crate) loci: Loci,
    pub(crate) words: CardBuffer<'c, i64>,
    /// The octets this publication took across the bus.
    pub(crate) octets: usize,
}

impl<'c> Publication<'c> {
    /// **Publish loci on the card**: laid out as `previous`, the predecessor's words copied on the
    /// card and the moved words scattered (`(index, word)` each); otherwise the words whole.
    pub(crate) fn publish(
        card: &'c Card,
        loci: Loci,
        previous: Option<&Publication<'c>>,
    ) -> Result<Self, HnnError> {
        let device = |error: DeviceError| error.into_hnn();
        let words = card.alloc::<i64>(loci.words.len()).map_err(device)?;
        let octets = match previous.filter(|previous| previous.loci.layout == loci.layout) {
            Some(previous) => {
                card.copy_within(&previous.words, 0, &words, 0, loci.words.len())
                    .map_err(device)?;
                let (indices, values): (Vec<u64>, Vec<i64>) = loci
                    .words
                    .iter()
                    .zip(&previous.loci.words)
                    .enumerate()
                    .filter(|(_, (now, then))| now != then)
                    .map(|(index, (now, _))| (index as u64, *now))
                    .unzip();
                scatter(card, &words, &indices, &values).map_err(device)?;
                indices.len() * 16
            }
            None => {
                card.write(&words, 0, &loci.words).map_err(device)?;
                loci.words.len() * 8
            }
        };
        Ok(Self {
            loci,
            words,
            octets,
        })
    }
}

/// Scatter moved words into a resident buffer (one transfer of the indices and words, one launch).
fn scatter(
    card: &Card,
    target: &CardBuffer<'_, i64>,
    indices: &[u64],
    values: &[i64],
) -> Result<(), DeviceError> {
    if indices.is_empty() {
        return Ok(());
    }
    let count = u32::try_from(indices.len()).map_err(|_| DeviceError::Shape {
        what: "a scatter's words within the 32-bit wire",
        expected: u32::MAX as usize,
        found: indices.len(),
    })?;
    let staged_indices = card.upload(indices)?;
    let staged_values = card.upload(values)?;
    let entry = card.entry(SCATTER_ENTRY)?;
    let single = copy_layout(card.census(), &entry, 1, indices.len())?;
    let threads = single.block.x;
    let blocks = count.div_ceil(threads).min(card.census().max_grid.x);
    let layout = crate::hnn::card::Layout {
        grid: crate::cuda::Dim3::x(blocks),
        ..single
    };
    card.owns(target)?;
    let mut target_ptr = target.device_ptr();
    let mut indices_ptr = staged_indices.device_ptr();
    let mut values_ptr = staged_values.device_ptr();
    let mut count_wire = count;
    let mut params: [*mut c_void; 4] = [
        &mut target_ptr as *mut _ as *mut c_void,
        &mut indices_ptr as *mut _ as *mut c_void,
        &mut values_ptr as *mut _ as *mut c_void,
        &mut count_wire as *mut _ as *mut c_void,
    ];
    card.launch(SCATTER_ENTRY, &layout, &mut params)?;
    // The staged indices and words are released after the stream passes the launch.
    Ok(())
}

impl DeviceError {
    /// **A device refusal as the port's refusal**: the carrier's refusals by name, every other
    /// realization refusal as [`HnnError::Realization`] (the driver's code stays in the device's own
    /// error, which the port's typed return cannot carry by name).
    pub(crate) fn into_hnn(self) -> HnnError {
        match self {
            DeviceError::Hnn(error) => error,
            DeviceError::Carrier { .. } => HnnError::Carrier {
                what: "a resident read's l1 certificate at 2^127",
            },
            DeviceError::Refused { .. } => HnnError::Carrier {
                what: "a resident word's entry (carrier, word or operand)",
            },
            DeviceError::Driver(_) => refused("the CUDA driver refused a call"),
            DeviceError::NoKernels { .. } => refused("the HNN kernels are not built"),
            DeviceError::Census { .. } => refused("the card's census"),
            DeviceError::ForeignBuffer => refused("a buffer of another card"),
            DeviceError::Launch { .. } => refused("a launch the card's census cannot carry"),
            DeviceError::Shape { .. } => refused("a resident shape"),
            DeviceError::OffLattice { .. } => refused("an entry off its lattice"),
            DeviceError::Word { .. } => refused("a coordinate past the signed 64-bit word"),
            DeviceError::Malformed { .. } => refused("a malformed gather"),
            DeviceError::Exponent { .. } => refused("an exponent past its ceiling"),
            DeviceError::OffCell { .. } => refused("a remainder off its cell"),
            DeviceError::Status { .. } => refused("a status word naming no refusal"),
            DeviceError::Graph => refused("a graph launched off its capture"),
        }
    }
}
