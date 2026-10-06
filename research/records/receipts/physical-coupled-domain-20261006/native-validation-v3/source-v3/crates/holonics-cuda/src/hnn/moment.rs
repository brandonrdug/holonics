//! **The source moment resident on the card, and its ingest** (kernel `hnn_moment_ingest`,
//! `kernels/hnn.cu`).
//!
//! [definition] The host owner is `holonics::hnn::SourceMoment` with `Field::selective_step`
//! (design (c), realization of `ingest`: "an exact prefix scan of the integer steps `c_g(x_k)`
//! with carries, then a histogram reduction into `M_g[phase]`"). Its entries are **integer
//! counts**, `u64` on the host with a refusal past the word (`HnnError::CountOverflow`): the
//! phase-binned counts `M_g` (`d_g × |A|`) and the offset counts `C_g(δ)` (`d_g × |A| × |A|`) on
//! every source ring, and the last `max Δ` raw cells, held as a delay line. A
//! [`ResidentMoment`] keeps all of them on the card, with the rings' phase classes; the host keeps
//! only the lift's words (`λ_g`, unbounded integers, advanced by the ingest's per-ring advances)
//! and the cell count.
//!
//! [definition] **The word certificate of the counts.** Every count is at most the cells ingested
//! since the moment's open, so a moment of fewer than `2^63` cells keeps every count within a
//! signed 64-bit word: the ingest refuses a batch past it (`HnnError::CountOverflow`), which
//! certifies both the 64-bit atomic additions and the counts' use as the lattice read's operand at
//! `L_x = 0` ([`ResidentMoment::phase_operand`]).
//!
//! [definition] **The advance chart belongs to the admitted encoding.** An identity uses the
//! declared field's `[class ∈ N_g]`, mounted at the open; a located passage mounts its actual
//! digits `a_g(class)` at their exact `u64` width. The kernel adds the predecessor's carry,
//! scans at `u64` width and counts at the executed resulting phase. The field's native
//! `selective_step` checks `D E = ρ` and `E T = U E` on the admitted prefix before launch, and
//! the kernel's actual receipt and full lift must equal that owner afterwards. It computes no
//! label, key or task answer. This is the helix and its paired moment's device realization;
//! the boundary labels, material/port evolution and receiving decoder keep their own consumers.
//!
//! [definition] **A mutating device failure invalidates the moment.** Launch and transfer errors
//! can follow a partial device mutation. Before a launch or re-key write the moment is marked
//! invalid; only a checked successful receipt restores validity. A failure then requires dropping
//! it and opening a new moment: no consuming entry, device reading or operand accepts it again.
//! The host lift and cell count remain the last checked receipt, not a rollback of device buffers.

use core::ffi::c_void;
use core::marker::PhantomData;

use holonics::hnn::encoding::Encoded;
use holonics::hnn::moment::Ingested;
use holonics::hnn::{Current, Field, HnnError};
use num_bigint::BigInt;

use crate::hnn::DeviceError;
use crate::hnn::card::{Card, CardBuffer, Layout, Operand, ingest_layout};

/// The entry's name in the image.
pub const INGEST_ENTRY: &str = "hnn_moment_ingest";

/// The ring periods the resident phase wire admits. With each advance at most its period and
/// a batch/thread count within `u32`, every `u64` scan and batch advance is below `2^63`.
const PERIOD_CEILING: u64 = 1 << 31;

/// [definition] **The source moment resident on a card.** See the module header.
pub struct ResidentMoment<'c> {
    card: &'c Card,
    field: Field,
    alphabet: usize,
    periods: Vec<u64>,
    sources: Vec<usize>,
    offsets: Vec<usize>,
    lift: Vec<BigInt>,
    opening: Vec<BigInt>,
    cells: u64,
    valid: bool,
    first_base: Vec<u64>,
    paired_base: Vec<u64>,
    chart: CardBuffer<'c, u64>,
    period_words: CardBuffer<'c, u32>,
    source_words: CardBuffer<'c, u32>,
    offset_words: CardBuffer<'c, u32>,
    first_base_words: CardBuffer<'c, u64>,
    paired_base_words: CardBuffer<'c, u64>,
    window: CardBuffer<'c, u32>,
    phases: CardBuffer<'c, u32>,
    first: CardBuffer<'c, u64>,
    paired: CardBuffer<'c, u64>,
    receipt: CardBuffer<'c, u64>,
}

/// [definition] **The moment's counts read back** (a transfer): the host moment's accessors.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MomentCounts {
    alphabet: usize,
    periods: Vec<u64>,
    sources: Vec<usize>,
    offsets: Vec<usize>,
    first_base: Vec<u64>,
    paired_base: Vec<u64>,
    first: Vec<u64>,
    paired: Vec<u64>,
}

fn source_index(sources: &[usize], ring: usize) -> Result<usize, DeviceError> {
    sources
        .iter()
        .position(|source| *source == ring)
        .ok_or(DeviceError::Hnn(HnnError::MissingSourcePort { ring }))
}

impl MomentCounts {
    /// `M_g[c]`: the counts of each exterior class at phase `c` of source ring `g`.
    pub fn phase_counts(&self, ring: usize, phase: usize) -> Result<&[u64], DeviceError> {
        let s = source_index(&self.sources, ring)?;
        let a = self.alphabet;
        let start = self.first_base[s] as usize + phase * a;
        Ok(&self.first[start..start + a])
    }

    /// `C_g(δ)[c]`: the offset counts at phase `c` of source ring `g`, row the current cell.
    pub fn offset_counts(
        &self,
        ring: usize,
        offset: usize,
        phase: usize,
    ) -> Result<&[u64], DeviceError> {
        let s = source_index(&self.sources, ring)?;
        let o = self
            .offsets
            .iter()
            .position(|declared| *declared == offset)
            .ok_or(DeviceError::Hnn(HnnError::Offset { offset }))?;
        let block = self.alphabet * self.alphabet;
        let start = self.paired_base[s * self.offsets.len() + o] as usize + phase * block;
        Ok(&self.paired[start..start + block])
    }

    /// Ring `g`'s period, `d_g`.
    pub fn period(&self, ring: usize) -> u64 {
        self.periods[ring]
    }
}

fn words(values: &[usize], what: &'static str) -> Result<Vec<u32>, DeviceError> {
    values
        .iter()
        .map(|value| {
            u32::try_from(*value).map_err(|_| DeviceError::Shape {
                what,
                expected: u32::MAX as usize,
                found: *value,
            })
        })
        .collect()
}

impl<'c> ResidentMoment<'c> {
    /// **Open a moment on the card** at a lift point: every count zero, no cell held, the
    /// field's lock chart and the rings' phase classes mounted (transfers).
    pub fn open(card: &'c Card, field: &Field, current: &Current) -> Result<Self, DeviceError> {
        let alphabet = field.alphabet();
        let rings = field.rings().len();
        let periods: Vec<u64> = field.rings().iter().map(|ring| ring.period()).collect();
        if let Some(ring) = periods.iter().position(|d| *d >= PERIOD_CEILING) {
            return Err(DeviceError::Shape {
                what: "a ring period within the resident phase wire and exact scan bound",
                expected: PERIOD_CEILING as usize,
                found: periods[ring] as usize,
            });
        }
        let sources = field.sources().to_vec();
        let offsets = field.offsets().to_vec();
        let mut chart = Vec::with_capacity(rings * alphabet);
        for ring in field.rings() {
            for code in 0..alphabet {
                chart.push(u64::from(ring.fits(ring.port(code))));
            }
        }
        let phases = (0..rings)
            .map(|g| {
                let phase = current.phase(field, g)?;
                Ok(u32::try_from(phase).expect("a phase lies below its period"))
            })
            .collect::<Result<Vec<u32>, DeviceError>>()?;
        let square = (alphabet * alphabet) as u64;
        let mut first_base = Vec::with_capacity(sources.len());
        let mut paired_base = Vec::with_capacity(sources.len() * offsets.len());
        let (mut first_len, mut paired_len) = (0u64, 0u64);
        for &source in &sources {
            let d = periods[source];
            first_base.push(first_len);
            first_len += d * alphabet as u64;
            for _ in &offsets {
                paired_base.push(paired_len);
                paired_len += d * square;
            }
        }
        let extent = offsets.iter().copied().max().unwrap_or(0);
        let period_words = periods
            .iter()
            .map(|d| u32::try_from(*d).expect("checked below the ceiling"))
            .collect::<Vec<u32>>();
        Ok(Self {
            card,
            field: field.clone(),
            alphabet,
            lift: current.lift().to_vec(),
            opening: current.lift().to_vec(),
            cells: 0,
            valid: true,
            chart: card.upload(&chart)?,
            period_words: card.upload(&period_words)?,
            source_words: card.upload(&words(&sources, "a source ring within 32 bits")?)?,
            offset_words: card.upload(&words(&offsets, "an offset within 32 bits")?)?,
            first_base_words: card.upload(&first_base)?,
            paired_base_words: card.upload(&paired_base)?,
            window: card.zeroed(1 + extent)?,
            phases: card.upload(&phases)?,
            first: card.zeroed(first_len as usize)?,
            paired: card.zeroed(paired_len as usize)?,
            receipt: card.zeroed(2 + rings)?,
            periods,
            sources,
            offsets,
            first_base,
            paired_base,
        })
    }

    /// **Ingest cells in order** at the layout derived from the card's census: the lift point's
    /// selective steps, then the phase-binned and offset counts on every source ring, then the
    /// held cells. Stops after the cell whose step carries the joint clock out, and reports it.
    pub fn ingest(&mut self, encoded: &Encoded) -> Result<Ingested, DeviceError> {
        Ok(self.ingest_in(encoded, None)?.0)
    }

    /// The ingest with the block narrowed to at most `lanes` threads (a realization choice that
    /// changes no value), returning the layout it ran at.
    pub fn ingest_in(
        &mut self,
        encoded: &Encoded,
        lanes: Option<u32>,
    ) -> Result<(Ingested, Layout), DeviceError> {
        self.ensure_valid()?;
        self.field.admit(encoded)?;
        let codes: Vec<usize> = encoded.classes_read().collect();
        if let Some(&code) = codes.iter().find(|code| **code >= self.alphabet) {
            return Err(DeviceError::Hnn(HnnError::CellOutside {
                code,
                alphabet: self.alphabet,
            }));
        }
        let cells_wire = u32::try_from(codes.len()).map_err(|_| DeviceError::Shape {
            what: "a batch of cells within the kernel's 32-bit wire",
            expected: u32::MAX as usize,
            found: codes.len(),
        })?;
        // The word certificate of the counts: every count stays within a signed 64-bit word.
        if self
            .cells
            .checked_add(codes.len() as u64)
            .is_none_or(|total| total > i64::MAX as u64)
        {
            return Err(DeviceError::Hnn(HnnError::CountOverflow));
        }
        // Reuse the existing exact owner for admission: its consumer checks the founded squares
        // at each actually admitted occurrence. Stop at the same first carry as the kernel, so
        // an occurrence outside this receipt's prefix is not compared or counted.
        let mut expected_lift = Current::at(&self.field, self.lift.clone())?;
        let mut expected = Ingested {
            cells: 0,
            carry_out: false,
        };
        for at in 0..encoded.len() {
            let step = expected_lift.step(&self.field, encoded, at)?;
            expected.cells = at + 1;
            if step.carry_out {
                expected.carry_out = true;
                break;
            }
        }
        let card = self.card;
        let rings = self.periods.len();
        let entry = card.entry(INGEST_ENTRY)?;
        let layout = ingest_layout(card.census(), &entry, rings, codes.len(), lanes)?;
        if encoded.is_empty() {
            return Ok((expected, layout));
        }
        // Mount the actual digits of every class the tile scans may read, including occurrences
        // after the first stopping cell. Only the admitted prefix is counted and committed.
        // A mounted value is an encoding's actual resident transport face, not an inferred or
        // authored table of answers.
        let located = if encoded.located().is_some() {
            let mut advances = vec![0u64; rings * self.alphabet];
            for at in 0..encoded.len() {
                let digits = encoded
                    .advance(at)
                    .ok_or(DeviceError::Hnn(HnnError::Unadmitted {
                        reason: "the located occurrence has no transport digits",
                    }))?;
                let class = codes[at];
                for (g, (&digit, &period)) in digits.iter().zip(&self.periods).enumerate() {
                    if digit >= period {
                        return Err(DeviceError::Hnn(HnnError::Unadmitted {
                            reason: "a located digit lies outside its admitted ring period",
                        }));
                    }
                    advances[g * self.alphabet + class] = digit;
                }
            }
            Some(card.upload(&advances)?)
        } else {
            None
        };
        let staged = card.upload(&words(&codes, "a cell class within 32 bits")?)?;
        let mut codes_ptr = staged.device_ptr();
        let mut cells = cells_wire;
        let mut rings_wire = rings as u32;
        let mut periods = self.period_words.device_ptr();
        let mut chart = located.as_ref().unwrap_or(&self.chart).device_ptr();
        let mut alphabet = self.alphabet as u32;
        let mut sources_wire = self.sources.len() as u32;
        let mut sources = self.source_words.device_ptr();
        let mut offsets_wire = self.offsets.len() as u32;
        let mut offsets = self.offset_words.device_ptr();
        let mut window = self.window.device_ptr();
        let mut extent = (self.window.len() - 1) as u32;
        let mut phases = self.phases.device_ptr();
        let mut first = self.first.device_ptr();
        let mut first_base = self.first_base_words.device_ptr();
        let mut paired = self.paired.device_ptr();
        let mut paired_base = self.paired_base_words.device_ptr();
        let mut receipt = self.receipt.device_ptr();
        let mut params: [*mut c_void; 18] = [
            &mut codes_ptr as *mut _ as *mut c_void,
            &mut cells as *mut _ as *mut c_void,
            &mut rings_wire as *mut _ as *mut c_void,
            &mut periods as *mut _ as *mut c_void,
            &mut chart as *mut _ as *mut c_void,
            &mut alphabet as *mut _ as *mut c_void,
            &mut sources_wire as *mut _ as *mut c_void,
            &mut sources as *mut _ as *mut c_void,
            &mut offsets_wire as *mut _ as *mut c_void,
            &mut offsets as *mut _ as *mut c_void,
            &mut window as *mut _ as *mut c_void,
            &mut extent as *mut _ as *mut c_void,
            &mut phases as *mut _ as *mut c_void,
            &mut first as *mut _ as *mut c_void,
            &mut first_base as *mut _ as *mut c_void,
            &mut paired as *mut _ as *mut c_void,
            &mut paired_base as *mut _ as *mut c_void,
            &mut receipt as *mut _ as *mut c_void,
        ];
        // A refused or failed launch/fetch may already have changed the card. Only a receipt
        // checked against the exact owner can make this instance usable again.
        self.valid = false;
        card.launch(INGEST_ENTRY, &layout, &mut params)?;
        let read = card.fetch(&self.receipt)?;
        let consumed = read[0];
        if consumed != expected.cells as u64 || read[1] != u64::from(expected.carry_out) {
            return Err(DeviceError::Hnn(HnnError::Shape {
                what: "the resident ingest prefix against the exact field owner",
                expected: expected.cells,
                found: consumed as usize,
            }));
        }
        let mut actual_lift = self.lift.clone();
        for (lift, advance) in actual_lift.iter_mut().zip(&read[2..]) {
            *lift += *advance;
        }
        if actual_lift.as_slice() != expected_lift.lift() {
            return Err(DeviceError::Hnn(HnnError::Shape {
                what: "the resident ingest lift against the exact field owner",
                expected: 0,
                found: 1,
            }));
        }
        self.lift = actual_lift;
        self.cells += consumed;
        self.valid = true;
        Ok((
            Ingested {
                cells: consumed as usize,
                carry_out: read[1] == 1,
            },
            layout,
        ))
    }

    /// Whether every mutating device operation has a checked successful receipt. A false
    /// reading is terminal for this instance; drop it and open a new moment.
    pub fn is_valid(&self) -> bool {
        self.valid
    }

    fn ensure_valid(&self) -> Result<(), DeviceError> {
        if !self.valid {
            return Err(DeviceError::Hnn(HnnError::Unadmitted {
                reason: "the resident moment has an unchecked device mutation; discard it",
            }));
        }
        Ok(())
    }

    /// `λ`, the lift point in the last checked receipt. After invalidation this is diagnostic
    /// host state, not the device's current lift (see [`Self::is_valid`]).
    pub fn lift(&self) -> &[BigInt] {
        &self.lift
    }

    /// The lift point at the open.
    pub fn opening(&self) -> &[BigInt] {
        &self.opening
    }

    /// The cells in the last checked receipt, `n`. After invalidation this is diagnostic host
    /// state, not a reading of the device buffers (see [`Self::is_valid`]).
    pub fn cells(&self) -> u64 {
        self.cells
    }

    /// The lift point as the host's [`Current`].
    pub fn current(&self, field: &Field) -> Result<Current, DeviceError> {
        self.ensure_valid()?;
        Ok(Current::at(field, self.lift.clone())?)
    }

    /// **The rings' phase classes on the card** (a transfer).
    pub fn phases(&self) -> Result<Vec<u32>, DeviceError> {
        self.ensure_valid()?;
        self.card.fetch(&self.phases)
    }

    /// **The counts read back** (a transfer).
    pub fn counts(&self) -> Result<MomentCounts, DeviceError> {
        self.ensure_valid()?;
        Ok(MomentCounts {
            alphabet: self.alphabet,
            periods: self.periods.clone(),
            sources: self.sources.clone(),
            offsets: self.offsets.clone(),
            first_base: self.first_base.clone(),
            paired_base: self.paired_base.clone(),
            first: self.card.fetch(&self.first)?,
            paired: self.card.fetch(&self.paired)?,
        })
    }

    /// **The held cells, most recent first** (`win[1], win[2], …`), `None` before enough
    /// cells (a transfer).
    pub fn window(&self) -> Result<Vec<Option<usize>>, DeviceError> {
        self.ensure_valid()?;
        let words = self.card.fetch(&self.window)?;
        let (valid, cells) = (words[0] as usize, &words[1..]);
        Ok((1..cells.len() + 1)
            .map(|offset| (offset <= valid).then(|| cells[valid - offset] as usize))
            .collect())
    }

    /// **A copy of the counts frozen at the cut, on the card** (a pending ratio's operand: the
    /// host's `PendingRatio` copies the moment's counts at its cut, and its later reads read that
    /// copy, never the moment that later ingests extend). Nothing crosses the bus.
    pub fn snapshot(&self) -> Result<MomentSnapshot<'c>, DeviceError> {
        self.ensure_valid()?;
        let card = self.card;
        let first = card.alloc::<u64>(self.first.len())?;
        let paired = card.alloc::<u64>(self.paired.len())?;
        card.copy_within(&self.first, 0, &first, 0, self.first.len())?;
        card.copy_within(&self.paired, 0, &paired, 0, self.paired.len())?;
        Ok(MomentSnapshot {
            first,
            paired,
            first_base: self.first_base.clone(),
            paired_base: self.paired_base.clone(),
            offsets: self.offsets.len(),
            cells: self.cells,
        })
    }

    /// **Re-key the rings' phase classes** at a lift point (`Current::rekey` moved only phase
    /// classes; the counts and the held cells are untouched): the phases written (a transfer of one
    /// word per ring) and the lift kept.
    pub fn rekey(&mut self, field: &Field, current: &Current) -> Result<(), DeviceError> {
        self.ensure_valid()?;
        let phases = (0..field.rings().len())
            .map(|g| {
                let phase = current.phase(field, g)?;
                Ok(u32::try_from(phase).expect("a phase lies below its period"))
            })
            .collect::<Result<Vec<u32>, DeviceError>>()?;
        self.valid = false;
        self.card.write(&self.phases, 0, &phases)?;
        self.lift = current.lift().to_vec();
        self.valid = true;
        Ok(())
    }

    /// **The phase rows `M_g[c]` of a source ring as a resident operand**: `d_g` vectors of `|A|`
    /// counts at `L_x = 0`, read as signed 64-bit words under the moment's word certificate.
    pub fn phase_operand(&self, ring: usize) -> Result<Operand<'_>, DeviceError> {
        self.ensure_valid()?;
        let s = source_index(&self.sources, ring)?;
        let octets = self.first_base[s] * core::mem::size_of::<u64>() as u64;
        Ok(Operand {
            card: self.card,
            pointer: self.first.device_ptr() + octets,
            vectors: self.periods[ring] as usize,
            width: self.alphabet,
            exponent: 0,
            _borrow: PhantomData,
        })
    }
}

/// [definition] **A moment's counts frozen at a cut, resident on the card**
/// ([`ResidentMoment::snapshot`]): the phase-binned and offset counts of every source ring, laid
/// out as the moment's, and the cells they count.
pub struct MomentSnapshot<'c> {
    first: CardBuffer<'c, u64>,
    paired: CardBuffer<'c, u64>,
    first_base: Vec<u64>,
    paired_base: Vec<u64>,
    offsets: usize,
    cells: u64,
}

impl MomentSnapshot<'_> {
    /// The cells the frozen counts count.
    pub fn cells(&self) -> u64 {
        self.cells
    }

    /// Source `s`'s phase rows' base in the phase-binned counts.
    pub(crate) fn first_base(&self, source: usize) -> u64 {
        self.first_base[source]
    }

    /// Source `s`'s offset block's base at its `o`-th declared offset.
    pub(crate) fn paired_base(&self, source: usize, offset: usize) -> u64 {
        self.paired_base[source * self.offsets + offset]
    }

    /// The phase-binned counts on the card.
    pub(crate) fn first_pointer(&self) -> crate::ffi::CUdeviceptr {
        self.first.device_ptr()
    }

    /// Source `s`'s offset block at its `o`-th declared offset, on the card.
    pub(crate) fn paired_pointer(&self, source: usize, offset: usize) -> crate::ffi::CUdeviceptr {
        self.paired.device_ptr()
            + self.paired_base(source, offset) * core::mem::size_of::<u64>() as u64
    }
}
