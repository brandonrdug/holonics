//! **The lattice read on the card**: a constitution locus carried on its lattice, read exactly
//! against a resident operand (kernel `hnn_lattice_read`, `kernels/hnn.cu`).
//!
//! [definition] Every entry of a learned locus `ℓ` lives on its declared lattice `2^(−L_ℓ)ℤ`
//! (`holonics::hnn::Lattice`, Decision 22), so the locus is its integer coordinates:
//! `A = a · 2^(−L_A)` ([`LatticeCoordinates::of_matrix`]). An operand on its own lattice is
//! `x = ξ · 2^(−L_x)`: the moment's counts `M_g[c]` at `L_x = 0`
//! ([`crate::hnn::ResidentMoment::phase_operand`]), or a lattice vector
//! ([`LatticeCoordinates::of_vectors`]). The read is
//!
//! ```text
//! y_b = A x_b = (Σ_j a_ij ξ_b,γ_b(j)) · 2^(−(L_A + L_x))
//! ```
//!
//! with an optional gather `γ_b` of the operand's coordinates ([`Gather`]): the ring rotation
//! `P_R^(τ_R)` is a permutation of the realified coordinates, so the receiving read
//! `f = R · P_R^(τ_R) v_R` (`holonics::hnn::ReceivingPhases::read`) is `R` against the gathered
//! anchor, with no arithmetic in the rotation. The integer sum is taken in the ring `ℤ/2^128` and
//! read under its l1 certificate (`kernels/exact_integer.cuh`): an entry whose bound
//! `Σ_j |a_ij ξ_j|` reaches `2^127` is refused ([`DeviceError::Carrier`]), whatever its value, so
//! the refusal depends on the exact terms alone and never on the realization's order.
//!
//! [definition] **The word boundary.** A coordinate enters the card as a signed 64-bit word, so a
//! product of two coordinates is at most `2^126` in magnitude and is always a word of the carrier.
//! An entry off its lattice ([`DeviceError::OffLattice`]) or whose coordinate needs more than 64
//! bits ([`DeviceError::Word`]) is refused at the mount, by position; nothing is rounded.
//!
//! Its campaign-1 instances are `E_0` (`10 × 256` on `2^(−L)ℤ`, `L = ⌈log₂(32 n)⌉`, read against the
//! five phase rows `M_0[c]` of the moment) and `R` (`512 × 22` on `2^(−10)ℤ`, read against the
//! receiving anchors). The anchors are lattice vectors only once the word's transients are fixed
//! width (Decision 24, being derived); until then the read's operand is a declared lattice vector.

use core::ffi::c_void;
use core::marker::PhantomData;

use holonics::hnn::Lattice;
use holonics::ratio::Rat;
use holonics::ratio::linear::ExactRatMatrix;
use num_bigint::BigInt;
use num_traits::{One, ToPrimitive};

use crate::hnn::DeviceError;
use crate::hnn::card::{Card, CardBuffer, Layout, Operand, read_layout};

/// The entry's name in the image.
pub const READ_ENTRY: &str = "hnn_lattice_read";

const EXACT: u32 = 0;
const REFUSED_CARRIER: u32 = 1;

// -------------------------------------------------------------------------------------------
// the coordinates

/// [definition] **The integer coordinates of a lattice-carried array**: `rows × columns` signed
/// 64-bit words `a`, row-major, the array being `a · 2^(−exponent)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LatticeCoordinates {
    rows: usize,
    columns: usize,
    exponent: u32,
    words: Vec<i64>,
}

impl LatticeCoordinates {
    /// **A locus's array on its declared lattice**: each entry's coordinate `entry · 2^L`, refused
    /// off the lattice or beyond the word.
    pub fn of_matrix(matrix: &ExactRatMatrix, lattice: Lattice) -> Result<Self, DeviceError> {
        Self::of_entries(matrix.rows(), matrix.columns(), matrix.entries(), lattice)
    }

    /// **Vectors on one declared lattice**, one row each.
    pub fn of_vectors(vectors: &[Vec<Rat>], lattice: Lattice) -> Result<Self, DeviceError> {
        let width = vectors.first().map_or(0, Vec::len);
        if let Some(vector) = vectors.iter().find(|vector| vector.len() != width) {
            return Err(DeviceError::Shape {
                what: "the vectors' common width",
                expected: width,
                found: vector.len(),
            });
        }
        Self::of_entries(vectors.len(), width, &vectors.concat(), lattice)
    }

    fn of_entries(
        rows: usize,
        columns: usize,
        entries: &[Rat],
        lattice: Lattice,
    ) -> Result<Self, DeviceError> {
        let exponent = lattice.exponent();
        let scale = BigInt::one() << exponent as usize;
        let words = entries
            .iter()
            .enumerate()
            .map(|(index, entry)| {
                let (row, column) = (index / columns, index % columns);
                if !lattice.contains(entry) {
                    return Err(DeviceError::OffLattice {
                        row,
                        column,
                        exponent,
                    });
                }
                let coordinate = entry.numer() * (&scale / entry.denom());
                coordinate.to_i64().ok_or(DeviceError::Word {
                    row,
                    column,
                    bits: coordinate.bits(),
                })
            })
            .collect::<Result<Vec<i64>, DeviceError>>()?;
        Ok(Self {
            rows,
            columns,
            exponent,
            words,
        })
    }

    pub fn rows(&self) -> usize {
        self.rows
    }

    pub fn columns(&self) -> usize {
        self.columns
    }

    /// `L`.
    pub fn exponent(&self) -> u32 {
        self.exponent
    }

    /// The words `a`, row-major.
    pub fn words(&self) -> &[i64] {
        &self.words
    }
}

// -------------------------------------------------------------------------------------------
// the resident locus and the gather

/// [definition] **A lattice-carried array resident on a card**: its coordinates in one buffer.
pub struct ResidentLattice<'c> {
    coordinates: CardBuffer<'c, i64>,
    rows: usize,
    columns: usize,
    exponent: u32,
}

impl<'c> ResidentLattice<'c> {
    /// Mount an array's coordinates (a transfer).
    pub fn mount(card: &'c Card, coordinates: &LatticeCoordinates) -> Result<Self, DeviceError> {
        Ok(Self {
            coordinates: card.upload(&coordinates.words)?,
            rows: coordinates.rows,
            columns: coordinates.columns,
            exponent: coordinates.exponent,
        })
    }

    pub fn rows(&self) -> usize {
        self.rows
    }

    pub fn columns(&self) -> usize {
        self.columns
    }

    pub fn exponent(&self) -> u32 {
        self.exponent
    }

    /// **The array's rows as an operand**: `rows` vectors of `columns` words at its exponent.
    pub fn operand(&self) -> Operand<'_> {
        Operand {
            card: self.coordinates_card(),
            pointer: self.coordinates.device_ptr(),
            vectors: self.rows,
            width: self.columns,
            exponent: self.exponent,
            _borrow: PhantomData,
        }
    }

    fn coordinates_card(&self) -> &'c Card {
        self.coordinates.card()
    }
}

/// [definition] **A gather per operand vector**: `vectors × columns` indices, index `j` of vector
/// `b` naming the operand coordinate the locus's column `j` reads (the rotation's permutation).
pub struct Gather<'c> {
    indices: CardBuffer<'c, u32>,
    vectors: usize,
    columns: usize,
}

impl<'c> Gather<'c> {
    /// Mount one index map per operand vector, each of one width.
    pub fn mount(card: &'c Card, maps: &[Vec<usize>]) -> Result<Self, DeviceError> {
        let columns = maps.first().map_or(0, Vec::len);
        let mut words = Vec::with_capacity(maps.len() * columns);
        for map in maps {
            if map.len() != columns {
                return Err(DeviceError::Shape {
                    what: "the gather's common width",
                    expected: columns,
                    found: map.len(),
                });
            }
            for &index in map {
                words.push(u32::try_from(index).map_err(|_| DeviceError::Shape {
                    what: "a gather index within the 32-bit wire",
                    expected: u32::MAX as usize,
                    found: index,
                })?);
            }
        }
        Ok(Self {
            indices: card.upload(&words)?,
            vectors: maps.len(),
            columns,
        })
    }
}

// -------------------------------------------------------------------------------------------
// the read

/// [definition] **A read resident on the card**: its ring words and statuses, the exponent of its
/// values, and the layout it ran at. Nothing crosses the bus until [`ResidentRead::fetch`].
pub struct ResidentRead<'c> {
    card: &'c Card,
    values: CardBuffer<'c, i128>,
    status: CardBuffer<'c, u32>,
    rows: usize,
    vectors: usize,
    exponent: u32,
    layout: Layout,
}

/// [definition] **A read on the host**: `vectors × rows` exact integers `S`, each value
/// `S · 2^(−exponent)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LatticeRead {
    rows: usize,
    vectors: usize,
    exponent: u32,
    coordinates: Vec<i128>,
}

impl LatticeRead {
    pub fn rows(&self) -> usize {
        self.rows
    }

    pub fn vectors(&self) -> usize {
        self.vectors
    }

    /// `L_A + L_x`.
    pub fn exponent(&self) -> u32 {
        self.exponent
    }

    /// The integer `S` of row `row` of vector `vector`.
    pub fn coordinate(&self, vector: usize, row: usize) -> i128 {
        self.coordinates[vector * self.rows + row]
    }

    /// The exact value `S · 2^(−exponent)`.
    pub fn value(&self, vector: usize, row: usize) -> Rat {
        Rat::new(
            BigInt::from(self.coordinate(vector, row)),
            BigInt::one() << self.exponent as usize,
        )
    }

    /// One vector's values.
    pub fn vector(&self, vector: usize) -> Vec<Rat> {
        (0..self.rows).map(|row| self.value(vector, row)).collect()
    }
}

impl ResidentRead<'_> {
    pub fn layout(&self) -> &Layout {
        &self.layout
    }

    /// **Read the values back** (a transfer): the exact integers, or the refused entries.
    pub fn fetch(&self) -> Result<LatticeRead, DeviceError> {
        let status = self.card.fetch(&self.status)?;
        let refused = |bit: u32| -> Vec<(usize, usize)> {
            status
                .iter()
                .enumerate()
                .filter(|(_, word)| **word & bit != 0)
                .map(|(at, _)| (at / self.rows, at % self.rows))
                .collect()
        };
        if status.iter().any(|word| *word != EXACT) {
            let carrier = refused(REFUSED_CARRIER);
            let malformed = refused(!REFUSED_CARRIER);
            if !malformed.is_empty() {
                return Err(DeviceError::Malformed { entries: malformed });
            }
            return Err(DeviceError::Carrier { entries: carrier });
        }
        Ok(LatticeRead {
            rows: self.rows,
            vectors: self.vectors,
            exponent: self.exponent,
            coordinates: self.card.fetch(&self.values)?,
        })
    }
}

impl Card {
    /// **The lattice read** `y_b = A x_b` (see the module header), resident: launched on the card's
    /// stream at the layout derived from its census ([`read_layout`]).
    pub fn read<'c>(
        &'c self,
        locus: &ResidentLattice<'c>,
        operand: Operand<'_>,
        gather: Option<&Gather<'c>>,
    ) -> Result<ResidentRead<'c>, DeviceError> {
        self.owns(&locus.coordinates)?;
        if !core::ptr::eq(operand.card, self) {
            return Err(DeviceError::ForeignBuffer);
        }
        match gather {
            Some(gather) => {
                self.owns(&gather.indices)?;
                if gather.vectors != operand.vectors || gather.columns != locus.columns {
                    return Err(DeviceError::Shape {
                        what: "the gather's vectors × columns",
                        expected: operand.vectors * locus.columns,
                        found: gather.vectors * gather.columns,
                    });
                }
            }
            None if operand.width != locus.columns => {
                return Err(DeviceError::Shape {
                    what: "the operand's width against the locus's columns",
                    expected: locus.columns,
                    found: operand.width,
                });
            }
            None => {}
        }
        let exponent = locus
            .exponent
            .checked_add(operand.exponent)
            .ok_or(DeviceError::Shape {
                what: "the read's exponent within 32 bits",
                expected: u32::MAX as usize,
                found: locus.exponent as usize,
            })?;
        let entry = self.entry(READ_ENTRY)?;
        let layout = read_layout(
            self.census(),
            &entry,
            locus.rows,
            locus.columns,
            operand.vectors,
        )?;
        let wire = |extent: usize| u32::try_from(extent).expect("the layout checked the wire");
        let entries = operand.vectors * locus.rows;
        let values = self.alloc::<i128>(entries)?;
        let status = self.alloc::<u32>(entries)?;
        let mut a = locus.coordinates.device_ptr();
        let mut rows = wire(locus.rows);
        let mut columns = wire(locus.columns);
        let mut x = operand.pointer;
        let mut vectors = wire(operand.vectors);
        let mut width = wire(operand.width);
        let mut indices = gather.map_or(0, |gather| gather.indices.device_ptr());
        let mut y = values.device_ptr();
        let mut statuses = status.device_ptr();
        let mut params: [*mut c_void; 9] = [
            &mut a as *mut _ as *mut c_void,
            &mut rows as *mut _ as *mut c_void,
            &mut columns as *mut _ as *mut c_void,
            &mut x as *mut _ as *mut c_void,
            &mut vectors as *mut _ as *mut c_void,
            &mut width as *mut _ as *mut c_void,
            &mut indices as *mut _ as *mut c_void,
            &mut y as *mut _ as *mut c_void,
            &mut statuses as *mut _ as *mut c_void,
        ];
        self.launch(READ_ENTRY, &layout, &mut params)?;
        Ok(ResidentRead {
            card: self,
            values,
            status,
            rows: locus.rows,
            vectors: operand.vectors,
            exponent,
            layout,
        })
    }
}

// -------------------------------------------------------------------------------------------
// the normal law's deposit on the card (campaign 2)

/// The deposit's entries in the image.
pub const OUTER_ENTRY: &str = "hnn_outer_update";
pub const SPLIT_ENTRY: &str = "hnn_budgeted_split";

/// [definition] **A window's dyadic samples for one outer update** `U = Σ_t a_t l_t r_tᵀ` (kernel
/// `hnn_outer_update`): the weights, left and right vectors as signed 64-bit coordinates at their
/// least common dyadic exponents, the weights' raised so the update's scale `S = σ_a + σ_l + σ_r`
/// is at least a declared floor (the budgeted split reads the update at or below its fine
/// lattice). Refused off the dyadics or past the word.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OuterSamples {
    samples: usize,
    rows: usize,
    columns: usize,
    weights: Vec<i64>,
    left: Vec<i64>,
    right: Vec<i64>,
    exponent: u32,
}

fn dyadic_words(values: &[Rat], exponent: u32) -> Result<Vec<i64>, DeviceError> {
    values
        .iter()
        .map(|value| {
            crate::hnn::dyadic::word(value, exponent, "a deposit sample's coordinate")
                .map_err(DeviceError::Hnn)
        })
        .collect()
}

impl OuterSamples {
    /// The samples of `U = Σ_t a_t l_t r_tᵀ` (`l_t` of `rows`, `r_t` of `columns` entries), with the
    /// update's scale raised to at least `floor`.
    pub fn of(
        weights: &[Rat],
        left: &[Vec<Rat>],
        right: &[Vec<Rat>],
        rows: usize,
        columns: usize,
        floor: u32,
    ) -> Result<Self, DeviceError> {
        use crate::hnn::dyadic::common_exponent;
        if left.len() != weights.len() || right.len() != weights.len() {
            return Err(DeviceError::Shape {
                what: "a deposit's samples (weight, left, right)",
                expected: weights.len(),
                found: left.len().min(right.len()),
            });
        }
        if left.iter().any(|l| l.len() != rows) || right.iter().any(|r| r.len() != columns) {
            return Err(DeviceError::Shape {
                what: "a deposit sample's vectors",
                expected: rows + columns,
                found: 0,
            });
        }
        let refusal = DeviceError::Hnn;
        let sigma_l =
            common_exponent(left.iter().flatten(), "a deposit's left vectors").map_err(refusal)?;
        let sigma_r = common_exponent(right.iter().flatten(), "a deposit's right vectors")
            .map_err(refusal)?;
        let sigma_a = common_exponent(weights.iter(), "a deposit's weights").map_err(refusal)?;
        let raised = floor.saturating_sub(sigma_a + sigma_l + sigma_r);
        let sigma_a = sigma_a + raised;
        Ok(Self {
            samples: weights.len(),
            rows,
            columns,
            weights: dyadic_words(weights, sigma_a)?,
            left: dyadic_words(&left.concat(), sigma_l)?,
            right: dyadic_words(&right.concat(), sigma_r)?,
            exponent: sigma_a + sigma_l + sigma_r,
        })
    }

    /// `S`, the update's scale: its entries lie on `2^(−S)ℤ`.
    pub fn exponent(&self) -> u32 {
        self.exponent
    }
}

/// [definition] **An outer update read back**: its `rows × columns` entries on `2^(−S)ℤ` and their
/// statuses.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OuterUpdate {
    pub rows: usize,
    pub columns: usize,
    pub exponent: u32,
    pub words: Vec<i128>,
    pub status: Vec<u32>,
}

impl OuterUpdate {
    /// The update's entries as exact values, or the first refused entry's position.
    pub fn values(&self) -> Result<Vec<Rat>, usize> {
        self.words
            .iter()
            .zip(&self.status)
            .enumerate()
            .map(|(at, (&word, &status))| {
                if status == EXACT {
                    Ok(Rat::new(
                        BigInt::from(word),
                        BigInt::one() << self.exponent as usize,
                    ))
                } else {
                    Err(at)
                }
            })
            .collect()
    }
}

/// [definition] **One array's budgeted split read back**: the entries' coordinates on `2^(−L)ℤ`,
/// their carried remainders on `2^(−(L+k))ℤ`, the released residuals on `2^(−S)ℤ`, the applied
/// coordinates and the statuses.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SplitRecord {
    pub entries: Vec<i64>,
    pub remainders: Vec<i128>,
    pub released: Vec<i128>,
    pub applied: Vec<i128>,
    pub status: Vec<u32>,
}

impl Card {
    /// **The outer update on the card** (kernel `hnn_outer_update`): one block per entry, its
    /// threads over the samples.
    pub fn outer_update(&self, samples: &OuterSamples) -> Result<OuterUpdate, DeviceError> {
        let entry = self.entry(OUTER_ENTRY)?;
        let base = read_layout(
            self.census(),
            &entry,
            samples.rows,
            samples.samples.max(1),
            samples.columns,
        )?;
        let layout = Layout {
            realization: crate::hnn::card::Realization::EntryOverSamples {
                entries: (samples.rows * samples.columns) as u64,
                threads: base.block.x,
                per_thread: samples.samples.div_ceil(base.block.x as usize) as u32,
            },
            ..base
        };
        let weights = self.upload(&samples.weights)?;
        let left = self.upload(&samples.left)?;
        let right = self.upload(&samples.right)?;
        let count = samples.rows * samples.columns;
        let update = self.zeroed::<i128>(count)?;
        let status = self.zeroed::<u32>(count)?;
        let (mut weights_ptr, mut left_ptr, mut right_ptr) =
            (weights.device_ptr(), left.device_ptr(), right.device_ptr());
        let mut n_samples = u32::try_from(samples.samples).map_err(|_| DeviceError::Shape {
            what: "a deposit's samples on the 32-bit wire",
            expected: u32::MAX as usize,
            found: samples.samples,
        })?;
        let (mut rows, mut columns) = (samples.rows as u32, samples.columns as u32);
        let (mut update_ptr, mut status_ptr) = (update.device_ptr(), status.device_ptr());
        let mut params: [*mut c_void; 8] = [
            &mut weights_ptr as *mut _ as *mut c_void,
            &mut left_ptr as *mut _ as *mut c_void,
            &mut right_ptr as *mut _ as *mut c_void,
            &mut n_samples as *mut _ as *mut c_void,
            &mut rows as *mut _ as *mut c_void,
            &mut columns as *mut _ as *mut c_void,
            &mut update_ptr as *mut _ as *mut c_void,
            &mut status_ptr as *mut _ as *mut c_void,
        ];
        self.launch(OUTER_ENTRY, &layout, &mut params)?;
        Ok(OuterUpdate {
            rows: samples.rows,
            columns: samples.columns,
            exponent: samples.exponent,
            words: self.fetch(&update)?,
            status: self.fetch(&status)?,
        })
    }

    /// **The budgeted split on the card** (kernel `hnn_budgeted_split`) of an update on `2^(−S)ℤ`
    /// onto an array on the lattice `2^(−L)ℤ` with its carried remainders on `2^(−(L+k))ℤ`,
    /// `S ≥ L + k`: one thread per entry.
    pub fn budgeted_split(
        &self,
        update: &OuterUpdate,
        lattice: Lattice,
        precision: u32,
        entries: &[i64],
        remainders: &[i128],
    ) -> Result<SplitRecord, DeviceError> {
        let fine = lattice.exponent() + precision;
        if update.exponent < fine
            || entries.len() != update.words.len()
            || remainders.len() != update.words.len()
        {
            return Err(DeviceError::Shape {
                what: "a budgeted split (the update at or below the fine lattice, one per entry)",
                expected: update.words.len(),
                found: entries.len().min(remainders.len()),
            });
        }
        let count = entries.len();
        let entry = self.entry(SPLIT_ENTRY)?;
        // One thread per entry, a warp's worth of blocks at least: the block is the census's
        // ceiling at most, and the entries stride the grid.
        let threads = entry
            .max_threads_per_block
            .min(self.census().max_threads_per_block)
            .clamp(1, self.census().warp.max(1) * 8);
        let layout = Layout {
            grid: crate::cuda::Dim3::x(
                u32::try_from(count.div_ceil(threads as usize).max(1)).map_err(|_| {
                    DeviceError::Launch {
                        entry: SPLIT_ENTRY,
                        clause: "the entries fit the grid's X extent",
                    }
                })?,
            ),
            block: crate::cuda::Dim3::x(threads),
            shared: 0,
            realization: crate::hnn::card::Realization::CopyPerBlock {
                copies: count.div_ceil(threads as usize) as u64,
                threads,
            },
        };
        let words = self.upload(&update.words)?;
        let statuses = self.upload(&update.status)?;
        let entry_buffer = self.upload(entries)?;
        let remainder_buffer = self.upload(remainders)?;
        let released = self.zeroed::<i128>(count)?;
        let applied = self.zeroed::<i128>(count)?;
        let status = self.zeroed::<u32>(count)?;
        let (mut words_ptr, mut statuses_ptr) = (words.device_ptr(), statuses.device_ptr());
        let mut n = count as u32;
        let mut down = update.exponent - fine;
        let mut k = precision;
        let (mut entry_ptr, mut remainder_ptr) =
            (entry_buffer.device_ptr(), remainder_buffer.device_ptr());
        let (mut released_ptr, mut applied_ptr, mut status_ptr) = (
            released.device_ptr(),
            applied.device_ptr(),
            status.device_ptr(),
        );
        let mut params: [*mut c_void; 10] = [
            &mut words_ptr as *mut _ as *mut c_void,
            &mut statuses_ptr as *mut _ as *mut c_void,
            &mut n as *mut _ as *mut c_void,
            &mut down as *mut _ as *mut c_void,
            &mut k as *mut _ as *mut c_void,
            &mut entry_ptr as *mut _ as *mut c_void,
            &mut remainder_ptr as *mut _ as *mut c_void,
            &mut released_ptr as *mut _ as *mut c_void,
            &mut applied_ptr as *mut _ as *mut c_void,
            &mut status_ptr as *mut _ as *mut c_void,
        ];
        self.launch(SPLIT_ENTRY, &layout, &mut params)?;
        Ok(SplitRecord {
            entries: self.fetch(&entry_buffer)?,
            remainders: self.fetch(&remainder_buffer)?,
            released: self.fetch(&released)?,
            applied: self.fetch(&applied)?,
            status: self.fetch(&status)?,
        })
    }
}
