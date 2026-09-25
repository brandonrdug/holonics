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
