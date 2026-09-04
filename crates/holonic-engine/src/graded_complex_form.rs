//! The canonical octet form of a [`GradedCausalComplex`], and the only one.
//!
//! `archive/plans/THE_ASSEMBLY.md` step 6 asks for a plate schema carrying a rebase-invariants reading.
//! A plate holds form codecs that already exist and defines none of its own — that is the sentence
//! `applications/holon-plate/src/lib.rs` opens with — so the codec belongs here, beside the type it
//! encodes, exactly as `HTEC` lives in `crates/holonic-life/src/holonic_training.rs` and `ERST` in
//! `crates/holonic-membrane/src/live_current.rs`.
//!
//! # What is deposited, and what is not
//!
//! The octets are the **incidence**: cells, grades, source events, and oriented boundary chains.
//! They are not the reading. A rebase-invariants reading is *taken over* an incidence by
//! [`crate::rebase_invariants`] and is recomputed by whoever mounts the form; depositing the reading
//! instead of the incidence would deposit a conclusion nobody downstream could re-derive or refute.
//! The magic is `RBIN` because the reading is what this form exists to be read for.
//!
//! # The wire
//!
//! Every integer is little-endian. Every extent is exact. There is no padding and no field whose
//! width depends on its value.
//!
//! ```text
//!   0    4   magic            b"RBIN"
//!   4    4   layout_version   u32 = 1
//!   8    8   schema_octets    u64
//!        n   schema           UTF-8, the complex's own `schema` field, verbatim
//!        8   next_cell        u64
//!        8   cells            u64
//!   then `cells` cells, ASCENDING by id:
//!        8   id               u64
//!        8   name_octets      u64
//!        n   name             UTF-8
//!        8   grade            u64, must fit u32
//!        8   source_events    u64, at least one
//!          each: 8  event     u64, STRICTLY ascending
//!        8   terms            u64
//!          each, STRICTLY ascending by cell:
//!            8  cell          u64
//!            8  positive_octets u64
//!            n  positive      big-endian magnitude, MINIMAL (empty is zero)
//!            8  negative_octets u64
//!            n  negative      big-endian magnitude, MINIMAL (empty is zero)
//! ```
//!
//! # Canonicity is enforced, not hoped for
//!
//! A plate re-takes the form from the body it mounted and refuses if the two differ
//! (`FormNotCanonical`). That refusal names a length, not a cause. Every way this wire could carry
//! the same complex twice is therefore refused *here*, by name:
//!
//! - **cells and terms must ascend.** The complex stores both in `BTreeMap`s, so any other order
//!   re-encodes differently.
//! - **a magnitude may not carry a leading zero octet.** Zero is the empty run and nothing else.
//! - **a coefficient may not have both counts nonzero.** [`ComparativeMultiplicity::new`] removes
//!   the common population silently, so `(3, 1)` would mount as `(2, 0)` and re-encode differently.
//!   Counts are primary and the pair is retained; what is refused is a *redundant* pair, not a
//!   signed one.
//! - **a coefficient may not have both counts zero.** [`CausalChain::add_term`] drops a zero term.
//!
//! # The declared aperture
//!
//! Reconstruction runs through [`GradedCausalComplex::found_cell`], which is the only public way to
//! found a cell and which refuses `d d != 0`, a mis-graded face, an uncaused cell and an unreduced
//! coefficient. Nothing here writes a cell into the map behind that check.
//!
//! That founder assigns identities `1, 2, 3, ...` in founding order, so this codec's aperture is
//! exactly the complexes it can build: **cell identities `1..=cells`, contiguous and ascending,
//! with `next_cell == cells + 1`**. A complex outside that aperture — one deserialized with
//! permuted identities, say — is refused by [`encode_native_bytes`] rather than encoded into a form
//! that could not be mounted back. Declaring the aperture is `CLAUDE.md` §8; an organ used past a
//! declared aperture is a defect even when it appears to return.
//!
//! **Both halves are enforced, and until 2026-08-08 only one was.** The encoder checked the
//! identity half and then wrote `cells + 1` unconditionally, overwriting the body's own
//! `next_cell`; a body with contiguous identities and `next_cell = 99` was accepted, and
//! `decode_native_bytes(encode_native_bytes(x))` returned a complex that differed from `x` in
//! exactly that field. The declaration overstated what the code checked, which is the defect the
//! declaration exists to prevent. `GradedCausalComplex::validate` does not close it either: it
//! refuses only `next_cell <= max_identity`, so `99` passes there.

use std::collections::BTreeSet;

use num_bigint::BigUint;
use num_traits::Zero;
use thiserror::Error;

use crate::algebraic::{
    CausalAlgebraicError, CausalCellId, CausalChain, ComparativeMultiplicity, GradedCausalComplex,
};
use crate::causal::EventId;

/// The codec's own magic, four octets of `[A-Z0-9]` so a container can carry it as a schema tag.
pub const GRADED_COMPLEX_FORM_MAGIC: [u8; 4] = *b"RBIN";

/// The codec's own layout version. A reader that holds this form reads its version from **here**
/// rather than copying a literal, so that bumping the wire stops old plates by version instead of
/// mis-reading them as the version the reader holds.
pub const GRADED_COMPLEX_FORM_LAYOUT_VERSION: u32 = 1;

const HEAD_OCTETS: usize = 8;

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum GradedComplexFormError {
    #[error("not a graded-complex form; octets 0..4 are {found:?} where the form opens `RBIN`")]
    NotAForm { found: [u8; 4] },
    #[error("graded-complex form layout version {found} is not held; this codec holds {held}")]
    LayoutVersionUnheld { found: u32, held: u32 },
    #[error("the form's `{field}` declares {declared} octets with {remaining} remaining")]
    ExtentOverruns {
        field: &'static str,
        declared: u64,
        remaining: u64,
    },
    #[error("the form carries {octets} trailing octets after its last declared cell")]
    TrailingOctets { octets: usize },
    #[error("the form's `{field}` is not UTF-8")]
    NotUtf8 { field: &'static str },
    #[error(
        "the form's `{field}` does not ascend: {found} follows {previous}, so the same body has \
         two encodings"
    )]
    NotAscending {
        field: &'static str,
        previous: u64,
        found: u64,
    },
    #[error(
        "a `{field}` magnitude opens with a zero octet; a magnitude is minimal big-endian and zero \
         is the empty run"
    )]
    LeadingZeroMagnitude { field: &'static str },
    #[error(
        "the boundary term on cell {cell} declares no occurrence on either hand; a chain does not \
         retain a zero coefficient"
    )]
    ZeroTerm { cell: u64 },
    #[error(
        "the form declares cell identity {found} where this codec's aperture is the contiguous \
         run 1..=cells and {expected} is next"
    )]
    IdentityNotContiguous { expected: u64, found: u64 },
    #[error(
        "the form declares next_cell={declared} over {cells} cells; a complex founded through \
         `found_cell` carries next_cell = cells + 1"
    )]
    NextCellDisagrees { declared: u64, cells: u64 },
    #[error("the form declares grade {grade}, which does not fit a chain degree")]
    GradeOverruns { grade: u64 },
    #[error("cell {cell} declares no source event; an uncaused cell is refused at the founder")]
    UncausedCell { cell: u64 },
    #[error("the mounted incidence refused the form: {0}")]
    Refused(#[from] CausalAlgebraicError),
}

/// Take the canonical octets of one complex.
///
/// Refuses a complex outside the declared aperture rather than emitting octets that would not mount
/// back. See the module doc.
pub fn encode_native_bytes(
    complex: &GradedCausalComplex,
) -> Result<Vec<u8>, GradedComplexFormError> {
    let cells = complex.cells();
    let count = cells.len() as u64;
    for (expected, id) in (1u64..).zip(cells.keys()) {
        if id.0 != expected {
            return Err(GradedComplexFormError::IdentityNotContiguous {
                expected,
                found: id.0,
            });
        }
    }

    let next_cell = next_identity(complex);
    if next_cell != count + 1 {
        return Err(GradedComplexFormError::NextCellDisagrees {
            declared: next_cell,
            cells: count,
        });
    }

    let mut octets = Vec::new();
    octets.extend_from_slice(&GRADED_COMPLEX_FORM_MAGIC);
    octets.extend_from_slice(&GRADED_COMPLEX_FORM_LAYOUT_VERSION.to_le_bytes());
    put_bytes(&mut octets, complex.schema.as_bytes());
    put_u64(&mut octets, next_cell);
    put_u64(&mut octets, count);
    for cell in cells.values() {
        put_u64(&mut octets, cell.id.0);
        put_bytes(&mut octets, cell.name.as_bytes());
        put_u64(&mut octets, u64::from(cell.grade));
        put_u64(&mut octets, cell.source_events.len() as u64);
        for event in &cell.source_events {
            put_u64(&mut octets, event.0);
        }
        let terms = cell.boundary.coefficients();
        put_u64(&mut octets, terms.len() as u64);
        for (face, coefficient) in terms {
            put_u64(&mut octets, face.0);
            put_magnitude(&mut octets, coefficient.positive_count());
            put_magnitude(&mut octets, coefficient.negative_count());
        }
    }
    Ok(octets)
}

/// Mount one canonical form through the real founder.
///
/// Every cell goes through [`GradedCausalComplex::found_cell`], so a form whose incidence does not
/// close does not become a complex.
pub fn decode_native_bytes(octets: &[u8]) -> Result<GradedCausalComplex, GradedComplexFormError> {
    if octets.len() < HEAD_OCTETS {
        return Err(GradedComplexFormError::ExtentOverruns {
            field: "head",
            declared: HEAD_OCTETS as u64,
            remaining: octets.len() as u64,
        });
    }
    let magic: [u8; 4] = octets[0..4].try_into().expect("four");
    if magic != GRADED_COMPLEX_FORM_MAGIC {
        return Err(GradedComplexFormError::NotAForm { found: magic });
    }
    let layout = u32::from_le_bytes(octets[4..8].try_into().expect("four"));
    if layout != GRADED_COMPLEX_FORM_LAYOUT_VERSION {
        return Err(GradedComplexFormError::LayoutVersionUnheld {
            found: layout,
            held: GRADED_COMPLEX_FORM_LAYOUT_VERSION,
        });
    }

    let mut cursor = Cursor::new(&octets[HEAD_OCTETS..]);
    let schema = cursor.utf8("schema")?;
    let next_cell = cursor.u64("next_cell")?;
    let declared_cells = cursor.u64("cells")?;

    let mut complex = GradedCausalComplex::default();
    complex.schema = schema;
    for expected in 1..=declared_cells {
        let id = cursor.u64("cell id")?;
        if id != expected {
            return Err(GradedComplexFormError::IdentityNotContiguous {
                expected,
                found: id,
            });
        }
        let name = cursor.utf8("cell name")?;
        let grade = cursor.u64("grade")?;
        let grade =
            u32::try_from(grade).map_err(|_| GradedComplexFormError::GradeOverruns { grade })?;

        let event_count = cursor.u64("source_events")?;
        if event_count == 0 {
            return Err(GradedComplexFormError::UncausedCell { cell: id });
        }
        let mut source_events: BTreeSet<EventId> = BTreeSet::new();
        let mut previous: Option<u64> = None;
        for _ in 0..event_count {
            let event = cursor.u64("source event")?;
            if let Some(previous) = previous
                && event <= previous
            {
                return Err(GradedComplexFormError::NotAscending {
                    field: "source events",
                    previous,
                    found: event,
                });
            }
            previous = Some(event);
            source_events.insert(EventId(event));
        }

        let term_count = cursor.u64("terms")?;
        let mut boundary = CausalChain::default();
        let mut previous: Option<u64> = None;
        for _ in 0..term_count {
            let face = cursor.u64("term cell")?;
            if let Some(previous) = previous
                && face <= previous
            {
                return Err(GradedComplexFormError::NotAscending {
                    field: "boundary terms",
                    previous,
                    found: face,
                });
            }
            previous = Some(face);
            let positive = cursor.magnitude("positive")?;
            let negative = cursor.magnitude("negative")?;
            if positive.is_zero() && negative.is_zero() {
                return Err(GradedComplexFormError::ZeroTerm { cell: face });
            }
            boundary.add_term(
                CausalCellId(face),
                ComparativeMultiplicity::new(positive, negative),
            );
        }

        complex.found_cell(name, source_events, grade, boundary)?;
    }
    cursor.finish()?;

    if next_cell != declared_cells + 1 {
        return Err(GradedComplexFormError::NextCellDisagrees {
            declared: next_cell,
            cells: declared_cells,
        });
    }
    Ok(complex)
}

/// The identity the founder would hand out next.
///
/// `GradedCausalComplex::next_cell` is private to `algebraic` and has no accessor, and the only
/// public surface that carries it is the founder itself: found one throwaway cell on a clone and
/// read the identity it returns. A grade-zero cell with an empty boundary and one source event
/// passes every gate in `found_cell` — no uncaused refusal, an empty chain validates, a vertex is
/// allowed no boundary and has none, the face loop is empty and `d d` of nothing is zero — so this
/// cannot refuse and the `expect` is a proof, not a hope.
///
/// The clone is the price of the missing accessor. `algebraic.rs` gaining
/// `pub const fn next_cell(&self) -> u64` would remove it, and this function with it.
fn next_identity(complex: &GradedCausalComplex) -> u64 {
    let mut probe = complex.clone();
    probe
        .found_cell("", BTreeSet::from([EventId(1)]), 0, CausalChain::default())
        .expect("a grade-zero cell with an empty boundary and one source event is always founded")
        .0
}

fn put_u64(octets: &mut Vec<u8>, value: u64) {
    octets.extend_from_slice(&value.to_le_bytes());
}

fn put_bytes(octets: &mut Vec<u8>, run: &[u8]) {
    put_u64(octets, run.len() as u64);
    octets.extend_from_slice(run);
}

fn put_magnitude(octets: &mut Vec<u8>, value: &BigUint) {
    if value.is_zero() {
        put_u64(octets, 0);
    } else {
        put_bytes(octets, &value.to_bytes_be());
    }
}

struct Cursor<'a> {
    octets: &'a [u8],
    at: usize,
}

impl<'a> Cursor<'a> {
    fn new(octets: &'a [u8]) -> Self {
        Self { octets, at: 0 }
    }

    fn take(
        &mut self,
        field: &'static str,
        extent: usize,
    ) -> Result<&'a [u8], GradedComplexFormError> {
        let end = self
            .at
            .checked_add(extent)
            .filter(|end| *end <= self.octets.len())
            .ok_or(GradedComplexFormError::ExtentOverruns {
                field,
                declared: extent as u64,
                remaining: (self.octets.len() - self.at) as u64,
            })?;
        let taken = &self.octets[self.at..end];
        self.at = end;
        Ok(taken)
    }

    fn u64(&mut self, field: &'static str) -> Result<u64, GradedComplexFormError> {
        let row = self.take(field, 8)?;
        Ok(u64::from_le_bytes(row.try_into().expect("eight")))
    }

    fn run(&mut self, field: &'static str) -> Result<&'a [u8], GradedComplexFormError> {
        let extent = self.u64(field)?;
        let extent =
            usize::try_from(extent).map_err(|_| GradedComplexFormError::ExtentOverruns {
                field,
                declared: extent,
                remaining: (self.octets.len() - self.at) as u64,
            })?;
        self.take(field, extent)
    }

    fn utf8(&mut self, field: &'static str) -> Result<String, GradedComplexFormError> {
        let run = self.run(field)?;
        String::from_utf8(run.to_vec()).map_err(|_| GradedComplexFormError::NotUtf8 { field })
    }

    fn magnitude(&mut self, field: &'static str) -> Result<BigUint, GradedComplexFormError> {
        let run = self.run(field)?;
        if run.first() == Some(&0) {
            return Err(GradedComplexFormError::LeadingZeroMagnitude { field });
        }
        Ok(BigUint::from_bytes_be(run))
    }

    fn finish(&self) -> Result<(), GradedComplexFormError> {
        if self.at == self.octets.len() {
            Ok(())
        } else {
            Err(GradedComplexFormError::TrailingOctets {
                octets: self.octets.len() - self.at,
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rebase_invariants::{PivotRule, rebase_invariants};
    use num_bigint::BigInt;

    fn source() -> BTreeSet<EventId> {
        BTreeSet::from([EventId(1)])
    }

    /// Three vertices and three edges, founded through the real founder.
    fn hollow_triangle() -> GradedCausalComplex {
        let mut complex = GradedCausalComplex::default();
        let a = complex
            .found_cell("a", source(), 0, CausalChain::default())
            .expect("a vertex");
        let b = complex
            .found_cell("b", source(), 0, CausalChain::default())
            .expect("a vertex");
        let c = complex
            .found_cell(
                "c",
                BTreeSet::from([EventId(1), EventId(9)]),
                0,
                CausalChain::default(),
            )
            .expect("a vertex");
        for (name, from, to) in [("ab", a, b), ("bc", b, c), ("ca", c, a)] {
            let mut boundary = CausalChain::default();
            boundary.add_term(to, ComparativeMultiplicity::positive(1u32));
            boundary.add_term(from, ComparativeMultiplicity::negative(1u32));
            complex
                .found_cell(name, source(), 1, boundary)
                .expect("an edge");
        }
        complex
    }

    /// One vertex, one loop whose boundary cancels, and a face attached twice around it. The
    /// coefficient `2` is the only place in these fixtures where a magnitude is not one, so it is
    /// also the only fixture that can catch a magnitude codec that always writes a unit.
    fn doubled_attachment() -> GradedCausalComplex {
        let mut complex = GradedCausalComplex::default();
        let a = complex
            .found_cell("a", source(), 0, CausalChain::default())
            .expect("a vertex");
        let mut loop_boundary = CausalChain::default();
        loop_boundary.add_term(a, ComparativeMultiplicity::positive(1u32));
        loop_boundary.add_term(a, ComparativeMultiplicity::negative(1u32));
        let edge = complex
            .found_cell("loop", source(), 1, loop_boundary)
            .expect("a loop");
        let mut face = CausalChain::default();
        face.add_term(edge, ComparativeMultiplicity::positive(2u32));
        complex
            .found_cell("twice", source(), 2, face)
            .expect("a doubled attachment");
        complex
    }

    /// A coefficient far past a `u64`, so the magnitude wire is exercised beyond one octet.
    fn wide_coefficient() -> GradedCausalComplex {
        let mut complex = GradedCausalComplex::default();
        let a = complex
            .found_cell("a", source(), 0, CausalChain::default())
            .expect("a vertex");
        let mut loop_boundary = CausalChain::default();
        loop_boundary.add_term(a, ComparativeMultiplicity::positive(1u32));
        loop_boundary.add_term(a, ComparativeMultiplicity::negative(1u32));
        let edge = complex
            .found_cell("loop", source(), 1, loop_boundary)
            .expect("a loop");
        let wide: BigUint = BigUint::parse_bytes(b"340282366920938463463374607431768211457", 10)
            .expect("a wide magnitude");
        let mut face = CausalChain::default();
        face.add_term(edge, ComparativeMultiplicity::new(wide, BigUint::zero()));
        complex
            .found_cell("wide", source(), 2, face)
            .expect("a wide attachment");
        complex
    }

    /// Three parallel edges and a face attached to them with unequal winding, `4*e1 - 6*e2 + 2*e3`.
    /// It closes because the coefficients sum to zero. It is the one fixture here whose boundary
    /// magnitudes differ from each other, which is what makes the three pivot rules take three
    /// different walks over it — see `rebase_invariants`'s module doc.
    fn staggered_attachment() -> GradedCausalComplex {
        let mut complex = GradedCausalComplex::default();
        let a = complex
            .found_cell("a", source(), 0, CausalChain::default())
            .expect("a vertex");
        let b = complex
            .found_cell("b", source(), 0, CausalChain::default())
            .expect("a vertex");
        let mut edges = Vec::new();
        for name in ["first", "second", "third"] {
            let mut boundary = CausalChain::default();
            boundary.add_term(b, ComparativeMultiplicity::positive(1u32));
            boundary.add_term(a, ComparativeMultiplicity::negative(1u32));
            edges.push(
                complex
                    .found_cell(name, source(), 1, boundary)
                    .expect("an edge"),
            );
        }
        let mut face = CausalChain::default();
        face.add_term(edges[0], ComparativeMultiplicity::positive(4u32));
        face.add_term(edges[1], ComparativeMultiplicity::negative(6u32));
        face.add_term(edges[2], ComparativeMultiplicity::positive(2u32));
        complex
            .found_cell("staggered", source(), 2, face)
            .expect("a staggered attachment");
        complex
    }

    fn bodies() -> Vec<(&'static str, GradedCausalComplex)> {
        vec![
            ("hollow_triangle", hollow_triangle()),
            ("doubled_attachment", doubled_attachment()),
            ("staggered_attachment", staggered_attachment()),
            ("wide_coefficient", wide_coefficient()),
            ("empty", GradedCausalComplex::default()),
        ]
    }

    #[test]
    fn the_form_round_trips_through_a_real_mount_and_is_byte_identical() {
        for (label, complex) in bodies() {
            let form = encode_native_bytes(&complex).expect("a form");
            let mounted = decode_native_bytes(&form).expect("a mount");
            assert_eq!(
                mounted, complex,
                "{label}: the mounted complex is not the one encoded"
            );
            let retaken = encode_native_bytes(&mounted).expect("a form");
            assert_eq!(
                retaken, form,
                "{label}: re-taking the form did not return the octets"
            );
        }
    }

    #[test]
    fn the_head_names_the_codec_and_its_own_layout_version() {
        let form = encode_native_bytes(&hollow_triangle()).expect("a form");
        assert_eq!(&form[0..4], b"RBIN".as_slice());
        assert_eq!(
            u32::from_le_bytes(form[4..8].try_into().expect("four")),
            GRADED_COMPLEX_FORM_LAYOUT_VERSION
        );
        let mut foreign = form.clone();
        foreign[1] = b'X';
        assert!(matches!(
            decode_native_bytes(&foreign),
            Err(GradedComplexFormError::NotAForm { .. })
        ));
        let mut future = form.clone();
        future[4] = 9;
        assert!(matches!(
            decode_native_bytes(&future),
            Err(GradedComplexFormError::LayoutVersionUnheld { found: 9, held: 1 })
        ));
    }

    /// The wide-magnitude fixture is the one that can catch a codec truncating to a machine word.
    #[test]
    fn a_magnitude_wider_than_a_machine_word_survives_the_wire() {
        let complex = wide_coefficient();
        let form = encode_native_bytes(&complex).expect("a form");
        let mounted = decode_native_bytes(&form).expect("a mount");
        let face = mounted.cell(CausalCellId(3)).expect("the wide cell");
        let coefficient = face.boundary.coefficient(CausalCellId(2));
        assert_eq!(
            coefficient.difference(),
            BigInt::parse_bytes(b"340282366920938463463374607431768211457", 10).expect("wide"),
            "the magnitude did not survive the wire"
        );
        assert!(
            coefficient.difference() > BigInt::from(u64::MAX),
            "this fixture must exceed a machine word or it cannot catch a truncation"
        );
    }

    #[test]
    fn a_form_whose_incidence_does_not_close_is_refused_by_the_founder() {
        // Rewrite the doubled attachment's coefficient from 2 to 1 while leaving its loop alone:
        // still closes. Then rewrite the loop's own boundary to a single term, which does not.
        let complex = hollow_triangle();
        let form = encode_native_bytes(&complex).expect("a form");
        // find the last cell's single-term boundary and delete one of its two terms by declaring
        // one term where two are written -- the trailing octets refusal fires first, so instead
        // build the broken complex directly and hand-write its wire.
        let mut broken = Vec::new();
        broken.extend_from_slice(&GRADED_COMPLEX_FORM_MAGIC);
        broken.extend_from_slice(&GRADED_COMPLEX_FORM_LAYOUT_VERSION.to_le_bytes());
        put_bytes(&mut broken, complex.schema.as_bytes());
        put_u64(&mut broken, 3);
        put_u64(&mut broken, 2);
        // cell 1: a vertex
        put_u64(&mut broken, 1);
        put_bytes(&mut broken, b"a");
        put_u64(&mut broken, 0);
        put_u64(&mut broken, 1);
        put_u64(&mut broken, 1);
        put_u64(&mut broken, 0);
        // cell 2: a grade-2 cell whose boundary is a grade-0 cell -- a mis-graded face
        put_u64(&mut broken, 2);
        put_bytes(&mut broken, b"bad");
        put_u64(&mut broken, 2);
        put_u64(&mut broken, 1);
        put_u64(&mut broken, 1);
        put_u64(&mut broken, 1);
        put_u64(&mut broken, 1);
        put_magnitude(&mut broken, &BigUint::from(1u32));
        put_magnitude(&mut broken, &BigUint::zero());
        assert_ne!(broken, form);

        let refusal = decode_native_bytes(&broken).expect_err("a mis-graded face must refuse");
        assert!(
            matches!(
                refusal,
                GradedComplexFormError::Refused(CausalAlgebraicError::BoundaryGrade { .. })
            ),
            "expected the founder's own grade refusal, got {refusal}"
        );
    }

    #[test]
    fn a_non_ascending_wire_refuses_because_it_would_be_a_second_encoding() {
        let complex = hollow_triangle();
        let form = encode_native_bytes(&complex).expect("a form");
        // The last cell "ca" has two boundary terms, ascending. Swap them.
        let mut swapped = form.clone();
        let tail = swapped.len();
        // each term is 8 (cell) + 8 (positive extent) + 1 + 8 (negative extent) + 0 = 25 or
        // 8 + 8 + 0 + 8 + 1 = 25 depending on hand; locate the two term runs from the end.
        let second = tail - 25;
        let first = second - 25;
        let (left, right) = (
            swapped[first..second].to_vec(),
            swapped[second..tail].to_vec(),
        );
        swapped[first..second].copy_from_slice(&right);
        swapped[second..tail].copy_from_slice(&left);
        assert_ne!(swapped, form, "the swap must actually move octets");

        let refusal = decode_native_bytes(&swapped).expect_err("a descending wire must refuse");
        assert!(
            matches!(
                refusal,
                GradedComplexFormError::NotAscending {
                    field: "boundary terms",
                    ..
                }
            ),
            "expected a boundary-term ordering refusal, got {refusal}"
        );
    }

    #[test]
    fn an_unreduced_or_zero_coefficient_refuses_rather_than_mounting_as_another_one() {
        let head = |terms: &[(u64, u32, u32)]| {
            let mut wire = Vec::new();
            wire.extend_from_slice(&GRADED_COMPLEX_FORM_MAGIC);
            wire.extend_from_slice(&GRADED_COMPLEX_FORM_LAYOUT_VERSION.to_le_bytes());
            put_bytes(&mut wire, b"holonic-engine.graded-causal-complex.v1");
            put_u64(&mut wire, 3);
            put_u64(&mut wire, 2);
            put_u64(&mut wire, 1);
            put_bytes(&mut wire, b"a");
            put_u64(&mut wire, 0);
            put_u64(&mut wire, 1);
            put_u64(&mut wire, 1);
            put_u64(&mut wire, 0);
            put_u64(&mut wire, 2);
            put_bytes(&mut wire, b"e");
            put_u64(&mut wire, 1);
            put_u64(&mut wire, 1);
            put_u64(&mut wire, 1);
            put_u64(&mut wire, terms.len() as u64);
            for (cell, positive, negative) in terms {
                put_u64(&mut wire, *cell);
                put_magnitude(&mut wire, &BigUint::from(*positive));
                put_magnitude(&mut wire, &BigUint::from(*negative));
            }
            wire
        };

        // (3, 1) mounts as (3, 1): the wire carries both arms and the body retains both.
        let mounted = decode_native_bytes(&head(&[(1, 3, 1)])).expect("a retained pair");
        let term = mounted
            .cells()
            .values()
            .find(|cell| cell.grade == 1)
            .expect("the grade-one cell")
            .boundary
            .coefficient(CausalCellId(1));
        assert_eq!(
            (term.positive_count(), term.negative_count()),
            (&BigUint::from(3u32), &BigUint::from(1u32)),
            "four passages crossed the wire and four were mounted"
        );
        // (0, 0) would be dropped by `add_term` and re-encode with one term fewer.
        let refusal = decode_native_bytes(&head(&[(1, 0, 0)])).expect_err("a zero pair");
        assert!(
            matches!(refusal, GradedComplexFormError::ZeroTerm { cell: 1 }),
            "expected a zero-term refusal, got {refusal}"
        );
        // and the honest pair mounts
        let mounted = decode_native_bytes(&head(&[(1, 1, 0)])).expect("an honest term");
        assert_eq!(mounted.cells().len(), 2);
    }

    #[test]
    fn a_padded_magnitude_refuses_because_zero_is_the_empty_run() {
        let mut wire = Vec::new();
        wire.extend_from_slice(&GRADED_COMPLEX_FORM_MAGIC);
        wire.extend_from_slice(&GRADED_COMPLEX_FORM_LAYOUT_VERSION.to_le_bytes());
        put_bytes(&mut wire, b"holonic-engine.graded-causal-complex.v1");
        put_u64(&mut wire, 3);
        put_u64(&mut wire, 2);
        put_u64(&mut wire, 1);
        put_bytes(&mut wire, b"a");
        put_u64(&mut wire, 0);
        put_u64(&mut wire, 1);
        put_u64(&mut wire, 1);
        put_u64(&mut wire, 0);
        put_u64(&mut wire, 2);
        put_bytes(&mut wire, b"e");
        put_u64(&mut wire, 1);
        put_u64(&mut wire, 1);
        put_u64(&mut wire, 1);
        put_u64(&mut wire, 1);
        put_u64(&mut wire, 1);
        put_bytes(&mut wire, &[0x00, 0x01]); // 1, written in two octets
        put_magnitude(&mut wire, &BigUint::zero());
        let refusal = decode_native_bytes(&wire).expect_err("a padded magnitude must refuse");
        assert!(
            matches!(
                refusal,
                GradedComplexFormError::LeadingZeroMagnitude { field: "positive" }
            ),
            "expected a leading-zero refusal, got {refusal}"
        );
    }

    #[test]
    fn a_forged_identity_or_next_cell_refuses() {
        let form = encode_native_bytes(&hollow_triangle()).expect("a form");
        let schema_at = HEAD_OCTETS;
        let schema_octets =
            u64::from_le_bytes(form[schema_at..schema_at + 8].try_into().expect("eight")) as usize;
        let next_cell_at = schema_at + 8 + schema_octets;
        let cells_at = next_cell_at + 8;
        let first_id_at = cells_at + 8;

        let mut forged = form.clone();
        forged[next_cell_at] = 9;
        let refusal = decode_native_bytes(&forged).expect_err("a forged next_cell must refuse");
        assert!(
            matches!(
                refusal,
                GradedComplexFormError::NextCellDisagrees {
                    declared: 9,
                    cells: 6
                }
            ),
            "expected a next_cell refusal, got {refusal}"
        );

        let mut forged = form.clone();
        forged[first_id_at] = 4;
        let refusal = decode_native_bytes(&forged).expect_err("a forged identity must refuse");
        assert!(
            matches!(
                refusal,
                GradedComplexFormError::IdentityNotContiguous {
                    expected: 1,
                    found: 4
                }
            ),
            "expected an identity refusal, got {refusal}"
        );
    }

    #[test]
    fn a_truncated_or_trailing_form_refuses() {
        let form = encode_native_bytes(&hollow_triangle()).expect("a form");
        let mut trailing = form.clone();
        trailing.push(0);
        assert!(matches!(
            decode_native_bytes(&trailing),
            Err(GradedComplexFormError::TrailingOctets { octets: 1 })
        ));
        assert!(matches!(
            decode_native_bytes(&form[..form.len() - 1]),
            Err(GradedComplexFormError::ExtentOverruns { .. })
        ));
        assert!(matches!(
            decode_native_bytes(b"RBI"),
            Err(GradedComplexFormError::ExtentOverruns { field: "head", .. })
        ));
    }

    /// The declared aperture, refused at the encoder rather than emitted as an unmountable form.
    ///
    /// `found_cell` cannot produce a body outside the aperture — it hands out `1, 2, 3, ...` — so
    /// the only way in is a deserializer, which is exactly the way a caller could reach it in
    /// earnest. The fixture asserts its own surgery worked: if the serialized spelling of a cell
    /// identity ever moves, this fails loudly rather than passing on a complex that was never
    /// permuted.
    #[test]
    fn a_complex_outside_the_contiguous_identity_aperture_is_refused_at_the_encoder() {
        let mut complex = GradedCausalComplex::default();
        complex
            .found_cell("a", source(), 0, CausalChain::default())
            .expect("a vertex");
        let text = ron::to_string(&complex).expect("ron");
        let faithful: GradedCausalComplex = ron::from_str(&text).expect("ron");
        assert_eq!(
            faithful, complex,
            "the ron round trip must be faithful first"
        );

        let shifted = text.replace("(1)", "(7)");
        assert_ne!(
            shifted, text,
            "the serialized spelling of an identity moved"
        );
        let permuted: GradedCausalComplex = ron::from_str(&shifted).expect("ron");
        assert_eq!(
            permuted.cells().keys().copied().collect::<Vec<_>>(),
            vec![CausalCellId(7)],
            "this fixture must actually carry a non-contiguous identity or it proves nothing"
        );

        let refusal =
            encode_native_bytes(&permuted).expect_err("a permuted identity must refuse encoding");
        assert!(
            matches!(
                refusal,
                GradedComplexFormError::IdentityNotContiguous {
                    expected: 1,
                    found: 7
                }
            ),
            "expected an aperture refusal, got {refusal}"
        );
    }

    /// The other half of the declared aperture, and the half that was declared and not enforced.
    ///
    /// A body with contiguous identities and a next identity of `99` used to encode without
    /// complaint, because the encoder wrote `cells + 1` over it. The octets then mounted back to a
    /// *different* body — one whose next identity is `2` — so `decode(encode(x)) != x` on exactly
    /// the material the module doc says is out of aperture. The decoder has carried
    /// `NextCellDisagrees` for this condition all along; now the encoder refuses instead of
    /// manufacturing the agreement.
    #[test]
    fn a_complex_whose_next_identity_is_not_cells_plus_one_is_refused_at_the_encoder() {
        let mut complex = GradedCausalComplex::default();
        complex
            .found_cell("a", source(), 0, CausalChain::default())
            .expect("a vertex");
        let text = ron::to_string(&complex).expect("ron");
        let faithful: GradedCausalComplex = ron::from_str(&text).expect("ron");
        assert_eq!(
            faithful, complex,
            "the ron round trip must be faithful first"
        );

        let drifted = text.replace("next_cell:2", "next_cell:99");
        assert_ne!(
            drifted, text,
            "the serialized spelling of `next_cell` moved"
        );
        let drifted: GradedCausalComplex = ron::from_str(&drifted).expect("ron");
        assert_eq!(
            drifted.cells().keys().copied().collect::<Vec<_>>(),
            vec![CausalCellId(1)],
            "the identity half of the aperture must still hold, or this tests the wrong refusal"
        );
        assert_ne!(
            drifted, complex,
            "the two bodies differ in `next_cell` alone, which is the field under test"
        );

        let refusal = encode_native_bytes(&drifted)
            .expect_err("a next identity outside the aperture must refuse encoding");
        assert!(
            matches!(
                refusal,
                GradedComplexFormError::NextCellDisagrees {
                    declared: 99,
                    cells: 1
                }
            ),
            "expected a next-identity refusal, got {refusal}"
        );

        // and the body inside the aperture still round trips, so the refusal is the aperture and
        // not a codec that stopped working
        let form = encode_native_bytes(&complex).expect("a form");
        assert_eq!(decode_native_bytes(&form).expect("a mount"), complex);
    }

    /// A hand-written wire carrying exactly one grade-zero cell, with the three fields the
    /// refusals below turn on exposed. The honest spelling mounts, which is what makes each
    /// refusal attributable to the one field that was changed.
    fn one_cell_wire(schema: &[u8], grade: u64, events: &[u64]) -> Vec<u8> {
        let mut wire = Vec::new();
        wire.extend_from_slice(&GRADED_COMPLEX_FORM_MAGIC);
        wire.extend_from_slice(&GRADED_COMPLEX_FORM_LAYOUT_VERSION.to_le_bytes());
        put_bytes(&mut wire, schema);
        put_u64(&mut wire, 2);
        put_u64(&mut wire, 1);
        put_u64(&mut wire, 1);
        put_bytes(&mut wire, b"a");
        put_u64(&mut wire, grade);
        put_u64(&mut wire, events.len() as u64);
        for event in events {
            put_u64(&mut wire, *event);
        }
        put_u64(&mut wire, 0);
        wire
    }

    const HONEST_SCHEMA: &[u8] = b"holonic-engine.graded-causal-complex.v1";

    /// Three refusals the wire declares by name and nothing exercised: a schema run that is not
    /// UTF-8, a grade no chain degree carries, and a cell declaring no source event.
    #[test]
    fn a_non_utf8_schema_an_overrunning_grade_and_an_uncaused_cell_each_refuse_by_name() {
        // the control: the same builder, honest, mounts
        let mounted = decode_native_bytes(&one_cell_wire(HONEST_SCHEMA, 0, &[1]))
            .expect("the honest spelling must mount or these refusals prove nothing");
        assert_eq!(mounted.cells().len(), 1);

        let refusal = decode_native_bytes(&one_cell_wire(&[0xff, 0xfe], 0, &[1]))
            .expect_err("a schema run that is not UTF-8 must refuse");
        assert!(
            matches!(refusal, GradedComplexFormError::NotUtf8 { field: "schema" }),
            "expected a UTF-8 refusal, got {refusal}"
        );

        let overrun = u64::from(u32::MAX) + 1;
        let refusal = decode_native_bytes(&one_cell_wire(HONEST_SCHEMA, overrun, &[1]))
            .expect_err("a grade wider than a chain degree must refuse");
        assert!(
            matches!(refusal, GradedComplexFormError::GradeOverruns { grade } if grade == overrun),
            "expected a grade refusal, got {refusal}"
        );
        // and the widest grade that does fit is not refused, so the bound is the bound
        decode_native_bytes(&one_cell_wire(HONEST_SCHEMA, u64::from(u32::MAX), &[1]))
            .expect("u32::MAX is a chain degree");

        let refusal = decode_native_bytes(&one_cell_wire(HONEST_SCHEMA, 0, &[]))
            .expect_err("a cell declaring no source event must refuse");
        assert!(
            matches!(refusal, GradedComplexFormError::UncausedCell { cell: 1 }),
            "expected an uncaused-cell refusal, got {refusal}"
        );
    }

    /// The source-event leg of the ascent refusal. The complex stores `source_events` in a
    /// `BTreeSet`, so a descending or repeated run is a *second encoding of the same body* — the
    /// exact hazard the module doc says is refused here by name, and the leg no test reached.
    #[test]
    fn a_source_event_run_that_does_not_ascend_refuses_because_it_would_be_a_second_encoding() {
        let refusal = decode_native_bytes(&one_cell_wire(HONEST_SCHEMA, 0, &[5, 3]))
            .expect_err("a descending source-event run must refuse");
        assert!(
            matches!(
                refusal,
                GradedComplexFormError::NotAscending {
                    field: "source events",
                    previous: 5,
                    found: 3
                }
            ),
            "expected a source-event ordering refusal, got {refusal}"
        );

        // a repeat is the same hazard: a set does not retain it, so it would mount one event short
        let refusal = decode_native_bytes(&one_cell_wire(HONEST_SCHEMA, 0, &[5, 5]))
            .expect_err("a repeated source event must refuse");
        assert!(
            matches!(
                refusal,
                GradedComplexFormError::NotAscending {
                    field: "source events",
                    previous: 5,
                    found: 5
                }
            ),
            "expected a source-event ordering refusal, got {refusal}"
        );

        // and the ascending run mounts, carrying both events
        let mounted = decode_native_bytes(&one_cell_wire(HONEST_SCHEMA, 0, &[3, 5]))
            .expect("an ascending run must mount");
        assert_eq!(
            mounted
                .cell(CausalCellId(1))
                .expect("the cell")
                .source_events
                .iter()
                .map(|event| event.0)
                .collect::<Vec<_>>(),
            vec![3, 5]
        );
    }

    /// The reading the form exists to be read for, taken over a mounted form rather than the
    /// complex that was encoded, and identical under all three pivot rules.
    #[test]
    fn the_reading_over_a_mounted_form_is_the_reading_over_the_body_that_founded_it() {
        for (label, complex) in bodies() {
            let mounted = decode_native_bytes(&encode_native_bytes(&complex).expect("a form"))
                .expect("mount");
            for rule in PivotRule::ALL {
                let founded = rebase_invariants(&complex, rule).expect("a reading");
                let remounted = rebase_invariants(&mounted, rule).expect("a reading");
                assert_eq!(founded, remounted, "{label} under {rule:?}");
            }
        }
    }
}
