//! `RBIN` — a rebase-invariants reading over one graded causal incidence.
//!
//! Owner: `crates/holonic-engine/src/graded_complex_form.rs` (`encode_native_bytes`,
//! `decode_native_bytes`) for the form, and `crates/holonic-engine/src/rebase_invariants.rs`
//! (`rebase_invariants`, `invariants_agree`) for the reading. The plate holds both; it defines
//! neither.
//!
//! # What is on the disk and what is in the census
//!
//! The **form** is the incidence: cells, grades, source events, oriented boundary chains. The
//! **census** is the reading taken over it — Smith normal forms of every boundary map, per-grade
//! free ranks, torsion coefficients, Euler characteristic. That split is the whole point of this
//! schema. Depositing the reading would deposit a conclusion; depositing the incidence means the
//! resumer *re-derives* the conclusion and the plate's second frame is a real recomputation rather
//! than a copy.
//!
//! `archive/plans/THE_ASSEMBLY.md`: *"the resumer must compute a census field the depositor could
//! not."* The depositor of an `RBIN` form is whatever grew the incidence — a circuit, a production
//! trace, a substitution ecology — and what it wrote out was cells and boundaries. The homology is
//! computed here, on the way back in.
//!
//! # The pivot rule never reaches the census, and the check that says so is auditable
//!
//! `rebase_invariants.rs` names the hazard directly: *a solver's pivot order promoted into a
//! reduction* is a receiver-visible coordinate becoming an invariant. The census is therefore
//! computed under **all three** [`PivotRule`]s and the three must agree by
//! [`invariants_agree`] before any field is written. They disagree, the schema refuses the form.
//! This is not decoration: it is the module's own falsifier fired at the plate's mouth, where a
//! forged or drifted incidence would arrive.
//!
//! **It was decoration until 2026-08-08.** Measured on all five declared fixtures, the three rules
//! produced *identical pivot traces*: every nonzero entry of a simplicial boundary matrix has
//! magnitude one, `find_pivot` breaks ties with strict `<` and `>`, so every rule selected the
//! first nonzero and the loop ran one computation three times and compared it with itself twice.
//! Cutting `PivotRule::ALL` to a single rule killed no test.
//!
//! So [`reading_of`] now returns the [`ReadingSchedule`] each rule walked beside the invariants
//! they agreed on, and the fixture family carries `staggered_attachment` — a face attached with
//! *unequal* winding around parallel edges, `4*e1 - 6*e2 + 2*e3`, which closes because the
//! coefficients sum to zero and which the three rules enter at three different rows. The agreement
//! is now checkable for being an agreement between different computations, which is the only form
//! in which it is evidence.
//!
//! # The census carries no population, and that is not a reduction
//!
//! A census is fixed ASCII names against exact `u64` values, by construction, so a varying-arity
//! family like `betti_0 .. betti_k` cannot be one and the actual torsion coefficients — `BigInt`s,
//! possibly wide — cannot be either. `torsion_factors` counts them.
//!
//! That count is a **declaration**, not a hand-off. `archive/plans/THE_ASSEMBLY.md`: *"no adapter may
//! reduce one of these structures to a boolean or a scalar on its way to the next organ."* The
//! structure itself is returned by [`RebaseBody::reading`], which hands back the whole
//! [`RebaseInvariants`] — every grade, every Betti number, every torsion coefficient at full width.
//! The census declares; the reading is what travels.
//!
//! And the census is **derived from that reading** rather than computed beside it: [`LitBody::census`]
//! calls [`RebaseBody::reading`] and counts what it returned. So the full-width structure is on the
//! path of every deposit, resume and re-deposit of an `RBIN` plate, not an escape hatch declared
//! and never opened.
//!
//! # The Euler characteristic is a declared bijection, never a cast
//!
//! `chi` is signed and a census value is a `u64`. It is carried as the pair
//! `euler_positive` / `euler_negative`, at most one of which is nonzero, by
//! [`encode_euler`] — a total bijection from `i64` onto that pair, with [`decode_euler`] as its
//! inverse and a `None` for any pair outside the image. `chi as u64` would be a cast: it would send
//! `-1` to `18446744073709551615` and nothing downstream could tell that from a body with
//! eighteen quintillion generators.
//!
//! **[`decode_euler`] has no production caller and that is a stated debt, not an oversight.**
//! `encode_euler` runs on every census; the inverse runs only under test. The one place it belongs
//! is `holon-plate`'s `inspect` arm, which prints `report.census.render()` and so shows
//! `euler_negative=1` as a bare count where the body's characteristic is `-1`. It is kept rather
//! than cut because a bijection with its inverse removed is a one-way encoding wearing a
//! bijection's name, and `archive/plans/THE_ASSEMBLY.md` step 6 asks for the bijection.
//!
//! # The field the hand-off moves, and why the others are insufficient
//!
//! `CLAUDE.md` §8: *a law that returns zero proves nothing about itself.* [`present_and_require_change`]
//! refuses a deed that leaves the form byte-identical — but that fires on the **form**, and a
//! census none of whose fields ever move would leave `DeedChangedNothing` as the only control,
//! firing on the container rather than on the declaration.
//!
//! The field this schema names is **`betti_total`**, and the argument is exact. The deed founds one
//! cell at grade `g` with a declared boundary. Writing `n_k` for the cells at grade `k` and `r_k`
//! for `rank(d_k)`, the free rank is `b_k = n_k - r_k - r_{k+1}`. Founding one cell adds a column
//! to `d_g` and a zero row to `d_{g+1}`, so exactly one of two things happens:
//!
//! - the new column is independent of the standing boundaries: `r_g` rises by one, `b_g` holds and
//!   `b_{g-1}` falls by one — **the deed killed a generator**, `betti_total` moves by `-1`;
//! - the new column is not: `r_g` holds and `b_g` rises by one — **the deed founded a generator**,
//!   `betti_total` moves by `+1`.
//!
//! So `betti_total` always moves, and *which way it moves says what the deed did to the homology*.
//! The other five:
//!
//! - **`cells`** does move, by `+1`, on every accepted deed — and it moves by `+1` whichever of the
//!   two things happened. It is the extent of the storage, the same species as `ERST`'s
//!   `carrier_words`: it witnesses that the wire grew, which the form digest already witnesses. A
//!   census resting on it would be declaring the form's length in another spelling.
//! - **`grades`** does not move at all unless the deed opens a grade above the standing top.
//! - **`boundary_rank_total`** moves only in the first case. A deed founding a vertex, or any cell
//!   whose boundary is already a boundary, leaves it exactly where it was.
//! - **`torsion_factors`** is zero on every incidence without a doubled attachment. It is the field
//!   this schema exists to carry and it is precisely the one that must not be required to move.
//! - **`euler_positive` / `euler_negative`** also move on every accepted deed, by exactly one — but
//!   by `(-1)^g` in *both* cases above. The pair records the grade the deed was written at, not
//!   what it did. It is a second always-mover and not a second witness.
//!
//! # The further deed
//!
//! One further cell, founded through [`GradedCausalComplex::found_cell`] — the same founder the
//! form codec mounts through, which refuses `d d != 0`, a mis-graded face, an uncaused cell and an
//! unreduced coefficient. A deed that would break the incidence is refused and the body stays
//! exactly where it was.
//!
//! Boundary coefficients travel as a pair of nonnegative counts rather than a signed scalar,
//! because `algebraic.rs` opens by saying so: *"Counts are primary. Signed coefficients are their
//! exact group completion."* A pair whose two counts are equal declares no incidence and is
//! refused rather than silently dropped.

use std::collections::BTreeSet;

use holonic_engine::algebraic::{
    CausalCellId, CausalChain, ComparativeMultiplicity, GradedCausalComplex,
};
use holonic_engine::causal::EventId;
use holonic_engine::graded_complex_form::{
    decode_native_bytes, encode_native_bytes, GRADED_COMPLEX_FORM_LAYOUT_VERSION,
};
use holonic_engine::rebase_invariants::{
    invariants_agree, rebase_invariants_with_schedule, PivotRule, ReadingSchedule, RebaseInvariants,
};
use num_bigint::BigUint;

use crate::census::Census;
use crate::deed::{deed_head, open_deed, put_bytes, put_u64, Cursor};
use crate::plate::SchemaTag;
use crate::schema::{LitBody, PlateSchema};

/// `RBIN`, the form codec's own magic read as ASCII.
pub const REBASE_TAG: SchemaTag = match SchemaTag::new(*b"RBIN") {
    Some(tag) => tag,
    None => panic!("RBIN is four octets of [A-Z0-9]"),
};

/// The codec's own layout version, **read from the codec** rather than copied. If the engine bumps
/// the graded-complex wire, this reader stops holding the old plates and says so by version instead
/// of mounting them as the version it does hold.
pub const REBASE_SCHEMA_VERSION: u32 = GRADED_COMPLEX_FORM_LAYOUT_VERSION;

pub struct RebaseSchema;

pub static REBASE_SCHEMA: RebaseSchema = RebaseSchema;

impl PlateSchema for RebaseSchema {
    fn tag(&self) -> SchemaTag {
        REBASE_TAG
    }

    fn version(&self) -> u32 {
        REBASE_SCHEMA_VERSION
    }

    fn shape(&self) -> &'static str {
        "graded causal incidence with a rebase-invariants reading: cells, grades, source events \
         and exact oriented boundary chains on the wire; Smith-normal-form ranks, free ranks, \
         torsion coefficients and the Euler characteristic in the census, recomputed on mount \
         under all three pivot rules"
    }

    fn deed_shape(&self) -> &'static str {
        "one further cell, founded through the incidence's own founder:\n    \
         u64 name_octets, name       (UTF-8)\n    \
         u64 grade                   (chain degree; grade 0 takes no boundary)\n    \
         u64 events, each u64        (source occurrences; at least one -- an uncaused cell \
         refuses)\n    \
         u64 terms, each { u64 cell, u64 positive, u64 negative }\n                                \
         (counts are primary; equal counts declare no incidence and refuse)"
    }

    fn relight(&self, form: &[u8]) -> Result<Box<dyn LitBody>, String> {
        Ok(Box::new(RebaseBody::mount(form)?))
    }
}

/// A re-lit incidence, live: it can be asked for its reading and it can be founded on.
pub struct RebaseBody {
    complex: GradedCausalComplex,
}

impl RebaseBody {
    /// Mount stored octets through the engine's real founder. Every cell goes through
    /// `found_cell`, so a form whose incidence does not close does not become a body.
    pub fn mount(form: &[u8]) -> Result<Self, String> {
        let complex = decode_native_bytes(form).map_err(|refusal| refusal.to_string())?;
        Ok(Self { complex })
    }

    /// The whole reading — every grade, every free rank, every torsion coefficient at full width,
    /// and the three pivot walks the cross-check ran over.
    ///
    /// This is what travels to a next organ, and it is what [`LitBody::census`] counts, so it is on
    /// the path of every deposit and every resume rather than beside it. The census is a
    /// declaration of `u64`s and is never a substitute for this.
    pub fn reading(&self) -> Result<RebaseReading, String> {
        reading_of(&self.complex)
    }
}

/// One reading, with the three computations it was cross-checked across.
///
/// `invariants` is the artifact. `schedules` is the **evidence that the cross-check was a
/// cross-check**: one entry per declared [`PivotRule`], each carrying the exact pivot positions
/// that rule's reductions chose. Three identical schedules mean one computation compared with
/// itself twice — the shape this pair exists to make visible, and the shape every fixture in this
/// project had until `staggered_attachment` was founded.
///
/// A schedule is a receiver coordinate. It is returned to be audited and never compared as an
/// invariant; [`invariants_agree`] does not read it and no census field is derived from it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RebaseReading {
    pub invariants: RebaseInvariants,
    pub schedules: Vec<ReadingSchedule>,
}

/// The reading, taken under every pivot rule and required to agree.
///
/// The refusal is a genuine falsifier of the reduction rather than a restatement of a theorem:
/// Smith normal form is unique up to units over a principal ideal domain, so a disagreement here
/// is a defect in `smith_normal_form`, which is exactly the class of defect a returned invariant
/// must not carry. It cannot fire while that reduction is correct, and that is what makes the
/// *schedules* the thing to check — see [`RebaseReading`].
fn reading_of(complex: &GradedCausalComplex) -> Result<RebaseReading, String> {
    let mut settled: Option<RebaseInvariants> = None;
    let mut schedules = Vec::new();
    for rule in PivotRule::ALL {
        let (reading, schedule) =
            rebase_invariants_with_schedule(complex, rule).map_err(|error| format!("{error:?}"))?;
        schedules.push(schedule);
        match &settled {
            None => settled = Some(reading),
            Some(first) => {
                if !invariants_agree(first, &reading) {
                    return Err(format!(
                        "the pivot rule {rule:?} moved the returned invariants; a solver \
                         coordinate reached a returned invariant and this reading is not one. \
                         settled: {:?}; moved: {:?}",
                        first.grades, reading.grades
                    ));
                }
            }
        }
    }
    let invariants = settled.ok_or_else(|| "no pivot rule was declared".to_owned())?;
    Ok(RebaseReading {
        invariants,
        schedules,
    })
}

/// Carry a signed Euler characteristic as a pair of `u64`s, at most one nonzero.
///
/// A total bijection from `i64` onto `{(p, 0)} u {(0, n)}`, with `0 <-> (0, 0)`. `i64::MIN` is in
/// range: its magnitude is `2^63`, which a `u64` holds exactly.
pub const fn encode_euler(characteristic: i64) -> (u64, u64) {
    if characteristic >= 0 {
        (characteristic as u64, 0)
    } else {
        (0, characteristic.unsigned_abs())
    }
}

/// The inverse. `None` for any pair outside the image — both nonzero, or a magnitude no `i64`
/// carries. A census whose two Euler fields are both nonzero declares something this encoding
/// cannot mean, and reading it as either one would be a guess.
pub const fn decode_euler(positive: u64, negative: u64) -> Option<i64> {
    match (positive, negative) {
        (positive, 0) => {
            if positive <= i64::MAX as u64 {
                Some(positive as i64)
            } else {
                None
            }
        }
        (0, negative) => {
            if negative <= (i64::MAX as u64) + 1 {
                // `negative == 2^63` casts to `i64::MIN`, whose negation is itself; both are the
                // one value `-2^63`, which is what this arm means.
                Some((negative as i64).wrapping_neg())
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Count what the reading returned.
///
/// **There is no guard in here, and the two that were here until 2026-08-08 were removed rather
/// than kept as cheap insurance.** Both were forced identities that no input could fire, and a
/// theorem asserted as if it were evidence reads as rigour while carrying none:
///
/// - `Σ_k cells_at(k) == complex.cells().len()`. `rebase_invariants_on` builds grades `0..=top`
///   where `top` is the maximum cell grade over the same population, so the sum ranges over a
///   partition of that population. It is the loop's own bounds restated.
/// - `Σ(-1)^k b_k == Σ(-1)^k n_k`. With `b_k = n_k - r_k - r_{k+1}` the difference telescopes to
///   `r_0 + (-1)^top r_{top+1}`, and both vanish: `d_0` has no rows and `d_{top+1}` has no columns,
///   so both reductions return rank zero. The two Euler figures are two projections of one vector,
///   not two frames.
///
/// Inverting either branch failed eleven tests, which proves only that the branch is on the live
/// path — it was always false, and no input reaches the other side. The real second frame is the
/// plate's: the depositor's declared census against the resumer's recomputed one, which
/// `a_forged_rbin_census_refuses_and_names_the_field` fires.
fn census_of(reading: &RebaseReading) -> Result<Census, String> {
    let invariants = &reading.invariants;

    let mut cells = 0u64;
    let mut boundary_rank_total = 0u64;
    let mut betti_total = 0u64;
    let mut torsion_factors = 0u64;
    for grade in &invariants.grades {
        cells += grade.cells as u64;
        boundary_rank_total += grade.boundary_rank as u64;
        betti_total += grade.betti as u64;
        torsion_factors += grade.torsion.len() as u64;
    }

    let (euler_positive, euler_negative) = encode_euler(invariants.euler_characteristic());
    Census::found([
        ("cells", cells),
        ("grades", invariants.grades.len() as u64),
        ("boundary_rank_total", boundary_rank_total),
        ("betti_total", betti_total),
        ("torsion_factors", torsion_factors),
        ("euler_positive", euler_positive),
        ("euler_negative", euler_negative),
    ])
    .map_err(|refusal| refusal.to_string())
}

impl LitBody for RebaseBody {
    fn form(&self) -> Result<Vec<u8>, String> {
        encode_native_bytes(&self.complex).map_err(|refusal| refusal.to_string())
    }

    fn census(&self) -> Result<Census, String> {
        census_of(&self.reading()?)
    }

    fn present(&mut self, deed: &[u8]) -> Result<(), String> {
        let founding = RebaseDeed::decode(deed)?;
        let mut source_events: BTreeSet<EventId> = BTreeSet::new();
        for event in &founding.source_events {
            if !source_events.insert(EventId(*event)) {
                return Err(format!(
                    "the deed repeats the source occurrence {event}; an occurrence recurs, a \
                     source event does not"
                ));
            }
        }
        let mut boundary = CausalChain::default();
        for term in &founding.boundary {
            if term.positive == term.negative {
                return Err(format!(
                    "the deed's boundary term on cell {} declares {} occurrences on each hand, \
                     which is no incidence at all; a chain does not retain a zero coefficient",
                    term.cell, term.positive
                ));
            }
            boundary.add_term(
                CausalCellId(term.cell),
                ComparativeMultiplicity::new(
                    BigUint::from(term.positive),
                    BigUint::from(term.negative),
                ),
            );
        }
        // The founder is the aperture: `d d != 0`, a mis-graded face, an uncaused cell and an
        // unreduced coefficient are all refused there, and a refusal leaves the incidence
        // untouched.
        self.complex
            .found_cell(founding.name, source_events, founding.grade, boundary)
            .map_err(|error| format!("{error}"))?;
        Ok(())
    }
}

/// One oriented incidence of a deed's boundary, as the two nonnegative counts the engine's
/// coefficient carrier is founded on.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BoundaryTerm {
    pub cell: u64,
    pub positive: u64,
    pub negative: u64,
}

/// One further deed for a graded causal incidence, in its exact wire.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RebaseDeed {
    pub name: String,
    pub grade: u32,
    pub source_events: Vec<u64>,
    pub boundary: Vec<BoundaryTerm>,
}

impl RebaseDeed {
    pub fn encode(&self) -> Vec<u8> {
        let mut octets = deed_head(REBASE_TAG);
        put_bytes(&mut octets, self.name.as_bytes());
        put_u64(&mut octets, u64::from(self.grade));
        put_u64(&mut octets, self.source_events.len() as u64);
        for event in &self.source_events {
            put_u64(&mut octets, *event);
        }
        put_u64(&mut octets, self.boundary.len() as u64);
        for term in &self.boundary {
            put_u64(&mut octets, term.cell);
            put_u64(&mut octets, term.positive);
            put_u64(&mut octets, term.negative);
        }
        octets
    }

    pub fn decode(deed: &[u8]) -> Result<Self, String> {
        let mut cursor: Cursor<'_> = open_deed(deed, REBASE_TAG)?;
        let name = cursor.utf8("cell name")?;
        let grade = cursor.u64()?;
        let grade = u32::try_from(grade)
            .map_err(|_| format!("the deed declares grade {grade}, which is not a chain degree"))?;
        let event_count = cursor.usize()?;
        let mut source_events = Vec::new();
        for _ in 0..event_count {
            source_events.push(cursor.u64()?);
        }
        let term_count = cursor.usize()?;
        let mut boundary = Vec::new();
        for _ in 0..term_count {
            let cell = cursor.u64()?;
            let positive = cursor.u64()?;
            let negative = cursor.u64()?;
            boundary.push(BoundaryTerm {
                cell,
                positive,
                negative,
            });
        }
        cursor.finish()?;
        Ok(Self {
            name,
            grade,
            source_events,
            boundary,
        })
    }
}
