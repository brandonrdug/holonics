//! **The engine's enclosure scatter, declared as a D3 incidence.**
//!
//! [D3](../../../docs/plans/THE_EXACT_DEVICE_LAW_IS_CONSTRUCTED.md) names
//! `kernels/normal_enclosure_ports.cuh::section_normal_enclosure_scatter_section` the one true
//! `(region, slot) -> global index` scatter in the engine's hand-written section set, and the
//! cleanest candidate instance of `holonics_cuda::section_layout`'s generated gather / local apply /
//! coloured scatter triple. This module is that declaration, and its tests are the proof that the
//! generated triple reproduces the hand-written kernel's coordinate result exactly.
//!
//! **What the hand-written kernel does.** `ResidentNormalEnclosureSection::scatter_components`
//! takes a section of `rows` enclosures, each `width` real coordinates plus a radius word, and a
//! declared injective destination row per source row. Source row `r` contributes its window
//! `[start, start + count)` to destination row `d[r]`, which is the global coordinate range
//! `[d[r] * count, d[r] * count + count)`. The kernel refuses a duplicate destination at run time
//! through an occupancy flag in the unpublished upper packet; the generated receipt refuses the
//! same table at construction, names the colliding pair, and needs no flag.
//!
//! **How it is an instance.** `SectionLayout` applies one operator on one common field: the gather
//! index *is* the address table and the scatter is its transpose, so a map whose source and
//! destination are different spaces is declared by embedding **both** in one address extent and
//! carrying the map inside the region's local block. Here the common field is the flat source
//! section followed by the flat destination field,
//!
//! ```text
//! address(source row r, coordinate j) = r * width + j                 for r < rows, j < width
//! address(destination row t, coordinate j) = rows * width + t * count + j
//! ```
//!
//! region `r` is the `2 * count` slots
//! `[r*width+start .. r*width+start+count) ++ [rows*width + d[r]*count .. + count)`, and the local
//! operator is the `2c x 2c` block `L[c + j][j] = 1`, every other entry zero — the window
//! projection followed by the placement. Then `scatterAdd(applyLocal(gather x))` leaves the source
//! half of the field zero and the destination half carrying exactly the scattered window, which is
//! the hand-written kernel's coordinate result. The incidence is injective (distinct source
//! windows, distinct destination rows), so the receipt is `ScatterRequest::Injective` and no
//! colouring or accumulation is involved.
//!
//! **What the generated triple does not carry, and what it would owe.** Two things, both exact and
//! both named rather than implied.
//!
//! 1. **The word.** The engine's coordinate is a 128-bit signed `wide`, held as an `int64` low/high
//!    pair, with a `REFUSED_CARRIER` overflow refusal. The generated device arm realizes exactly
//!    `Z/(2^61 - 1)` in one `u64` word. The two agree **bit for bit** on any coordinate word that
//!    is non-negative and below `2^61 - 1`, because the local operator here is a permutation of the
//!    gathered words and no ring operation but `x * 1 + 0` touches them; outside that window the
//!    generated arm folds a residue where the engine keeps an exact integer. A general adoption
//!    therefore owes a second device ring — 128-bit signed words carried as two device words, with
//!    the engine's own overflow refusal — not a wider modulus.
//! 2. **The radius.** Each engine enclosure carries one radius word after its coordinates, and the
//!    scattered output's radius is the **sum of the participating source radii**: one further
//!    address every region accumulates into, under exact integer addition with an overflow refusal.
//!    That is `AccumulationLaw::IntegerAdd`, which `SectionKernels::enact` refuses on device for
//!    the stated reason (a kernel cannot raise the overflow refusal the law owes). The declaration
//!    below carries the coordinates only, and says so.
//!
//! Neither is a defect in either owner; they are the exact seam, and no engine result is changed by
//! this module. Nothing here is on a production path: it is the declaration and its cross-check.

use holonics::ratio::ring::ModularWords;
use holonics_cuda::section_layout::{
    IncidenceDeclaration, LocalOperator, SectionClause, SectionRefusal, Sectioned,
};

/// Declare the incidence of one `scatter_components` call over the common source/destination
/// field described in this module's documentation.
///
/// Every clause `ResidentNormalEnclosureSection::scatter_components` checks is checked here, at the
/// declaration, and each product that could leave `usize` or the `u32` index wire is checked before
/// any table is built: the address table's length is `rows * 2 * count`, and the caller's own
/// `destinations` slice bounds `rows`.
pub fn enclosure_scatter_incidence(
    width: usize,
    start: usize,
    count: usize,
    destinations: &[usize],
    output_rows: usize,
) -> Sectioned<IncidenceDeclaration> {
    let refuse = |what: String| Err(SectionRefusal::new(SectionClause::AddressWithinExtent, what));
    let rows = destinations.len();
    if rows == 0 || count == 0 || !count.is_multiple_of(2) || !start.is_multiple_of(2) || output_rows == 0 {
        return refuse(format!(
            "the engine's scatter carries a positive even window and a positive destination \
             population; got rows {rows}, start {start}, count {count}, output rows {output_rows}"
        ));
    }
    if start.checked_add(count).is_none_or(|end| end > width) {
        return refuse(format!(
            "the window {start}..+{count} leaves a row of {width} coordinates"
        ));
    }
    let source_words = rows
        .checked_mul(width)
        .ok_or_else(|| SectionRefusal::new(SectionClause::GlobalExtentWire, "source extent"))?;
    let destination_words = output_rows
        .checked_mul(count)
        .ok_or_else(|| SectionRefusal::new(SectionClause::GlobalExtentWire, "destination extent"))?;
    let global_extent = source_words.checked_add(destination_words).ok_or_else(|| {
        SectionRefusal::new(SectionClause::GlobalExtentWire, "common field extent")
    })?;
    if global_extent > u32::MAX as usize {
        return Err(SectionRefusal::new(
            SectionClause::GlobalExtentWire,
            format!("a common field of {global_extent} addresses leaves the u32 index wire"),
        ));
    }
    for (row, destination) in destinations.iter().enumerate() {
        if *destination >= output_rows {
            return refuse(format!(
                "source row {row} declares destination {destination}; there are {output_rows} \
                 destination rows"
            ));
        }
    }
    // Injectivity is decided by ordering the caller's own `destinations`, never by a `seen` table
    // indexed by the declared `output_rows`: that table would be an allocation sized by a declared
    // number, which this construction does not make.
    let mut ordered = destinations.to_vec();
    ordered.sort_unstable();
    if let Some(repeated) = ordered.windows(2).find(|pair| pair[0] == pair[1]) {
        return refuse(format!(
            "two source rows repeat destination {}; this scatter is injective",
            repeated[0]
        ));
    }
    // The only allocation here is the address table the declaration returns, and the caller must
    // hold it either way. Its length is checked against the same `u32` slot wire
    // `IncidenceDeclaration` admits **before** a byte is reserved.
    let slots = rows
        .checked_mul(2)
        .and_then(|n| n.checked_mul(count))
        .filter(|slots| *slots <= u32::MAX as usize)
        .ok_or_else(|| {
            SectionRefusal::new(
                SectionClause::SlotWire,
                format!("{rows} regions of {count} placed coordinates leave the u32 slot wire"),
            )
        })?;
    let mut addresses: Vec<u32> = Vec::with_capacity(slots);
    for (row, destination) in destinations.iter().enumerate() {
        for j in 0..count {
            addresses.push((row * width + start + j) as u32);
        }
        for j in 0..count {
            addresses.push((source_words + destination * count + j) as u32);
        }
    }
    IncidenceDeclaration::uniform(global_extent, 2 * count, addresses)
}

/// The local block of that declaration: the `2c x 2c` window projection followed by the placement,
/// `L[c + j][j] = 1` and every other entry zero. Over `Z/(2^61 - 1)` the one coefficient is the
/// canonical `1`, so the whole table is canonical by construction.
///
/// Unlike [`LocalOperator::dense`], which takes its table by value, this one *builds* a dense
/// `(2c)^2` table from the declared `count`, so it takes the caller's own `entry_ceiling` and
/// refuses past it under [`SectionClause::WorkCeiling`] **before** a single element is reserved.
/// A caller that has a layout in hand passes `layout.tile().max_width().pow(2)`; nothing here is
/// sized by a declared number alone.
pub fn window_placement_operator(count: usize, entry_ceiling: usize) -> Sectioned<LocalOperator<u64>> {
    let width = count.checked_mul(2).ok_or_else(|| {
        SectionRefusal::new(
            SectionClause::LocalOperatorWidth,
            format!("a local block of {count} placed coordinates leaves the wire"),
        )
    })?;
    let entries = width.checked_mul(width).ok_or_else(|| {
        SectionRefusal::new(
            SectionClause::LocalOperatorWidth,
            format!("a {width}x{width} local block leaves the wire"),
        )
    })?;
    if entries > entry_ceiling {
        return Err(SectionRefusal::new(
            SectionClause::WorkCeiling,
            format!(
                "a {width}x{width} local block is {entries} entries; the declared ceiling is \
                 {entry_ceiling}"
            ),
        ));
    }
    let mut table = vec![0u64; entries];
    for j in 0..count {
        table[(count + j) * width + j] = 1;
    }
    LocalOperator::dense_canonical(width, table, &ModularWords::MERSENNE61)
}

// ===============================================================================================
// Issue #50: what the generated tile boundary supports, and what the exact algebra needs of it
// ===============================================================================================

/// **The clause that blocks each of Issue #50's two operations at the generated tile boundary.**
///
/// [definition] The contract forbids inferring a solver from the presence of a generated modular
/// matrix product, and this is the declaration that keeps that honest: each operation is named
/// against the clause of `holonics_cuda::section_layout` it does not satisfy, and
/// [`self::tests`] exhibits the second one rather than asserting it.
///
/// Neither is a defect in either owner. `SectionLayout` generates `Σ_r P_rᵀ L_r P_r` faithfully;
/// these are two operations that are not of that form as the declaration stands.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GeneratedTileObstacle {
    /// **A modular pivot sweep is not a linear local apply.**
    ///
    /// `SectionLayout::apply_local_reference` and the generated `APPLY` entry compute
    /// `L · (gathered x)` for a table `L` fixed before the call. The elimination's update is
    /// `a_ij ← a_ij − m_i · a_kj`, whose multiplier `m_i = a_ik` is **read from the field**: the
    /// operation is bilinear in two gathered words where the generated apply is linear in one.
    /// No choice of `L` expresses it, and no schedule of launches does either, because `m_i`
    /// changes at every pivot.
    ///
    /// The extension this names is a generated entry whose local apply takes a *second* gathered
    /// operand — a rank-one update tile — with its own declared ring, `launch_law` requirement and
    /// exclusive-write partition per pivot. That is a new kernel, not a new caller.
    PivotSweepIsBilinear,
    /// **A contact assembly needs one local operator per region, not one shared by all.**
    ///
    /// `SectionLayout::assemble_dense` and `SectionKernels::enact` both take a single
    /// `&LocalOperator<V>`, and every region uses its leading `width(r) × width(r)` block of *that*
    /// table. `M_contact = Σ_f w_f J_fᵀ D_f J_f` is exactly the assembly identity the layout names,
    /// with region `f` the face's support — but `L_f = w_f J_fᵀ D_f J_f` differs per face, and two
    /// bars in different directions have different blocks.
    ///
    /// The extension this names is a per-region coefficient offset in the staged table — one
    /// `u32` offsets array beside the existing region offsets — so the generated apply reads
    /// `L_r` instead of `L`. That is the smaller of the two extensions and it is the one that would
    /// place the contact assembly, not the elimination, on the card.
    SharedLocalOperator,
}

impl GeneratedTileObstacle {
    /// The operation this obstacle blocks, and the clause it violates, in one line each.
    pub const fn declared(self) -> (&'static str, &'static str) {
        match self {
            Self::PivotSweepIsBilinear => (
                "prime_image_algebra::PrimeImage::reduce, one chart's modular Gauss-Jordan",
                "the generated local apply is linear in one gathered operand",
            ),
            Self::SharedLocalOperator => (
                "holonic_interaction::ContactDissipation::assemble, the sparse contact assembly",
                "one LocalOperator is shared by every region of a SectionLayout",
            ),
        }
    }
}

#[cfg(test)]
mod tests;
