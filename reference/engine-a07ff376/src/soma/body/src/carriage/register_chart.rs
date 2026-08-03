//! The §XXXII-c lineage-local REGISTER as one substrate-neutral OWN face.
//!
//! The boundary may reserve more cells than the current has accepted. The register begins at axis
//! one regardless of that aperture and changes its gauge only on its own arrive/depart events. The
//! header dies with OWN at the receiving edge; K and SLEEP carry none of it.

use crate::chart::Register;
use crate::manifold;
use crate::medium::{FeltTerm, RegionalForm, FORM_WORDS};
use crate::num;
use crate::place::{self, Place};

use super::WordSeam;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct RegisterFace {
    pub axis: u32,
    pub occupancy: u64,
    pub releases: u64,
    pub narrows: u64,
}

impl RegisterFace {
    pub const BORN: RegisterFace = RegisterFace {
        axis: 1,
        occupancy: 0,
        releases: 0,
        narrows: 0,
    };

    #[inline]
    fn register(self) -> Register {
        Register {
            axis: self.axis,
            occupancy: self.occupancy,
        }
    }

    #[inline]
    fn take_register(&mut self, register: Register) {
        self.axis = register.axis;
        self.occupancy = register.occupancy;
    }
}

#[inline(always)]
fn read<S: WordSeam>(words: &[u32], at: usize) -> u32 {
    unsafe { S::read_u32_unchecked(words, at) }
}

#[inline(always)]
fn store<S: WordSeam>(words: &mut [u32], at: usize, value: u32) {
    unsafe { S::store_u32_unchecked(words, at, value) }
}

#[inline]
fn read_u64<S: WordSeam>(words: &[u32], lo: usize, hi: usize) -> u64 {
    read::<S>(words, lo) as u64 | ((read::<S>(words, hi) as u64) << 32)
}

#[inline]
fn store_u64<S: WordSeam>(words: &mut [u32], lo: usize, hi: usize, value: u64) {
    store::<S>(words, lo, value as u32);
    store::<S>(words, hi, (value >> 32) as u32);
}

pub(super) fn read_face<S: WordSeam>(words: &[u32], header: usize) -> RegisterFace {
    let axis = read::<S>(words, header + manifold::OWN_REGISTER_AXIS);
    if axis == 0 {
        RegisterFace::BORN
    } else {
        RegisterFace {
            axis,
            occupancy: read_u64::<S>(
                words,
                header + manifold::OWN_REGISTER_OCCUPANCY_LO,
                header + manifold::OWN_REGISTER_OCCUPANCY_HI,
            ),
            releases: read_u64::<S>(
                words,
                header + manifold::OWN_REGISTER_RELEASES_LO,
                header + manifold::OWN_REGISTER_RELEASES_HI,
            ),
            narrows: read_u64::<S>(
                words,
                header + manifold::OWN_REGISTER_NARROWS_LO,
                header + manifold::OWN_REGISTER_NARROWS_HI,
            ),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum DepositResult {
    Accepted,
    NeedsOwnRecast { old_axis: u32, new_axis: u32 },
    Invalid,
}

pub(super) fn store_face<S: WordSeam>(words: &mut [u32], header: usize, face: RegisterFace) {
    store::<S>(words, header + manifold::OWN_REGISTER_AXIS, face.axis);
    store_u64::<S>(
        words,
        header + manifold::OWN_REGISTER_OCCUPANCY_LO,
        header + manifold::OWN_REGISTER_OCCUPANCY_HI,
        face.occupancy,
    );
    store_u64::<S>(
        words,
        header + manifold::OWN_REGISTER_RELEASES_LO,
        header + manifold::OWN_REGISTER_RELEASES_HI,
        face.releases,
    );
    store_u64::<S>(
        words,
        header + manifold::OWN_REGISTER_NARROWS_LO,
        header + manifold::OWN_REGISTER_NARROWS_HI,
        face.narrows,
    );
}

#[inline]
fn cell_at(cell_base: usize, grip: usize) -> usize {
    cell_base + grip * manifold::OWN_CELL_WORDS
}

#[inline]
fn cell_live<S: WordSeam>(words: &[u32], cell_base: usize, grip: usize) -> bool {
    read::<S>(words, cell_at(cell_base, grip) + manifold::OWN_CELL_LIVE) != 0
}

#[inline]
fn clear_cell<S: WordSeam>(words: &mut [u32], at: usize) {
    let mut word = 0usize;
    while word < manifold::OWN_CELL_WORDS {
        store::<S>(words, at + word, 0);
        word += 1;
    }
}

#[inline]
fn unpack_form<S: WordSeam>(words: &[u32], at: usize) -> RegionalForm {
    unsafe { RegionalForm::unpack_unchecked_with::<S>(words, at) }
}

#[inline]
fn store_form<S: WordSeam>(words: &mut [u32], at: usize, form: RegionalForm) {
    let mut word = 0usize;
    while word < FORM_WORDS {
        store::<S>(words, at + word, form.packed_word(word));
        word += 1;
    }
}

#[inline]
fn founder<S: WordSeam>(words: &[u32], at: usize) -> Place {
    (
        num::read_cog_with::<S>(words, at + manifold::OWN_CELL_POSITION),
        num::read_cog_with::<S>(
            words,
            at + manifold::OWN_CELL_POSITION + manifold::COG_WORDS,
        ),
    )
}

#[inline]
fn write_founder<S: WordSeam>(words: &mut [u32], at: usize, position: Place) {
    let mut word = 0usize;
    while word < manifold::COG_WORDS {
        store::<S>(
            words,
            at + manifold::OWN_CELL_POSITION + word,
            manifold::cog_packed_word(position.0, word),
        );
        store::<S>(
            words,
            at + manifold::OWN_CELL_POSITION + manifold::COG_WORDS + word,
            manifold::cog_packed_word(position.1, word),
        );
        word += 1;
    }
}

fn narrow_cascade<S: WordSeam>(
    words: &mut [u32],
    cell_base: usize,
    capacity_cells: usize,
    face: &mut RegisterFace,
) {
    loop {
        if face.axis <= 1 {
            return;
        }
        let tooth = crate::chart::hand(face.axis >> 1);
        if face.occupancy & !(tooth - 1) != 0 {
            return;
        }

        let new_axis = face.axis >> 1;
        let cells = face.axis as usize * face.axis as usize;
        let mut grip = 0usize;
        while grip < cells {
            let at = cell_at(cell_base, grip);
            if read::<S>(words, at + manifold::OWN_CELL_LIVE) != 0
                && crate::chart::zero_extended_source(grip as u32, new_axis, face.axis)
                    != Some(place::ground(founder::<S>(words, at), new_axis as i64))
            {
                return;
            }
            grip += 1;
        }
        if !manifold::narrow_own_cells_in_place_with::<S>(
            words,
            cell_base,
            capacity_cells,
            face.axis,
            new_axis,
        ) {
            return;
        }
        let retired = face.register().digit_retired();
        face.take_register(retired);
        face.narrows = face.narrows.wrapping_add(1);
    }
}

/// Deposit one term through the exact host-register law using the current's reserved card words.
/// The active axis is event-derived; `capacity_cells` is only the present mounting aperture. A
/// required larger axis freezes the enclosing caller in its carrier and returns without mutating
/// the row or face; the boundary supplies the exact recast row before relaunch.
pub(super) fn deposit<S: WordSeam>(
    words: &mut [u32],
    cell_base: usize,
    capacity_cells: usize,
    face: &mut RegisterFace,
    position: Place,
    term: FeltTerm,
) -> DepositResult {
    let active_cells = face.axis as usize * face.axis as usize;
    if active_cells > capacity_cells {
        return DepositResult::Invalid;
    }

    let mut grip = place::ground(position, face.axis as i64) as usize;
    let mut at = cell_at(cell_base, grip);
    if !cell_live::<S>(words, cell_base, grip) {
        loop {
            let current = face.register();
            let (next, carried) = current.arrive();
            if !carried {
                face.take_register(next);
                break;
            }
            let Some(new_axis) = face.axis.checked_mul(2) else {
                return DepositResult::Invalid;
            };
            let Some(new_cells) = (new_axis as usize).checked_mul(new_axis as usize) else {
                return DepositResult::Invalid;
            };
            if new_cells > capacity_cells {
                return DepositResult::NeedsOwnRecast {
                    old_axis: face.axis,
                    new_axis,
                };
            }
            if !manifold::zero_extend_own_cells_in_place_with::<S>(
                words,
                cell_base,
                capacity_cells,
                face.axis,
                new_axis,
            ) {
                return DepositResult::Invalid;
            }
            // The pending infall is re-judged at the climbed hand. As in the host Medium, the
            // tentative old-hand increment does not become the new hand's occupancy.
            let digit = current.digit();
            face.take_register(digit);
            grip = place::ground(position, face.axis as i64) as usize;
            at = cell_at(cell_base, grip);
            if cell_live::<S>(words, cell_base, grip) {
                break;
            }
        }
        if !cell_live::<S>(words, cell_base, grip) {
            write_founder::<S>(words, at, position);
        }
    }

    let form_at = at + manifold::OWN_CELL_FORM;
    let form = unpack_form::<S>(words, form_at).deposit(term);
    let (same, other) = form.resultant();
    let (this_way, that_way) = form.fiber();
    if same.mag == 0
        && other.mag == 0
        && this_way == crate::num::Rung::ZERO
        && that_way == crate::num::Rung::ZERO
    {
        clear_cell::<S>(words, at);
        let (register, _borrowed) = face.register().depart();
        face.take_register(register);
        face.releases = face.releases.wrapping_add(1);
        narrow_cascade::<S>(words, cell_base, capacity_cells, face);
        return DepositResult::Accepted;
    }

    store_form::<S>(words, form_at, form);
    store::<S>(words, at + manifold::OWN_CELL_LIVE, 1);
    DepositResult::Accepted
}

/// Validate one safe host/reference register row before mutation. The reserved tail is required to
/// stay all-zero, so capacity cannot masquerade as occupied gauge. Occupancy is exactly the live
/// grip count at the accepted hand.
fn row_is_canonical_with_pending_digit(
    words: &[u32],
    header: usize,
    capacity_cells: usize,
    allow_pending_digit: bool,
) -> bool {
    let Some(cell_words) = capacity_cells.checked_mul(manifold::OWN_CELL_WORDS) else {
        return false;
    };
    let cell_base = header + manifold::OWN_REGISTER_WORDS;
    let Some(end) = cell_base.checked_add(cell_words) else {
        return false;
    };
    if end > words.len() {
        return false;
    }
    let axis = words[header + manifold::OWN_REGISTER_AXIS];
    if axis == 0 {
        return words[header..end].iter().all(|word| *word == 0);
    }
    if !axis.is_power_of_two() {
        return false;
    }
    let Some(active_cells) = (axis as usize).checked_mul(axis as usize) else {
        return false;
    };
    if active_cells > capacity_cells {
        return false;
    }
    let occupancy = words[header + manifold::OWN_REGISTER_OCCUPANCY_LO] as u64
        | ((words[header + manifold::OWN_REGISTER_OCCUPANCY_HI] as u64) << 32);
    let mut live = 0u64;
    let mut grip = 0usize;
    while grip < capacity_cells {
        let at = cell_at(cell_base, grip);
        if grip < active_cells {
            let cell_live = words[at + manifold::OWN_CELL_LIVE];
            if cell_live > 1
                || RegionalForm::unpack_compact_checked(words, at + manifold::OWN_CELL_FORM)
                    .is_err()
                || !crate::num::packed_cog_is_canonical(words, at + manifold::OWN_CELL_POSITION)
                || !crate::num::packed_cog_is_canonical(
                    words,
                    at + manifold::OWN_CELL_POSITION + manifold::COG_WORDS,
                )
            {
                return false;
            }
            if cell_live == 0 {
                if words[at..at + manifold::OWN_CELL_WORDS]
                    .iter()
                    .any(|word| *word != 0)
                {
                    return false;
                }
            } else {
                let Ok(form) =
                    RegionalForm::unpack_compact_checked(words, at + manifold::OWN_CELL_FORM)
                else {
                    return false;
                };
                if !form.occupied() {
                    return false;
                }
                let founder = manifold::own_cell_position(words, at);
                let mut ancestor_axis = 1u32;
                let mut construction_holds = false;
                while ancestor_axis <= axis {
                    let grounded = place::ground(founder, ancestor_axis as i64);
                    if crate::chart::zero_extend_grip(grounded, ancestor_axis, axis) == grip as u32
                    {
                        construction_holds = true;
                        break;
                    }
                    let Some(next) = ancestor_axis.checked_mul(2) else {
                        break;
                    };
                    ancestor_axis = next;
                }
                if !construction_holds {
                    return false;
                }
                live += 1;
            }
        } else if words[at..at + manifold::OWN_CELL_WORDS]
            .iter()
            .any(|word| *word != 0)
        {
            return false;
        }
        grip += 1;
    }
    if occupancy != live {
        return false;
    }

    // A wider, low-occupancy posture has two reachable causes. A surviving construction may block
    // the exact inverse section after a departure. Or the arrival which carried into this digit
    // may, when re-judged at the finer gauge, meet an existing zero-extended cell. In the latter
    // case the arrival changes that cell without adding occupancy: the new axis therefore stands
    // at exactly one below the retired hand. No departure occurred, so no narrow was owed. This is
    // not the pending-recast allowance below; the infall has already landed and its changed form is
    // part of the row.
    if axis > 1 {
        let new_axis = axis >> 1;
        let tooth = crate::chart::hand(new_axis);
        if occupancy & !(tooth - 1) == 0 {
            let mut barrier = false;
            let mut grip = 0usize;
            while grip < active_cells {
                let at = cell_at(cell_base, grip);
                if words[at + manifold::OWN_CELL_LIVE] != 0
                    && crate::chart::zero_extended_source(grip as u32, new_axis, axis)
                        != Some(place::ground(
                            manifold::own_cell_position(words, at),
                            new_axis as i64,
                        ))
                {
                    barrier = true;
                    break;
                }
                grip += 1;
            }
            let arrival_held_digit = occupancy.checked_add(1) == Some(tooth);
            let pending_digit =
                allow_pending_digit && active_cells == capacity_cells && arrival_held_digit;
            if !barrier && !arrival_held_digit && !pending_digit {
                return false;
            }
        }
    }
    true
}

pub(super) fn row_is_canonical(words: &[u32], header: usize, capacity_cells: usize) -> bool {
    row_is_canonical_with_pending_digit(words, header, capacity_cells, false)
}

pub(super) fn pending_row_is_canonical(
    words: &[u32],
    header: usize,
    capacity_cells: usize,
) -> bool {
    row_is_canonical_with_pending_digit(words, header, capacity_cells, true)
}

/// Prove the two and only two REGISTER postures of a frozen pending infall. Before the boundary
/// move, the ordinary exact row's arrival carries beyond its present extent. After the move, the
/// transient prepared digit is canonical only under the pending allowance and that same arrival no
/// longer carries. No arbitrary wide low-occupancy row can use the pending face as admission.
pub(super) fn pending_stage_is_formed<S: WordSeam>(
    words: &[u32],
    header: usize,
    capacity_cells: usize,
    face: RegisterFace,
    position: Place,
) -> bool {
    if !pending_row_is_canonical(words, header, capacity_cells) {
        return false;
    }
    let ordinary = row_is_canonical(words, header, capacity_cells);
    let prepared_cells = (face.axis as usize).checked_mul(face.axis as usize);
    let prepared_digit = face.axis > 1
        && prepared_cells == Some(capacity_cells)
        && face.occupancy.checked_add(1) == Some(crate::chart::hand(face.axis >> 1));
    let grip = place::ground(position, face.axis as i64) as usize;
    if grip >= capacity_cells {
        return false;
    }
    if cell_live::<S>(words, header + manifold::OWN_REGISTER_WORDS, grip) {
        return prepared_digit;
    }
    let (_, carried) = face.register().arrive();
    if carried {
        let Some(new_axis) = face.axis.checked_mul(2) else {
            return false;
        };
        let Some(new_cells) = (new_axis as usize).checked_mul(new_axis as usize) else {
            return false;
        };
        ordinary && new_cells > capacity_cells
    } else {
        prepared_digit
    }
}

/// Transactionally form the exact next digit outside the mounted row. The old row is immutable;
/// the fresh row must be zeroed and exactly `header + (2A)^2 cells`. Its header installs only the
/// already-caused digit. The pending infall itself remains unlanded and will be re-judged by the
/// same carriage after the boundary swaps rows.
pub(super) fn recast_exact(old: &[u32], fresh: &mut [u32]) -> Option<(u32, u32)> {
    if old.len() < manifold::OWN_REGISTER_WORDS
        || fresh.len() < manifold::OWN_REGISTER_WORDS
        || (old.len() - manifold::OWN_REGISTER_WORDS) % manifold::OWN_CELL_WORDS != 0
        || (fresh.len() - manifold::OWN_REGISTER_WORDS) % manifold::OWN_CELL_WORDS != 0
        || fresh.iter().any(|word| *word != 0)
    {
        return None;
    }
    let old_cells = (old.len() - manifold::OWN_REGISTER_WORDS) / manifold::OWN_CELL_WORDS;
    let face = read_face::<crate::seam::SliceWordSeam>(old, 0);
    let old_axis = face.axis;
    let new_axis = old_axis.checked_mul(2)?;
    let exact_old = (old_axis as usize).checked_mul(old_axis as usize)?;
    let exact_new = (new_axis as usize).checked_mul(new_axis as usize)?;
    if old_cells != exact_old
        || (fresh.len() - manifold::OWN_REGISTER_WORDS) / manifold::OWN_CELL_WORDS != exact_new
        || !row_is_canonical(old, 0, old_cells)
    {
        return None;
    }

    fresh[..manifold::OWN_REGISTER_WORDS].copy_from_slice(&old[..manifold::OWN_REGISTER_WORDS]);
    fresh[manifold::OWN_REGISTER_AXIS] = new_axis;
    manifold::zero_extend_own_cells(
        &old[manifold::OWN_REGISTER_WORDS..],
        &mut fresh[manifold::OWN_REGISTER_WORDS..],
        old_axis as i64,
        new_axis as i64,
    );
    pending_row_is_canonical(fresh, 0, exact_new).then_some((old_axis, new_axis))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::channel::WindingQuantum;
    use crate::manifold;
    use crate::num::{Cog, Rung};
    use crate::seam::SliceWordSeam;
    use crate::soul::Chi;

    fn ride(same: i64, other: i64) -> FeltTerm {
        FeltTerm {
            chi: Chi {
                same: Cog::lit(same),
                other: Cog::lit(other),
            },
            winding: WindingQuantum::None,
        }
    }

    #[test]
    fn the_reserved_register_breathes_to_its_byte_identical_seed_and_regrows() {
        const CAPACITY: usize = 16;
        let cell_base = manifold::OWN_REGISTER_WORDS;
        let mut words = std::vec![
            0u32;
            manifold::OWN_REGISTER_WORDS + CAPACITY * manifold::OWN_CELL_WORDS
        ];
        let born = words.clone();
        let position = manifold::wind(b"the breath");
        let mut face = RegisterFace::BORN;

        assert_eq!(
            deposit::<SliceWordSeam>(
                &mut words,
                cell_base,
                CAPACITY,
                &mut face,
                position,
                ride(3, 4),
            ),
            DepositResult::Accepted
        );
        assert_eq!((face.axis, face.occupancy), (2, 1));
        assert_eq!((face.releases, face.narrows), (0, 0));
        let first_grown_cells = words[cell_base..].to_vec();

        assert_eq!(
            deposit::<SliceWordSeam>(
                &mut words,
                cell_base,
                CAPACITY,
                &mut face,
                position,
                ride(-3, -4),
            ),
            DepositResult::Accepted
        );
        assert_eq!((face.axis, face.occupancy), (1, 0));
        assert_eq!((face.releases, face.narrows), (1, 1));
        assert!(words[cell_base..].iter().all(|word| *word == 0));

        assert_eq!(
            deposit::<SliceWordSeam>(
                &mut words,
                cell_base,
                CAPACITY,
                &mut face,
                position,
                ride(3, 4),
            ),
            DepositResult::Accepted
        );
        assert_eq!((face.axis, face.occupancy), (2, 1));
        assert_eq!(
            &words[cell_base..],
            first_grown_cells.as_slice(),
            "the cell construction regrows without a width ratchet"
        );

        store_face::<SliceWordSeam>(&mut words, 0, face);
        assert!(row_is_canonical(&words, 0, CAPACITY));
        assert_ne!(words, born, "the regrown current is contemporarily live");
    }

    #[test]
    fn a_rejudged_arrival_may_hold_the_digit_it_caused() {
        const CAPACITY: usize = 64;
        let cell_base = manifold::OWN_REGISTER_WORDS;
        let mut words = std::vec![
            0u32;
            manifold::OWN_REGISTER_WORDS + CAPACITY * manifold::OWN_CELL_WORDS
        ];
        let mut face = RegisterFace::BORN;
        let first = (Cog::lit(1), Cog::lit(1));
        let arriving = (Cog::lit(2), Cog::lit(2));

        assert_eq!(place::ground(first, 2), 0);
        assert_eq!(place::ground(arriving, 2), 3);
        assert_eq!(
            place::ground(arriving, 4),
            crate::chart::zero_extend_grip(place::ground(first, 2), 2, 4),
            "the positions differ before the carry and meet only after its finer re-judgment"
        );

        assert_eq!(
            deposit::<SliceWordSeam>(
                &mut words,
                cell_base,
                CAPACITY,
                &mut face,
                first,
                ride(3, 4),
            ),
            DepositResult::Accepted
        );
        assert_eq!((face.axis, face.occupancy), (2, 1));
        assert_eq!(
            deposit::<SliceWordSeam>(
                &mut words,
                cell_base,
                CAPACITY,
                &mut face,
                arriving,
                ride(5, 6),
            ),
            DepositResult::Accepted
        );
        assert_eq!((face.axis, face.occupancy), (4, 1));
        assert_eq!((face.releases, face.narrows), (0, 0));

        store_face::<SliceWordSeam>(&mut words, 0, face);
        assert!(
            row_is_canonical(&words, 0, CAPACITY),
            "the landed collision, not a departure or a fabricated resident poll, holds the digit"
        );

        let old_grip = place::ground(first, 4) as usize;
        let wide_grip = crate::chart::zero_extend_grip(old_grip as u32, 4, 8) as usize;
        let old_at = cell_at(cell_base, 0);
        let wide_at = cell_at(cell_base, wide_grip);
        let cell = words[old_at..old_at + manifold::OWN_CELL_WORDS].to_vec();
        words[old_at..old_at + manifold::OWN_CELL_WORDS].fill(0);
        words[wide_at..wide_at + manifold::OWN_CELL_WORDS].copy_from_slice(&cell);
        words[manifold::OWN_REGISTER_AXIS] = 8;
        assert_eq!(
            crate::chart::zero_extended_source(wide_grip as u32, 4, 8),
            Some(old_grip as u32)
        );
        assert!(
            !row_is_canonical(&words, 0, CAPACITY),
            "the arrival-held exception admits only the exact carried hand"
        );
    }

    #[test]
    fn winding_prevents_release_after_exact_resultant_cancellation() {
        const CAPACITY: usize = 4;
        let cell_base = manifold::OWN_REGISTER_WORDS;
        let mut words = std::vec![
            0u32;
            manifold::OWN_REGISTER_WORDS + CAPACITY * manifold::OWN_CELL_WORDS
        ];
        let position = manifold::wind(b"the wound breath");
        let mut face = RegisterFace::BORN;
        for term in [
            FeltTerm {
                chi: Chi {
                    same: Cog::lit(3),
                    other: Cog::lit(4),
                },
                winding: WindingQuantum::ThisWay,
            },
            FeltTerm {
                chi: Chi {
                    same: Cog::lit(-3),
                    other: Cog::lit(-4),
                },
                winding: WindingQuantum::ThatWay,
            },
        ] {
            assert_eq!(
                deposit::<SliceWordSeam>(
                    &mut words, cell_base, CAPACITY, &mut face, position, term,
                ),
                DepositResult::Accepted
            );
        }
        assert_eq!((face.axis, face.occupancy), (2, 1));
        assert_eq!((face.releases, face.narrows), (0, 0));
        let grip = place::ground(position, 2) as usize;
        let form = RegionalForm::unpack(&words, cell_at(cell_base, grip) + manifold::OWN_CELL_FORM);
        assert_eq!(form.resultant(), (Cog::ZERO, Cog::ZERO));
        assert_ne!(form.fiber(), (Rung::ZERO, Rung::ZERO));
    }

    #[test]
    fn the_safe_mouth_rejects_unreachable_gauge_and_founder_faces() {
        const CAPACITY: usize = 16;
        let cell_base = manifold::OWN_REGISTER_WORDS;

        let mut empty_wide = std::vec![
            0u32;
            manifold::OWN_REGISTER_WORDS + CAPACITY * manifold::OWN_CELL_WORDS
        ];
        store_face::<SliceWordSeam>(
            &mut empty_wide,
            0,
            RegisterFace {
                axis: 4,
                occupancy: 0,
                releases: 0,
                narrows: 0,
            },
        );
        assert!(
            !row_is_canonical(&empty_wide, 0, CAPACITY),
            "an empty current would already have breathed back to rank zero"
        );

        let mut words = std::vec![
            0u32;
            manifold::OWN_REGISTER_WORDS + CAPACITY * manifold::OWN_CELL_WORDS
        ];
        let mut salt = 0u32;
        let position = loop {
            let candidate = manifold::wind(&salt.to_le_bytes());
            if place::ground(candidate, 2) != 0 {
                break candidate;
            }
            salt += 1;
        };
        let mut face = RegisterFace::BORN;
        assert_eq!(
            deposit::<SliceWordSeam>(
                &mut words,
                cell_base,
                CAPACITY,
                &mut face,
                position,
                ride(3, 4),
            ),
            DepositResult::Accepted
        );
        store_face::<SliceWordSeam>(&mut words, 0, face);
        assert!(row_is_canonical(&words, 0, CAPACITY));
        let grip = place::ground(position, 2) as usize;

        let alien = loop {
            salt += 1;
            let candidate = manifold::wind(&salt.to_le_bytes());
            if place::ground(candidate, 2) as usize != grip {
                break candidate;
            }
        };
        write_founder::<SliceWordSeam>(&mut words, cell_at(cell_base, grip), alien);
        assert!(
            !row_is_canonical(&words, 0, CAPACITY),
            "a live grip cannot carry a founder whose construction reaches no ancestor section"
        );
    }
}
