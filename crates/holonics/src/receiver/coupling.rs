//! Acceptance-side ordered holding contacts, beside the listener.
//!
//! `lambda` is the greatest number of equal, strictly order-consistent contacts and
//! `F* = |H| + |T| - 2 lambda`. Prefix/suffix lengths retain the **union** of all optimal
//! couplings. That union is generally not itself a coupling: crossing contacts remain
//! alternatives. Maximal contiguous diagonal plateaus are individually co-admissible.
//! No selected alignment, repaired class, target-conditioned prediction or deposition is
//! returned. The consumer is the campaign's offline reader of the preserved terminal lives.
//!
//! This is the Rust realization of the validated exterior `coupling_reader.py` recurrence.
//! The equality face is codec-neutral (text, image, sound and motor charts may supply their
//! own cells); the actual 32-class framing adapter is separate. Lock phases are supplied by
//! [`crate::geometry::solenoid::field`], never inferred from cell lag or advanced here.
//! Equal multisets with the same key cancel their group sum at the terminal section;
//! individual intermediate plateaus can still have nonzero phase difference. No converse
//! content inference is made from a phase alone. The joined exact optimal-contact/phase-reading
//! statement remains a Lean obligation #62.

use crate::geometry::solenoid::field::LockPhase;
use num_bigint::{BigInt, BigUint, Sign};
use num_traits::{One, Zero};
pub use holonics_engine::inherited::coupling::{Coupling, CouplingCode, CouplingRefusal, OptimalContact, PhaseDefect, Plateau, Strand, TemperatureRefusal, coupling, coupling_code};
#[cfg(test)]
use holonics_engine::inherited::coupling::{CODE_BITS, MANTISSA_BITS, Mass};

/// The external 32-class chart excludes exactly a trailing `[0,0]`.
/// A zero octet `[0,16]` is payload; an internal end is refused without cutting.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Payload32<'a> {
    pub cells: &'a [usize],
    pub framing_end_present: bool,
}

pub fn payload32(whole: &[usize], strand: Strand) -> Result<Payload32<'_>, CouplingRefusal> {
    for (index, &class) in whole.iter().enumerate() {
        if class >= 32 {
            return Err(CouplingRefusal::Class {
                strand,
                index,
                class,
            });
        }
    }
    if let Some(index) = whole.windows(2).position(|pair| pair == [0, 0]) {
        if index + 2 != whole.len() {
            return Err(CouplingRefusal::InternalEnd { strand, index });
        }
        Ok(Payload32 {
            cells: &whole[..index],
            framing_end_present: true,
        })
    } else {
        Ok(Payload32 {
            cells: whole,
            framing_end_present: false,
        })
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FramedCoupling {
    pub coupling: Coupling,
    pub h_framing_end_present: bool,
    pub t_framing_end_present: bool,
}

pub fn coupling32(h_whole: &[usize], t_whole: &[usize]) -> Result<FramedCoupling, CouplingRefusal> {
    let h = payload32(h_whole, Strand::H)?;
    let t = payload32(t_whole, Strand::T)?;
    Ok(FramedCoupling {
        coupling: coupling(h.cells, t.cells)?,
        h_framing_end_present: h.framing_end_present,
        t_framing_end_present: t.framing_end_present,
    })
}

/// Exact `Delta-lambda = V_H - V_T`, including the supplied Z lift.
/// `z_lift = residue + modulus * whole_winding`; digits are least significant first.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PhaseDifference {
    pub z_lift: BigInt,
    pub residue: BigUint,
    pub whole_winding: BigInt,
    pub digits: Vec<BigUint>,
}

/// Carries of the actual participants, retained even when their difference is constant.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PairedCarry {
    pub h_index: usize,
    pub t_index: usize,
    pub h_winding: BigInt,
    pub t_winding: BigInt,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LockPlateau {
    /// Index of the co-admissible diagonal plateau before phase refinement.
    pub contact_plateau: usize,
    pub h_start: usize,
    pub t_start: usize,
    pub length: usize,
    pub first_rank: usize,
    pub delta: PhaseDifference,
    pub carries: Vec<PairedCarry>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LockReading {
    /// Ordered factors are retained, including non-prime ring radices.
    pub radices: Vec<BigUint>,
    pub modulus: BigUint,
    /// All geometric plateaus, split only where the actual lifted difference changes.
    pub plateaus: Vec<LockPlateau>,
    pub least_friction: usize,
    /// Friction read at both strands' supplied terminal sections, also for empty replies.
    pub end_delta: PhaseDifference,
    pub h_end_winding: BigInt,
    pub t_end_winding: BigInt,
}

fn validate_path(
    path: &[LockPhase],
    cells: usize,
    strand: Strand,
    radices: &[BigUint],
    modulus: &BigUint,
) -> Result<(), CouplingRefusal> {
    let expected = cells.checked_add(1).ok_or(CouplingRefusal::Shape)?;
    if path.len() != expected {
        return Err(CouplingRefusal::PhaseShape {
            strand,
            expected,
            actual: path.len(),
        });
    }
    for (index, phase) in path.iter().enumerate() {
        let refuse = |reason| CouplingRefusal::Phase {
            strand,
            index,
            reason,
        };
        if phase.digits.len() != radices.len() {
            return Err(refuse(PhaseDefect::DigitArity));
        }
        let mut value = BigUint::zero();
        let mut place = BigUint::one();
        for (digit, radix) in phase.digits.iter().zip(radices) {
            if digit >= radix {
                return Err(refuse(PhaseDefect::DigitRange));
            }
            value += digit * &place;
            place *= radix;
        }
        if phase.value >= *modulus {
            return Err(refuse(PhaseDefect::ValueRange));
        }
        if value != phase.value {
            return Err(refuse(PhaseDefect::DigitValue));
        }
        if phase.lift != BigInt::from(value) + BigInt::from(modulus.clone()) * &phase.winding {
            return Err(refuse(PhaseDefect::Lift));
        }
    }
    Ok(())
}

fn difference(
    h: &LockPhase,
    t: &LockPhase,
    radices: &[BigUint],
    modulus: &BigUint,
) -> PhaseDifference {
    let z_lift = &h.lift - &t.lift;
    let modulus_z = BigInt::from(modulus.clone());
    let mut remainder = &z_lift % &modulus_z;
    if remainder.sign() == Sign::Minus {
        remainder += &modulus_z;
    }
    let whole_winding = (&z_lift - &remainder) / modulus_z;
    let residue = remainder
        .to_biguint()
        .expect("Euclidean remainder is nonnegative");
    let mut digits = Vec::with_capacity(radices.len());
    let mut rest = residue.clone();
    for radix in radices {
        digits.push(&rest % radix);
        rest /= radix;
    }
    PhaseDifference {
        z_lift,
        residue,
        whole_winding,
        digits,
    }
}

/// Annotate the class reading through actual J1 phases at each cell's entrance and at
/// the terminal section (`path.len() == cells.len()+1`). The caller supplies the declared
/// Lock chain radices; Own clocks are not folded into this modulus. An annotation does
/// not assert a dynamical lock: it checks/splits constancy of the observed phase difference.
/// Carries come from J1's current, not from a second stepping law.
pub fn annotate_lock_phases(
    reading: &Coupling,
    radices: &[BigUint],
    h: &[LockPhase],
    t: &[LockPhase],
) -> Result<LockReading, CouplingRefusal> {
    let mut modulus = BigUint::one();
    for (level, radix) in radices.iter().enumerate() {
        if radix.is_zero() {
            return Err(CouplingRefusal::ZeroRadix { level });
        }
        modulus *= radix;
    }
    validate_path(h, reading.h_cells, Strand::H, radices, &modulus)?;
    validate_path(t, reading.t_cells, Strand::T, radices, &modulus)?;
    let total = reading
        .h_cells
        .checked_add(reading.t_cells)
        .ok_or(CouplingRefusal::Shape)?;
    if reading.lambda > reading.h_cells.min(reading.t_cells)
        || reading.least_friction != total - 2 * reading.lambda
        || reading.unresolved_h_per_optimum != reading.h_cells - reading.lambda
        || reading.unresolved_t_per_optimum != reading.t_cells - reading.lambda
        || reading.plural_optimal_contacts.len() < reading.lambda
    {
        return Err(CouplingRefusal::ContactShape);
    }
    let mut previous = None;
    for contact in &reading.plural_optimal_contacts {
        let here = (contact.h_index, contact.t_index);
        if contact.h_index >= reading.h_cells
            || contact.t_index >= reading.t_cells
            || contact.rank_on_any_optimal_coupling == 0
            || contact.rank_on_any_optimal_coupling > reading.lambda
            || previous.is_some_and(|before| before >= here)
        {
            return Err(CouplingRefusal::ContactShape);
        }
        previous = Some(here);
    }
    let mut covered = Vec::new();
    let mut plateaus = Vec::<LockPlateau>::new();
    for (contact_plateau, plateau) in reading.maximal_contiguous_plateaus.iter().enumerate() {
        if plateau.length == 0
            || plateau.h_start > reading.h_cells
            || plateau.t_start > reading.t_cells
            || plateau.length > reading.h_cells - plateau.h_start
            || plateau.length > reading.t_cells - plateau.t_start
            || plateau.first_rank == 0
            || plateau.first_rank > reading.lambda
            || plateau.length > reading.lambda - plateau.first_rank + 1
        {
            return Err(CouplingRefusal::ContactShape);
        }
        for k in 0..plateau.length {
            let (i, j) = (plateau.h_start + k, plateau.t_start + k);
            let contact_index = reading
                .plural_optimal_contacts
                .binary_search_by_key(&(i, j), |c| (c.h_index, c.t_index))
                .map_err(|_| CouplingRefusal::ContactShape)?;
            if reading.plural_optimal_contacts[contact_index].rank_on_any_optimal_coupling
                != plateau.first_rank + k
            {
                return Err(CouplingRefusal::ContactShape);
            }
            covered.push((i, j));
            let delta = difference(&h[i], &t[j], radices, &modulus);
            let carry = PairedCarry {
                h_index: i,
                t_index: j,
                h_winding: h[i].winding.clone(),
                t_winding: t[j].winding.clone(),
            };
            if let Some(last) = plateaus
                .last_mut()
                .filter(|p| p.contact_plateau == contact_plateau && p.delta == delta)
            {
                last.length += 1;
                last.carries.push(carry);
            } else {
                plateaus.push(LockPlateau {
                    contact_plateau,
                    h_start: i,
                    t_start: j,
                    length: 1,
                    first_rank: plateau.first_rank + k,
                    delta,
                    carries: vec![carry],
                });
            }
        }
    }
    covered.sort_unstable();
    if !covered.iter().copied().eq(reading
        .plural_optimal_contacts
        .iter()
        .map(|c| (c.h_index, c.t_index)))
    {
        return Err(CouplingRefusal::ContactShape);
    }
    let h_end = &h[reading.h_cells];
    let t_end = &t[reading.t_cells];
    Ok(LockReading {
        radices: radices.to_vec(),
        end_delta: difference(h_end, t_end, radices, &modulus),
        modulus,
        plateaus,
        least_friction: reading.least_friction,
        h_end_winding: h_end.winding.clone(),
        t_end_winding: t_end.winding.clone(),
    })
}

/// `log₂(v / 2^62)` on `2^(−20)` for `v > 0` (the tests' exact reading of a whole number's logarithm).
#[cfg(test)]
fn log2_ratio(v: u128) -> i128 {
    let x = Mass::of(v, -(MANTISSA_BITS as i64));
    x.log2()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    // ---- The coupling at temperature one (#601) ----

    /// A face from weights over the classes (masses at 2^40 each unit), its total their sum.
    fn face(weights: &[u128]) -> (Vec<u128>, u128) {
        let masses: Vec<u128> = weights.iter().map(|&w| w << 40).collect();
        let total = masses.iter().sum();
        (masses, total)
    }

    fn view(faces: &[(Vec<u128>, u128)]) -> Vec<(&[u128], u128)> {
        faces.iter().map(|(m, t)| (m.as_slice(), *t)).collect()
    }

    /// `−log₂(m/t)` on 2^(−20), the field's own reading of a face's code.
    fn bits(m: u128, t: u128) -> i64 {
        crate::hnn::tower::face_code(m, t)
    }

    /// `log₂ v` on 2^(−20) for a whole `v ≥ 1`: its width, and its leading 63 bits read by [`log2_ratio`].
    fn log2_whole(v: &BigUint) -> i128 {
        let width = v.bits();
        let top: u128 = if width > 63 { (v >> (width - 63)).try_into().unwrap() } else { u128::try_from(v.clone()).unwrap() << (63 - width) };
        ((width as i128 - 1) << CODE_BITS) + log2_ratio(top)
    }

    /// The place-wise code: each cell at its own place, every later place the void.
    fn place_wise(faces: &[(Vec<u128>, u128)], void: usize, target: &[usize]) -> i64 {
        faces.iter().enumerate().map(|(i, (m, t))| bits(m[target.get(i).copied().unwrap_or(void)], *t)).sum()
    }

    /// A sharp face on `class` among `classes` (one part in 2^20 spread over the rest).
    fn sharp(class: usize, classes: usize) -> (Vec<u128>, u128) {
        face(&(0..classes).map(|c| if c == class { 1u128 << 20 } else { 1 }).collect::<Vec<_>>())
    }

    #[test]
    fn with_as_many_places_as_cells_the_coupling_is_the_place_wise_code() {
        let faces: Vec<_> = [[3u128, 1, 2, 5], [1, 4, 1, 1], [2, 2, 7, 1]].iter().map(|w| face(w)).collect();
        let target = [1usize, 1, 2];
        let read = coupling_code(&view(&faces), 0, &target, None).unwrap();
        assert!((read.code - place_wise(&faces, 0, &target)).abs() <= 8, "{} against {}", read.code, place_wise(&faces, 0, &target));
        for (i, placed) in read.placed.iter().enumerate() {
            assert_eq!(placed, &vec![(target[i], 1u64 << 24), (0, 0)], "place {i}");
        }
        assert!(read.lag.iter().all(|&(mass, lag)| mass == 1 << 24 && lag == 0));
    }

    /// A code: every target the places can write (each place a class or the void) has its coupling `Z(T | H)`, read
    /// here by enumerating every writing in exact rationals; the `Z` of every target sum to one exactly (each writing maps
    /// to one target once its voids are dropped), and each coupling's code is `−log₂ Z` to a few grains of its reading.
    #[test]
    fn the_coupling_is_a_code() {
        use num_rational::BigRational;
        let weights: [[u128; 3]; 3] = [[2, 1, 3], [1, 1, 1], [4, 1, 2]];
        let faces: Vec<_> = weights.iter().map(|w| face(w)).collect();
        // Z(T | H) by enumeration: every writing of the three places, its voids dropped.
        let mut z: std::collections::BTreeMap<Vec<usize>, BigRational> = std::collections::BTreeMap::new();
        for writing in 0..27usize {
            let classes: Vec<usize> = (0..3).map(|i| writing / 3usize.pow(i as u32) % 3).collect();
            let p = classes.iter().enumerate().fold(BigRational::from_integer(1.into()), |acc, (i, &c)| acc * BigRational::new((weights[i][c]).into(), weights[i].iter().sum::<u128>().into()));
            let target: Vec<usize> = classes.into_iter().filter(|&c| c != 0).collect();
            *z.entry(target).or_insert_with(|| BigRational::from_integer(0.into())) += p;
        }
        assert_eq!(z.values().fold(BigRational::from_integer(0.into()), |a, b| a + b), BigRational::from_integer(1.into()));
        for (target, zt) in &z {
            let read = coupling_code(&view(&faces), 0, target, None).unwrap();
            let (num, den) = (zt.numer().to_biguint().unwrap(), zt.denom().to_biguint().unwrap());
            let exact = log2_whole(&den) - log2_whole(&num);
            assert!((read.code as i128 - exact).abs() <= 16, "{target:?}: {} against {exact}", read.code);
        }
        let mut targets: Vec<Vec<usize>> = vec![vec![]];
        for len in 1..=3usize {
            let mut next = Vec::new();
            for t in targets.iter().filter(|t| t.len() == len - 1) {
                for c in 1..3 {
                    let mut u = t.clone();
                    u.push(c);
                    next.push(u);
                }
            }
            targets.extend(next);
        }
        assert_eq!(targets.iter().filter(|t| z.contains_key(*t)).count(), z.len(), "every target the places write is read");
    }

    #[test]
    fn the_coupling_is_never_worse_than_the_place() {
        let faces: Vec<_> = [[3u128, 1, 2, 5], [1, 4, 1, 1], [2, 2, 7, 1], [5, 1, 1, 1], [1, 1, 1, 9]].iter().map(|w| face(w)).collect();
        for target in [vec![1usize, 2], vec![3, 3, 3], vec![2, 1, 3, 1], vec![1, 1, 2, 2, 3]] {
            let read = coupling_code(&view(&faces), 0, &target, None).unwrap();
            assert!(read.code <= place_wise(&faces, 0, &target) + 8, "{target:?}");
        }
    }

    /// [the comparison record §3.5] **The witness**: a release equal to its target one place late, and one with a byte
    /// inserted, are charged their slip alone by the coupling where the place-wise code charges every byte after it,
    /// and the lag field reads `+1` after the slip; one with a byte deleted is charged its slip alone where a cell may be
    /// omitted (the lock face), and reads `−1` after it. The place-wise code charges each.
    #[test]
    fn the_witness_one_late_one_inserted_one_deleted() {
        let (classes, void) = (6usize, 0usize);
        let target = [1usize, 2, 3, 4, 5, 1, 2, 3];
        let slip = 8 * (1i64 << 20); // eight bits: a slip costs about log₂ of the face's sharpness (20 bits), well under it
        // One place late: a leading void, then the target.
        let late: Vec<_> = std::iter::once(void).chain(target.iter().copied()).map(|c| sharp(c, classes)).collect();
        let read = coupling_code(&view(&late), void, &target, None).unwrap();
        assert!(read.code < 4 * (1i64 << 20), "late: {}", read.code);
        assert!(place_wise(&late, void, &target) > (target.len() as i64 - 1) * slip, "the place charges every byte after the slip");
        assert!(read.lag[2..].iter().all(|&(mass, lag)| mass > (1 << 24) - 64 && (lag - (1 << 24)).abs() < 64), "lag +1 after the slip");
        // One byte inserted (a 9 after the third cell): n = m + 1.
        let mut inserted: Vec<usize> = target.to_vec();
        inserted.insert(3, 5);
        let faces: Vec<_> = inserted.iter().map(|&c| sharp(c, classes)).collect();
        let read = coupling_code(&view(&faces), void, &target, None).unwrap();
        assert!(read.code < 24 * (1i64 << 20), "inserted: the slip alone, {}", read.code);
        assert!(place_wise(&faces, void, &target) > 4 * slip);
        assert!(read.lag[4..].iter().all(|&(_, lag)| (lag - (1 << 24)).abs() < 1 << 12), "lag +1 after the insertion");
        // One byte deleted (the fourth cell), the release padded with a void place: omissions at a declared cost.
        let mut deleted: Vec<usize> = target.to_vec();
        deleted.remove(3);
        deleted.push(void);
        let faces: Vec<_> = deleted.iter().map(|&c| sharp(c, classes)).collect();
        let omit = 3 * (1i64 << 20);
        let read = coupling_code(&view(&faces), void, &target, Some(omit)).unwrap();
        assert!(read.code < omit + 4 * (1i64 << 20), "deleted: the slip alone, {}", read.code);
        assert!(place_wise(&faces, void, &target) > 4 * slip);
        assert!(read.lag[3..7].iter().all(|&(_, lag)| (lag + (1 << 24)).abs() < 1 << 12), "lag −1 after the deletion: {:?}", read.lag);
    }

    /// Long strands on wide faces (a GSM8K port: 122 classes, hundreds of places) carry their mass to the end, with many
    /// spare places and with one.
    #[test]
    fn a_long_port_carries_its_mass() {
        let flat = face(&[1u128; 122]);
        for (n, m) in [(1000usize, 300usize), (301, 300), (300, 300), (5, 0), (1229, 40)] {
            let faces = vec![flat.clone(); n];
            let target: Vec<usize> = (0..m).map(|j| 1 + j % 120).collect();
            let read = coupling_code(&view(&faces), 0, &target, None);
            assert!(read.is_ok(), "n {n} m {m}: {read:?}");
        }
    }

    #[test]
    fn the_coupling_refuses_what_it_cannot_read() {
        let faces: Vec<_> = [[1u128, 1], [1, 1]].iter().map(|w| face(w)).collect();
        assert_eq!(coupling_code(&view(&faces), 0, &[1, 1, 1], None), Err(TemperatureRefusal::Short { cells: 3, places: 2 }));
        assert_eq!(coupling_code(&view(&faces), 0, &[0], None), Err(TemperatureRefusal::VoidCell));
        assert_eq!(coupling_code(&view(&faces), 0, &[2], None), Err(TemperatureRefusal::Face));
    }

    type Choice = Vec<(usize, usize)>;

    // Independent exhaustive enumeration of all increasing chains of equal contacts;
    // no prefix/suffix dynamic-programming recurrence is used in this oracle.
    fn brute(h: &[u8], t: &[u8]) -> BTreeSet<Choice> {
        fn visit(
            h: &[u8],
            t: &[u8],
            i: usize,
            j: usize,
            chain: &mut Choice,
            choices: &mut BTreeSet<Choice>,
        ) {
            choices.insert(chain.clone());
            for a in i..h.len() {
                for b in j..t.len() {
                    if h[a] == t[b] {
                        chain.push((a, b));
                        visit(h, t, a + 1, b + 1, chain, choices);
                        chain.pop();
                    }
                }
            }
        }
        let mut choices = BTreeSet::new();
        visit(h, t, 0, 0, &mut Vec::new(), &mut choices);
        let longest = choices.iter().map(Vec::len).max().unwrap();
        choices.into_iter().filter(|c| c.len() == longest).collect()
    }

    fn contact_set(q: &Coupling) -> BTreeSet<(usize, usize)> {
        q.plural_optimal_contacts
            .iter()
            .map(|c| (c.h_index, c.t_index))
            .collect()
    }

    fn plateau_set(q: &Coupling) -> BTreeSet<(usize, usize, usize, usize)> {
        q.maximal_contiguous_plateaus
            .iter()
            .map(|p| (p.h_start, p.t_start, p.length, p.first_rank))
            .collect()
    }

    fn check(h: &[u8], t: &[u8]) {
        let q = coupling(h, t).unwrap();
        let choices = brute(h, t);
        let lambda = choices.first().unwrap().len();
        let union: BTreeSet<_> = choices.iter().flatten().copied().collect();
        assert_eq!(q.lambda, lambda, "{h:?} {t:?}");
        assert_eq!(q.least_friction, h.len() + t.len() - 2 * lambda);
        assert_eq!(q.unresolved_h_per_optimum, h.len() - lambda);
        assert_eq!(q.unresolved_t_per_optimum, t.len() - lambda);
        assert_eq!(contact_set(&q), union);
        for c in &q.plural_optimal_contacts {
            for choice in choices
                .iter()
                .filter(|v| v.contains(&(c.h_index, c.t_index)))
            {
                assert_eq!(
                    choice
                        .iter()
                        .position(|v| *v == (c.h_index, c.t_index))
                        .unwrap()
                        + 1,
                    c.rank_on_any_optimal_coupling
                );
            }
        }
        let may_h: BTreeSet<_> = choices
            .iter()
            .flat_map(|c| (0..h.len()).filter(move |i| !c.iter().any(|(a, _)| a == i)))
            .collect();
        let may_t: BTreeSet<_> = choices
            .iter()
            .flat_map(|c| (0..t.len()).filter(move |j| !c.iter().any(|(_, b)| b == j)))
            .collect();
        assert_eq!(
            q.may_be_unresolved_h_indices,
            may_h.iter().copied().collect::<Vec<_>>()
        );
        assert_eq!(
            q.may_be_unresolved_t_indices,
            may_t.iter().copied().collect::<Vec<_>>()
        );
        assert_eq!(
            q.always_held_h_indices,
            (0..h.len())
                .filter(|i| !may_h.contains(i))
                .collect::<Vec<_>>()
        );
        assert_eq!(
            q.always_held_t_indices,
            (0..t.len())
                .filter(|j| !may_t.contains(j))
                .collect::<Vec<_>>()
        );
        assert_eq!(
            q.never_held_h_indices,
            (0..h.len())
                .filter(|i| !union.iter().any(|(a, _)| a == i))
                .collect::<Vec<_>>()
        );
        assert_eq!(
            q.never_held_t_indices,
            (0..t.len())
                .filter(|j| !union.iter().any(|(_, b)| b == j))
                .collect::<Vec<_>>()
        );
        let mut covered = BTreeSet::new();
        for p in &q.maximal_contiguous_plateaus {
            let members: BTreeSet<_> = (0..p.length)
                .map(|k| (p.h_start + k, p.t_start + k))
                .collect();
            assert!(
                choices
                    .iter()
                    .any(|c| members.iter().all(|v| c.contains(v))),
                "plateau must fit one optimum"
            );
            assert!(
                p.h_start == 0
                    || p.t_start == 0
                    || !union.contains(&(p.h_start - 1, p.t_start - 1))
            );
            assert!(!union.contains(&(p.h_start + p.length, p.t_start + p.length)));
            for member in members {
                assert!(covered.insert(member));
            }
        }
        assert_eq!(covered, union);
        let swap = coupling(t, h).unwrap();
        assert_eq!(
            (swap.lambda, swap.least_friction),
            (q.lambda, q.least_friction)
        );
        assert_eq!(
            contact_set(&swap),
            union.iter().map(|&(i, j)| (j, i)).collect()
        );
        assert_eq!(
            plateau_set(&swap),
            plateau_set(&q)
                .iter()
                .map(|&(i, j, n, rank)| (j, i, n, rank))
                .collect()
        );
        let hr: Vec<_> = h.iter().rev().copied().collect();
        let tr: Vec<_> = t.iter().rev().copied().collect();
        let reverse = coupling(&hr, &tr).unwrap();
        assert_eq!(
            (reverse.lambda, reverse.least_friction),
            (q.lambda, q.least_friction)
        );
        assert_eq!(
            contact_set(&reverse),
            union
                .iter()
                .map(|&(i, j)| (h.len() - 1 - i, t.len() - 1 - j))
                .collect()
        );
        assert_eq!(
            plateau_set(&reverse),
            plateau_set(&q)
                .iter()
                .map(|&(i, j, n, rank)| (
                    h.len() - i - n,
                    t.len() - j - n,
                    n,
                    lambda + 2 - rank - n
                ))
                .collect()
        );
        assert_eq!(
            reverse.may_be_unresolved_h_indices,
            may_h
                .iter()
                .rev()
                .map(|&i| h.len() - 1 - i)
                .collect::<Vec<_>>()
        );
        assert_eq!(
            reverse.may_be_unresolved_t_indices,
            may_t
                .iter()
                .rev()
                .map(|&j| t.len() - 1 - j)
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn bounded_exhaustive_plural_contacts_unresolved_and_symmetries() {
        // Same bounded population as the validated Python reader: 31 words, 961 pairs.
        let words: Vec<Vec<u8>> = (0..=4)
            .flat_map(|n| {
                (0..(1usize << n))
                    .map(move |bits| (0..n).map(|i| ((bits >> i) & 1) as u8).collect())
            })
            .collect();
        assert_eq!(words.len(), 31);
        for h in &words {
            for t in &words {
                check(h, t);
            }
        }
    }

    #[test]
    fn named_plural_crossing_stutter_and_disjoint_cases() {
        for (h, t, lambda, friction) in [
            (vec![], vec![], 0, 0),
            (vec![], vec![1, 2], 0, 2),
            (vec![1, 2, 3], vec![1, 2, 3], 3, 0),
            (vec![1, 1, 2], vec![1, 2], 2, 1),
            (vec![1, 2, 3], vec![1, 4, 3], 2, 2),
            (vec![1, 2], vec![2, 1], 1, 2),
            (vec![1, 3, 2, 4], vec![1, 2, 3, 4], 3, 2),
            (vec![1, 1], vec![2, 2], 0, 4),
        ] {
            check(&h, &t);
            let q = coupling(&h, &t).unwrap();
            assert_eq!((q.lambda, q.least_friction), (lambda, friction));
        }
        let stutter = coupling(&[1, 1, 2], &[1, 2]).unwrap();
        assert_eq!(stutter.plural_optimal_contacts.len(), 3);
        assert_eq!(stutter.may_be_unresolved_h_indices, [0, 1]);
        assert_eq!(stutter.always_held_h_indices, [2]);
        let crossing = coupling(&[1, 2], &[2, 1]).unwrap();
        assert_eq!(crossing.plural_optimal_contacts.len(), 2);
        assert_eq!(crossing.lambda, 1);
        assert_eq!(crossing.maximal_contiguous_plateaus.len(), 2);
        assert!(!coupling::<u8>(&[], &[]).unwrap().nonempty_zero_friction);
        assert!(coupling(&[1], &[1]).unwrap().nonempty_zero_friction);
    }

    #[test]
    fn declared_class_chart_preserves_zero_octet_and_refuses_internal_end() {
        let whole = [0, 16, 0, 0];
        assert_eq!(
            payload32(&whole, Strand::H).unwrap(),
            Payload32 {
                cells: &[0, 16],
                framing_end_present: true
            }
        );
        assert_eq!(payload32(&[5], Strand::T).unwrap().cells, [5]);
        assert_eq!(coupling32(&whole, &whole).unwrap().coupling.lambda, 2);
        assert!(matches!(
            payload32(&[0, 0, 3, 16], Strand::H),
            Err(CouplingRefusal::InternalEnd {
                strand: Strand::H,
                index: 0
            })
        ));
        assert!(matches!(
            payload32(&[32], Strand::T),
            Err(CouplingRefusal::Class {
                strand: Strand::T,
                index: 0,
                class: 32
            })
        ));
        assert!(matches!(
            payload32(&[0, 0, 0], Strand::T),
            Err(CouplingRefusal::InternalEnd { .. })
        ));
    }

    // Static supplied chart sections; this helper represents integers, never advances a Field.
    fn phase(lift: BigInt, radices: &[BigUint]) -> LockPhase {
        let modulus: BigUint = radices.iter().product();
        let n = BigInt::from(modulus.clone());
        let mut residue = &lift % &n;
        if residue.sign() == Sign::Minus {
            residue += &n;
        }
        let winding = (&lift - &residue) / &n;
        let value = residue.to_biguint().unwrap();
        let mut rest = value.clone();
        let digits = radices
            .iter()
            .map(|d| {
                let digit = &rest % d;
                rest /= d;
                digit
            })
            .collect();
        LockPhase {
            digits,
            value,
            lift,
            winding,
        }
    }

    fn path(values: &[i64], radices: &[BigUint]) -> Vec<LockPhase> {
        values
            .iter()
            .map(|&v| phase(BigInt::from(v), radices))
            .collect()
    }

    fn radices() -> Vec<BigUint> {
        vec![2u8.into(), 3u8.into()]
    }

    #[test]
    fn actual_lock_phase_splits_changes_and_retains_both_carry_series() {
        let r = radices();
        let q = coupling(&[1, 2, 3], &[1, 2, 3]).unwrap();
        let h = path(&[-1, 0, 2, 3], &r);
        let t = path(&[0, 1, 2, 4], &r);
        let lock = annotate_lock_phases(&q, &r, &h, &t).unwrap();
        assert_eq!(q.maximal_contiguous_plateaus.len(), 1);
        assert_eq!(
            lock.plateaus.iter().map(|p| p.length).collect::<Vec<_>>(),
            [2, 1]
        );
        let first = &lock.plateaus[0];
        assert_eq!(first.delta.z_lift, BigInt::from(-1));
        assert_eq!(first.delta.residue, BigUint::from(5u8));
        assert_eq!(first.delta.whole_winding, BigInt::from(-1));
        assert_eq!(first.delta.digits, [BigUint::from(1u8), BigUint::from(2u8)]);
        assert_eq!(
            first
                .carries
                .iter()
                .map(|c| c.h_winding.clone())
                .collect::<Vec<_>>(),
            [BigInt::from(-1), BigInt::zero()]
        );
        assert_eq!(lock.plateaus[1].delta.z_lift, BigInt::zero());
        assert_eq!(lock.plateaus[1].first_rank, 3);
        assert_eq!(lock.end_delta.z_lift, BigInt::from(-1));
        // Modulo equality must not erase a genuine difference in the Z lift.
        let q = coupling(&[1, 2], &[1, 2]).unwrap();
        let lock =
            annotate_lock_phases(&q, &r, &path(&[0, 6, 7], &r), &path(&[0, 0, 1], &r)).unwrap();
        assert_eq!(lock.plateaus.len(), 2);
        assert!(lock.plateaus.iter().all(|p| p.delta.residue.is_zero()));
        assert_eq!(lock.plateaus[1].delta.whole_winding, BigInt::one());
    }

    #[test]
    fn a_reordering_cancels_at_the_end_but_not_at_each_intermediate_plateau() {
        // A(a)=1, A(b)=2 in Z/6, same initial key. Cell-order lag cannot replace V_H-V_T.
        let r = radices();
        let q = coupling(&[1, 2], &[2, 1]).unwrap();
        let lock =
            annotate_lock_phases(&q, &r, &path(&[0, 1, 3], &r), &path(&[0, 2, 3], &r)).unwrap();
        assert_eq!(lock.end_delta.z_lift, BigInt::zero());
        assert_eq!(
            lock.plateaus
                .iter()
                .map(|p| p.delta.z_lift.clone())
                .collect::<Vec<_>>(),
            [BigInt::from(-2), BigInt::from(1)]
        );
        assert_eq!(q.lambda, 1);
        assert_eq!(lock.plateaus.len(), 2); // Both incompatible alternatives remain.
    }

    #[test]
    fn phase_uses_unbounded_lifts_and_swap_negates_the_actual_difference() {
        let r = radices();
        let q = coupling(&[1], &[1]).unwrap();
        let large: BigInt = (BigInt::one() << 256usize) + BigInt::from(17u8);
        let h = vec![phase(large.clone(), &r), phase(&large + 1, &r)];
        let t = path(&[-5, -4], &r);
        let forward = annotate_lock_phases(&q, &r, &h, &t).unwrap();
        let backward = annotate_lock_phases(&q, &r, &t, &h).unwrap();
        assert_eq!(forward.end_delta.z_lift, &large + 5);
        assert_eq!(backward.end_delta.z_lift, -&forward.end_delta.z_lift);
        for delta in [&forward.end_delta, &backward.end_delta] {
            assert_eq!(
                delta.z_lift,
                BigInt::from(delta.residue.clone())
                    + BigInt::from(forward.modulus.clone()) * &delta.whole_winding
            );
        }
    }

    #[test]
    fn native_j1_field_paths_supply_every_plural_plateau_without_a_second_clock() {
        use crate::geometry::solenoid::field::FieldSolenoid;
        use crate::hnn::field::{Field, FieldDeclaration};

        let field = Field::declare(FieldDeclaration::campaign_one(1 << 17)).unwrap();
        let chart = FieldSolenoid::from_field(&field).unwrap();
        let key: Vec<_> = field.rings().iter().map(|_| BigInt::one()).collect();
        let h = [0, 1, 0, 1];
        let t = [0, 1];
        let hp: Vec<_> = chart
            .phase_path(&field, &key, &h)
            .unwrap()
            .into_iter()
            .map(|p| p.lock)
            .collect();
        let tp: Vec<_> = chart
            .phase_path(&field, &key, &t)
            .unwrap()
            .into_iter()
            .map(|p| p.lock)
            .collect();
        let q = coupling(&h, &t).unwrap();
        let read = annotate_lock_phases(&q, chart.lock_radices(), &hp, &tp).unwrap();
        assert_eq!(q.lambda, 2);
        assert_eq!(q.least_friction, 2);
        assert_eq!(read.plateaus.len(), 2);
        assert!(read.plateaus.iter().all(|p| p.length == 2));
        assert_eq!(
            read.plateaus.iter().map(|p| p.length).sum::<usize>(),
            q.plural_optimal_contacts.len()
        );
        for p in &read.plateaus {
            for k in 0..p.length {
                assert_eq!(
                    p.delta.z_lift,
                    &hp[p.h_start + k].lift - &tp[p.t_start + k].lift
                );
            }
        }
        let skipped_sum =
            chart.class_increment(&field, 0).unwrap() + chart.class_increment(&field, 1).unwrap();
        assert_eq!(read.end_delta.z_lift, BigInt::from(skipped_sum));
    }

    #[test]
    fn actual_phase_chart_refuses_shape_digit_and_lift_defects() {
        let r = radices();
        let q = coupling(&[1], &[1]).unwrap();
        let good = path(&[0, 1], &r);
        assert!(matches!(
            annotate_lock_phases(&q, &r, &good[..1], &good),
            Err(CouplingRefusal::PhaseShape {
                strand: Strand::H,
                expected: 2,
                actual: 1
            })
        ));
        assert!(matches!(
            annotate_lock_phases(&q, &[], &good, &good),
            Err(CouplingRefusal::Phase {
                reason: PhaseDefect::DigitArity,
                ..
            })
        ));
        let no_lock = vec![phase(BigInt::zero(), &[]), phase(BigInt::zero(), &[])];
        let identity = annotate_lock_phases(&q, &[], &no_lock, &no_lock).unwrap();
        assert_eq!(identity.modulus, BigUint::one());
        assert!(identity.end_delta.digits.is_empty());
        assert!(matches!(
            annotate_lock_phases(&q, &[BigUint::zero()], &good, &good),
            Err(CouplingRefusal::ZeroRadix { level: 0 })
        ));
        for defect in [
            PhaseDefect::DigitArity,
            PhaseDefect::DigitRange,
            PhaseDefect::DigitValue,
            PhaseDefect::ValueRange,
            PhaseDefect::Lift,
        ] {
            let mut bad = good.clone();
            match defect {
                PhaseDefect::DigitArity => {
                    bad[0].digits.pop();
                }
                PhaseDefect::DigitRange => {
                    bad[0].digits[0] = 2u8.into();
                }
                PhaseDefect::DigitValue => {
                    bad[0].digits[0] = 1u8.into();
                }
                PhaseDefect::ValueRange => {
                    bad[0].value = 6u8.into();
                }
                PhaseDefect::Lift => {
                    bad[0].lift = BigInt::one();
                }
            }
            assert_eq!(
                annotate_lock_phases(&q, &r, &good, &bad),
                Err(CouplingRefusal::Phase {
                    strand: Strand::T,
                    index: 0,
                    reason: defect
                })
            );
        }
        let mut bad = q.clone();
        bad.maximal_contiguous_plateaus[0].length = 2;
        assert!(matches!(
            annotate_lock_phases(&bad, &r, &good, &good),
            Err(CouplingRefusal::ContactShape)
        ));
        // Empty replies still carry their independently supplied terminal section.
        let empty = coupling::<u8>(&[], &[]).unwrap();
        let reading = annotate_lock_phases(&empty, &r, &path(&[-1], &r), &path(&[3], &r)).unwrap();
        assert!(reading.plateaus.is_empty());
        assert_eq!(reading.end_delta.z_lift, BigInt::from(-4));
    }
}
