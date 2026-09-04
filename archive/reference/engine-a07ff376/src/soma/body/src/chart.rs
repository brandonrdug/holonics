//! chart — the standing body's own positional register (`FORMULA §XXXII-b`). The register does
//! not ask whether a scalar occupancy is beyond an authored threshold. Each newly occupied grip
//! increments the count, and the increment which carries into this rank's top tooth is the chart
//! digit. The event itself widens the chart; the standing construction then zero-extends into the
//! new digit. No founder, address table, comparison, or reverse migration is present here.

/// One chart register face. `occupancy` is the monotone count of founded standing grips; `axis`
/// names the current dyadic gauge. The count continues whole when the axis gains a digit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Register {
    pub axis: u32,
    pub occupancy: u64,
}

/// The top tooth of the occupancy register at this chart rank. Rank zero has the unit tooth; each
/// side-axis digit adds two occupancy teeth because the chart is a square.
#[inline]
pub fn hand(axis: u32) -> u64 {
    let rank = axis.trailing_zeros();
    let tooth = if rank == 0 { 0 } else { 2 * rank - 1 };
    1u64 << tooth
}

/// Read the carry produced by one already-performed unit increment. This is deliberately a read
/// of the transition `before -> after`, not a predicate over either resident state. For a lawful
/// register increment, exactly the transition which walks into the hand returns true.
#[inline]
pub fn carried_into_hand(before: u64, after: u64, axis: u32) -> bool {
    ((before ^ after) & after & hand(axis)) != 0
}

impl Register {
    /// One newly occupied grip arrives. The returned Boolean is the digit event itself.
    #[inline]
    pub fn arrive(self) -> (Register, bool) {
        let occupancy = self.occupancy.wrapping_add(1);
        (
            Register {
                axis: self.axis,
                occupancy,
            },
            carried_into_hand(self.occupancy, occupancy, self.axis),
        )
    }

    /// Apply the digit which has already occurred. Occupancy continues whole; the new chart digit
    /// is born at zero. Calling this without a carry is outside this pure mouth's responsibility.
    #[inline]
    pub fn digit(self) -> Register {
        Register {
            axis: self.axis << 1,
            occupancy: self.occupancy,
        }
    }

    /// One occupied grip releases (annihilation — Brandon's ruling, 2026-07-10: the chart must
    /// shrink as well as grow; successful compression and competitive selection lawfully vacate
    /// space). The returned Boolean is the borrow: the decrement whose transition walks OUT of
    /// the RETIRING rank's hand — the exact tooth whose crossing forced this axis's digit. The
    /// mirror is exact: the carry fires walking INTO `hand(axis)` at axis `A`; the borrow fires
    /// walking OUT of `hand(A)` at axis `2A`. Rank zero has no digit to retire. The borrow's
    /// CONSEQUENCE cascades at the medium's own event (`§XXXVI`): the retirement re-runs from
    /// the standing configuration, so a borrow blocked by an off-section survivor completes at
    /// the later event that clears the barrier — no flag is carried, because the wide-axis
    /// low-occupancy configuration is itself the standing fact.
    #[inline]
    pub fn depart(self) -> (Register, bool) {
        let occupancy = self.occupancy.wrapping_sub(1);
        let borrowed =
            self.axis > 1 && borrowed_from_hand(self.occupancy, occupancy, self.axis >> 1);
        (
            Register {
                axis: self.axis,
                occupancy,
            },
            borrowed,
        )
    }

    /// Apply the digit retirement which has already occurred. Occupancy continues whole; the
    /// chart's finest digit retires. Rank zero has no digit to retire.
    #[inline]
    pub fn digit_retired(self) -> Register {
        Register {
            axis: if self.axis > 1 { self.axis >> 1 } else { 1 },
            occupancy: self.occupancy,
        }
    }
}

/// Read the borrow produced by one already-performed unit decrement — the mirror of
/// `carried_into_hand`: exactly the transition which walks the given rank's hand bit OFF returns
/// true. `depart` calls this with the RETIRING rank (`axis >> 1`), the tooth whose crossing
/// forced the current digit.
#[inline]
pub fn borrowed_from_hand(before: u64, after: u64, axis: u32) -> bool {
    ((before ^ after) & before & hand(axis)) != 0
}

/// Recast an old dense grip into a wider dyadic chart. Each newly introduced coordinate digit is
/// zero: `(x,y) -> (2^r x, 2^r y)`. The form at the grip is untouched.
#[inline]
pub fn zero_extend_grip(grip: u32, old_axis: u32, new_axis: u32) -> u32 {
    let x = grip / old_axis;
    let y = grip - x * old_axis;
    let scale = new_axis / old_axis;
    (x * scale) * new_axis + y * scale
}

/// If a grip in the wider gauge is the zero-extension of an old grip, return that old grip. This
/// is the direct section used while an arriving light sizes its receiving chart; no table or
/// content-dependent address participates.
#[inline]
pub fn zero_extended_source(grip: u32, old_axis: u32, new_axis: u32) -> Option<u32> {
    let scale = new_axis / old_axis;
    let x = grip / new_axis;
    let y = grip - x * new_axis;
    let low = scale - 1;
    if (x & low) != 0 || (y & low) != 0 {
        return None;
    }
    Some((x / scale) * old_axis + y / scale)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_carry_is_an_arrival_not_a_resident_comparison() {
        let mut register = Register {
            axis: 4,
            occupancy: 0,
        };
        let mut events = Vec::new();
        for arrival in 1..=9 {
            let (next, carry) = register.arrive();
            if carry {
                events.push(arrival);
            }
            register = next;
        }
        assert_eq!(hand(4), 8);
        assert_eq!(events, [8]);
        assert!(!carried_into_hand(
            register.occupancy,
            register.occupancy,
            4
        ));
    }

    #[test]
    fn the_first_light_forces_rank_zero_and_a_large_edge_cascades() {
        let (rank_zero, carry) = Register {
            axis: 1,
            occupancy: 0,
        }
        .arrive();
        assert!(carry);
        assert_eq!(rank_zero.digit().axis, 2);

        let mut axis = 2;
        let arrivals = 40;
        loop {
            let mut register = Register { axis, occupancy: 0 };
            let mut carry = false;
            for _ in 0..arrivals {
                let (next, event) = register.arrive();
                register = next;
                carry |= event;
            }
            if !carry {
                assert_eq!(axis, 16);
                break;
            }
            axis = register.digit().axis;
        }
    }

    #[test]
    fn zero_extension_is_a_composing_section() {
        let old_axis = 8;
        for grip in 0..old_axis * old_axis {
            let once = zero_extend_grip(grip, old_axis, 16);
            let twice = zero_extend_grip(once, 16, 32);
            let direct = zero_extend_grip(grip, old_axis, 32);
            assert_eq!(twice, direct);
            assert_eq!(zero_extended_source(direct, old_axis, 32), Some(grip));
        }
        assert_eq!(zero_extended_source(1, 8, 16), None);
    }
}
