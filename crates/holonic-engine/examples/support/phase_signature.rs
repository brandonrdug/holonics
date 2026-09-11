use num_traits::Zero;
use relational_geometry::{ComplexInterval, Rat};

// Closed quadrant signatures. Axis uncertainty is retained as a set of possible quadrants.
pub fn phase_signature(z: &ComplexInterval) -> u64 {
    let mut mask = 0;
    for re_negative in 0..2 {
        for im_negative in 0..2 {
            let re = if re_negative == 1 {
                z.re.lower <= Rat::zero()
            } else {
                z.re.upper >= Rat::zero()
            };
            let im = if im_negative == 1 {
                z.im.lower <= Rat::zero()
            } else {
                z.im.upper >= Rat::zero()
            };
            if re && im {
                mask |= 1 << (2 * re_negative + im_negative);
            }
        }
    }
    mask
}
