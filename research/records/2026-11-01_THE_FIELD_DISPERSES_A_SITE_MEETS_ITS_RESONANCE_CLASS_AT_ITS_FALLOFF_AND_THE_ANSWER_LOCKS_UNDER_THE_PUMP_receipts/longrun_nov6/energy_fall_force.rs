//! A scratch probe (not committed): theory's fall along F (November 7, 04:04) on the 400-site line state of energy131's
//! founding (energy133's probe state): the central fall Phi(x - dF) - Phi(x + dF) against 2 d <F, F> (lane-tangent) at
//! d = 2^-8 .. 2^-12 of a site's scale, at the opening and after the four ticks.
use holonics::hnn::tower::field::{FieldLearner, Region};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let field = FieldLearner::from_text(&std::fs::read_to_string(&args[1]).unwrap()).unwrap().field;
    let a = field.declaration.alphabet;
    let len = 400usize;
    let mut s = 0x9E37_79B9_7F4A_7C15u64;
    let truth: Vec<usize> = (0..len).map(|_| { s ^= s << 13; s ^= s >> 7; s ^= s << 17; (s % (a as u64 - 1)) as usize }).collect();
    let mut open = vec![false; len];
    (open[300], open[302]) = (true, true);
    let region = Region { classes: &truth, unresolved: &open, faces: &[], locked: &[], echo: &[], domain: None, port: None };
    for ticks in [0usize, 4] {
        for h in 8u32..=12 {
            let t0 = std::time::Instant::now();
            let (first, fall, central) = field.energy_fall(&region, ticks, h).unwrap();
            println!("ticks {ticks} h {h}: first {first} one-sided {fall} central {central} central/2first {:.6} one-sided/first {:.6} ms {}",
                central as f64 / (2 * first) as f64, fall as f64 / first as f64, t0.elapsed().as_millis());
        }
    }
}
