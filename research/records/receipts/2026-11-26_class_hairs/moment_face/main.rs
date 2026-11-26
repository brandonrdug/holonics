// A ruler: the moment face's block for each turned slot, the two columns (re, im) of its moment read into the state's width;
// its two singular values and the angle of its principal direction in the ring's plane. Host floats, a ruler's.
use holonics_engine::field::*;
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let text = std::fs::read_to_string(&a[1]).unwrap();
    let learner = Learner::from_text(&text).unwrap();
    let f = &learner.field;
    let d = f.declaration;
    let l = f.layout();
    let (dw, heads, n) = (d.width, d.heads, d.modes);
    let m = heads * n;
    let m2 = 2 * m;
    let periods = ring_periods(d.turned_slots(), d.reach);
    println!("MFACE width={dw} heads={heads} modes={n} frames={} still={} turned_slots={} periods={:?}", d.frames, d.still, d.turned_slots(), periods);
    for h in 0..heads {
        let set = h % d.frames;
        let turned = set >= d.still && !d.is_depth(h);
        for li in 0..n {
            let c = h * n + li;
            let col = |k: usize| -> Vec<f64> { (0..dw).map(|r| f.theta[l.moment_face + r * m2 + k] as f64 / 65536.0).collect() };
            let (x, y) = (col(c), col(m + c));
            let (sxx, syy, sxy): (f64, f64, f64) = (x.iter().map(|v| v * v).sum(), y.iter().map(|v| v * v).sum(), x.iter().zip(&y).map(|(a, b)| a * b).sum());
            let tr = sxx + syy;
            let det = sxx * syy - sxy * sxy;
            let disc = ((tr * tr / 4.0 - det).max(0.0)).sqrt();
            let (l1, l2) = (tr / 2.0 + disc, (tr / 2.0 - disc).max(0.0));
            let angle = 0.5 * (2.0 * sxy).atan2(sxx - syy);
            let period = if turned { periods.get(li * (d.frames - d.still) + set - d.still).copied().unwrap_or(0) } else { 0 };
            println!("MFACE_SLOT head={h} mode={li} turned={turned} period={period} s1={:.5} s2={:.5} ratio={:.4} principal_angle_turns={:.4}", l1.sqrt(), l2.sqrt(), (l2 / l1.max(1e-30)).sqrt(), angle / std::f64::consts::TAU);
        }
    }
}
