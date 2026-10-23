// Exterior read: context-tree weighting in its ratio form, with the ratio released at a bound.
// Cells are base-4 digits of the bytes, high pair first; one tree per frame phase; prequential.
// Each internal node carries beta = P_e / prod_children P_w (Willems' ratio); the conditional is
//   q_k(a) = (beta_k e_k(a) + q_(k+1)(a)) / (beta_k + 1),   q_D(a) = e_D(a),
// and after the actual symbol u, beta_k <- beta_k e_k(u) / q_(k+1)(u). Unreleased, this is exactly
// the joint form. Released, |log2 beta| <= K: a cell then costs at most log2(1 + 2^-K) bits more at
// a node than the unreleased mixture of the same two faces would, and the carrier is K bits wide
// whatever the population. K = 0 reads unreleased. The passage term (m, w) is as in passage_ctw.
// An optional sixth argument lists cell offsets (comma-separated); at each the cumulative code and
// the code of the block since the previous offset are printed.
use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};
use std::time::Instant;

#[derive(Default)]
struct Fx(u64);
impl Hasher for Fx {
    fn finish(&self) -> u64 { self.0 }
    fn write(&mut self, _: &[u8]) { unreachable!() }
    fn write_u64(&mut self, x: u64) { self.0 = (x ^ (x >> 31)).wrapping_mul(0x9E37_79B9_7F4A_7C15); }
}

struct Node { n: [u32; 4], l: [f64; 4], tl: u32, lb: f64 }

fn peak_mib() -> u64 {
    let s = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
    s.lines().find(|l| l.starts_with("VmHWM:"))
        .and_then(|l| l.split_whitespace().nth(1)).and_then(|v| v.parse::<u64>().ok())
        .map(|k| k / 1024).unwrap_or(0)
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let depth: usize = a[1].parse().unwrap();
    let kbits: f64 = a[2].parse().unwrap();
    let m: i32 = a[3].parse().unwrap();
    let w: f64 = a[4].parse().unwrap();
    let data = std::fs::read(&a[5]).unwrap();
    let marks: Vec<usize> = a.get(6).map(|m| m.trim().split(',').map(|x| x.parse().unwrap()).collect()).unwrap_or_default();
    let mut mi = 0usize;
    let (mut last_cell, mut last_bits) = (0usize, 0.0f64);
    assert!(depth <= 24);
    let t0 = Instant::now();
    let d: Vec<u8> = data.iter().flat_map(|&b| [b >> 6, (b >> 4) & 3, (b >> 2) & 3, b & 3]).collect();
    let n = d.len();
    let gamma = if m > 0 { 1.0 - (2f64).powi(-m) } else { 0.0 };
    let bound = if kbits > 0.0 { kbits * std::f64::consts::LN_2 } else { f64::INFINITY };
    let mut index: HashMap<u64, u32, BuildHasherDefault<Fx>> = HashMap::default();
    let mut nodes: Vec<Node> = Vec::new();
    let mask = |k: usize| -> u64 { if k == 0 { 0 } else { (1u64 << (2 * k)) - 1 } };
    let mut ctx: u64 = 0;
    let mut bits = 0.0f64;
    let q4 = (n / 4).max(1);
    let mut seg = [0.0f64; 4];
    let mut path = vec![0usize; depth + 1];
    let mut e = vec![[0.0f64; 4]; depth + 1];
    let mut qs = vec![[0.0f64; 4]; depth + 2];
    let mut clamped: u64 = 0;
    let mut max_lb: f64 = 0.0;
    for t in 0..n {
        let u = d[t] as usize;
        let ph = (t % 4) as u64;
        for k in 0..=depth {
            let key = ((k as u64) << 58) | (ph << 56) | (ctx & mask(k));
            let len = nodes.len() as u32;
            let i = *index.entry(key).or_insert(len) as usize;
            if i == nodes.len() {
                nodes.push(Node { n: [0; 4], l: [0.0; 4], tl: t as u32, lb: 0.0 });
            }
            let nd = &mut nodes[i];
            if m > 0 {
                let f = gamma.powi((t as u32 - nd.tl) as i32);
                for s in 0..4 { nd.l[s] *= f; }
                nd.tl = t as u32;
            }
            let mut c = [0.0f64; 4];
            let mut tot = 0.0;
            for s in 0..4 { c[s] = nd.n[s] as f64 + w * nd.l[s]; tot += c[s]; }
            for s in 0..4 { e[k][s] = (c[s] + 0.5) / (tot + 2.0); }
            path[k] = i;
        }
        // conditionals from the deepest node up
        qs[depth] = e[depth];
        for k in (0..depth).rev() {
            let b = nodes[path[k]].lb.exp();
            for s in 0..4 { qs[k][s] = (b * e[k][s] + qs[k + 1][s]) / (b + 1.0); }
        }
        let z: f64 = qs[0].iter().sum();
        let lb = -(qs[0][u] / z).log2();
        bits += lb;
        seg[(t / q4).min(3)] += lb;
        for k in 0..depth {
            let nd = &mut nodes[path[k]];
            let mut v = nd.lb + e[k][u].ln() - qs[k + 1][u].ln();
            if v > bound { v = bound; clamped += 1; } else if v < -bound { v = -bound; clamped += 1; }
            if v.abs() > max_lb { max_lb = v.abs(); }
            nd.lb = v;
        }
        for k in 0..=depth {
            let nd = &mut nodes[path[k]];
            nd.n[u] += 1;
            if m > 0 { nd.l[u] += 1.0; }
        }
        ctx = ((ctx << 2) | u as u64) & mask(24);
        if mi < marks.len() && t + 1 == marks[mi] {
            println!("  at {:>9} cells: cumulative {:.4}; block from {:>9}: {:.4} bits/cell  ({:.1} s, nodes {})",
                t + 1, bits / (t + 1) as f64, last_cell, (bits - last_bits) / (t + 1 - last_cell) as f64,
                t0.elapsed().as_secs_f64(), nodes.len());
            last_cell = t + 1; last_bits = bits; mi += 1;
        }
    }
    let el = t0.elapsed().as_secs_f64();
    println!(
        "D={:2} K={} m={:2} w={} cells {}: online {:.4} bits/digit; quarters {:.4} {:.4} {:.4} {:.4}; max |log2 beta| {:.1}; releases {}; nodes {}  ({:.1} s, {:.2} us/cell, peak {} MiB)",
        depth, kbits, m, w, n, bits / n as f64,
        seg[0] / q4 as f64, seg[1] / q4 as f64, seg[2] / q4 as f64, seg[3] / (n - 3 * q4) as f64,
        max_lb / std::f64::consts::LN_2, clamped, nodes.len(), el, 1e6 * el / n as f64, peak_mib()
    );
}
