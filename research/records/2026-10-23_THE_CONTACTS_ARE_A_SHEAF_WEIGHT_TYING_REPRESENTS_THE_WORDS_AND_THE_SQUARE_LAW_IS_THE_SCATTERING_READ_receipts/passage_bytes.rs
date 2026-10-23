// Exterior read: what does a passage tree add over the receiving tree? (This copy also writes each
// byte's code length, the sum over its four cells, as little-endian f32 to the path in argument 5.)
// Cells are base-4 digits of the bytes, high pair first (quarter-characters). Every cell is scored
// before it is counted (prequential): the online code length per cell.
// The tree: context-tree weighting over depths 0..D, one tree per frame phase (t mod 4). A node at
// depth k is addressed by the last k digits; its estimator predicts
//   q(a) = (c_a + 1/2) / (C + 2)                                  (KT when c = n),
// and P_w = 1/2 P_e + 1/2 prod_children P_w at internal nodes, P_w = P_e at depth D.
// The plain tree counts with lambda = 1: c = n. The passage tree adds the same indicator's mode at
// lambda = 1 - 2^-m (l, decayed lazily at each visit): c = n + w l. m = 0 reads the plain tree.
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

struct Node { n: [u32; 4], l: [f64; 4], tl: u32, lpe: f64, lpw: f64, lkids: f64 }

fn peak_mib() -> u64 {
    let s = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
    s.lines().find(|l| l.starts_with("VmHWM:"))
        .and_then(|l| l.split_whitespace().nth(1)).and_then(|v| v.parse::<u64>().ok())
        .map(|k| k / 1024).unwrap_or(0)
}

fn lae(a: f64, b: f64) -> f64 { let m = a.max(b); m + ((a - m).exp() + (b - m).exp()).ln() }

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let depth: usize = a[1].parse().unwrap();
    let m: i32 = a[2].parse().unwrap();
    let w: f64 = a[3].parse().unwrap();
    let data = std::fs::read(&a[4]).unwrap();
    assert!(depth <= 24);
    let t0 = Instant::now();
    let d: Vec<u8> = data.iter().flat_map(|&b| [b >> 6, (b >> 4) & 3, (b >> 2) & 3, b & 3]).collect();
    let n = d.len();
    let gamma = if m > 0 { 1.0 - (2f64).powi(-m) } else { 0.0 };
    let ln2 = std::f64::consts::LN_2;
    let mut index: HashMap<u64, u32, BuildHasherDefault<Fx>> = HashMap::default();
    let mut nodes: Vec<Node> = Vec::new();
    let mask = |k: usize| -> u64 { if k == 0 { 0 } else { (1u64 << (2 * k)) - 1 } };
    let mut ctx: u64 = 0;
    let mut bits = 0.0f64;
    let q = (n / 4).max(1);
    let mut seg = [0.0f64; 4];
    let mut path = vec![0usize; depth + 1];
    let mut byte_bits = vec![0.0f32; n / 4];
    let mut pe = vec![[0.0f64; 4]; depth + 1];
    for t in 0..n {
        let u = d[t] as usize;
        let ph = (t % 4) as u64;
        for k in 0..=depth {
            let key = ((k as u64) << 58) | (ph << 56) | (ctx & mask(k));
            let len = nodes.len() as u32;
            let i = *index.entry(key).or_insert(len) as usize;
            if i == nodes.len() {
                nodes.push(Node { n: [0; 4], l: [0.0; 4], tl: t as u32, lpe: 0.0, lpw: 0.0, lkids: 0.0 });
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
            for s in 0..4 { pe[k][s] = ((c[s] + 0.5) / (tot + 2.0)).ln(); }
            path[k] = i;
        }
        // the new root weight for each candidate symbol
        let mut p = [0.0f64; 4];
        let root_old = nodes[path[0]].lpw;
        for s in 0..4 {
            let mut child_old = 0.0;
            let mut child_new = 0.0;
            for k in (0..=depth).rev() {
                let nd = &nodes[path[k]];
                let lpe = nd.lpe + pe[k][s];
                let lpw = if k == depth { lpe } else { lae(lpe, nd.lkids + child_new - child_old) - ln2 };
                child_old = nd.lpw;
                child_new = lpw;
            }
            p[s] = (child_new - root_old).exp();
        }
        let z: f64 = p.iter().sum();
        let lb = -(p[u] / z).log2();
        bits += lb;
        byte_bits[t / 4] += lb as f32;
        seg[(t / q).min(3)] += lb;
        // commit the actual symbol
        let mut child_old = 0.0;
        let mut child_new = 0.0;
        for k in (0..=depth).rev() {
            let nd = &mut nodes[path[k]];
            nd.lpe += pe[k][u];
            if k < depth { nd.lkids += child_new - child_old; }
            let lpw = if k == depth { nd.lpe } else { lae(nd.lpe, nd.lkids) - ln2 };
            child_old = nd.lpw;
            child_new = lpw;
            nd.lpw = lpw;
            nd.n[u] += 1;
            if m > 0 { nd.l[u] += 1.0; }
        }
        ctx = ((ctx << 2) | u as u64) & mask(24);
    }
    std::fs::write(&a[5], byte_bits.iter().flat_map(|v| v.to_le_bytes()).collect::<Vec<u8>>()).unwrap();
    let el = t0.elapsed().as_secs_f64();
    println!(
        "D={:2} m={:2} w={} cells {}: online {:.4} bits/digit; quarters {:.4} {:.4} {:.4} {:.4}; nodes {}  ({:.1} s, {:.2} us/cell, peak {} MiB)",
        depth, m, w, n, bits / n as f64,
        seg[0] / q as f64, seg[1] / q as f64, seg[2] / q as f64, seg[3] / (n - 3 * q) as f64,
        nodes.len(), el, 1e6 * el / n as f64, peak_mib()
    );
}
