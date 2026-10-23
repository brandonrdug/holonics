// Exterior read: what a located equality adds over the released tree and its passage.
// Base: context-tree weighting, one tree per frame phase, ratio released into [2^-K, 2^K], each
// node's estimator over c = n + w l (the passage term at gamma = 1 - 2^-m), as in ctw_beta.rs.
// The located equality predicts that the next cell equals one earlier cell, c_hat, and joins the
// face as P(c) ~ base(c) 2^(alpha [c = c_hat]); alpha is held per bin (the lock's run length by
// octave, and the depth that located it, by fours) and stepped by the cumulative curvature,
// alpha <- alpha - (P(c_hat) - [u = c_hat]) / (ln 2 (1 + sum P(c_hat)(1 - P(c_hat)))).
// Two locks are read, each beside the base alone:
//   node:  c_hat is the successor of the deepest node's last visit (the indicator's mode at
//          lambda = 0); its run is the count of consecutive cells it predicted.
//   ring:  an offset delta is located at the deepest node with an earlier visit (delta = t - that
//          visit, the context's run of closed squares); while its contact holds (u_t = u_(t-delta))
//          the offset is kept and the run grows; at a slip it is released and located again.
// Arguments: D K m w file [bytes_out]. Prints the online code of the base and of each arm.
// LOCK_NO_RUN=1 is the control: the bins read the locating depth only, not the run.
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

struct Node { n: [u32; 4], l: [f64; 4], tl: u32, lb: f64, nx: u8 }

const NONE: u8 = 255;
const OCT: usize = 12;
const DB: usize = 7;

struct Arm { alpha: Vec<f64>, h: Vec<f64>, bits: f64, run: u32, hits: u64, tries: u64 }
impl Arm {
    fn new() -> Self { Arm { alpha: vec![0.0; OCT * DB], h: vec![0.0; OCT * DB], bits: 0.0, run: 0, hits: 0, tries: 0 } }
}

fn octave(run: u32) -> usize {
    // LOCK_NO_RUN=1 reads the control whose bins ignore the run (depth alone)
    if std::env::var("LOCK_NO_RUN").map(|v| v == "1").unwrap_or(false) { return 0; }
    ((32 - (run + 1).leading_zeros()) as usize - 1).min(OCT - 1)
}

// score u under base joined with the lock (c_hat, bin); step alpha; return bits
fn join(arm: &mut Arm, base: &[f64; 4], u: usize, c_hat: Option<usize>, bin: usize) -> f64 {
    match c_hat {
        None => -base[u].log2(),
        Some(c) => {
            let a = arm.alpha[bin];
            let e = a.exp2();
            let z = 1.0 + base[c] * (e - 1.0);
            let pc = base[c] * e / z;
            let pu = if u == c { pc } else { base[u] / z };
            let g = pc - if u == c { 1.0 } else { 0.0 };
            arm.h[bin] += pc * (1.0 - pc);
            arm.alpha[bin] = a - g / (std::f64::consts::LN_2 * (1.0 + arm.h[bin]));
            arm.tries += 1;
            if u == c { arm.hits += 1; }
            -pu.log2()
        }
    }
}

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
    let bytes_out = a.get(6).cloned();
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
    let mut path = vec![0usize; depth + 1];
    let mut prev = vec![u32::MAX; depth + 1];
    let mut e = vec![[0.0f64; 4]; depth + 1];
    let mut qs = vec![[0.0f64; 4]; depth + 2];
    let mut base_bits = 0.0f64;
    let (mut node_arm, mut ring_arm) = (Arm::new(), Arm::new());
    let (mut delta, mut ring_depth): (usize, usize) = (0, 0);
    let mut byte_bits: Vec<[f32; 3]> = vec![[0.0; 3]; if bytes_out.is_some() { n / 4 } else { 0 }];
    let ln2 = std::f64::consts::LN_2;
    for t in 0..n {
        let u = d[t] as usize;
        let ph = (t % 4) as u64;
        for k in 0..=depth {
            let key = ((k as u64) << 58) | (ph << 56) | (ctx & mask(k));
            let len = nodes.len() as u32;
            let i = *index.entry(key).or_insert(len) as usize;
            if i == nodes.len() {
                nodes.push(Node { n: [0; 4], l: [0.0; 4], tl: u32::MAX, lb: 0.0, nx: NONE });
            }
            let nd = &mut nodes[i];
            prev[k] = nd.tl;
            if m > 0 && nd.tl != u32::MAX {
                let f = gamma.powi((t as u32 - nd.tl) as i32);
                for s in 0..4 { nd.l[s] *= f; }
            }
            nd.tl = t as u32;
            let mut c = [0.0f64; 4];
            let mut tot = 0.0;
            for s in 0..4 { c[s] = nd.n[s] as f64 + w * nd.l[s]; tot += c[s]; }
            for s in 0..4 { e[k][s] = (c[s] + 0.5) / (tot + 2.0); }
            path[k] = i;
        }
        qs[depth] = e[depth];
        for k in (0..depth).rev() {
            let b = nodes[path[k]].lb.exp();
            for s in 0..4 { qs[k][s] = (b * e[k][s] + qs[k + 1][s]) / (b + 1.0); }
        }
        let z: f64 = qs[0].iter().sum();
        let mut base = qs[0];
        for s in 0..4 { base[s] /= z; }
        let lb0 = -base[u].log2();
        base_bits += lb0;

        // node lock: the deepest node holding a successor
        let mut nhat = None;
        let mut ndep = 0;
        for k in (0..=depth).rev() {
            let x = nodes[path[k]].nx;
            if x != NONE { nhat = Some(x as usize); ndep = k; break; }
        }
        let nbin = octave(node_arm.run) * DB + (ndep / 4).min(DB - 1);
        let lb1 = join(&mut node_arm, &base, u, nhat, nbin);
        node_arm.bits += lb1;
        match nhat { Some(c) if c == u => node_arm.run += 1, _ => node_arm.run = 0 }

        // ring lock: a located offset held while its contact holds
        if delta == 0 {
            for k in (1..=depth).rev() {
                if prev[k] != u32::MAX { delta = t - prev[k] as usize; ring_depth = k; ring_arm.run = 0; break; }
            }
        }
        let rhat = if delta > 0 { Some(d[t - delta] as usize) } else { None };
        let rbin = octave(ring_arm.run) * DB + (ring_depth / 4).min(DB - 1);
        let lb2 = join(&mut ring_arm, &base, u, rhat, rbin);
        ring_arm.bits += lb2;
        match rhat { Some(c) if c == u => ring_arm.run += 1, _ => { delta = 0; ring_arm.run = 0; } }

        if bytes_out.is_some() { let bb = &mut byte_bits[t / 4]; bb[0] += lb0 as f32; bb[1] += lb1 as f32; bb[2] += lb2 as f32; }

        for k in 0..depth {
            let nd = &mut nodes[path[k]];
            let mut v = nd.lb + e[k][u].ln() - qs[k + 1][u].ln();
            if v > bound { v = bound; } else if v < -bound { v = -bound; }
            nd.lb = v;
        }
        for k in 0..=depth {
            let nd = &mut nodes[path[k]];
            nd.n[u] += 1;
            if m > 0 { nd.l[u] += 1.0; }
            nd.nx = u as u8;
        }
        ctx = ((ctx << 2) | u as u64) & mask(24);
    }
    let _ = ln2;
    let el = t0.elapsed().as_secs_f64();
    println!("D={} K={} m={} w={} cells {}: base {:.4}; node lock {:.4} (predicts {:.3} of cells, right {:.3}); ring lock {:.4} (predicts {:.3}, right {:.3})  ({:.1} s, {:.2} us/cell, peak {} MiB, nodes {})",
        depth, kbits, m, w, n, base_bits / n as f64,
        node_arm.bits / n as f64, node_arm.tries as f64 / n as f64, node_arm.hits as f64 / node_arm.tries.max(1) as f64,
        ring_arm.bits / n as f64, ring_arm.tries as f64 / n as f64, ring_arm.hits as f64 / ring_arm.tries.max(1) as f64,
        el, 1e6 * el / n as f64, peak_mib(), nodes.len());
    if let Some(p) = bytes_out {
        let mut out = Vec::with_capacity(byte_bits.len() * 12);
        for b in &byte_bits { for x in b { out.extend_from_slice(&x.to_le_bytes()); } }
        std::fs::write(p, out).unwrap();
    }
}
