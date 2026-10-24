// Exterior read: what can a tower level driven by the face's news add over the tree and passage tree?
// The base face p is the passage tree below (context-tree weighting, c = n + w l). Two drives, both
// martingale differences when p is the true conditional:
//   news       e_t = [u_t] - p_t                     (direction, four coordinates, zero sum)
//   surprise   c_t = -ln p_t(u_t) - H(p_t)            (confidence; the covector of the face's temperature)
// Real modes z_k' = lam_k z_k + e_t, y_k' = lam_k y_k + c_t, horizons 2^2 .. 2^12 cells.
// Read: logits x = tau ln p + a with a_s = sum_k w_k z_(k,s) (arm A) and tau = 1 + sum_k v_k y_k
// (arm B), both (arm AB). Parameters theta = -(sum G'FG + I)^-1 sum G'(p - [u]), the Newton point of
// the quadratic model at the base face over the past (online: solved before the cell is scored).
// Also reported: the lagged correlation of each drive.
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
    const K: usize = 6;
    let lam: [f64; K] = [2, 4, 6, 8, 10, 12].map(|h: i32| 1.0 - (2f64).powi(-h));
    let mut zs = [[0.0f64; 4]; K];
    let mut ys = [0.0f64; K];
    let mut amat = [[0.0f64; 12]; 12];
    for i in 0..12 { amat[i][i] = 1.0; }
    let mut bvec = [0.0f64; 12];
    let mut bits_arm = [0.0f64; 3];
    let mut seg_arm = [[0.0f64; 4]; 3];
    let arms: [Vec<usize>; 3] = [(0..K).collect(), (K..2 * K).collect(), (0..2 * K).collect()];
    const LAGS: [usize; 12] = [1, 2, 3, 4, 8, 16, 32, 64, 128, 256, 1024, 4096];
    let mut ring_e = vec![[0.0f64; 4]; 4096];
    let mut ring_c = vec![0.0f64; 4096];
    let (mut se, mut sc, mut se0, mut sc0) = ([0.0f64; 12], [0.0f64; 12], 0.0f64, 0.0f64);
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
        let pb: [f64; 4] = [p[0] / z, p[1] / z, p[2] / z, p[3] / z];
        let lb = -pb[u].log2();
        bits += lb;
        seg[(t / q).min(3)] += lb;
        // the tower read, solved from the past before this cell is scored
        let lnp: [f64; 4] = pb.map(|x| x.ln());
        let mut g = [[0.0f64; 12]; 4];
        for s in 0..4 { for k in 0..K { g[s][k] = zs[k][s]; g[s][K + k] = lnp[s] * ys[k]; } }
        for (arm, idx) in arms.iter().enumerate() {
            let th = solve(&amat, &bvec, idx);
            let mut x = lnp;
            for s in 0..4 { for (j, &col) in idx.iter().enumerate() { x[s] += g[s][col] * th[j]; } }
            let mx = x.iter().cloned().fold(f64::MIN, f64::max);
            let ex: Vec<f64> = x.iter().map(|v| (v - mx).exp()).collect();
            let zz: f64 = ex.iter().sum();
            let la = -(ex[u] / zz).log2();
            bits_arm[arm] += la;
            seg_arm[arm][(t / q).min(3)] += la;
        }
        let mut gp = [0.0f64; 12];
        for j in 0..12 { for s in 0..4 { gp[j] += g[s][j] * pb[s]; } }
        for i in 0..12 { for j in 0..12 {
            let mut v = -gp[i] * gp[j];
            for s in 0..4 { v += pb[s] * g[s][i] * g[s][j]; }
            amat[i][j] += v;
        } }
        for j in 0..12 { bvec[j] += gp[j] - g[u][j]; }
        // the drives: news and centred surprise
        let mut e = [-pb[0], -pb[1], -pb[2], -pb[3]];
        e[u] += 1.0;
        let h: f64 = -(0..4).map(|s| if pb[s] > 0.0 { pb[s] * lnp[s] } else { 0.0 }).sum::<f64>();
        let c = -lnp[u] - h;
        for (i, &lag) in LAGS.iter().enumerate() {
            if t >= lag {
                let o = (t - lag) % 4096;
                se[i] += (0..4).map(|s| e[s] * ring_e[o][s]).sum::<f64>();
                sc[i] += c * ring_c[o];
            }
        }
        se0 += (0..4).map(|s| e[s] * e[s]).sum::<f64>();
        sc0 += c * c;
        ring_e[t % 4096] = e;
        ring_c[t % 4096] = c;
        for k in 0..K {
            for s in 0..4 { zs[k][s] = lam[k] * zs[k][s] + e[s]; }
            ys[k] = lam[k] * ys[k] + c;
        }
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
    let el = t0.elapsed().as_secs_f64();
    println!(
        "D={:2} m={:2} w={} cells {}: online {:.4} bits/digit; quarters {:.4} {:.4} {:.4} {:.4}; nodes {}  ({:.1} s, {:.2} us/cell, peak {} MiB)",
        depth, m, w, n, bits / n as f64,
        seg[0] / q as f64, seg[1] / q as f64, seg[2] / q as f64, seg[3] / (n - 3 * q) as f64,
        nodes.len(), el, 1e6 * el / n as f64, peak_mib()
    );
    for (arm, name) in ["A news", "B surprise", "AB both"].iter().enumerate() {
        let sa = &seg_arm[arm];
        println!("  tower {:<10}: online {:.4}; quarters {:.4} {:.4} {:.4} {:.4}", name, bits_arm[arm] / n as f64,
            sa[0] / q as f64, sa[1] / q as f64, sa[2] / q as f64, sa[3] / (n - 3 * q) as f64);
    }
    println!("  lag:             {}", LAGS.iter().map(|l| format!("{:>8}", l)).collect::<Vec<_>>().join(""));
    println!("  news corr:       {}", se.iter().map(|v| format!("{:>8.4}", v / se0)).collect::<Vec<_>>().join(""));
    println!("  surprise corr:   {}", sc.iter().map(|v| format!("{:>8.4}", v / sc0)).collect::<Vec<_>>().join(""));
}

// theta = -A^-1 b on the sub-block idx (Gaussian elimination with partial pivoting)
fn solve(a: &[[f64; 12]; 12], b: &[f64; 12], idx: &[usize]) -> Vec<f64> {
    let k = idx.len();
    let mut m = vec![vec![0.0f64; k + 1]; k];
    for i in 0..k { for j in 0..k { m[i][j] = a[idx[i]][idx[j]]; } m[i][k] = -b[idx[i]]; }
    for c in 0..k {
        let piv = (c..k).max_by(|&x, &y| m[x][c].abs().partial_cmp(&m[y][c].abs()).unwrap()).unwrap();
        m.swap(c, piv);
        for r in 0..k { if r != c {
            let f = m[r][c] / m[c][c];
            for j in c..=k { m[r][j] -= f * m[c][j]; }
        } }
    }
    (0..k).map(|i| m[i][k] / m[i][i]).collect()
}
