//! **Participation: a site reads the passage's earlier sites through the modes' own transport**
//! (#404, #406; record `2026-10-28_ATTENTION_IS_THE_FIELDS_PARTICIPATION_THROUGH_ITS_OWN_TRANSPORT…`,
//! §3 and §6).
//!
//! [definition; agent-inferred, October 29] One head is one rung of the turn ladder: modes that share
//! a memory. Each mode carries, from the section's opening, its frame `U_t = Π_(k≤t) u_k` (the unit
//! moves' running product, `u = λ/|λ|`) and its met dissipation `L_t = Σ_(k≤t) −log₂|λ_k|`, so the
//! transport between two sites is `U_i conj(U_j) 2^(−(L_i − L_j))`. A site presents its charts rotated
//! back into the opening's frame, and the present site probes with its own:
//!
//! ```text
//! charts     q_i = conj(U_i) ⊙ Ȟ_i,   k_j = conj(U_j) ⊙ H_j,   w_j = conj(U_j) ⊙ Ψ_j
//! face       z_ij = β Re⟨q_i, k_j⟩ − κ (L̄_i − L̄_j),   j ≤ i        L̄ the head's mean, in bits
//! weights    e_ij = 2^(z_ij − max_j z_ij)                            the Gibbs face, its origin a gauge
//! current    m_i = Σ_j e_ij,   J_i = Σ_j e_ij w_j,   y_i = U_i ⊙ J_i / m_i
//! return     g'_i = conj(U_i) ⊙ g_i,   a_ij = e_ij / m_i
//!            g_w_j = a_ij g'_i,   g_a_ij = Re⟨w_j, g'_i⟩,   g_z_ij = ln 2 · a_ij (g_a_ij − Σ_k a_ik g_a_ik)
//!            g_q_i = β Σ_j g_z_ij k_j,   g_k_j = β g_z_ij q_i,   g_κ = −Σ_j g_z_ij (L̄_i − L̄_j)
//! ```
//!
//! `Re⟨q, k⟩ = Re Σ_m conj(q_m) k_m` is the pairing of a coholon chart with a Holon chart through
//! the turn the modes carried between them; `κ ≥ 0` is the head's friction, the dissipation its
//! contact meets as it slips back along the passage. Nothing is written to be looked up: the sites'
//! charts are the section's present terrain, the address is the transport, and the weights are
//! recomputed from the present field at every site.
//!
//! **What the tower already was.** With no pairing (`q = 0`) and unit friction, `m_i y_i` is the
//! head's recurrence `h_i = Σ_(j≤i) T_ij Ψ_j`: the tower is this law's participation-one restriction
//! (tested below).
//!
//! **The reach is released, never authored.** A site whose face lies `2^(UNIT)` or more below the
//! peak would weigh less than the mass's grain; it is released by that partition and counted
//! (`released`), its share of the mass below `released · 2^(−62)` of the peak's.
//!
//! **Exact integers, grains declared.** Charts, faces and the current on `2^(−16)`; frames on
//! `2^(−30)`; weights on `2^(−62)` relative to the peak; the return on `2^(−24)`. Every product's
//! remainder below its grain is released to the nearest numerator, and every sum is an integer sum,
//! so the sites summed in any order give the same bits.
//!
//! **Not claimed.** The return stops at the frame and the dissipation: the transport's own covector
//! `Σ a dU Ψ` into the gates and turns is owed, as is the pump's reflection share (record §8).
use super::{div_nearest, fit64, refuse, release, Result, FACE_BITS, MOVE_BITS, UNIT_BITS};
use crate::hnn::keyed_modes::{ln2_face, Exponential};

/// A complex numerator pair on a declared grain.
pub type Phasor = (i64, i64);

/// One head's declared and learned law: the pairing's scale `β = 2^(−beta_shift)` and the friction
/// `κ` on `2^(−16)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Head {
    pub beta_shift: u32,
    pub friction: i64,
}

impl Head {
    /// [agent-inferred] The founded head over `modes` modes: `β = 2^(−⌈½ log₂ modes⌉)`, so the
    /// pairing of two unit-power charts keeps a spread of order one, and `κ = 1`, so a head first
    /// forgets as its rung does (the recurrence's own decay).
    pub fn founded(modes: usize) -> Self {
        let bits = usize::BITS - modes.max(1).next_power_of_two().leading_zeros() - 1;
        Self { beta_shift: bits.div_ceil(2), friction: 1 << FACE_BITS }
    }
}

/// An admitted site's rotated charts and its mean met dissipation (bits on `2^(−16)`).
#[derive(Clone, Copy, Debug)]
pub struct Site<'a> {
    pub k: &'a [Phasor],
    pub w: &'a [Phasor],
    pub dissipation: i64,
}

/// The present site's rotated probe, its frame on `2^(−30)` and its mean met dissipation.
#[derive(Clone, Copy, Debug)]
pub struct Probe<'a> {
    pub q: &'a [Phasor],
    pub unit: &'a [Phasor],
    pub dissipation: i64,
}

/// The participating current at one site, with the weights and mass its return reads.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Participation {
    /// `y_i` on `2^(−16)`, one phasor a mode.
    pub current: Vec<Phasor>,
    /// `e_ij` on `2^(−62)` relative to the peak; zero for a released site.
    pub weights: Vec<u128>,
    pub mass: u128,
    pub released: usize,
}

/// The covectors the participation returns, on `2^(−24)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParticipationReturn {
    pub probe: Vec<Phasor>,
    pub keys: Vec<Vec<Phasor>>,
    pub currents: Vec<Vec<Phasor>>,
    pub friction: i128,
}

fn conj_mul(a: Phasor, b: Phasor) -> (i128, i128) {
    let (ar, ai, br, bi) = (a.0 as i128, a.1 as i128, b.0 as i128, b.1 as i128);
    (ar * br + ai * bi, ar * bi - ai * br)
}

fn mul(a: Phasor, b: Phasor) -> (i128, i128) {
    let (ar, ai, br, bi) = (a.0 as i128, a.1 as i128, b.0 as i128, b.1 as i128);
    (ar * br - ai * bi, ar * bi + ai * br)
}

fn released(v: (i128, i128), bits: u32) -> Result<Phasor> {
    Ok((fit64(release(v.0, bits))?, fit64(release(v.1, bits))?))
}

/// A mode's frame advanced by one move: `U ← U u`, both on `2^(−30)`.
pub fn advance_frame(frame: Phasor, unit: Phasor) -> Result<Phasor> {
    released(mul(frame, unit), MOVE_BITS)
}

/// `conj(U) ⊙ c`: a chart on `2^(−16)` rotated back by its site's frame on `2^(−30)`.
pub fn rotate_back(frame: &[Phasor], chart: &[Phasor]) -> Result<Vec<Phasor>> {
    if frame.len() != chart.len() {
        return refuse("a chart and its frame of different modes");
    }
    frame.iter().zip(chart).map(|(&u, &c)| released(conj_mul(u, c), MOVE_BITS)).collect()
}

/// `z_ij` on `2^(−16)`.
fn face(head: &Head, probe: &Probe, site: &Site) -> Result<i128> {
    if site.k.len() != probe.q.len() {
        return refuse("a site of other modes than the probe");
    }
    let pairing: i128 = probe.q.iter().zip(site.k).map(|(&q, &k)| conj_mul(q, k).0).sum();
    let score = release(pairing, FACE_BITS + head.beta_shift);
    let met = probe.dissipation as i128 - site.dissipation as i128;
    Ok(score - release(head.friction as i128 * met, FACE_BITS))
}

/// The participation of the admitted sites at the probe (the sites `j ≤ i`, the present one last).
pub fn participate(head: &Head, probe: &Probe, sites: &[Site], exponential: &Exponential) -> Result<Participation> {
    if sites.is_empty() {
        return refuse("a participation with no admitted site");
    }
    if head.friction < 0 {
        return refuse("a friction that pumps");
    }
    let modes = probe.q.len();
    if probe.unit.len() != modes || sites.iter().any(|s| s.w.len() != modes) {
        return refuse("a site of other modes than the probe");
    }
    let faces = sites.iter().map(|s| face(head, probe, s)).collect::<Result<Vec<_>>>()?;
    let peak = *faces.iter().max().expect("nonempty");
    let reach = (UNIT_BITS as i128) << FACE_BITS;
    let mut weights = Vec::with_capacity(sites.len());
    let (mut mass, mut released_sites) = (0u128, 0usize);
    let mut current = vec![(0i128, 0i128); modes];
    for (site, &z) in sites.iter().zip(&faces) {
        if peak - z >= reach {
            weights.push(0);
            released_sites += 1;
            continue;
        }
        let e = exponential.below_one(z - peak);
        mass += e;
        for (c, &w) in current.iter_mut().zip(site.w) {
            c.0 = c.0.checked_add(e as i128 * w.0 as i128).ok_or(super::TowerError::Refused("a current past its carrier"))?;
            c.1 = c.1.checked_add(e as i128 * w.1 as i128).ok_or(super::TowerError::Refused("a current past its carrier"))?;
        }
        weights.push(e);
    }
    let mass_i = mass as i128;
    let current = current
        .iter()
        .zip(probe.unit)
        .map(|(&(re, im), &u)| {
            let mean = (fit64(div_nearest(re, mass_i))?, fit64(div_nearest(im, mass_i))?);
            released(mul(u, mean), MOVE_BITS)
        })
        .collect::<Result<Vec<_>>>()?;
    Ok(Participation { current, weights, mass, released: released_sites })
}

/// The participation's return for the covector `g` on its current (`2^(−24)`, one phasor a mode).
pub fn participation_return(head: &Head, probe: &Probe, sites: &[Site], part: &Participation, g: &[Phasor]) -> Result<ParticipationReturn> {
    let modes = probe.q.len();
    if g.len() != modes || part.weights.len() != sites.len() || part.mass == 0 {
        return refuse("a return that is not its participation's");
    }
    let mass = part.mass as i128;
    // g'_i = conj(U_i) ⊙ g_i on 2^(−24).
    let back = probe.unit.iter().zip(g).map(|(&u, &c)| released(conj_mul(u, c), MOVE_BITS)).collect::<Result<Vec<_>>>()?;
    // g_a_ij = Re⟨w_j, g'⟩ on 2^(−24), and its weighted mean Ē.
    let ga: Vec<i128> = sites
        .iter()
        .map(|s| release(s.w.iter().zip(&back).map(|(&w, &b)| conj_mul(w, b).0).sum(), FACE_BITS))
        .collect();
    let mean = div_nearest(part.weights.iter().zip(&ga).map(|(&e, &a)| e as i128 * a).sum(), mass);
    let ln2 = ln2_face();
    let mut ret = ParticipationReturn { probe: vec![(0, 0); modes], keys: Vec::with_capacity(sites.len()), currents: Vec::with_capacity(sites.len()), friction: 0 };
    let mut probe_acc = vec![(0i128, 0i128); modes];
    for ((site, &e), &a) in sites.iter().zip(&part.weights).zip(&ga) {
        let e = e as i128;
        ret.currents.push(back.iter().map(|&b| Ok((fit64(div_nearest(e * b.0 as i128, mass))?, fit64(div_nearest(e * b.1 as i128, mass))?))).collect::<Result<Vec<_>>>()?);
        let gz = release(ln2 * div_nearest(e * (a - mean), mass), MOVE_BITS);
        let met = probe.dissipation as i128 - site.dissipation as i128;
        ret.friction -= release(gz * met, FACE_BITS);
        // g_k_j = β g_z q_i and g_q_i += β g_z k_j, on 2^(−24).
        let scale = FACE_BITS + head.beta_shift;
        ret.keys.push(probe.q.iter().map(|&q| Ok((fit64(release(gz * q.0 as i128, scale))?, fit64(release(gz * q.1 as i128, scale))?))).collect::<Result<Vec<_>>>()?);
        for (acc, &k) in probe_acc.iter_mut().zip(site.k) {
            acc.0 += gz * k.0 as i128;
            acc.1 += gz * k.1 as i128;
        }
    }
    ret.probe = probe_acc.iter().map(|&(re, im)| Ok((fit64(release(re, FACE_BITS + head.beta_shift))?, fit64(release(im, FACE_BITS + head.beta_shift))?))).collect::<Result<Vec<_>>>()?;
    Ok(ret)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mix(seed: &mut u64) -> u64 {
        *seed = seed.wrapping_add(0x9e3779b97f4a7c15);
        let mut x = *seed;
        x = (x ^ (x >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        x = (x ^ (x >> 27)).wrapping_mul(0x94d049bb133111eb);
        x ^ (x >> 31)
    }
    fn draw(seed: &mut u64, reach: i64) -> i64 {
        (mix(seed) % (2 * reach as u64 + 1)) as i64 - reach
    }
    fn phasors(seed: &mut u64, n: usize, reach: i64) -> Vec<Phasor> {
        (0..n).map(|_| (draw(seed, reach), draw(seed, reach))).collect()
    }
    fn unit_of(seed: &mut u64) -> Phasor {
        // A unit on 2^(−30) from a Pythagorean pair (3,4,5)-style scaled exactly: (a² − b², 2ab)/(a² + b²).
        let a = (mix(seed) % 200 + 1) as i128;
        let b = (mix(seed) % 200) as i128;
        let n = a * a + b * b;
        (div_nearest((a * a - b * b) << MOVE_BITS, n) as i64, div_nearest((2 * a * b) << MOVE_BITS, n) as i64)
    }

    struct Passage {
        q: Vec<Phasor>,
        unit: Vec<Phasor>,
        k: Vec<Vec<Phasor>>,
        w: Vec<Vec<Phasor>>,
        l: Vec<i64>,
        probe_l: i64,
    }
    impl Passage {
        fn new(seed: u64, modes: usize, sites: usize) -> Self {
            let mut s = seed;
            let q = phasors(&mut s, modes, 1 << 17);
            let unit = (0..modes).map(|_| unit_of(&mut s)).collect();
            let k = (0..sites).map(|_| phasors(&mut s, modes, 1 << 17)).collect();
            let w = (0..sites).map(|_| phasors(&mut s, modes, 1 << 18)).collect();
            let l: Vec<i64> = (0..sites).map(|j| (j as i64) * (1 << 13)).collect();
            let probe_l = *l.last().unwrap();
            Self { q, unit, k, w, l, probe_l }
        }
        fn sites(&self) -> Vec<Site<'_>> {
            (0..self.k.len()).map(|j| Site { k: &self.k[j], w: &self.w[j], dissipation: self.l[j] }).collect()
        }
        fn probe(&self) -> Probe<'_> {
            Probe { q: &self.q, unit: &self.unit, dissipation: self.probe_l }
        }
    }

    fn exponential() -> Exponential {
        Exponential::new(FACE_BITS)
    }

    #[test]
    fn a_common_quarter_turn_and_a_common_origin_leave_the_participation_unchanged() {
        let p = Passage::new(7, 8, 24);
        let head = Head { beta_shift: 2, friction: 3 << 15 };
        let base = participate(&head, &p.probe(), &p.sites(), &exponential()).unwrap();
        // Every site's frame turned by i: q, k and w turn by conj(i), the probe's frame by i.
        let back = |v: &[Phasor]| v.iter().map(|&(re, im)| (im, -re)).collect::<Vec<_>>();
        let mut t = Passage { q: back(&p.q), unit: p.unit.iter().map(|&(re, im)| (-im, re)).collect(), k: p.k.iter().map(|v| back(v)).collect(), w: p.w.iter().map(|v| back(v)).collect(), l: p.l.clone(), probe_l: p.probe_l };
        let turned = participate(&head, &t.probe(), &t.sites(), &exponential()).unwrap();
        assert_eq!(base, turned);
        // A common origin of the met dissipation.
        t = Passage { q: p.q.clone(), unit: p.unit.clone(), k: p.k.clone(), w: p.w.clone(), l: p.l.iter().map(|l| l + 12_345).collect(), probe_l: p.probe_l + 12_345 };
        assert_eq!(base, participate(&head, &t.probe(), &t.sites(), &exponential()).unwrap());
    }

    #[test]
    fn relabeling_the_sites_leaves_the_current_unchanged() {
        let p = Passage::new(11, 6, 17);
        let head = Head::founded(6);
        let base = participate(&head, &p.probe(), &p.sites(), &exponential()).unwrap();
        let mut sites = p.sites();
        sites.reverse();
        sites.swap(2, 9);
        let relabeled = participate(&head, &p.probe(), &sites, &exponential()).unwrap();
        assert_eq!(base.current, relabeled.current);
        assert_eq!(base.mass, relabeled.mass);
    }

    #[test]
    fn with_no_pairing_and_unit_friction_the_current_is_the_recurrence_over_its_mass() {
        // One rung: every mode keeps |λ| = 1 − 2^(−4), each its own unit u_m.
        let (modes, sites) = (4, 40);
        let mut s = 3u64;
        let units: Vec<Phasor> = (0..modes).map(|_| unit_of(&mut s)).collect();
        let pushes: Vec<Vec<Phasor>> = (0..sites).map(|_| phasors(&mut s, modes, 1 << 18)).collect();
        let rho = (1i128 << MOVE_BITS) - (1i128 << (MOVE_BITS - 4));
        let met = -crate::hnn::keyed_modes::log2_face((rho as u128) << (UNIT_BITS - MOVE_BITS), FACE_BITS) as i64;
        // The recurrence h_t = ρ u h_(t−1) + Ψ_t on 2^(−16).
        let mut h = vec![(0i128, 0i128); modes];
        let mut frames = vec![vec![(1i64 << MOVE_BITS, 0i64); modes]];
        for t in 0..sites {
            if t > 0 {
                let last = frames.last().unwrap().clone();
                frames.push(last.iter().zip(&units).map(|(&f, &u)| advance_frame(f, u).unwrap()).collect());
            }
            for m in 0..modes {
                let (re, im) = mul((h[m].0 as i64, h[m].1 as i64), units[m]);
                let (re, im) = (release(re, MOVE_BITS) * rho, release(im, MOVE_BITS) * rho);
                h[m] = (release(re, MOVE_BITS) + pushes[t][m].0 as i128, release(im, MOVE_BITS) + pushes[t][m].1 as i128);
            }
        }
        let w: Vec<Vec<Phasor>> = (0..sites).map(|j| rotate_back(&frames[j], &pushes[j]).unwrap()).collect();
        let zero = vec![(0i64, 0i64); modes];
        let site_list: Vec<Site> = (0..sites).map(|j| Site { k: &zero, w: &w[j], dissipation: met * j as i64 }).collect();
        let probe = Probe { q: &zero, unit: &frames[sites - 1], dissipation: met * (sites as i64 - 1) };
        let head = Head { beta_shift: 0, friction: 1 << FACE_BITS };
        let part = participate(&head, &probe, &site_list, &exponential()).unwrap();
        for m in 0..modes {
            let (re, im) = (part.current[m].0 as i128 * part.mass as i128, part.current[m].1 as i128 * part.mass as i128);
            let (re, im) = (release(re, UNIT_BITS), release(im, UNIT_BITS));
            let tol = (sites as i128) << 8;
            assert!((re - h[m].0).abs() <= tol && (im - h[m].1).abs() <= tol, "mode {m}: {re},{im} against {:?}", h[m]);
        }
    }

    fn reading(head: &Head, p: &Passage, c: &[Phasor]) -> i128 {
        let part = participate(head, &p.probe(), &p.sites(), &exponential()).unwrap();
        part.current.iter().zip(c).map(|(&y, &c)| conj_mul(c, y).0).sum()
    }

    #[test]
    fn the_return_matches_the_difference_of_a_declared_reading() {
        let p = Passage::new(19, 4, 9);
        let head = Head { beta_shift: 1, friction: 1 << 14 };
        let mut s = 5u64;
        // f(y) = Re⟨c, y⟩ with c on 2^(−24): its covector on y is c.
        let c = phasors(&mut s, 4, 1 << 24);
        let part = participate(&head, &p.probe(), &p.sites(), &exponential()).unwrap();
        let ret = participation_return(&head, &p.probe(), &p.sites(), &part, &c).unwrap();
        // df = Re(conj(G) dx) for each complex input. f's numerators sit on 2^(−40), an input's on
        // 2^(−16) and the return's on 2^(−24), so a step of δ input numerators moves f by G δ numerators.
        let delta = 1i64 << 12;
        let floor = 1i128 << 14;
        let carried = std::cell::Cell::new(0usize);
        let check = |name: &str, plus: i128, minus: i128, predicted: i64| {
            let measured = (plus - minus) / (2 * delta as i128);
            let predicted = predicted as i128;
            let tol = predicted.abs() / 16 + floor;
            assert!((measured - predicted).abs() <= tol, "{name}: measured {measured}, predicted {predicted}");
            if predicted.abs() > 8 * floor {
                carried.set(carried.get() + 1);
            }
        };
        for m in 0..4 {
            let mut up = Passage { q: p.q.clone(), unit: p.unit.clone(), k: p.k.clone(), w: p.w.clone(), l: p.l.clone(), probe_l: p.probe_l };
            let mut down = Passage { q: p.q.clone(), unit: p.unit.clone(), k: p.k.clone(), w: p.w.clone(), l: p.l.clone(), probe_l: p.probe_l };
            up.w[3][m].0 += delta;
            down.w[3][m].0 -= delta;
            check("w", reading(&head, &up, &c), reading(&head, &down, &c), ret.currents[3][m].0);
            let (mut up, mut down) = (Passage { w: p.w.clone(), ..up }, Passage { w: p.w.clone(), ..down });
            up.k[5][m].1 += delta;
            down.k[5][m].1 -= delta;
            check("k", reading(&head, &up, &c), reading(&head, &down, &c), ret.keys[5][m].1);
            let (mut up, mut down) = (Passage { k: p.k.clone(), ..up }, Passage { k: p.k.clone(), ..down });
            up.q[m].0 += delta;
            down.q[m].0 -= delta;
            check("q", reading(&head, &up, &c), reading(&head, &down, &c), ret.probe[m].0);
        }
        // The check is not carried by its floor: most predicted covectors stand well above it.
        assert!(carried.get() >= 8, "only {} of 12 covectors stood above the floor", carried.get());
    }

    #[test]
    fn a_site_past_the_mass_grain_is_released_and_counted() {
        let p = Passage::new(23, 3, 64);
        let head = Head { beta_shift: 4, friction: 1 << 20 };
        let part = participate(&head, &p.probe(), &p.sites(), &exponential()).unwrap();
        assert!(part.released > 0 && part.released < 64);
        let kept: Vec<Site> = p.sites().into_iter().zip(&part.weights).filter(|(_, e)| **e > 0).map(|(s, _)| s).collect();
        let alone = participate(&head, &p.probe(), &kept, &exponential()).unwrap();
        assert_eq!(alone.current, part.current);
        assert_eq!(alone.released, 0);
    }
}
