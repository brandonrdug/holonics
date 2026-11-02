//! [definition; agent-inferred, November 2] **The clock located by loop closure on the class sheet** (the dispersing
//! field's §16.15 and §16.16): the pace's rates are a key, located at a lap boundary from regions already seen (the
//! key schedule's D1), never descended.
//!
//! - **The menu** is the crib's alignment, admitted only where definite: every maximal run of equal classes between a
//!   region's answer and its question whose string occurs exactly once in each (a run that occurs at several places
//!   is a plural edge, an unlocated choice), entered at its first edge `(i ← j)`.
//! - **A loop** pairs two admitted runs whose answer targets one front band holds (their nearest edges fewer than the
//!   band's extent apart, §14.6's `[f, f + 5)`): one band's copies are read at one lag, one stationary transport.
//!   Its row is the gap `(j₁, i₁]`'s class counts less `(j₂, i₂]`'s; it closes the transport's whole ratio, the turn
//!   `Σ r_x κ_x = 0` and the skin `Σ r_x |κ_x| = 0`.
//! - **The fibre** `S` (the rates are homogeneous in a row) is computed by propagation: it opens as the intersection of
//!   the hyperplanes of regions with exactly one loop; a region with a loop whose hyperplane holds `S` is satisfied; a
//!   region with one live loop is forced; to a fixpoint. A region left with several live loops none holding `S` cuts
//!   it, and the fibre is plural: nothing is published. Then the forced loops' skin rows: where one side of a row is
//!   zero on `S`, the bytes of its other side are pinned at 0, to a fixpoint.
//! - **Publication** (a declared symmetry-breaking convention, beside hnn::keys's `S(p₀) = 0`): the current rates
//!   projected onto `S` in the port metric, `κ_pub = B(BᵀB)⁻¹Bᵀ κ_cur`, exactly; a direction no row reaches keeps its
//!   current rate (the free directions `N` are not deposited, §16.16).

use super::super::{refuse, Result};
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::Rat;
use num_bigint::BigInt;
use std::collections::BTreeSet;

/// One region's definite menu: its admitted runs `(i, j, length)` and its loops' rows (class counts over `classes`
/// classes), with each loop's two first edges.
#[derive(Clone, Debug)]
pub struct DefiniteMenu {
    pub runs: usize,
    pub admitted: Vec<(usize, usize, usize)>,
    pub rows: Vec<Vec<i64>>,
    pub edges: Vec<((usize, usize), (usize, usize))>,
}

/// [definition] **A region's definite menu** (the module header): `region` the question's classes then the answer's,
/// the question's length `question`, `classes` the class count, `band` the front band's extent.
pub fn definite_menu(region: &[usize], question: usize, classes: usize, band: usize) -> DefiniteMenu {
    let occurs = |s: &[usize], within: &[usize]| within.windows(s.len()).filter(|w| *w == s).count();
    let (asked, answer) = (&region[..question], &region[question..]);
    let (mut runs, mut admitted) = (0usize, Vec::new());
    for i in question..region.len() {
        for j in 0..question {
            let continues = i > question && j > 0 && region[i - 1] == region[j - 1];
            if region[i] != region[j] || continues {
                continue;
            }
            let mut length = 1;
            while i + length < region.len() && j + length < question && region[i + length] == region[j + length] {
                length += 1;
            }
            runs += 1;
            let s = &region[i..i + length];
            if occurs(s, asked) == 1 && occurs(s, answer) == 1 {
                admitted.push((i, j, length));
            }
        }
    }
    let (mut rows, mut edges) = (Vec::new(), Vec::new());
    for (k, &(i1, j1, l1)) in admitted.iter().enumerate() {
        for &(i2, j2, l2) in &admitted[k + 1..] {
            let apart = if i1 < i2 { i2 - (i1 + l1 - 1) } else { i1 - (i2 + l2 - 1) };
            if apart >= band || (i1 < i2) != (j1 < j2) || i1 == i2 || j1 == j2 {
                continue;
            }
            let ((i1, j1), (i2, j2)) = if i1 < i2 { ((i1, j1), (i2, j2)) } else { ((i2, j2), (i1, j1)) };
            let mut row = vec![0i64; classes];
            for &c in &region[j1 + 1..=i1] {
                row[c] += 1;
            }
            for &c in &region[j2 + 1..=i2] {
                row[c] -= 1;
            }
            edges.push(((i1, j1), (i2, j2)));
            rows.push(row);
        }
    }
    DefiniteMenu { runs, admitted, rows, edges }
}

/// [definition] **A located class clock** and its receipts: the published rates (one a class, `None` where the fibre
/// is plural or empty and nothing is published), the propagation's steps (`S`'s dimension after each), the regions
/// satisfied, cutting, empty and silent, the classes the skin pinned, and the forced loops live on both sides.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClassClock {
    pub published: Option<Vec<Rat>>,
    pub steps: Vec<(usize, usize)>,
    pub dimension: usize,
    pub satisfied: usize,
    pub cutting: usize,
    pub empty: usize,
    pub silent: usize,
    pub forcing: usize,
    pub skin_pinned: Vec<usize>,
    pub both_live: usize,
}

/// [definition] **Locate the class clock** (the module header) from seen regions `(classes, question length)`, with
/// the current rates `current` (one a class) and the front band `band`.
pub fn locate_class_clock(regions: &[(Vec<usize>, usize)], classes: usize, band: usize, current: &[Rat]) -> Result<ClassClock> {
    if current.len() != classes {
        return refuse("a class clock's current rates that are not one a class");
    }
    let menus: Vec<DefiniteMenu> = regions.iter().map(|(region, question)| definite_menu(region, *question, classes, band)).collect();
    let rat = |v: i64| Rat::from_integer(BigInt::from(v));
    let basis = |forcing: &[Vec<i64>]| -> Result<Vec<Vec<Rat>>> {
        if forcing.is_empty() {
            return Ok((0..classes).map(|b| (0..classes).map(|k| rat(i64::from(k == b))).collect()).collect());
        }
        let m = ExactRatMatrix::new(forcing.iter().map(|r| r.iter().map(|&v| rat(v)).collect()).collect()).map_err(|_| super::super::TowerError::Refused("a class clock's rows that are not a matrix"))?;
        m.kernel_basis().map_err(|_| super::super::TowerError::Refused("a class clock's kernel that does not reduce"))
    };
    let pairs = |row: &[i64], b: &[Rat]| -> Rat { row.iter().zip(b).map(|(&v, x)| rat(v) * x.clone()).sum() };
    let mut forcing: Vec<Vec<i64>> = menus.iter().filter(|m| m.rows.len() == 1 && m.rows[0].iter().any(|&v| v != 0)).map(|m| m.rows[0].clone()).collect();
    let mut b = basis(&forcing)?;
    let mut steps = vec![(forcing.len(), b.len())];
    let (satisfied, cutting, empty, silent) = loop {
        let (mut forced_now, mut sat, mut cut, mut emp, mut sil) = (Vec::new(), 0usize, 0usize, 0usize, 0usize);
        for m in &menus {
            if m.rows.is_empty() {
                sil += 1;
                continue;
            }
            let holds = |row: &Vec<i64>| b.iter().all(|v| pairs(row, v) == rat(0));
            if m.rows.iter().any(holds) {
                sat += 1;
                continue;
            }
            let live: Vec<&Vec<i64>> = m.rows.iter().filter(|row| b.len() >= 2 || holds(row)).collect();
            match live.len() {
                0 => emp += 1,
                1 => forced_now.push(live[0].clone()),
                _ => cut += 1,
            }
        }
        if emp > 0 || forced_now.is_empty() {
            break (sat, cut, emp, sil);
        }
        forcing.extend(forced_now.iter().cloned());
        b = basis(&forcing)?;
        steps.push((forced_now.len(), b.len()));
    };
    // The skin: the forced loops' rows close `Σ r |κ|` too.
    let loops_forced = forcing.clone();
    let (mut skin_pinned, mut both_live) = (Vec::new(), 0usize);
    loop {
        let zero_on_s = |x: usize| b.iter().all(|v| v[x] == rat(0));
        let (mut pins, mut live) = (BTreeSet::new(), 0usize);
        for row in &loops_forced {
            let (pos, neg): (Vec<usize>, Vec<usize>) = ((0..classes).filter(|&x| row[x] > 0).collect(), (0..classes).filter(|&x| row[x] < 0).collect());
            match (pos.iter().all(|&x| zero_on_s(x)), neg.iter().all(|&x| zero_on_s(x))) {
                (true, false) => pins.extend(neg.iter().copied().filter(|&x| !zero_on_s(x))),
                (false, true) => pins.extend(pos.iter().copied().filter(|&x| !zero_on_s(x))),
                (false, false) => live += 1,
                (true, true) => {}
            }
        }
        both_live = live;
        if pins.is_empty() {
            break;
        }
        skin_pinned.extend(pins.iter().copied());
        forcing.extend(pins.iter().map(|&x| (0..classes).map(|k| i64::from(k == x)).collect::<Vec<i64>>()));
        b = basis(&forcing)?;
    }
    let dimension = b.len();
    let forced = steps.iter().map(|s| s.0).sum();
    // Publication: one piece only (no region cutting, none empty), the current rates projected onto `S`.
    let published = if cutting == 0 && empty == 0 {
        let m = b.len();
        let gram = ExactRatMatrix::new((0..m).map(|x| (0..m).map(|y| b[x].iter().zip(&b[y]).map(|(p, q)| p.clone() * q.clone()).sum()).collect()).collect()).map_err(|_| super::super::TowerError::Refused("a class clock's Gram matrix"))?;
        let rhs: Vec<Rat> = (0..m).map(|x| b[x].iter().zip(current).map(|(p, q)| p.clone() * q.clone()).sum()).collect();
        let solved = gram.preimage_fibre(&rhs).map_err(|_| super::super::TowerError::Refused("a class clock's projection"))?;
        solved.map(|(w, _)| (0..classes).map(|c| (0..m).map(|x| w[x].clone() * b[x][c].clone()).sum()).collect())
    } else {
        None
    };
    Ok(ClassClock { published, steps, dimension, satisfied, cutting, empty, silent, forcing: forced, skin_pinned, both_live })
}
