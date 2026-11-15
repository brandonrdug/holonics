//! **A level on its news: landmarks of surprise.**
//!
//! the news `c_t` (the opening's code at a written place, the expected code elsewhere); a site where `ρ_t ≥ σ`, `σ` the flat
//! face's code; each epoch led by a site, run on its own clock
//!
//! Kind: gate a site, then sum over an epoch. Kernels: `field_level_news`, `field_level_chart32`, `field_level_chart64`, `field_level_unchart`
//! (`hnn/level.rs`).
//! Lean: none yet.
//! Records: `2026-11-13_A_LEVELS_SITES_ARE…`. The derivations' history is in the records; the items below keep their reasons.

#[allow(unused_imports)]
use crate::field::*;
#[allow(unused_imports)]
use rayon::prelude::*;

impl Constitution {

    /// [definition; agent-inferred, November 1] **The landmarks** (the dispersing field's §3
    /// receipt): for each of `sites`, the `count` sites before `question` carrying the most weight in
    /// its still heads' currents at the last tick, `Σ_(h still) e_ij / Σ_k e_ik` on `2^(−16)` (each
    /// with its weight), the places where the answer's contacts converge. A reading only; nothing
    /// drives the release from it.
    pub fn landmarks(&self, region: &Region, question: usize, sites: &[usize], count: usize) -> Result<Vec<Vec<(usize, u64)>>> {
        let pass = self.pass(region, true)?;
        let d = &self.declaration;
        let cell = pass.ticks.last().ok_or(TowerError::Refused("a pass with no tick"))?;
        let n = region.classes.len();
        if sites.iter().any(|&i| i >= n) || question > n {
            return refuse("a landmark site outside its region");
        }
        let rows = sites
            .iter()
            .map(|&i| (0..d.heads).filter(|h| h % d.frames < d.still).map(|h| (cell.rows[h * n + i].iter().map(|src| (src.j, src.p)).collect(), 1u64 << SHARE_BITS)).collect())
            .collect::<Vec<Vec<_>>>();
        Ok(landmarks_of(&rows, question, count))
    }
}

/// [`Constitution::landmarks`] from each site's still heads' weight rows at the last tick (each row's met
/// sources with their weights, and its mass): `Σ_h e_ij 2^16 / mass_i` at each source before
/// `question`, the `count` heaviest (the earlier source on a tie). A realization reads the rows; the
/// ranking is one law.
pub fn landmarks_of(rows: &[Vec<(Vec<(u32, u64)>, u64)>], question: usize, count: usize) -> Vec<Vec<(usize, u64)>> {
    rows.iter()
        .map(|heads| {
            let mut weight = vec![0u64; question];
            for (row, mass) in heads {
                for &(j, e) in row.iter().filter(|&&(j, _)| (j as usize) < question) {
                    weight[j as usize] += (((e as u128) << STATE_BITS) / *mass as u128) as u64;
                }
            }
            let mut ranked: Vec<(usize, u64)> = weight.into_iter().enumerate().filter(|&(_, w)| w > 0).collect();
            ranked.sort_by_key(|&(j, w)| (std::cmp::Reverse(w), j));
            ranked.truncate(count);
            ranked
        })
        .collect()
}
