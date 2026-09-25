//! **The face map of a navigator family against terrain: its kernel is retention, its cokernel
//! the residual.**
//!
//! [definition] Terrain is a configuration space `X = ℚⁿ`; the navigator family acts on it by the
//! exact linear passages of a [`NavigatorFamily`], composed along ordered words with the last
//! letter acting first (`Foundation/TransportWord`); an admitted receiver family reads faces
//! through [`ReceiverReading`]s. The **face map** sends a configuration to its joint future face
//! (Lean `Compression/Core/FaceMap.faceMap`, the causal signature of `Foundation/Standing`):
//!
//! ```text
//! F x (ρ, w) = ρ(T_w x)          T_{g₁ g₂ ⋯ g_k} = T_{g₁} T_{g₂} ⋯ T_{g_k}
//! B₀ = ⋂_ρ ker ρ                 B_{n+1} = B₀ ∩ ⋂_g T_g⁻¹ B_n        ker F = ⋂_n B_n
//! ```
//!
//! [proved-derived; implemented-exact] What this owner computes, each over ℚ:
//!
//! - **The kernel by the blind-subspace recursion, never by enumerating words** (Lean
//!   `horizonBlind`, `mem_horizonBlind_iff`, `ker_faceMap_eq_iInf_horizonBlind`). `B_n` is carried
//!   by its defining covectors `O_n`, `B_n = ker O_n`: the intersection stacks the defining rows of
//!   `B₀` and of every comap, and the comap is `T_g⁻¹ B_n = ker(O_n T_g)`. Once two consecutive
//!   horizons agree they agree forever (`horizonBlind_stable_forever`), so [`FaceMap::new`] stops
//!   there and [`FaceMap::kernel`] is the relevance kernel (`ker_faceMap_eq_relevanceKernel`): the
//!   differences no admitted future receiver distinguishes after any word.
//! - **Finitely many observations read it, by horizon `dim X − 1`.** Each strict step lowers
//!   `dim B_n` by at least one, and `B₀ = X` forces `B₁ = X`, so the recursion is stable by
//!   `dim X − 1` ([`FaceMap::stable_at`]; Lean `exists_stable_le_finrank_pred`,
//!   `horizonBlind_finrank_pred_eq_ker`), and the shift chain attains it (`Shift.horizon_sharp`).
//! - **Retention** ([`FaceMap::quotient`]) is the kernel quotient `X ⧸ ker F` in the chart of the
//!   reduced row basis `V` of the stable covectors, with every present receiver and every navigator
//!   descended to it (`kernelReceiverQuotient`, `descendedNavigator`, `kernelHistoryCompression`,
//!   `kernelClass_after_word`). It is the coarsest lawful retention
//!   (`kernelQuotient_is_coarsest_retention`): its classes are exactly future agreement
//!   (`kernelQuotient_eq_iff_futureAgreement`), and its [`Retention::standing`] is a
//!   [`StandingLaw`] that `crate::receiver::standing::sufficiency` accepts.
//! - **The cokernel is horizon-relative.** A [`FiniteFaceMap`] is the face map on the declared
//!   request set of one horizon `N` (Lean `horizonFaceMap`): every receiver after every word of
//!   length at most `N`, `|R| Σ_{n≤N} |G|ⁿ` requests, bounded by the standing owner's word
//!   ceilings. Its [`Cokernel`] carries that horizon and request count, because `dim coker F_N`
//!   grows with `N` (on the ramp it is `N − 1`). A face is reachable exactly when its cokernel
//!   class is zero, exactly when every cocycle vanishes on it (`reachable_iff_cokernelClass_zero`,
//!   `reachable_iff_cocycles_vanish`), and an unreachable face is certified by one cocycle: it is
//!   residual, to be emanated or retained. Its [`FaceLedger`] reads `rank + dim ker = dim X` and
//!   `dim coker = dim faces − rank` (`rank_nullity_ledger`, `finrank_faces`, `cokernel_ledger`).
//!
//! [definition; agent-inferred] Receivers may read faces of different extents; the face space is
//! then the sum of their extents over the words, and Lean's `#requests · dim V` is the uniform
//! case. This owner is over ℚ. Over ℤ a class can be reachable only in a multiple, exactly when its
//! cokernel class is nonzero torsion (Lean
//! `HolonicsResearch/Landmarks/IntegralCokernel.reachableOnlyInMultiple_iff`); the integral ledger
//! is owed in #62.

use std::collections::HashMap;
use std::ops::Range;

use num_traits::{One, Zero};

use crate::compression::CompressionError;
use crate::ratio::Rat;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::{dot, matrix};
use crate::receiver::standing::{NavigatorFamily, ReceiverReading, StandingLaw};

/// [definition] **A navigator family against terrain and an admitted receiver family**, with the
/// blind-subspace recursion read to its fixed point.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FaceMap {
    navigators: NavigatorFamily,
    receivers: Vec<ReceiverReading>,
    /// `O_0, …, O_m`: a basis of the covectors defining `B_n`, for `n` up to the stable horizon.
    defining: Vec<Vec<Vec<Rat>>>,
}

impl FaceMap {
    /// **The face map, with its kernel read by the blind-subspace recursion.** The recursion
    /// stops at the first horizon whose blind subspace equals the next one's.
    pub fn new(
        navigators: NavigatorFamily,
        receivers: Vec<ReceiverReading>,
    ) -> Result<Self, CompressionError> {
        check_receivers(&navigators, &receivers)?;
        let extent = navigators.extent();
        let present: Vec<Vec<Rat>> = receivers
            .iter()
            .flat_map(|reading| reading.matrix().to_rows())
            .collect();
        let base = row_basis(present, extent)?;
        let transposes = navigators
            .maps()
            .iter()
            .map(ExactRatMatrix::transpose)
            .collect::<Result<Vec<_>, _>>()?;
        let mut defining = vec![base.clone()];
        loop {
            let current = &defining[defining.len() - 1];
            let mut rows = base.clone();
            for transpose in &transposes {
                for covector in current {
                    rows.push(transpose.apply(covector)?);
                }
            }
            let next = row_basis(rows, extent)?;
            if next.len() == current.len() {
                break;
            }
            defining.push(next);
        }
        Ok(Self {
            navigators,
            receivers,
            defining,
        })
    }

    /// `dim X`.
    pub fn terrain_extent(&self) -> usize {
        self.navigators.extent()
    }

    /// The navigator family.
    pub fn navigators(&self) -> &NavigatorFamily {
        &self.navigators
    }

    /// The admitted receiver family.
    pub fn receivers(&self) -> &[ReceiverReading] {
        &self.receivers
    }

    /// **The stabilization horizon** `m`: the first with `B_m = B_{m+1}`, never past `dim X − 1`
    /// (Lean `exists_stable_le_finrank_pred`).
    pub fn stable_at(&self) -> usize {
        self.defining.len() - 1
    }

    /// `rank F_n = dim O_n` for `n = 0, …, m`, strictly increasing.
    pub fn observed_ranks(&self) -> Vec<usize> {
        self.defining.iter().map(Vec::len).collect()
    }

    /// **The horizon-`n` blind subspace** `B_n`: what no receiver reads after any word of length at
    /// most `n` (Lean `mem_horizonBlind_iff`). Past the stabilization horizon it is the kernel.
    pub fn blind(&self, horizon: usize) -> Result<Vec<Vec<Rat>>, CompressionError> {
        let defining = &self.defining[horizon.min(self.stable_at())];
        null_space(defining, self.terrain_extent())
    }

    /// **The kernel: the relevance kernel**, the differences no admitted future receiver
    /// distinguishes after any word (Lean `ker_faceMap_eq_relevanceKernel`,
    /// `horizonBlind_finrank_pred_eq_ker`, `horizonBlind_eq_ker_of_le`).
    pub fn kernel(&self) -> Result<Vec<Vec<Rat>>, CompressionError> {
        self.blind(self.stable_at())
    }

    /// **Retention: the kernel quotient**, with the present receivers and the navigators descended
    /// to it. Every factorization is checked exactly: `V T_g = T̄_g V` (Lean `ker_faceMap_invariant`)
    /// and `ρ = ρ̄ V`.
    pub fn quotient(&self) -> Result<Retention, CompressionError> {
        let extent = self.terrain_extent();
        let stable = &self.defining[self.stable_at()];
        let (retain, pivots) = if stable.is_empty() {
            (ExactRatMatrix::zero(0, extent)?, Vec::new())
        } else {
            let factored = ExactRatMatrix::shaped(stable.len(), extent, stable.clone())?
                .rank_factorization()?;
            (factored.right, factored.pivot_columns)
        };
        // `V` is reduced: its pivot columns carry the identity, so the section picking them is a
        // right inverse, `V σ = 1`.
        let section = matrix(extent, pivots.len(), |row, column| {
            if pivots[column] == row {
                Rat::one()
            } else {
                Rat::zero()
            }
        })?;
        let mut navigators = Vec::with_capacity(self.navigators.count());
        for (navigator, map) in self.navigators.maps().iter().enumerate() {
            let carried = retain.multiply(map)?;
            let descended = carried.multiply(&section)?;
            if descended.multiply(&retain)? != carried {
                return Err(CompressionError::KernelNotInvariant { navigator });
            }
            navigators.push(descended);
        }
        let mut readings = Vec::with_capacity(self.receivers.len());
        for (receiver, reading) in self.receivers.iter().enumerate() {
            let factor = reading.matrix().multiply(&section)?;
            if factor.multiply(&retain)? != *reading.matrix() {
                return Err(CompressionError::ReceiverNotFactored { receiver });
            }
            readings.push(factor);
        }
        Ok(Retention {
            retain,
            navigators,
            readings,
        })
    }

    /// **The finite face map on the declared request set of horizon `N`**: every receiver after
    /// every word of length at most `N`, stacked receiver-major, words in the order of
    /// [`NavigatorFamily::words_within`], whose ceilings bound the request set before any transport
    /// is formed.
    pub fn at_horizon(&self, horizon: usize) -> Result<FiniteFaceMap, CompressionError> {
        let extent = self.terrain_extent();
        let words = self.navigators.words_within(horizon)?;
        let transports = word_transports(&self.navigators, &words)?;
        let mut requests = Vec::new();
        let mut rows: Vec<Vec<Rat>> = Vec::new();
        for (receiver, reading) in self.receivers.iter().enumerate() {
            for (word, transport) in words.iter().zip(&transports) {
                let block = reading.matrix().multiply(transport)?;
                let start = rows.len();
                rows.extend(block.to_rows());
                requests.push(Request {
                    receiver,
                    word: word.clone(),
                    coordinates: start..rows.len(),
                });
            }
        }
        Ok(FiniteFaceMap {
            horizon,
            terrain: extent,
            kernel: self.blind(horizon)?.len(),
            map: ExactRatMatrix::shaped(rows.len(), extent, rows)?,
            requests,
        })
    }
}

/// [definition] **One admitted future observation**: a receiver read after an ordered word, and
/// the face coordinates it owns in the face space.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Request {
    /// The receiver, by its index in the admitted family.
    pub receiver: usize,
    /// The ordered word, its last letter acting first.
    pub word: Vec<usize>,
    /// The coordinates of the face space this observation reads.
    pub coordinates: Range<usize>,
}

/// [definition] **The finite face map `F_N`** on the declared request set of one horizon (Lean
/// `horizonFaceMap`). Its kernel dimension is read from the recursion; its rank and cokernel from
/// the one exact matrix of its faces.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteFaceMap {
    horizon: usize,
    terrain: usize,
    kernel: usize,
    requests: Vec<Request>,
    map: ExactRatMatrix,
}

/// [definition] **The ledger of a finite face map** at its horizon (Lean `rank_nullity_ledger`,
/// `finrank_faces`, `cokernel_ledger`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FaceLedger {
    /// The declared horizon `N`.
    pub horizon: usize,
    /// `dim X`.
    pub terrain: usize,
    /// The number of declared observations `(ρ, w)`.
    pub requests: usize,
    /// `dim faces`: the sum of the observations' face extents.
    pub faces: usize,
    /// `rank F_N`, read from the face matrix.
    pub rank: usize,
    /// `dim B_N`, read from the recursion.
    pub kernel: usize,
    /// `dim coker F_N`: what the navigators' image does not reach on this request set.
    pub cokernel: usize,
}

impl FiniteFaceMap {
    /// The declared horizon `N`.
    pub fn horizon(&self) -> usize {
        self.horizon
    }

    /// The declared request set, in the order of the face coordinates.
    pub fn requests(&self) -> &[Request] {
        &self.requests
    }

    /// The face map as one exact matrix, `faces × dim X`.
    pub fn matrix(&self) -> &ExactRatMatrix {
        &self.map
    }

    /// The face `F_N x` on the declared request set.
    pub fn face(&self, terrain: &[Rat]) -> Result<Vec<Rat>, CompressionError> {
        check_extent("terrain configuration", self.terrain, terrain)?;
        Ok(self.map.apply(terrain)?)
    }

    /// **The rank/kernel/cokernel ledger** at this horizon.
    pub fn ledger(&self) -> Result<FaceLedger, CompressionError> {
        let factorization = self.map.factorization()?;
        Ok(FaceLedger {
            horizon: self.horizon,
            terrain: self.terrain,
            requests: self.requests.len(),
            faces: self.map.rows(),
            rank: factorization.rank,
            kernel: self.kernel,
            cokernel: factorization.open_exterior_dimension(),
        })
    }

    /// **The cokernel on this request set**, exhibited by its cocycles.
    pub fn cokernel(&self) -> Result<Cokernel, CompressionError> {
        Ok(Cokernel {
            horizon: self.horizon,
            requests: self.requests.len(),
            cocycles: self.map.cokernel_annihilator()?,
            faces: self.map.rows(),
        })
    }

    /// **Whether a face is reached by the navigators' image**: exactly when its cokernel class is
    /// zero (Lean `reachable_iff_cokernelClass_zero`).
    pub fn reachable(&self, face: &[Rat]) -> Result<bool, CompressionError> {
        Ok(self.cokernel()?.class(face)?.iter().all(Zero::is_zero))
    }
}

/// [definition] **The cokernel of a finite face map**, exhibited by its cocycles (the coholons `ω`
/// with `ωᵀ F_N = 0`) and carrying the horizon and request set it is relative to. The class of a
/// face `y` in `faces ⧸ range F_N` is read in the dual chart `(⟨ω_i, y⟩)_i`, an isomorphism
/// because the cocycles are a basis of `(range F_N)^⊥`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cokernel {
    horizon: usize,
    requests: usize,
    cocycles: Vec<Vec<Rat>>,
    faces: usize,
}

impl Cokernel {
    /// The horizon this residual is relative to.
    pub fn horizon(&self) -> usize {
        self.horizon
    }

    /// The number of declared observations it is relative to.
    pub fn requests(&self) -> usize {
        self.requests
    }

    /// The cocycles, a basis of the coholons annihilating the image.
    pub fn cocycles(&self) -> &[Vec<Rat>] {
        &self.cocycles
    }

    /// `dim coker F_N`.
    pub fn dimension(&self) -> usize {
        self.cocycles.len()
    }

    /// **The cokernel class of a face**, as its pairing with every cocycle.
    pub fn class(&self, face: &[Rat]) -> Result<Vec<Rat>, CompressionError> {
        check_extent("face", self.faces, face)?;
        Ok(self
            .cocycles
            .iter()
            .map(|cocycle| dot(cocycle, face))
            .collect())
    }

    /// **The cocycle certifying that a face is unreachable**, or `None` when every cocycle vanishes
    /// on it (Lean `reachable_iff_cocycles_vanish`).
    pub fn obstruction(&self, face: &[Rat]) -> Result<Option<Vec<Rat>>, CompressionError> {
        check_extent("face", self.faces, face)?;
        Ok(self
            .cocycles
            .iter()
            .find(|cocycle| !dot(cocycle, face).is_zero())
            .cloned())
    }
}

/// [definition] **Retention: the kernel quotient `X ⧸ ker F`** in the chart of the reduced row
/// basis `V` of the stable covectors (`ker V = ker F`), with every present receiver `ρ = ρ̄ V` and
/// every navigator descended, `V T_g = T̄_g V` (Lean `kernelReceiverQuotient`,
/// `descendedNavigator`, `kernelHistoryCompression`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Retention {
    retain: ExactRatMatrix,
    navigators: Vec<ExactRatMatrix>,
    readings: Vec<ExactRatMatrix>,
}

impl Retention {
    /// The retention map `V : X → X ⧸ ker F`, of full row rank.
    pub fn retain(&self) -> &ExactRatMatrix {
        &self.retain
    }

    /// `dim (X ⧸ ker F) = rank F`.
    pub fn extent(&self) -> usize {
        self.retain.rows()
    }

    /// The retained class `V x` of a terrain configuration.
    pub fn retained(&self, terrain: &[Rat]) -> Result<Vec<Rat>, CompressionError> {
        check_extent("terrain configuration", self.retain.columns(), terrain)?;
        Ok(self.retain.apply(terrain)?)
    }

    /// The navigator `g` descended to retention, `T̄_g` with `V T_g = T̄_g V`.
    pub fn navigator(&self, navigator: usize) -> Option<&ExactRatMatrix> {
        self.navigators.get(navigator)
    }

    /// The present receiver `r` read on retention, `ρ̄_r` with `ρ_r = ρ̄_r V`.
    pub fn reading(&self, receiver: usize) -> Option<&ExactRatMatrix> {
        self.readings.get(receiver)
    }

    /// **The navigator runs on retention**: the descended word applied to a retained class, its
    /// last letter acting first (Lean `kernelClass_after_word`: `V T_w x = T̄_w V x`).
    pub fn transport_word(
        &self,
        word: &[usize],
        retained: &[Rat],
    ) -> Result<Vec<Rat>, CompressionError> {
        check_extent("retained class", self.extent(), retained)?;
        let mut current = retained.to_vec();
        for letter in word.iter().rev() {
            let map = self
                .navigators
                .get(*letter)
                .ok_or(CompressionError::Extent {
                    what: "navigator index",
                    expected: self.navigators.len(),
                    found: *letter,
                })?;
            current = map.apply(&current)?;
        }
        Ok(current)
    }

    /// **Every future face read from retention alone**: receiver `r` after word `w` reads
    /// `ρ̄_r T̄_w q` (Lean `kernelReceiverQuotient.factor`).
    pub fn face(
        &self,
        receiver: usize,
        word: &[usize],
        retained: &[Rat],
    ) -> Result<Vec<Rat>, CompressionError> {
        let reading = self
            .readings
            .get(receiver)
            .ok_or(CompressionError::Extent {
                what: "receiver index",
                expected: self.readings.len(),
                found: receiver,
            })?;
        Ok(reading.apply(&self.transport_word(word, retained)?)?)
    }

    /// **The kernel quotient as a standing law** of `crate::receiver::standing`. A zero rank
    /// retains nothing, and the standing owner refuses an empty extent.
    pub fn standing(&self, lineage: impl Into<String>) -> Result<StandingLaw, CompressionError> {
        Ok(StandingLaw::declared(lineage, self.retain.clone())?)
    }
}

/// A basis of the row space of the declared rows, drawn from the rows themselves.
fn row_basis(rows: Vec<Vec<Rat>>, extent: usize) -> Result<Vec<Vec<Rat>>, CompressionError> {
    if rows.is_empty() {
        return Ok(Vec::new());
    }
    Ok(ExactRatMatrix::shaped(rows.len(), extent, rows)?
        .transpose()?
        .image_basis()?)
}

/// A basis of the common kernel of the declared covectors.
fn null_space(covectors: &[Vec<Rat>], extent: usize) -> Result<Vec<Vec<Rat>>, CompressionError> {
    Ok(ExactRatMatrix::shaped(covectors.len(), extent, covectors.to_vec())?.kernel_basis()?)
}

/// The transport `T_w` of every word, each extending an earlier prefix: `T_{w g} = T_w T_g`.
fn word_transports(
    navigators: &NavigatorFamily,
    words: &[Vec<usize>],
) -> Result<Vec<ExactRatMatrix>, CompressionError> {
    let mut index: HashMap<&[usize], usize> = HashMap::with_capacity(words.len());
    let mut transports: Vec<ExactRatMatrix> = Vec::with_capacity(words.len());
    for word in words {
        let transport = match word.split_last() {
            None => ExactRatMatrix::identity(navigators.extent())?,
            Some((last, prefix)) => {
                let earlier = index.get(prefix).copied().ok_or(CompressionError::Extent {
                    what: "word prefix",
                    expected: prefix.len(),
                    found: word.len(),
                })?;
                transports[earlier].multiply(&navigators.maps()[*last])?
            }
        };
        index.insert(word.as_slice(), transports.len());
        transports.push(transport);
    }
    Ok(transports)
}

fn check_receivers(
    navigators: &NavigatorFamily,
    receivers: &[ReceiverReading],
) -> Result<(), CompressionError> {
    if receivers.is_empty() {
        return Err(CompressionError::EmptyReceiverFamily);
    }
    for reading in receivers {
        if reading.source_extent() != navigators.extent() {
            return Err(CompressionError::Extent {
                what: "receiver source",
                expected: navigators.extent(),
                found: reading.source_extent(),
            });
        }
    }
    Ok(())
}

fn check_extent(
    what: &'static str,
    expected: usize,
    found: &[Rat],
) -> Result<(), CompressionError> {
    if found.len() != expected {
        return Err(CompressionError::Extent {
            what,
            expected,
            found: found.len(),
        });
    }
    Ok(())
}

#[cfg(test)]
mod tests;
