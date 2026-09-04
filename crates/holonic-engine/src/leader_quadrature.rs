//! Integration by lightning leaders: the area is the exact running sum over founded extensions.
//!
//! ## What is being built, in Brandon's words
//!
//! > *"If we consider any example plane with a curve defined by some function, and then suppose we
//! > want to find the area underneath the curve using lightning leaders that propagate and radiate
//! > potential and interfering fields in radii about the strike points, it becomes a problem like
//! > sphere-packing ... the limit is self-similarity; once the complex causal geometry has been
//! > literally founded, it must then also be an axis in which the founded area can **naturally**
//! > scale by without losing accuracy on the scaled area ... and the integration pathways must
//! > accomodate transformations of parameters."*
//! >
//! > — 2026-08-07, deposited in `docs/canon/THE_QUOTE_NETWORK.md` §9.
//!
//! ## The three rulings this module obeys
//!
//! **1. No sphere. No metric ball. No radiated field.** `THEORY/50_THE_STRIKE.md`, Brandon:
//! *"Light does not literally radiate from some central point in all directions in some 3D field,
//! light follows path and curvature"* — the omnidirectional field is *"the debris, the sphere that
//! was never real."* So the neighbourhood of a strike point is **reach along a founded path**, and
//! the covering is **path-length at a declared grain**: Minkowski content, not Vitali. There is no
//! ball, no radius, and no potential field anywhere below. A leader **extends**; it does not
//! radiate.
//!
//! **2. Each extension changes the material boundary from which later extension proceeds.**
//! `research/records/2026-07-17_THE_LEADER_GROWS_THE_CHANNEL_THE_RETURN_TRAVELS_THE_FOUND_PATH.md`,
//! Brandon-ratified: *"The leader is therefore not a probe moving through an unchanged atmosphere.
//! Each extension changes the material boundary from which later extension proceeds."* Here the
//! material boundary at a tip is its **local jet**, and every extension rebases it by an exact
//! Taylor shift. The jet the leader reads at extension `k+1` is literally not the jet it read at
//! extension `k`. The same record bans the shortcut this module must not take: *"No random route
//! chooser, target search, global path, standing-wave cause, or instantaneous return."* Growth
//! below is deterministic and local — one read of the standing form at the tip, one decision, one
//! deposit.
//!
//! **3. There is no continuum to subdivide.** `Derive_Integration.lean` (Brandon + Opus,
//! 2026-06-23), carried verbatim in
//! `research/records/2026-08-07_THE_INTEGRAL_IS_THE_PAIR_THE_DISAGREEMENT_IS_THE_HOLONOMY.md`:
//! *"there is no continuum to subdivide; there is a LINEAGE of discrete events (windings), and the
//! area IS the exact running sum of them. No mesh, no limit, no error."* Accordingly
//! [`LeaderQuadrature::area`] is a running sum of exact rational windings and there is no error
//! term, no tolerance, no refinement schedule and no limit anywhere in this file.
//!
//! ## The mechanism
//!
//! The material boundary is a contiguous family of [`RationalGerm`]s. A germ is a **chart-local**
//! object: an extent and a jet in its own local coordinate, with no absolute base point. That is
//! the no-absolute-frame rule doing real work — see [`MaterialBoundary::rescale_parameter`], where
//! the translation component of an affine reparametrization is invisible because no germ ever knew
//! where it was.
//!
//! The leader holds a tip offset and grows:
//!
//! ```text
//!   read the standing form at the tip        -- local: the rebased jet, and how far it conducts
//!   compare it against the founded axis      -- does the axis founded at the previous tip predict
//!                                               this material, exactly?
//!   agree    -> the founded geometry carries; the agreement lineage deepens
//!   disagree -> a REFOUNDING OBSTRUCTION is deposited and RETAINED, and the axis is refounded
//!   extend   -> FOUND one grain, or RIDE the founded axis across the standing reach
//!   deposit  -> the exact winding of that extension is added to the running sum
//! ```
//!
//! A winding is `∫_0^s j(t) dt` for the local jet `j` at the tip, computed by exact termwise
//! antidifferentiation over [`Rat`]. It is not a trapezoid, not a midpoint rule, and not a
//! quadrature weight: it is the exact swept content of that one extension, so the sum of any number
//! of extensions is exact and the returned area does not depend on the grain.
//!
//! `FOUND pays curvature; RIDE is cheap because the terrain already paid` (`CLAUDE.md` §2). A short
//! germ is founded grain by grain. A long germ is founded until it is an axis, then ridden whole.
//!
//! ## The self-similarity termination law
//!
//! This criterion is recorded as **undeposited** in `docs/canon/THE_QUOTE_NETWORK.md` §9 (*"The
//! self-similarity termination criterion is undeposited as a falsifier"*). It is what makes this
//! construction more than a Riemann sum, and it is stated here so it can be tested rather than
//! asserted.
//!
//! > **Law (self-similarity termination).** Founding stops on a standing germ when the axis founded
//! > by the extensions already taken has predicted the material exactly for as many consecutive
//! > extensions as the material required — [`LocalJet::rebase_movement_depth`], the order at which
//! > the exact Taylor rebase stops being able to contribute a difference. At that tip the founded jet `j` and its
//! > founded primitive `J(s) = Σ_i j_i · s^(i+1)/(i+1)` constitute an **axis the founded area
//! > scales along**: for every rational scale `λ ≥ 1` with `λ·grain` inside the germ's standing
//! > reach, the content swept by one extension of span `λ·grain` is exactly `J(λ·grain)`, with no
//! > residual at any `λ`. The leader therefore closes the remainder of the germ in **one**
//! > extension at scale `λ = reach / grain`, and the returned sum is identical to the sum it would
//! > have returned by founding every grain step.
//! >
//! > **Falsifier.** If the ridden sum and the grain-only sum ever differ on material inside the
//! > declared aperture, the founded geometry was not an axis and this law is false. If the
//! > extension count of a ridden run grows with the size of the region, the scaling was not free
//! > and this law is false.
//!
//! Both halves are tested. `self_similarity_termination_law_holds_at_every_scale` rides a region of
//! span `10^12` in the same number of extensions as a region of span `10`, returning `10^24/2`
//! exactly. This is the sense in which *"the founded area can naturally scale by without losing
//! accuracy on the scaled area"*: the scale factor `λ` is carried on a [`ScaleWitness`] and the
//! returned rational is unchanged.
//!
//! Note the standing-law reading this obeys, from the deposited record: *"Self-similarity is
//! restriction and lawful rebase, never return to an identical Place."* Nothing here looks for a
//! repeating shape. The axis carries because the rebase carries the same phase law.
//!
//! ## The witness depth is read off the material, and one is a special case rather than a default
//!
//! Ruling 2 above already bans the instantaneous return, and it is the same ban one level down: a
//! limit is not something a single comparison can certify, and the depth at which a limit *has*
//! been reached is the depth at which the mechanism transforming the information during transport
//! stops being able to contribute a difference. `docs/canon/THE_AUTHORED_LEVEL.md` §5.1 names the
//! excision this module owes on exactly that reading — *"what the material stopped the leader at …
//! **A leader whose witness depth is one takes a single step; that is not a leader.**"*
//!
//! The mechanism that transforms information during transport, here, is the exact Taylor rebase.
//! [`LocalJet::rebase_movement_depth`] is the order at which it can no longer contribute a
//! difference — the rank of the jet, by the finite-difference theorem stated there — and that is
//! the witness depth, **returned by the growth rather than declared into it**
//! ([`WitnessDepth::ReadOffTheJet`], carried out on every [`Extension`] as
//! `material_witness_depth`).
//!
//! A depth of one is not wrong everywhere; it is exactly right on a **constant** jet, where the
//! rebase of a constant is itself and one agreement is the complete measurement. It is wrong on
//! every jet of rank two or more, where the leader is still reading a moving jet when the gate
//! declares the limit reached. Authored as a constant it could not tell those two cases apart, and
//! it was authored as a constant: `derivation_integral.rs:135`, `LEADER_WITNESS_DEPTH: usize = 1`,
//! excised 2026-08-09 for `docs/canon/THE_AUTHORED_LEVEL.md` §5.1.
//!
//! **Exact scope of the agreement gate.** Measured, not assumed: replacing the jet-agreement
//! decision with a constant `true` leaves every returned area exact under
//! [`RideDiscipline::GermBounded`] and [`RideDiscipline::GrainOnly`], and kills only the two tests
//! that grade the obstruction population. That is the honest reading — under a germ-bounded ride
//! the founded axis is sound whether or not the leader noticed it was founded, so the agreement
//! lineage governs **which discrete events the leader deposits and which obstructions it retains**,
//! not whether the sum is exact. It becomes load-bearing for exactness only under
//! [`RideDiscipline::UnclampedAncestry`], where it is the sole gate between the leader and material
//! it has not read.
//!
//! ## Parameter transformation
//!
//! *"the integration pathways must accomodate transformations of parameters."* They do, and more
//! strongly than asked: under [`MaterialBoundary::rescale_parameter`] with the correspondingly
//! rescaled grain, the extension lineage is **identical** — same count, same kinds, same
//! obstruction population — and the area scales by exactly the rank-one Jacobian `1/α` with no
//! remainder. That is the half-Jacobian clause of the deposited record at this rank: *"An
//! invertible chart change creates no remainder."*
//!
//! ## The declared aperture, and the falsification it returns
//!
//! `CLAUDE.md` §8: *"An organ used past its declared aperture is a defect even when it appears to
//! return."* [`RideDiscipline::GermBounded`] is **sound by construction**: a ride never leaves the
//! germ whose jet founded it, and a germ is one polynomial over its whole extent, so `J(reach)` is
//! the exact content. [`RideDiscipline::UnclampedAncestry`] is the same organ conducted past that
//! aperture — it rides as far as it has already come, crossing standing forms, verifying only the
//! landing jet. It is retained so the aperture is **measured rather than asserted**:
//! `declared_aperture_falsifier_returns_a_measured_holonomy` exhibits material on which it returns
//! `49/2` where the true area is `23`, and [`path_disagreement`] returns the `3/2` residual.
//!
//! The deposited record sets the sharp falsifier for the holonomy hope: *"if two enclosing paths
//! always agree, the construction has assumed trivial cohomology and is the classical integral
//! wearing new vocabulary."* This module's honest return is that **within the declared aperture the
//! disagreement is exactly zero at this rank** — a returned falsification, not a success — and that
//! the disagreement is non-zero exactly when a leader is conducted past its aperture, where it
//! measures the violation. Recording that is `CLAUDE.md` §8's *"a falsification is a first-class
//! return."*
//!
//! ## Cost, both implementations
//!
//! `CLAUDE.md` §8: *"Where an independent implementation exists, state both costs."*
//! [`germwise_oracle_area`] is an independent implementation of the same return — one exact
//! antiderivative per germ, evaluated at the germ's extent — and it costs `O(G·m)` for `G` germs of
//! jet rank `m`. The leader costs `O(E·m²)` for `E` extensions, the `m²` being the exact Taylor
//! rebase at every tip, with `E ≥ G` always and `E = Θ(span/grain)` under
//! [`RideDiscipline::GrainOnly`]. The oracle is strictly cheaper and returns the same rational; it
//! grades the leader in `oracle_conformance_across_every_fixture`. What the oracle cannot return is
//! the lineage: the extension ancestry, the retained refounding obstructions that locate where the
//! material **actually** changed as opposed to where it was merely re-declared, the refused rides,
//! and the scale witnesses.
//!
//! ## What is not claimed
//!
//! This closes nothing. `continuous_integration_OPEN` in the frozen laboratory is a declared
//! frontier and this is one candidate mechanism exercised on piecewise-rational material, which is
//! material a germwise antiderivative already handles. No transcendental germ, no branch point, no
//! crossing, no arc out of the plane, and no hypergeometric entanglement of the strike geometry is
//! constructed here. The `1/2`-Jacobian result is used at rank one only, where it degenerates to a
//! scalar. Nothing here bears on any Millennium problem.

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use holonic_structure::{Chain, ChainEnd, Composes, Hand, Relating};
use relational_geometry::Rat;
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum LeaderError {
    #[error("a declared grain must be strictly positive; the covering is path-length at a grain")]
    GrainNotPositive,
    #[error("a witness depth of zero would ride before any axis was founded")]
    WitnessDepthZero,
    #[error(
        "at offset {offset} the material carries a jet of rank {required}, so the rebase is still \
         contributing a difference after {declared} agreement(s); a declared witness depth of \
         {declared} would certify a limit the jet had not reached"
    )]
    WitnessDepthBelowMaterial {
        offset: Rat,
        declared: usize,
        required: usize,
    },
    #[error("a material boundary must carry at least one standing germ")]
    EmptyMaterial,
    #[error("a standing germ must conduct over a strictly positive extent")]
    GermExtentNotPositive,
    #[error("a local jet must carry at least one coefficient")]
    EmptyJet,
    #[error("a parameter rescaling must be strictly positive to preserve extension order")]
    RescaleNotPositive,
}

// ---------------------------------------------------------------------------------------------
// exact rational helpers

fn rat_min<'a>(left: &'a Rat, right: &'a Rat) -> &'a Rat {
    if left <= right { left } else { right }
}

/// The least integer strictly greater than one.
///
/// This is not a preference and it is not a tuning knob. [`MaterialBoundary::declared_grain`]
/// carries the derivation: the condition for a RIDE to exist at all — `g < E/(d+1)` — is **open**,
/// so it names an interval and no coarsest member. The scale of the ride that grain produces is
/// `E/g − d`, and the admissible grains are exactly those whose scale exceeds one. Taking the
/// coarsest grain whose scale is a whole number of grains selects the least integer above one, and
/// `2 = 1 + 1` is that integer by arithmetic. It appears in the grain as `d + 2` and nowhere else.
///
/// `the_declared_grain_rides_by_at_least_one_rank_step` measures the consequence: at a material's
/// own declared grain every ride carries at least two grains — `CLAUDE.md` §2b's octave, one rank
/// step of magnitude — the bound is attained where the finest extent and the largest rank meet, and
/// one step coarser that germ stops riding altogether.
const LEAST_INTEGER_RIDE_SCALE: usize = 2;

// ---------------------------------------------------------------------------------------------
// the material boundary

/// The material at one tip, in that tip's own coordinate.
///
/// This is the whole of what a leader can read about the medium it stands in. There is no field
/// over space, no potential, and no radius. The jet is the local causal organization of the
/// boundary and **it changes at every extension**, because the next tip's jet is this one rebased.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LocalJet {
    coefficients: Vec<Rat>,
}

impl LocalJet {
    /// Coefficients of `Σ_i c_i t^i` in the tip-local coordinate `t`.
    ///
    /// Trailing zeros are stripped, so two declarations of the same polynomial compare equal. That
    /// normalization is load-bearing: agreement between a founded axis and the material is decided
    /// by jet equality, and a padded declaration must not read as a material change.
    pub fn new(coefficients: Vec<Rat>) -> Result<Self, LeaderError> {
        if coefficients.is_empty() {
            return Err(LeaderError::EmptyJet);
        }
        Ok(Self::normalized(coefficients))
    }

    /// Convenience constructor for integer coefficients.
    pub fn from_integers(coefficients: &[i64]) -> Result<Self, LeaderError> {
        Self::new(
            coefficients
                .iter()
                .map(|value| Rat::from_integer(BigInt::from(*value)))
                .collect(),
        )
    }

    fn normalized(mut coefficients: Vec<Rat>) -> Self {
        while coefficients.len() > 1
            && coefficients
                .last()
                .map(|value| value.is_zero())
                .unwrap_or(false)
        {
            coefficients.pop();
        }
        Self { coefficients }
    }

    pub fn coefficients(&self) -> &[Rat] {
        &self.coefficients
    }

    /// The jet's rank: one more than its degree, and the aperture it declares.
    pub fn rank(&self) -> usize {
        self.coefficients.len()
    }

    /// **How many consecutive extensions the rebase can still contribute a difference over.**
    ///
    /// This is the quantity a witness depth wants, read off the material rather than declared.
    ///
    /// > **Theorem.** Let `j` have rank `m` after normalization, and let a leader inside this germ
    /// > stand at accumulated offsets `σ_0 = 0, σ_1, σ_2, …`. Coefficient `t` of `j.rebase(σ)` is
    /// > `Σ_{i≥t} C(i,t)·c_i·σ^(i−t)`, a polynomial in `σ` of degree exactly `m−1−t` when
    /// > `c_{m−1} ≠ 0`. On any arithmetic progression of offsets — which is what a constant grain
    /// > produces — the `k`-th forward difference of a degree-`n` polynomial vanishes identically
    /// > for `k > n` and not for `k = n`. So the sequence of rebased jets is annihilated by `Δ^m`
    /// > and by no lower order: **`m` is exactly the order at which the transport stops being able
    /// > to contribute a difference.**
    ///
    /// Two readings follow, and they are the whole content of this method:
    ///
    /// - `m = 1` — a constant jet. The rebase of a constant is itself, so **one** agreement is the
    ///   complete measurement and nothing further can be learned by extending. This is the one case
    ///   where a depth of one is honest, and it is the case
    ///   [`crate::derivation_integral`]'s route material is in.
    /// - `m ≥ 2` — the jet is still moving after one agreement. A depth of one certifies a limit
    ///   the material has not reached: it reads a single comparison as though it were an
    ///   instantaneous measurement.
    ///
    /// `the_jet_stops_moving_at_its_own_rank` computes the annihilating difference order directly
    /// from the rebased sequence and requires it to equal this, and requires order `m−1` **not** to
    /// annihilate, so the theorem is measured rather than asserted.
    pub fn rebase_movement_depth(&self) -> usize {
        self.rank()
    }

    pub fn value_at(&self, argument: &Rat) -> Rat {
        let mut accumulator = Rat::zero();
        for coefficient in self.coefficients.iter().rev() {
            accumulator = &accumulator * argument + coefficient;
        }
        accumulator
    }

    /// The exact content swept by one extension of this span, `∫_0^span Σ_i c_i t^i dt`.
    ///
    /// This is the winding. It is exact for every span, which is why the returned area does not
    /// depend on the grain and why there is no error term to shrink.
    pub fn swept(&self, span: &Rat) -> Rat {
        let mut accumulator = Rat::zero();
        let mut power = span.clone();
        for (index, coefficient) in self.coefficients.iter().enumerate() {
            if !coefficient.is_zero() {
                let divisor = Rat::from_integer(BigInt::from(index + 1));
                accumulator += (coefficient * &power) / divisor;
            }
            power = &power * span;
        }
        accumulator
    }

    /// The material boundary as seen from a tip advanced by `shift`: an exact Taylor shift.
    ///
    /// This is the sentence *"each extension changes the material boundary from which later
    /// extension proceeds"* made mechanical. Nothing is approximated and no term is dropped.
    pub fn rebase(&self, shift: &Rat) -> Self {
        if shift.is_zero() {
            return self.clone();
        }
        let rank = self.coefficients.len();
        let mut shift_powers = Vec::with_capacity(rank);
        shift_powers.push(Rat::one());
        for index in 1..rank {
            let next = &shift_powers[index - 1] * shift;
            shift_powers.push(next);
        }

        let mut binomial: Vec<Vec<BigInt>> = Vec::with_capacity(rank);
        for row_index in 0..rank {
            let mut row = vec![BigInt::zero(); row_index + 1];
            row[0] = BigInt::one();
            for column in 1..=row_index {
                row[column] = if column < row_index {
                    &binomial[row_index - 1][column - 1] + &binomial[row_index - 1][column]
                } else {
                    binomial[row_index - 1][column - 1].clone()
                };
            }
            binomial.push(row);
        }

        let mut shifted = vec![Rat::zero(); rank];
        for target in 0..rank {
            let mut accumulator = Rat::zero();
            for source in target..rank {
                let coefficient = &self.coefficients[source];
                if coefficient.is_zero() {
                    continue;
                }
                let weight = Rat::from_integer(binomial[source][target].clone());
                accumulator += coefficient * &weight * &shift_powers[source - target];
            }
            shifted[target] = accumulator;
        }
        Self::normalized(shifted)
    }

    /// The jet of `t -> j(alpha * t)`: the parameter transformation at the jet.
    pub fn rescale_parameter(&self, alpha: &Rat) -> Self {
        let mut power = Rat::one();
        let mut rescaled = Vec::with_capacity(self.coefficients.len());
        for coefficient in &self.coefficients {
            rescaled.push(coefficient * &power);
            power = &power * alpha;
        }
        Self::normalized(rescaled)
    }
}

/// One standing form of the material: a jet, and the extent over which that jet conducts.
///
/// The extent is not a global lookup. It is the standing conductive aftermath at that place — the
/// reach of the germ the leader is inside — and reading it is the local read that makes RIDE cheap.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RationalGerm {
    extent: Rat,
    jet: LocalJet,
}

impl RationalGerm {
    pub fn new(extent: Rat, jet: LocalJet) -> Result<Self, LeaderError> {
        if !extent.is_positive() {
            return Err(LeaderError::GermExtentNotPositive);
        }
        Ok(Self { extent, jet })
    }

    pub fn extent(&self) -> &Rat {
        &self.extent
    }

    pub fn jet(&self) -> &LocalJet {
        &self.jet
    }

    /// The exact content this germ carries over its whole extent.
    pub fn content(&self) -> Rat {
        self.jet.swept(&self.extent)
    }
}

/// What a leader reads at a tip. One local read: the material, and how far it conducts.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StandingForm {
    pub germ_index: usize,
    pub jet: LocalJet,
    pub reach: Rat,
}

/// The curve, as a contiguous lineage of chart-local germs.
///
/// No germ carries an absolute position. The region is the concatenation of extents, and every jet
/// is expressed in its own germ's coordinate. `CLAUDE.md`: *"No absolute frame in a lineage."*
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MaterialBoundary {
    germs: Vec<RationalGerm>,
    prefix: Vec<Rat>,
}

impl MaterialBoundary {
    pub fn new(germs: Vec<RationalGerm>) -> Result<Self, LeaderError> {
        if germs.is_empty() {
            return Err(LeaderError::EmptyMaterial);
        }
        let mut prefix = Vec::with_capacity(germs.len() + 1);
        let mut running = Rat::zero();
        prefix.push(running.clone());
        for germ in &germs {
            running = &running + &germ.extent;
            prefix.push(running.clone());
        }
        Ok(Self { germs, prefix })
    }

    pub fn germs(&self) -> &[RationalGerm] {
        &self.germs
    }

    pub fn germ_count(&self) -> usize {
        self.germs.len()
    }

    pub fn span(&self) -> &Rat {
        &self.prefix[self.germs.len()]
    }

    /// The largest jet rank the material declares. Riding an axis of lower rank than this is not
    /// available; the aperture is recorded on every return.
    pub fn jet_aperture(&self) -> usize {
        self.germs
            .iter()
            .map(|germ| germ.jet.rank())
            .max()
            .unwrap_or(0)
    }

    /// The finest standing form this material declares: the least germ extent.
    ///
    /// A grain coarser than this is **clamped by the material** on that germ —
    /// `span = min(grain, reach)` — so it is indistinguishable from this extent there. This is the
    /// material's own resolution, and no covering finer than it is anything the material asked for.
    pub fn finest_standing_extent(&self) -> &Rat {
        self.germs
            .iter()
            .map(|germ| &germ.extent)
            .fold(&self.germs[0].extent, |least, extent| {
                rat_min(least, extent)
            })
    }

    /// **The grain this material declares for itself**, read off it rather than authored.
    ///
    /// A leader never crosses a standing form: [`integrate_by_leaders`] takes
    /// `span = min(grain, reach)`, so the last extension inside a germ is clamped to that germ's
    /// remaining reach and the leader lands **exactly** on the next germ's start. Every germ is
    /// therefore entered at its own origin, and the arithmetic below is about one germ at a time.
    ///
    /// > **Theorem (when a RIDE exists at all).** A leader entering a germ of extent `E` at its
    /// > start with no standing agreement, at grain `g` and effective witness depth `d`, FOUNDs `d`
    /// > extensions before the agreement lineage licenses a ride — the first extension has no
    /// > founded axis to compare against, so agreement first holds at the second, and the `d`-th
    /// > agreement lands at extension `d`. [`RideDiscipline::GermBounded`] then rides iff the
    /// > remaining reach exceeds one grain:
    /// >
    /// > ```text
    /// >    E − d·g > g     ⟺     g < E/(d+1)     and the ride's scale is  E/g − d
    /// > ```
    /// >
    /// > **The bound is open: there is no coarsest admissible grain.** So the material determines
    /// > an interval and not a number, and a grain cannot be read off it by that condition alone.
    /// > (A germ entered with agreements already standing — the previous germ's axis predicted it,
    /// > so no refounding was deposited — rides *earlier*, hence at a strictly larger scale, so the
    /// > inequality below is safe in that case too.)
    ///
    /// What closes it is the scale. `ScaleWitness.scale` is *how many grains the founded axis
    /// carried in one extension*; admissible grains are exactly those whose scale exceeds one.
    /// Taking `E_min = ` [`Self::finest_standing_extent`] and `d_max = ` [`Self::jet_aperture`]:
    ///
    /// ```text
    ///    grain = E_min / (d_max + 2)      ⟹    scale at any germ  =  E/g − d
    ///                                                            ≥  E_min/g − d_max  =  2
    /// ```
    ///
    /// > **This is the coarsest grain at which EVERY standing form of the material rides by at
    /// > least one whole rank step**, and the bound is attained exactly at a germ that realizes
    /// > both the finest extent and the largest rank. One step coarser — `E_min/(d_max + 1)` — that
    /// > germ does not ride at all, which is the open bound above, so `+2` is not slack.
    ///
    /// The min and the max are not decoration: under [`WitnessDepth::ReadOffTheJet`] the depth is
    /// **local**, so a grain derived from the shallowest germ would be clamped in the deepest, and
    /// one derived from the widest germ would be too coarse for the narrowest.
    ///
    /// The returned area does not depend on the grain — that is this module's own self-similarity
    /// law, measured by `returned_area_is_invariant_under_the_declared_grain` — so this decides the
    /// **lineage** and never the return.
    pub fn declared_grain(&self) -> Rat {
        let depth = self.jet_aperture();
        self.finest_standing_extent().clone()
            / Rat::from_integer(BigInt::from(depth + LEAST_INTEGER_RIDE_SCALE))
    }

    /// The one local read a leader is permitted. `None` past the far end of the region.
    ///
    /// Costs `O(log G + m^2)`: a binary search over the germ prefix, then an exact Taylor rebase.
    pub fn standing_at(&self, offset: &Rat) -> Option<StandingForm> {
        if offset.is_negative() || offset >= self.span() {
            return None;
        }
        let index = self.prefix.partition_point(|bound| bound <= offset) - 1;
        let local = offset - &self.prefix[index];
        Some(StandingForm {
            germ_index: index,
            jet: self.germs[index].jet.rebase(&local),
            reach: &self.prefix[index + 1] - offset,
        })
    }

    /// The material under `u -> f(alpha * u + beta)`.
    ///
    /// `beta` does not appear in the signature and cannot: a germ carries an extent and a jet in
    /// its own coordinate and has never known where it was, so the translation component of an
    /// affine reparametrization acts trivially on this representation. Only the dilation is
    /// visible, and it acts as the rank-one Jacobian.
    pub fn rescale_parameter(&self, alpha: &Rat) -> Result<Self, LeaderError> {
        if !alpha.is_positive() {
            return Err(LeaderError::RescaleNotPositive);
        }
        let germs = self
            .germs
            .iter()
            .map(|germ| RationalGerm::new(&germ.extent / alpha, germ.jet.rescale_parameter(alpha)))
            .collect::<Result<Vec<_>, _>>()?;
        Self::new(germs)
    }

    /// Re-declare one germ as two abutting germs carrying the same material.
    ///
    /// The result describes an identical boundary. It exists so a test can vary the **declaration**
    /// while holding the **material** fixed, which is the only way to show that the retained
    /// refounding obstructions locate real material change rather than declared bookkeeping.
    pub fn redeclare_split(&self, germ_index: usize, at: &Rat) -> Result<Self, LeaderError> {
        let mut germs = Vec::with_capacity(self.germs.len() + 1);
        for (index, germ) in self.germs.iter().enumerate() {
            if index != germ_index {
                germs.push(germ.clone());
                continue;
            }
            if !at.is_positive() || at >= &germ.extent {
                return Err(LeaderError::GermExtentNotPositive);
            }
            germs.push(RationalGerm::new(at.clone(), germ.jet.clone())?);
            germs.push(RationalGerm::new(&germ.extent - at, germ.jet.rebase(at))?);
        }
        Self::new(germs)
    }
}

// ---------------------------------------------------------------------------------------------
// the law the leader grows under

/// How far a founded axis is permitted to be ridden.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum RideDiscipline {
    /// Never ride. Every extension is one grain, clamped to the standing reach.
    GrainOnly,
    /// Ride the founded axis across the standing reach of the germ that founded it. Sound by
    /// construction: the ride never leaves the material that supplied its jet.
    GermBounded,
    /// Ride as far as the leader has already come, crossing standing forms, verifying only the
    /// landing jet. **Past the declared aperture**, retained so the aperture can be measured.
    UnclampedAncestry,
}

impl RideDiscipline {
    pub fn rides(self) -> bool {
        !matches!(self, RideDiscipline::GrainOnly)
    }
}

/// Where the witness depth comes from. There is no `Default`: a default here would be the organ
/// picking a depth because the caller was never asked.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum WitnessDepth {
    /// **Read at every tip off the jet the leader is standing in**, as
    /// [`LocalJet::rebase_movement_depth`] — the order at which the exact Taylor rebase stops being
    /// able to contribute a difference. The depth is therefore a *return* of the growth and not an
    /// input to it, and it is local: a rank-one germ licenses a ride after one agreement and a
    /// rank-three germ does not.
    ReadOffTheJet,
    /// A depth the caller declares outright.
    ///
    /// Lawful **only at or above what the material required**. Declaring deeper than the material
    /// asks is conservative — the leader founds more and rides later — and is admitted. Declaring
    /// shallower is refused at the first tip that needed more, by
    /// [`LeaderError::WitnessDepthBelowMaterial`], which names the offset, the declaration and the
    /// rank the material carried there. A shallow declaration is exactly the instantaneous
    /// measurement this module cannot make: it reads one comparison as a limit.
    Declared(usize),
}

impl WitnessDepth {
    /// What this declaration resolves to at a tip whose material required `required`.
    fn at_a_tip(self, offset: &Rat, required: usize) -> Result<usize, LeaderError> {
        match self {
            WitnessDepth::ReadOffTheJet => Ok(required),
            WitnessDepth::Declared(0) => Err(LeaderError::WitnessDepthZero),
            WitnessDepth::Declared(declared) if declared < required => {
                Err(LeaderError::WitnessDepthBelowMaterial {
                    offset: offset.clone(),
                    declared,
                    required,
                })
            }
            WitnessDepth::Declared(declared) => Ok(declared),
        }
    }
}

/// The declared law a leader population grows under.
///
/// `witness_depth` is **not a threshold on the return** under
/// [`RideDiscipline::GrainOnly`] or [`RideDiscipline::GermBounded`]: it selects when founding gives
/// way to riding, and `witness_depth_cannot_change_the_returned_area` measures that the returned
/// rational is identical across every admissible depth under both.
///
/// **Under [`RideDiscipline::UnclampedAncestry`] it is load-bearing on the returned rational**, and
/// measured to be so: on `reverting_material` at grain one the same organ returns `49/2` at
/// declared depth 1 or 2 and the true `23` at depth 3 or more. That is not a contradiction of the
/// previous paragraph — it is the aperture. Riding past the germ that supplied the jet is the one
/// place where the agreement lineage is the sole gate between the leader and material it has not
/// read, so the depth stops being a declaration of the lineage and starts deciding the answer.
/// `depth_one_certifies_a_limit_the_jet_had_not_reached` exhibits it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LeaderLaw {
    pub grain: Rat,
    pub discipline: RideDiscipline,
    pub witness_depth: WitnessDepth,
}

impl LeaderLaw {
    pub fn new(grain: Rat, discipline: RideDiscipline, witness_depth: WitnessDepth) -> Self {
        Self {
            grain,
            discipline,
            witness_depth,
        }
    }

    /// **The law this material declares for itself.** Both levels come off the material: the grain
    /// from [`MaterialBoundary::declared_grain`], the depth from the jet at every tip.
    ///
    /// This is the constructor a caller with no reason to declare its own covering scale should
    /// use. It is not a `Default` — it takes the material, and the material decides.
    pub fn read_off(material: &MaterialBoundary, discipline: RideDiscipline) -> Self {
        Self {
            grain: material.declared_grain(),
            discipline,
            witness_depth: WitnessDepth::ReadOffTheJet,
        }
    }

    pub fn validate(&self) -> Result<(), LeaderError> {
        if !self.grain.is_positive() {
            return Err(LeaderError::GrainNotPositive);
        }
        if self.witness_depth == WitnessDepth::Declared(0) {
            return Err(LeaderError::WitnessDepthZero);
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------------------------
// the two determination laws, as chain links — 2026-08-17

/// **What a step carried, and what it committed past without re-reading.**
///
/// Additive, because a quadrature's transport is a running sum. The second coordinate is the whole
/// content of the type: a `Found` re-reads the material at every grain and commits past nothing, so
/// its `uninspected` is zero; a `Ride` commits across its whole span on the strength of a run of
/// agreement, so its `uninspected` is that span less the one grain it did read.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CommittedTransport {
    /// The winding this step deposited into the running sum.
    pub winding: Rat,
    /// Material the step committed past without re-reading. Zero for a `Found`.
    pub uninspected: Rat,
}

impl Composes for CommittedTransport {
    type Defect = Self;
    /// **What the chain committed past**, undivided. A pure-`Found` chain's remainder is identically
    /// zero and *that receipt is a definition* — the evidence is a mixed chain whose remainder is
    /// not, and whose refoundings are named.
    type Remainder = Rat;

    fn identity() -> Self {
        Self {
            winding: Rat::zero(),
            uninspected: Rat::zero(),
        }
    }

    fn compose(&self, next: &Self) -> Self {
        Self {
            winding: &self.winding + &next.winding,
            uninspected: &self.uninspected + &next.uninspected,
        }
    }

    fn defect(direct: &Self, composed: &Self) -> Self {
        Self {
            winding: &direct.winding - &composed.winding,
            uninspected: &direct.uninspected - &composed.uninspected,
        }
    }

    fn closed(defect: &Self) -> bool {
        defect.winding.is_zero() && defect.uninspected.is_zero()
    }

    fn remainder(&self) -> Rat {
        self.uninspected.clone()
    }

    fn is_empty(remainder: &Rat) -> bool {
        remainder.is_zero()
    }
}

/// **One step of a growth, as a chain link — the two determination laws made composable.**
///
/// `integrate_by_leaders` has composed [`ExtensionKind::Found`] and [`ExtensionKind::Ride`] since it
/// was written, and they are genuinely two determination laws: a `Found` re-reads the material at its
/// tip and its span is one grain, while a `Ride` is licensed **only** by a run of exact agreement and
/// then extrapolates one jet across the whole reach **with no landing check** under
/// [`RideDiscipline::GermBounded`] — ballistic, its error legible at the next tip, where the residual
/// revokes the licence and refounds the axis.
///
/// **They lived inside one integrator and nothing could compose them.** Measured 2026-08-17 by
/// `grep -rn "impl Relating for" --include='*.rs' crates soma` → **3**, and neither was among them,
/// so `Chain::compose`, `defect_against`, `holonomy` and `remainder` could not see the growth at all.
/// This is that lift, and the question it makes askable is the one no existing chain can ask:
/// **what separates going through from going straight, when some of the steps were committed
/// ballistically?**
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CommittedStep {
    pub index: usize,
    pub kind: ExtensionKind,
    pub span: Rat,
    /// The residual the material returned against this step's own prediction. Zero when it agreed —
    /// and a run of zeros is exactly what licenses the next ride.
    pub residual: Rat,
    transport: CommittedTransport,
}

impl CommittedStep {
    /// Read one extension as a link, with the residual the growth returned at it.
    ///
    /// `residual` is the growth's own `RefoundingObstruction::winding_residual` where one was
    /// returned at this index, and zero where the material agreed.
    pub fn of_extension(extension: &Extension, residual: Rat, grain: &Rat) -> Self {
        let uninspected = match &extension.kind {
            ExtensionKind::Found => Rat::zero(),
            // The ride read the jet at its tip and committed across the rest.
            ExtensionKind::Ride { .. } => {
                let past = &extension.span - grain;
                if past.is_positive() {
                    past
                } else {
                    Rat::zero()
                }
            }
        };
        Self {
            index: extension.index,
            kind: extension.kind.clone(),
            span: extension.span.clone(),
            residual: residual.clone(),
            transport: CommittedTransport {
                winding: extension.winding.clone(),
                uninspected,
            },
        }
    }

    /// Whether this step committed past material it did not read.
    pub fn is_committed(&self) -> bool {
        !self.transport.uninspected.is_zero()
    }
}

impl Relating for CommittedStep {
    /// The reach WEIGHS: how far this step carried. It bends what follows and decides nothing.
    type Weight = Rat;
    type Transport = CommittedTransport;

    fn reach(&self) -> &Rat {
        &self.span
    }

    /// **The hand is the sign of the STORED face**, which is the convention every implementor in this
    /// tree reads and which was audited across all of them on 2026-08-17.
    ///
    /// For a step the stored face is the **residual** — what the material returned against the
    /// prediction and therefore did *not* transport — exactly as `M₂₁` is at a junction and `aim` is
    /// at an arrow. So `Ortho` is the step whose residual vanished: nothing stored, everything
    /// carried. **And that is not a coincidence of convention — a run of `Ortho` steps is precisely
    /// what licenses the next ride.**
    fn hand(&self) -> Hand {
        if self.residual.is_zero() {
            Hand::Ortho
        } else if self.residual.is_positive() {
            Hand::Cohere
        } else {
            Hand::Anti
        }
    }

    fn transport(&self) -> &CommittedTransport {
        &self.transport
    }
}

/// A growth read as a chain of its own steps.
pub type GrowthChain<N> = Chain<N, CommittedStep, GrowthStanding>;

/// Why a growth chain stands where it does.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum GrowthStanding {
    /// The growth is continuing and the axis stands.
    Carrying(Rat),
    /// The material ran out. The chain ends because the region does, not because a count did.
    RegionExhausted,
    /// The founded axis failed to predict the next tip and was refounded here.
    Refounded(Rat),
}

/// **Read a whole growth as a chain**, so its composition, its cocycle defect and its remainder are
/// the chain machinery's rather than this module's.
pub fn chain_of(quadrature: &LeaderQuadrature) -> GrowthChain<usize> {
    let residual_at: BTreeMap<usize, Rat> = quadrature
        .obstructions
        .iter()
        .map(|obstruction| {
            (
                obstruction.extension_index,
                obstruction.winding_residual.clone(),
            )
        })
        .collect();
    let mut chain = Chain::founded(
        0usize,
        ChainEnd::Continues(GrowthStanding::RegionExhausted),
        GrowthStanding::Carrying(Rat::zero()),
    );
    for extension in &quadrature.extensions {
        let residual = residual_at
            .get(&extension.index)
            .cloned()
            .unwrap_or_else(Rat::zero);
        let standing = if residual.is_zero() {
            GrowthStanding::Carrying(extension.running_sum.clone())
        } else {
            GrowthStanding::Refounded(residual.clone())
        };
        chain.carry(
            CommittedStep::of_extension(extension, residual, &quadrature.grain),
            extension.index + 1,
            standing,
        );
    }
    chain.terminate(GrowthStanding::RegionExhausted);
    chain
}

// ---------------------------------------------------------------------------------------------
// what the growth returns

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ExtensionKind {
    /// A locally new conducting axis was grown, one grain long. FOUND pays curvature.
    Found,
    /// The founded axis carried the whole remaining reach in one extension, at this scale. RIDE is
    /// cheap because the terrain already paid.
    Ride { scale: Rat },
}

/// One discrete event in the lineage. The area is the running sum of these windings.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Extension {
    pub index: usize,
    pub germ_index: usize,
    pub base_offset: Rat,
    pub span: Rat,
    pub winding: Rat,
    pub running_sum: Rat,
    pub kind: ExtensionKind,
    /// **What the material required at this tip**, read off the jet standing there. This is the
    /// witness depth as a return rather than as an input; under
    /// [`WitnessDepth::ReadOffTheJet`] it is also the depth the leader used.
    pub material_witness_depth: usize,
}

/// The founded axis failed to predict the material at the next tip: a real material change.
///
/// Retained, never discarded. The leader law: *"Branches which do not become the final cloud-ground
/// route are still real constructions."* In integration terms this is the part of the covering that
/// found no support — kept as the obstruction set.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RefoundingObstruction {
    pub extension_index: usize,
    pub offset: Rat,
    pub predicted_jet: LocalJet,
    pub returned_jet: LocalJet,
    /// What the founded axis would have deposited over the next span, minus what the material did.
    pub winding_residual: Rat,
}

/// A proposed ride whose landing jet disagreed with the founded axis. Refused and retained.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RefusedRide {
    pub extension_index: usize,
    pub offset: Rat,
    pub proposed_span: Rat,
    pub predicted_landing_jet: LocalJet,
    pub returned_landing_jet: LocalJet,
}

/// The self-similarity law firing: the founded area scaled by `scale` with no residual.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ScaleWitness {
    pub extension_index: usize,
    pub grain: Rat,
    /// `λ = span / grain`. The founded axis carried this many grains in one extension.
    pub scale: Rat,
    pub founded_rank: usize,
    pub scaled_winding: Rat,
}

/// The return: the sum **together with its path**.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LeaderQuadrature {
    pub schema: String,
    pub grain: Rat,
    pub discipline: RideDiscipline,
    /// Where the depth came from, as declared.
    pub witness_depth: WitnessDepth,
    /// **What the material stopped the leader at**: the deepest requirement any tip returned. Under
    /// [`WitnessDepth::ReadOffTheJet`] this is the whole of what governed the riding; under
    /// [`WitnessDepth::Declared`] it is the floor the declaration had to clear.
    pub material_witness_depth: usize,
    pub jet_aperture: usize,
    pub extensions: Vec<Extension>,
    pub obstructions: Vec<RefoundingObstruction>,
    pub refused_rides: Vec<RefusedRide>,
    pub scale_witnesses: Vec<ScaleWitness>,
    /// The exact running sum over founded extensions. No mesh, no limit, no error term.
    pub area: Rat,
}

impl LeaderQuadrature {
    pub fn extension_count(&self) -> usize {
        self.extensions.len()
    }

    pub fn found_count(&self) -> usize {
        self.extensions
            .iter()
            .filter(|extension| matches!(extension.kind, ExtensionKind::Found))
            .count()
    }

    pub fn ride_count(&self) -> usize {
        self.extensions
            .iter()
            .filter(|extension| matches!(extension.kind, ExtensionKind::Ride { .. }))
            .count()
    }

    /// The ordered spans of the lineage. Two runs whose spans agree grew the same path.
    pub fn extension_spans(&self) -> Vec<Rat> {
        self.extensions
            .iter()
            .map(|extension| extension.span.clone())
            .collect()
    }
}

// ---------------------------------------------------------------------------------------------
// the growth

/// Grow a leader population under `law` against `material` and return the lineage with its sum.
///
/// Deterministic and local. There is no route chooser, no target search and no global path: at
/// every tip the leader performs one read of the standing form, compares it with the axis it
/// founded at the previous tip, and extends.
pub fn integrate_by_leaders(
    material: &MaterialBoundary,
    law: &LeaderLaw,
) -> Result<LeaderQuadrature, LeaderError> {
    law.validate()?;

    let region_span = material.span().clone();
    let mut offset = Rat::zero();
    let mut area = Rat::zero();
    let mut ancestry = Rat::zero();
    let mut agreements: usize = 0;
    let mut material_witness_depth: usize = 0;
    let mut founded: Option<(LocalJet, Rat)> = None;

    let mut extensions: Vec<Extension> = Vec::new();
    let mut obstructions: Vec<RefoundingObstruction> = Vec::new();
    let mut refused_rides: Vec<RefusedRide> = Vec::new();
    let mut scale_witnesses: Vec<ScaleWitness> = Vec::new();

    while let Some(standing) = material.standing_at(&offset) {
        let returned_jet = standing.jet;
        let predicted_jet = founded.as_ref().map(|(axis, taken)| axis.rebase(taken));
        let agrees = predicted_jet
            .as_ref()
            .map(|predicted| *predicted == returned_jet)
            .unwrap_or(false);
        if agrees {
            agreements += 1;
        }

        // The depth is read here, off the jet standing at this tip, before anything decides to
        // ride. A declaration that is shallower than this is refused rather than clamped: the
        // material is not negotiable and a truncated depth would certify a limit it had not
        // reached.
        let required_depth = returned_jet.rebase_movement_depth();
        material_witness_depth = material_witness_depth.max(required_depth);
        let effective_depth = law.witness_depth.at_a_tip(&offset, required_depth)?;

        let extension_index = extensions.len();
        let mut span = rat_min(&law.grain, &standing.reach).clone();
        let mut kind = ExtensionKind::Found;

        if agrees && agreements >= effective_depth && law.discipline.rides() {
            match law.discipline {
                RideDiscipline::GrainOnly => {}
                RideDiscipline::GermBounded => {
                    if standing.reach > law.grain {
                        span = standing.reach.clone();
                        kind = ExtensionKind::Ride {
                            scale: &span / &law.grain,
                        };
                    }
                }
                RideDiscipline::UnclampedAncestry => {
                    let region_remaining = &region_span - &offset;
                    let proposed = rat_min(&ancestry, &region_remaining).clone();
                    if proposed > law.grain {
                        let predicted_landing = returned_jet.rebase(&proposed);
                        let landing = material.standing_at(&(&offset + &proposed));
                        match landing {
                            None => {
                                span = proposed;
                                kind = ExtensionKind::Ride {
                                    scale: &span / &law.grain,
                                };
                            }
                            Some(landing) if landing.jet == predicted_landing => {
                                span = proposed;
                                kind = ExtensionKind::Ride {
                                    scale: &span / &law.grain,
                                };
                            }
                            Some(landing) => {
                                refused_rides.push(RefusedRide {
                                    extension_index,
                                    offset: offset.clone(),
                                    proposed_span: proposed,
                                    predicted_landing_jet: predicted_landing,
                                    returned_landing_jet: landing.jet,
                                });
                            }
                        }
                    }
                }
            }
        }

        if let Some(predicted) = predicted_jet.filter(|_| !agrees) {
            let residual = predicted.swept(&span) - returned_jet.swept(&span);
            obstructions.push(RefoundingObstruction {
                extension_index,
                offset: offset.clone(),
                predicted_jet: predicted,
                returned_jet: returned_jet.clone(),
                winding_residual: residual,
            });
            agreements = 0;
        }

        let winding = returned_jet.swept(&span);
        area = &area + &winding;

        if let ExtensionKind::Ride { scale } = &kind {
            scale_witnesses.push(ScaleWitness {
                extension_index,
                grain: law.grain.clone(),
                scale: scale.clone(),
                founded_rank: returned_jet.rank(),
                scaled_winding: winding.clone(),
            });
        }

        extensions.push(Extension {
            index: extension_index,
            germ_index: standing.germ_index,
            base_offset: offset.clone(),
            span: span.clone(),
            winding,
            running_sum: area.clone(),
            kind,
            material_witness_depth: required_depth,
        });

        ancestry = &ancestry + &span;
        offset = &offset + &span;
        founded = Some((returned_jet, span));
    }

    Ok(LeaderQuadrature {
        schema: "holonics.leader-quadrature.v1".to_string(),
        grain: law.grain.clone(),
        discipline: law.discipline,
        witness_depth: law.witness_depth,
        material_witness_depth,
        jet_aperture: material.jet_aperture(),
        extensions,
        obstructions,
        refused_rides,
        scale_witnesses,
        area,
    })
}

/// The independent implementation, used to grade the leader. One antiderivative per germ.
///
/// Costs `O(G·m)`; the leader costs `O(E·m²)`. This is strictly the cheaper of the two and returns
/// the same rational. What it cannot return is the lineage.
pub fn germwise_oracle_area(material: &MaterialBoundary) -> Rat {
    material
        .germs()
        .iter()
        .fold(Rat::zero(), |sum, germ| sum + germ.content())
}

/// The `Chi` residual between two leader lineages: the disagreement of two paths over one region.
///
/// Exactly zero within the declared aperture, which is this construction's own returned
/// falsification of the holonomy hope at this rank; non-zero exactly when one lineage was conducted
/// past its aperture, where it measures the violation.
pub fn path_disagreement(left: &LeaderQuadrature, right: &LeaderQuadrature) -> Rat {
    &left.area - &right.area
}

// ---------------------------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use relational_geometry::{integer, rat};
    use std::collections::BTreeSet;

    fn jet(coefficients: &[(i64, i64)]) -> LocalJet {
        LocalJet::new(
            coefficients
                .iter()
                .map(|(numerator, denominator)| rat(*numerator, *denominator))
                .collect(),
        )
        .expect("a jet with coefficients")
    }

    fn germ(extent: Rat, coefficients: &[(i64, i64)]) -> RationalGerm {
        RationalGerm::new(extent, jet(coefficients)).expect("a germ of positive extent")
    }

    fn material(germs: Vec<RationalGerm>) -> MaterialBoundary {
        MaterialBoundary::new(germs).expect("a non-empty material boundary")
    }

    fn law(grain: Rat, discipline: RideDiscipline, witness_depth: usize) -> LeaderLaw {
        LeaderLaw::new(grain, discipline, WitnessDepth::Declared(witness_depth))
    }

    /// Every run whose depth is not itself under test reads the depth off the material.
    fn run(
        boundary: &MaterialBoundary,
        grain: Rat,
        discipline: RideDiscipline,
    ) -> LeaderQuadrature {
        integrate_by_leaders(
            boundary,
            &LeaderLaw::new(grain, discipline, WitnessDepth::ReadOffTheJet),
        )
        .expect("a lawful growth")
    }

    // --- the fixture family -------------------------------------------------------------------
    //
    // Every fixture below carries its area as a literal rational computed by hand, so the test is
    // not grading the implementation against itself.

    /// `f(t) = 3` over an extent of 2. Area 6.
    fn constant_slab() -> (MaterialBoundary, Rat) {
        (material(vec![germ(integer(2), &[(3, 1)])]), integer(6))
    }

    /// `f(t) = 5t` over an extent of 3. Area `5·9/2 = 45/2`.
    fn linear_ramp() -> (MaterialBoundary, Rat) {
        (
            material(vec![germ(integer(3), &[(0, 1), (5, 1)])]),
            rat(45, 2),
        )
    }

    /// `f(t) = t^2` over an extent of 2. Area `8/3`.
    fn quadratic_bowl() -> (MaterialBoundary, Rat) {
        (
            material(vec![germ(integer(2), &[(0, 1), (0, 1), (1, 1)])]),
            rat(8, 3),
        )
    }

    /// `f(t) = 1 + t + t^2 + t^3` over an extent of 1. Area `1 + 1/2 + 1/3 + 1/4 = 25/12`.
    fn cubic_unit() -> (MaterialBoundary, Rat) {
        (
            material(vec![germ(integer(1), &[(1, 1), (1, 1), (1, 1), (1, 1)])]),
            rat(25, 12),
        )
    }

    /// `f(t) = 2 - 3t + 4t^2 - 5t^3 + 6t^4` over an extent of `1/2`.
    /// `1 - 3/8 + 1/6 - 5/64 + 3/80 = 721/960`.
    fn quartic_alternating() -> (MaterialBoundary, Rat) {
        (
            material(vec![germ(
                rat(1, 2),
                &[(2, 1), (-3, 1), (4, 1), (-5, 1), (6, 1)],
            )]),
            rat(721, 960),
        )
    }

    /// `f(t) = t - 1` over an extent of 2. Signed area exactly zero: the material crosses the axis
    /// and the windings cancel. Not usable as a nonzero control, and never used as one.
    fn signed_cancellation() -> (MaterialBoundary, Rat) {
        (
            material(vec![germ(integer(2), &[(-1, 1), (1, 1)])]),
            integer(0),
        )
    }

    /// Three germs, degrees 1, 0, 1, with extents that are **not** grain multiples.
    ///
    /// `f = t` on `[0, 7/3)`, `f = 5/2` on `[7/3, 7/3 + 4/5)`, `f = 11/4 + 2t` on the last `3/2`.
    /// Contents: `(7/3)^2/2 = 49/18`; `(5/2)(4/5) = 2`; `(11/4)(3/2) + (3/2)^2 = 33/8 + 9/4 = 51/8`.
    /// Total `49/18 + 2 + 51/8 = 196/72 + 144/72 + 459/72 = 799/72`.
    fn unaligned_piecewise() -> (MaterialBoundary, Rat) {
        (
            material(vec![
                germ(rat(7, 3), &[(0, 1), (1, 1)]),
                germ(rat(4, 5), &[(5, 2)]),
                germ(rat(3, 2), &[(11, 4), (2, 1)]),
            ]),
            rat(799, 72),
        )
    }

    /// The reverting material the declared-aperture falsifier needs.
    ///
    /// `f(x) = x` on `[0,3)`, `f(x) = 2` on `[3,4)`, `f(x) = x` on `[4,7)`.
    /// `9/2 + 2 + (49/2 - 8) = 9/2 + 2 + 33/2 = 23`.
    fn reverting_material() -> (MaterialBoundary, Rat) {
        (
            material(vec![
                germ(integer(3), &[(0, 1), (1, 1)]),
                germ(integer(1), &[(2, 1)]),
                germ(integer(3), &[(4, 1), (1, 1)]),
            ]),
            integer(23),
        )
    }

    /// Material that changes abruptly and does not revert.
    ///
    /// `f(x) = x` on `[0,2)`, then `g(u) = 7 + 3u^2` on the next 4.
    /// `2 + (7·4 + 4^3) = 2 + 28 + 64 = 94`.
    fn abrupt_material() -> (MaterialBoundary, Rat) {
        (
            material(vec![
                germ(integer(2), &[(0, 1), (1, 1)]),
                germ(integer(4), &[(7, 1), (0, 1), (3, 1)]),
            ]),
            integer(94),
        )
    }

    /// A ramp `f(x) = x` over `[0, extent]`. Area `extent^2 / 2`.
    fn long_ramp(extent: &Rat) -> MaterialBoundary {
        material(vec![
            RationalGerm::new(
                extent.clone(),
                LocalJet::new(vec![Rat::zero(), Rat::one()]).unwrap(),
            )
            .unwrap(),
        ])
    }

    fn every_fixture() -> Vec<(&'static str, MaterialBoundary, Rat)> {
        let mut fixtures = Vec::new();
        let (boundary, area) = constant_slab();
        fixtures.push(("constant_slab", boundary, area));
        let (boundary, area) = linear_ramp();
        fixtures.push(("linear_ramp", boundary, area));
        let (boundary, area) = quadratic_bowl();
        fixtures.push(("quadratic_bowl", boundary, area));
        let (boundary, area) = cubic_unit();
        fixtures.push(("cubic_unit", boundary, area));
        let (boundary, area) = quartic_alternating();
        fixtures.push(("quartic_alternating", boundary, area));
        let (boundary, area) = signed_cancellation();
        fixtures.push(("signed_cancellation", boundary, area));
        let (boundary, area) = unaligned_piecewise();
        fixtures.push(("unaligned_piecewise", boundary, area));
        let (boundary, area) = reverting_material();
        fixtures.push(("reverting_material", boundary, area));
        let (boundary, area) = abrupt_material();
        fixtures.push(("abrupt_material", boundary, area));
        fixtures
    }

    fn declared_grains() -> Vec<Rat> {
        vec![
            integer(5),
            integer(1),
            rat(1, 3),
            rat(22, 7),
            rat(1, 64),
            rat(3, 7),
        ]
    }

    // --- exactness ----------------------------------------------------------------------------

    #[test]
    fn returned_area_equals_the_hand_computed_rational_on_every_fixture_and_grain() {
        for (name, boundary, expected) in every_fixture() {
            for grain in declared_grains() {
                for discipline in [RideDiscipline::GrainOnly, RideDiscipline::GermBounded] {
                    let quadrature = run(&boundary, grain.clone(), discipline);
                    assert_eq!(
                        quadrature.area, expected,
                        "{name} at grain {grain} under {discipline:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn returned_area_is_invariant_under_the_declared_grain() {
        for (name, boundary, _) in every_fixture() {
            let mut seen: Option<Rat> = None;
            let mut counts = Vec::new();
            for grain in declared_grains() {
                let quadrature = run(&boundary, grain.clone(), RideDiscipline::GrainOnly);
                counts.push(quadrature.extension_count());
                match &seen {
                    None => seen = Some(quadrature.area.clone()),
                    Some(first) => assert_eq!(
                        &quadrature.area, first,
                        "{name}: grain {grain} moved the returned area"
                    ),
                }
            }
            // The material of the test must actually vary: if every grain produced the same
            // lineage there would be nothing for grain-invariance to be invariant over.
            assert!(
                counts.iter().min() != counts.iter().max(),
                "{name}: the declared grains did not change the extension count, so this fixture \
                 cannot exercise grain invariance"
            );
        }
    }

    #[test]
    fn oracle_conformance_across_every_fixture() {
        for (name, boundary, expected) in every_fixture() {
            let oracle = germwise_oracle_area(&boundary);
            assert_eq!(
                oracle, expected,
                "{name}: the oracle disagrees with the hand figure"
            );
            // The declared depth sweeps from what the material required upward: a shallower
            // declaration is refused rather than silently accepted, which is the whole of the
            // excision.
            let floor = boundary.jet_aperture();
            for discipline in [RideDiscipline::GrainOnly, RideDiscipline::GermBounded] {
                let read_off = run(&boundary, rat(2, 5), discipline);
                assert_eq!(
                    read_off.area, oracle,
                    "{name} under {discipline:?}/read-off"
                );
                for depth in floor..=floor + 3 {
                    let quadrature =
                        integrate_by_leaders(&boundary, &law(rat(2, 5), discipline, depth))
                            .expect("a lawful growth");
                    assert_eq!(
                        quadrature.area, oracle,
                        "{name} under {discipline:?}/{depth}"
                    );
                }
            }
        }
    }

    // --- the self-similarity termination law --------------------------------------------------

    #[test]
    fn self_similarity_termination_law_holds_at_every_scale() {
        // The law: once founded, the geometry is an axis the founded area scales along. The
        // measured consequence is that the extension count does NOT grow with the region, while
        // the returned rational stays exact.
        let scales = [
            integer(10),
            integer(1_000),
            integer(1_000_000),
            Rat::from_integer(BigInt::from(1_000_000_000_000i64)),
        ];
        //
        // `long_ramp` carries `f(x) = x`, a rank-two jet, so the material returns a witness depth
        // of two: the leader FOUNDs twice before the agreement lineage licenses a ride. Under the
        // excised `LEADER_WITNESS_DEPTH = 1` it founded once, rode at scale `extent − 1`, and
        // returned two extensions. The depth read off the jet moves both — `extent − 2` and three
        // extensions — and moves neither with the size of the region, which is the law under test.
        let mut ridden_counts = Vec::new();
        for extent in &scales {
            let boundary = long_ramp(extent);
            let depth = Rat::from_integer(BigInt::from(boundary.jet_aperture()));
            assert_eq!(
                boundary.jet_aperture(),
                2,
                "f(x) = x carries a rank-two jet"
            );
            let ridden = run(&boundary, Rat::one(), RideDiscipline::GermBounded);
            let expected = (extent * extent) / integer(2);
            assert_eq!(
                ridden.area, expected,
                "the scaled area lost accuracy at {extent}"
            );
            assert_eq!(
                ridden.ride_count(),
                1,
                "the founded axis was not ridden at {extent}"
            );
            assert_eq!(
                ridden.material_witness_depth, 2,
                "the material returned a depth of two"
            );
            let witness = &ridden.scale_witnesses[0];
            assert_eq!(
                witness.scale,
                extent - &depth,
                "wrong scale witness at {extent}"
            );
            assert!(
                witness.scale > Rat::one(),
                "the witness must record a real scaling"
            );
            ridden_counts.push(ridden.extension_count());
        }
        assert_eq!(
            ridden_counts,
            vec![3, 3, 3, 3],
            "the founded axis did not scale for free: the extension count grew with the region"
        );

        // The other half of the falsifier: grain-only founding returns the identical rational and
        // its count DOES grow, so the constancy above is a property of riding, not of the fixture.
        let mut grain_only_counts = Vec::new();
        for extent in [integer(10), integer(100), integer(400)] {
            let boundary = long_ramp(&extent);
            let founded = run(&boundary, Rat::one(), RideDiscipline::GrainOnly);
            let ridden = run(&boundary, Rat::one(), RideDiscipline::GermBounded);
            assert_eq!(
                founded.area, ridden.area,
                "riding moved the sum at {extent}"
            );
            assert_eq!(founded.area, (&extent * &extent) / integer(2));
            grain_only_counts.push(founded.extension_count());
        }
        assert_eq!(grain_only_counts, vec![10, 100, 400]);
    }

    #[test]
    fn the_founded_axis_scales_the_area_at_every_rational_scale() {
        // The law as stated: for the founded jet j at a tip, the content swept by one extension of
        // span λ·grain is exactly J(λ·grain) for every rational λ. Exercised directly against a
        // hand figure so it cannot be satisfied by construction.
        //
        // j(t) = 1 + 2t + 3t^2  =>  J(s) = s + s^2 + s^3.
        let founded = jet(&[(1, 1), (2, 1), (3, 1)]);
        for (numerator, denominator) in [
            (1, 1),
            (7, 1),
            (1, 3),
            (13, 5),
            (101, 2),
            (1, 128),
            (9_999, 7),
        ] {
            let span = rat(numerator, denominator);
            let square = &span * &span;
            let expected = &span + &square + &square * &span;
            assert_eq!(
                founded.swept(&span),
                expected,
                "scale {numerator}/{denominator}"
            );
        }
    }

    #[test]
    fn witness_depth_cannot_change_the_returned_area_inside_the_aperture() {
        for (name, boundary, expected) in every_fixture() {
            let floor = boundary.jet_aperture();
            for discipline in [RideDiscipline::GrainOnly, RideDiscipline::GermBounded] {
                let read_off = run(&boundary, rat(1, 2), discipline);
                assert_eq!(
                    read_off.area, expected,
                    "{name}: the depth read off the material moved the return under {discipline:?}"
                );
                for depth in floor..=floor + 7 {
                    let quadrature =
                        integrate_by_leaders(&boundary, &law(rat(1, 2), discipline, depth))
                            .expect("a lawful growth");
                    assert_eq!(
                        quadrature.area, expected,
                        "{name}: witness depth {depth} under {discipline:?} moved the return"
                    );
                }
            }
        }
        // And the depth must actually be doing something, or the invariance is vacuous.
        let (boundary, _) = unaligned_piecewise();
        let floor = boundary.jet_aperture();
        let shallow = integrate_by_leaders(
            &boundary,
            &law(rat(1, 2), RideDiscipline::GermBounded, floor),
        )
        .unwrap();
        let deep = integrate_by_leaders(
            &boundary,
            &law(rat(1, 2), RideDiscipline::GermBounded, floor + 7),
        )
        .unwrap();
        assert!(
            shallow.extension_count() < deep.extension_count(),
            "witness depth did not change the lineage, so its invariance is untested"
        );
    }

    // --- the depth, read off the material ------------------------------------------------------

    #[test]
    fn the_jet_stops_moving_at_its_own_rank() {
        // The theorem `rebase_movement_depth` claims, measured rather than asserted: the sequence
        // of rebased jets along an arithmetic progression of offsets is annihilated by the
        // rank-th forward difference and by no lower order.
        //
        // The control is the second half. If `Δ^(m-1)` also annihilated, the rank would be an
        // over-estimate and this test would fail; it is exercised on rank 2, 3, 4 and 5 below.
        fn coefficients(jet: &LocalJet, rank: usize) -> Vec<Rat> {
            let mut padded = jet.coefficients().to_vec();
            padded.resize(rank, Rat::zero());
            padded
        }

        fn difference(rows: &[Vec<Rat>]) -> Vec<Vec<Rat>> {
            rows.windows(2)
                .map(|pair| {
                    pair[1]
                        .iter()
                        .zip(&pair[0])
                        .map(|(next, here)| next - here)
                        .collect()
                })
                .collect()
        }

        fn all_zero(rows: &[Vec<Rat>]) -> bool {
            rows.iter()
                .all(|row| row.iter().all(|value| value.is_zero()))
        }

        let declared = [
            jet(&[(7, 2)]),
            jet(&[(-1, 1), (1, 1)]),
            jet(&[(0, 1), (0, 1), (1, 1)]),
            jet(&[(1, 1), (1, 1), (1, 1), (1, 1)]),
            jet(&[(2, 1), (-3, 1), (4, 1), (-5, 1), (6, 1)]),
        ];
        for source in declared {
            let rank = source.rank();
            assert_eq!(source.rebase_movement_depth(), rank);
            for (step_numerator, step_denominator) in [(1, 1), (1, 3), (5, 2), (22, 7)] {
                let step = rat(step_numerator, step_denominator);
                // Rank + 3 offsets is enough to take rank + 2 differences.
                let mut offset = Rat::zero();
                let mut rows: Vec<Vec<Rat>> = Vec::new();
                for _ in 0..rank + 3 {
                    rows.push(coefficients(&source.rebase(&offset), rank));
                    offset = &offset + &step;
                }
                let mut order = 0usize;
                let mut current = rows;
                while !all_zero(&current) {
                    current = difference(&current);
                    order += 1;
                    assert!(
                        !current.is_empty(),
                        "rank {rank} at step {step}: the rebase never stopped moving"
                    );
                }
                assert_eq!(
                    order, rank,
                    "rank {rank} at step {step}: the rebase stopped contributing at order {order}"
                );
            }
        }
    }

    #[test]
    fn the_depth_the_material_returns_is_local_and_is_carried_on_every_extension() {
        // `unaligned_piecewise` carries ranks 2, 1, 2. The returned depth must be 2 inside the
        // outer germs and 1 inside the constant one — a *local* read, not a global maximum.
        let (boundary, _) = unaligned_piecewise();
        let quadrature = run(&boundary, rat(1, 4), RideDiscipline::GrainOnly);
        assert_eq!(quadrature.material_witness_depth, 2);
        let by_germ: Vec<(usize, usize)> = quadrature
            .extensions
            .iter()
            .map(|extension| (extension.germ_index, extension.material_witness_depth))
            .collect();
        for (germ_index, depth) in &by_germ {
            let expected = boundary.germs()[*germ_index].jet().rank();
            assert_eq!(
                *depth, expected,
                "germ {germ_index} returned depth {depth} for a rank-{expected} jet"
            );
        }
        // The material must actually carry two different depths, or "local" is untested.
        let distinct: BTreeSet<usize> = by_germ.iter().map(|(_, depth)| *depth).collect();
        assert_eq!(
            distinct,
            BTreeSet::from([1, 2]),
            "this fixture must return more than one depth or locality is vacuous"
        );
    }

    #[test]
    fn a_declared_depth_below_what_the_material_required_is_refused_by_name() {
        // The excision, as a refusal. `linear_ramp` carries a rank-2 jet: after one agreement the
        // rebase is still contributing a difference, so a declared depth of one is a claim about a
        // limit that has not been reached, and it is refused rather than accepted.
        let (boundary, _) = linear_ramp();
        assert_eq!(boundary.jet_aperture(), 2);
        assert_eq!(
            integrate_by_leaders(&boundary, &law(Rat::one(), RideDiscipline::GermBounded, 1)),
            Err(LeaderError::WitnessDepthBelowMaterial {
                offset: Rat::zero(),
                declared: 1,
                required: 2,
            })
        );
        // At the material's own requirement, and above it, the same declaration is admitted.
        for depth in 2..=5 {
            assert!(
                integrate_by_leaders(
                    &boundary,
                    &law(Rat::one(), RideDiscipline::GermBounded, depth)
                )
                .is_ok(),
                "depth {depth} is at or above what the material required and must be admitted"
            );
        }
        // And the control: a constant jet requires exactly one, so a declared one is NOT refused
        // there. Without this the refusal above could be a blanket ban on declaring one.
        let (constant, _) = constant_slab();
        assert_eq!(constant.jet_aperture(), 1);
        assert!(
            integrate_by_leaders(&constant, &law(Rat::one(), RideDiscipline::GermBounded, 1))
                .is_ok(),
            "one is the honest depth on a constant jet and must be admitted"
        );
    }

    #[test]
    fn depth_one_certifies_a_limit_the_jet_had_not_reached() {
        // The material on which the old pin was demonstrably wrong, and the measurement that says
        // so. `reverting_material`'s first germ carries `f(t) = t`: the jet at offset 0 is `[0,1]`
        // and at offset 1 it is `[1,1]`. The jet MOVED between extension one and extension two, so
        // an agreement lineage of length one has not witnessed a limit.
        let (boundary, truth) = reverting_material();
        let at_zero = boundary.standing_at(&Rat::zero()).unwrap().jet;
        let at_one = boundary.standing_at(&Rat::one()).unwrap().jet;
        assert_ne!(
            at_zero, at_one,
            "the separating material must actually move its jet between two extensions"
        );
        assert_eq!(at_zero.rebase_movement_depth(), 2);

        // Past the declared aperture, that difference is the whole return. The organ conducted
        // with an authored depth of one returns 49/2 where the truth is 23; every extra agreement
        // the material asked for and did not get is the 3/2.
        let shallow = integrate_by_leaders(
            &boundary,
            &LeaderLaw::new(
                Rat::one(),
                RideDiscipline::UnclampedAncestry,
                WitnessDepth::Declared(1),
            ),
        );
        assert_eq!(
            shallow,
            Err(LeaderError::WitnessDepthBelowMaterial {
                offset: Rat::zero(),
                declared: 1,
                required: 2,
            }),
            "the depth the pin authored is now refused on the material that separates it"
        );

        // The same growth at depths the material admits, so the movement is exhibited rather than
        // only refused. Depth 3 is above the requirement and recovers the truth; depth 2 does not.
        let at_two = integrate_by_leaders(
            &boundary,
            &LeaderLaw::new(
                Rat::one(),
                RideDiscipline::UnclampedAncestry,
                WitnessDepth::Declared(2),
            ),
        )
        .expect("two is at the material's requirement");
        let at_three = integrate_by_leaders(
            &boundary,
            &LeaderLaw::new(
                Rat::one(),
                RideDiscipline::UnclampedAncestry,
                WitnessDepth::Declared(3),
            ),
        )
        .expect("three is above the material's requirement");
        assert_eq!(at_two.area, rat(49, 2));
        assert_eq!(at_three.area, truth);
        assert_eq!(path_disagreement(&at_two, &at_three), rat(3, 2));
    }

    #[test]
    fn the_declared_grain_rides_by_at_least_one_rank_step() {
        let one_rank_step = Rat::from_integer(BigInt::from(2));

        // `declared_grain`'s derivation, measured: at the grain the material declares for itself,
        // EVERY standing form rides by at least one whole rank step.
        for (name, boundary, expected) in every_fixture() {
            let grain = boundary.declared_grain();
            assert!(grain.is_positive(), "{name}");
            assert_eq!(
                &grain * Rat::from_integer(BigInt::from(boundary.jet_aperture() + 2)),
                *boundary.finest_standing_extent(),
                "{name}: the declared grain is not the finest standing extent over depth + 2"
            );
            let quadrature = run(&boundary, grain.clone(), RideDiscipline::GermBounded);
            assert_eq!(quadrature.area, expected, "{name}");
            assert!(
                !quadrature.scale_witnesses.is_empty(),
                "{name}: the material's own grain founded no ride at all"
            );
            for witness in &quadrature.scale_witnesses {
                assert!(
                    witness.scale >= one_rank_step,
                    "{name}: a ride at the declared grain carried {} — less than one rank step",
                    witness.scale
                );
            }
        }

        // The bound is ATTAINED, not merely respected: on material whose one germ realizes both the
        // finest extent and the largest rank, the scale is exactly two. Without this the `+ 2`
        // could be any amount of slack.
        for (name, boundary, _) in [
            ("constant_slab", constant_slab().0, ()),
            ("linear_ramp", linear_ramp().0, ()),
            ("quadratic_bowl", quadratic_bowl().0, ()),
            ("cubic_unit", cubic_unit().0, ()),
            ("quartic_alternating", quartic_alternating().0, ()),
        ] {
            assert_eq!(
                boundary.germ_count(),
                1,
                "{name} must be a single standing form"
            );
            let quadrature = run(
                &boundary,
                boundary.declared_grain(),
                RideDiscipline::GermBounded,
            );
            assert_eq!(
                quadrature.scale_witnesses.len(),
                1,
                "{name}: one germ at its own grain founds exactly one ride"
            );
            assert_eq!(
                quadrature.scale_witnesses[0].scale, one_rank_step,
                "{name}: the bound is not attained, so the derivation has slack in it"
            );

            // And one step coarser — the open bound E/(d+1) — that germ does not ride at all.
            let bound = boundary.finest_standing_extent().clone()
                / Rat::from_integer(BigInt::from(boundary.jet_aperture() + 1));
            let at_the_bound = run(&boundary, bound.clone(), RideDiscipline::GermBounded);
            assert!(
                at_the_bound.scale_witnesses.is_empty(),
                "{name}: the open bound {bound} rode, so `+ 2` is not the least admissible step"
            );
        }
    }

    // --- parameter transformation -------------------------------------------------------------

    #[test]
    fn the_integration_pathways_accommodate_parameter_transformation() {
        for (name, boundary, expected) in every_fixture() {
            for (numerator, denominator) in [(3, 1), (1, 7), (100, 1), (22, 7)] {
                let alpha = rat(numerator, denominator);
                let rescaled = boundary
                    .rescale_parameter(&alpha)
                    .expect("a positive rescaling");
                for discipline in [RideDiscipline::GrainOnly, RideDiscipline::GermBounded] {
                    let original = run(&boundary, rat(1, 2), discipline);
                    let carried = run(&rescaled, rat(1, 2) / &alpha, discipline);

                    // The rank-one Jacobian, with no remainder: an invertible chart change creates
                    // none.
                    assert_eq!(
                        &carried.area * &alpha,
                        expected,
                        "{name} under alpha {alpha} / {discipline:?}"
                    );
                    // And the pathway itself is carried, not rebuilt: the same lineage, rescaled.
                    assert_eq!(
                        carried.extension_count(),
                        original.extension_count(),
                        "{name}: the extension lineage changed under reparametrization"
                    );
                    assert_eq!(
                        carried.obstructions.len(),
                        original.obstructions.len(),
                        "{name}: the obstruction population changed under reparametrization"
                    );
                    let carried_spans: Vec<Rat> = carried
                        .extension_spans()
                        .into_iter()
                        .map(|span| span * &alpha)
                        .collect();
                    assert_eq!(
                        carried_spans,
                        original.extension_spans(),
                        "{name}: the founded spans did not transport"
                    );
                }
            }
        }
    }

    // --- the retained obstruction population --------------------------------------------------

    #[test]
    fn obstructions_locate_real_material_change_and_not_declaration() {
        let (boundary, expected) = unaligned_piecewise();
        let plain = run(&boundary, rat(1, 4), RideDiscipline::GrainOnly);
        assert_eq!(plain.area, expected);
        assert_eq!(
            plain.obstructions.len(),
            2,
            "three germs of genuinely different material must refound twice"
        );

        // Re-declare the material with one extra germ that carries the SAME polynomial. The
        // boundary is identical; only the declaration changed.
        let redeclared = boundary
            .redeclare_split(0, &rat(1, 1))
            .expect("a lawful redeclaration");
        assert_eq!(redeclared.germ_count(), boundary.germ_count() + 1);
        assert_eq!(germwise_oracle_area(&redeclared), expected);

        let after = run(&redeclared, rat(1, 4), RideDiscipline::GrainOnly);
        assert_eq!(
            after.area, expected,
            "a redeclaration moved the returned area"
        );
        assert_eq!(
            after.obstructions.len(),
            plain.obstructions.len(),
            "a redeclaration that changed no material invented a refounding obstruction"
        );

        // And a split that DOES change the material must add one. Otherwise the assertion above
        // would pass for an implementation that never refounds at all.
        let changed = material(vec![
            germ(rat(1, 1), &[(0, 1), (1, 1)]),
            germ(rat(4, 3), &[(9, 1), (1, 1)]),
            germ(rat(4, 5), &[(5, 2)]),
            germ(rat(3, 2), &[(11, 4), (2, 1)]),
        ]);
        let changed_run = run(&changed, rat(1, 4), RideDiscipline::GrainOnly);
        assert_eq!(
            changed_run.obstructions.len(),
            plain.obstructions.len() + 1,
            "a real material change did not refound"
        );
    }

    #[test]
    fn a_single_germ_refounds_never_and_a_ride_witnesses_a_real_scaling() {
        let (boundary, expected) = quartic_alternating();
        let quadrature = run(&boundary, rat(1, 32), RideDiscipline::GermBounded);
        assert_eq!(quadrature.area, expected);
        assert!(
            quadrature.obstructions.is_empty(),
            "one germ of one polynomial cannot change material"
        );
        assert_eq!(quadrature.ride_count(), 1);
        assert!(quadrature.scale_witnesses[0].scale > Rat::one());
    }

    // --- provably nonzero controls ------------------------------------------------------------

    // -----------------------------------------------------------------------------------------
    // THE TWO DETERMINATION LAWS AS CHAIN LINKS — 2026-08-17
    // -----------------------------------------------------------------------------------------

    /// ★ WHAT SEPARATES GOING THROUGH FROM GOING STRAIGHT, WHEN SOME STEPS WERE COMMITTED
    /// BALLISTICALLY — the question no existing chain in this tree could ask.
    ///
    /// Two growths over **one material**: one that never rides, so every step re-reads the material
    /// at its own grain, and one that rides, so some steps commit across a whole reach on the
    /// strength of a run of exact agreement. The winding must agree — that is this module's own
    /// theorem and it is why riding is lawful — and the **committed remainder** must not, because
    /// that is the whole difference between the two determination laws.
    #[test]
    fn the_winding_agrees_and_the_committed_remainder_does_not() {
        let (boundary, expected) = unaligned_piecewise();
        let grain = rat(1, 4);
        let walked = run(&boundary, grain.clone(), RideDiscipline::GrainOnly);
        let ridden = run(&boundary, grain.clone(), RideDiscipline::GermBounded);

        // The material is the same and both growths return it exactly.
        assert_eq!(walked.area, expected);
        assert_eq!(ridden.area, expected);
        // THE ANTI-VACUITY ARM: the ridden growth must actually ride, or there are not two laws here.
        assert!(
            ridden.ride_count() > 0,
            "nothing was ridden; there is one law, not two"
        );
        assert_eq!(walked.ride_count(), 0, "the control must never ride");

        let walked_chain = chain_of(&walked);
        let ridden_chain = chain_of(&ridden);
        let straight = walked_chain.compose();
        let through = ridden_chain.compose();

        // ONE: the winding is the same. Going through and going straight deposit the same total.
        assert_eq!(straight.winding, through.winding);
        assert_eq!(straight.winding, expected);

        // TWO: the committed remainders are not. THIS IS THE DETERMINATION-LAW MISMATCH, and it is
        // invisible to the winding — a chain that carried only the running sum would report these
        // two growths as identical.
        assert!(
            straight.uninspected.is_zero(),
            "a chain that re-reads at every grain commits past nothing -- A DEFINITION, not evidence"
        );
        assert!(
            through.uninspected.is_positive(),
            "the ridden growth must have committed past material it did not read"
        );

        // THREE: the cocycle defect against the straight transport says exactly that, and says it in
        // one coordinate rather than in prose.
        let defect = ridden_chain.defect_against(&straight);
        assert!(
            defect.winding.is_zero(),
            "the windings do not separate them"
        );
        assert!(!defect.uninspected.is_zero(), "the commitment does");
        assert!(
            !<CommittedTransport as Composes>::closed(&defect),
            "the two determination laws do not compose to the same transport"
        );

        // FOUR: the chain's own remainder is the committed material, and `is_rebase` reads it.
        assert!(
            walked_chain.is_rebase(),
            "walking every grain is a rebase with no remainder"
        );
        assert!(!ridden_chain.is_rebase(), "riding is not");
    }

    /// ★ THE HAND READS THE STORED FACE HERE TOO, AND A COMMITTED STEP STORED NOTHING — with the
    /// relationship to the *preceding* step measured rather than assumed, because the first version
    /// of this test assumed it and was wrong.
    ///
    /// The hand is the sign of the **stored face** at every implementor in this tree — `aim` at an
    /// arrow, `M₂₁` at a junction, and the residual here, which is what the material returned against
    /// the step's own prediction and therefore did *not* transport. `Ortho` is the step that stored
    /// nothing.
    ///
    /// **What was assumed and is false:** that the step immediately before a ride also reads `Ortho`.
    /// It does not — measured on `unaligned_piecewise` at grain `1/4`, a step preceding a committed
    /// one reads `Anti`. A `RefoundingObstruction` is attributed to the extension whose *founded
    /// axis* failed, and that index is not the index of the tip at which the failure was discovered,
    /// so the residual sits one step from where a naive reading expects it. **That offset is a fact
    /// about the growth's own bookkeeping and it is reported rather than asserted away.**
    #[test]
    fn a_committed_step_stored_nothing_and_the_preceding_hand_is_measured() {
        let (boundary, _) = unaligned_piecewise();
        let ridden = run(&boundary, rat(1, 4), RideDiscipline::GermBounded);
        let chain = chain_of(&ridden);
        let links = chain.links();
        assert!(
            links.iter().any(|step| step.is_committed()),
            "no ride to check"
        );
        assert!(
            !ridden.obstructions.is_empty(),
            "the material must refound somewhere or the hand cannot vary"
        );

        // ONE, and it holds: every committed step's OWN residual vanished.
        let committed: Vec<&CommittedStep> =
            links.iter().filter(|step| step.is_committed()).collect();
        assert!(!committed.is_empty());
        for step in &committed {
            assert_eq!(
                step.hand(),
                Hand::Ortho,
                "a committed step stored nothing at index {}",
                step.index
            );
        }

        // TWO, MEASURED: the preceding hands are a population, not a constant. Both readings occur,
        // which is what makes the hand a reading of the material rather than of the ride.
        let preceding: Vec<Hand> = links
            .iter()
            .enumerate()
            .filter(|(at, step)| step.is_committed() && *at > 0)
            .map(|(at, _)| links[at - 1].hand())
            .collect();
        assert!(!preceding.is_empty());
        assert!(
            preceding.iter().any(|hand| *hand != Hand::Ortho),
            "if every preceding hand were Ortho the reading would be forced by the licence"
        );

        // THREE, THE ANTI-VACUITY ARM: a refounding step stored something, so its hand is NOT Ortho.
        // Without this the hand would be a constant wearing an enum.
        let refounded: Vec<Hand> = links
            .iter()
            .filter(|step| !step.residual.is_zero())
            .map(Relating::hand)
            .collect();
        assert!(!refounded.is_empty(), "no step stored anything");
        assert!(
            refounded.iter().all(|hand| *hand != Hand::Ortho),
            "a refounding step stored a residual and must not read Ortho"
        );
        // and both in-plane hands are reachable, so the sign is carrying information
        assert!(
            refounded.iter().any(|hand| *hand == Hand::Anti)
                || refounded.iter().any(|hand| *hand == Hand::Cohere),
            "the residual's sign must be readable"
        );
    }

    #[test]
    fn nonzero_controls() {
        // A law that returns zero proves nothing about itself (CLAUDE.md §8). Each population this
        // module can return is exercised here on material that forces it to be non-empty.
        let (boundary, expected) = unaligned_piecewise();
        assert!(expected > Rat::zero(), "the graded area must be nonzero");

        let ridden = run(&boundary, rat(1, 4), RideDiscipline::GermBounded);
        assert_eq!(ridden.area, expected);
        assert!(ridden.area > Rat::zero(), "the returned area is zero");
        assert!(ridden.extension_count() > 0, "no extension was founded");
        assert!(ridden.found_count() > 0, "nothing was FOUNDed");
        assert!(ridden.ride_count() > 0, "nothing was RIDden");
        assert!(
            !ridden.obstructions.is_empty(),
            "no obstruction was retained"
        );
        assert!(!ridden.scale_witnesses.is_empty(), "no scale was witnessed");
        assert!(
            ridden
                .obstructions
                .iter()
                .any(|obstruction| !obstruction.winding_residual.is_zero()),
            "every retained obstruction carried a zero residual, so none of them measured anything"
        );
        for obstruction in &ridden.obstructions {
            assert_ne!(
                obstruction.predicted_jet, obstruction.returned_jet,
                "an obstruction was retained where the material did not change"
            );
        }

        // The refused-ride population needs a leader conducted past its aperture against material
        // that changes at the landing tip of the ride it proposes.
        let (abrupt, abrupt_area) = abrupt_material();
        assert_eq!(
            run(&abrupt, rat(1, 2), RideDiscipline::GermBounded).area,
            abrupt_area
        );
        let refusing = integrate_by_leaders(
            &abrupt,
            &LeaderLaw::new(
                rat(1, 2),
                RideDiscipline::UnclampedAncestry,
                WitnessDepth::ReadOffTheJet,
            ),
        )
        .expect("a lawful growth");
        assert!(
            !refusing.refused_rides.is_empty(),
            "no ride was refused, so the refusal law is present in the code and absent from the \
             evidence"
        );
        for refusal in &refusing.refused_rides {
            assert!(refusal.proposed_span > refusing.grain);
            assert_ne!(
                refusal.predicted_landing_jet, refusal.returned_landing_jet,
                "a ride was refused where the landing material agreed"
            );
        }
    }

    // --- the declared aperture ----------------------------------------------------------------

    #[test]
    fn declared_aperture_falsifier_returns_a_measured_holonomy() {
        let (boundary, truth) = reverting_material();
        assert_eq!(truth, integer(23));
        assert_eq!(germwise_oracle_area(&boundary), truth);

        let grain_only = run(&boundary, Rat::one(), RideDiscipline::GrainOnly);
        let germ_bounded = run(&boundary, Rat::one(), RideDiscipline::GermBounded);
        assert_eq!(
            grain_only.area, truth,
            "grain-only founding is inside the aperture"
        );
        assert_eq!(
            germ_bounded.area, truth,
            "germ-bounded riding is inside the aperture"
        );
        assert_eq!(
            path_disagreement(&grain_only, &germ_bounded),
            Rat::zero(),
            "two paths inside the declared aperture must agree exactly"
        );

        // The same organ conducted past its aperture, at the depth the material itself returns. It
        // appears to return: the growth completes, every ride it took passed its landing-jet check,
        // and the number is wrong. The depth being read off the jet does not rescue this — nothing
        // does, which is what "past the declared aperture" means.
        let unclamped = integrate_by_leaders(
            &boundary,
            &LeaderLaw::new(
                Rat::one(),
                RideDiscipline::UnclampedAncestry,
                WitnessDepth::ReadOffTheJet,
            ),
        )
        .expect("a lawful growth");
        assert_eq!(
            unclamped.area,
            rat(49, 2),
            "the aperture violation did not reproduce; the falsifier fixture no longer bites"
        );
        assert!(
            unclamped.refused_rides.is_empty(),
            "this fixture must exhibit an aperture violation that passes every local check"
        );
        assert_eq!(
            path_disagreement(&unclamped, &grain_only),
            rat(3, 2),
            "the measured holonomy of the aperture violation changed"
        );
        assert_ne!(path_disagreement(&unclamped, &grain_only), Rat::zero());
    }

    #[test]
    fn two_paths_inside_the_aperture_disagree_nowhere() {
        // The deposited falsifier, run and reported rather than hoped for: at this rank the
        // construction's holonomy is exactly zero on every fixture, which is the honest return.
        for (name, boundary, _) in every_fixture() {
            let coarse = run(&boundary, integer(5), RideDiscipline::GrainOnly);
            let fine = run(&boundary, rat(1, 64), RideDiscipline::GrainOnly);
            let ridden = run(&boundary, rat(3, 7), RideDiscipline::GermBounded);
            assert_eq!(path_disagreement(&coarse, &fine), Rat::zero(), "{name}");
            assert_eq!(path_disagreement(&coarse, &ridden), Rat::zero(), "{name}");
            assert!(
                coarse.extension_spans() != fine.extension_spans(),
                "{name}: the two paths compared were the same path"
            );
        }
    }

    // --- the local jet, which every winding rests on ------------------------------------------

    #[test]
    fn rebase_is_an_exact_taylor_shift() {
        let source = jet(&[(3, 4), (-5, 2), (7, 3), (1, 1), (-2, 5)]);
        for (shift_numerator, shift_denominator) in [(1, 1), (-3, 2), (5, 7), (0, 1), (13, 4)] {
            let shift = rat(shift_numerator, shift_denominator);
            let shifted = source.rebase(&shift);
            for (argument_numerator, argument_denominator) in [(0, 1), (1, 1), (-2, 3), (11, 5)] {
                let argument = rat(argument_numerator, argument_denominator);
                assert_eq!(
                    shifted.value_at(&argument),
                    source.value_at(&(&argument + &shift)),
                    "rebase by {shift} evaluated at {argument}"
                );
            }
        }
        assert_eq!(source.rebase(&Rat::zero()), source);
        let composed = source.rebase(&rat(2, 3)).rebase(&rat(5, 7));
        assert_eq!(composed, source.rebase(&(rat(2, 3) + rat(5, 7))));
    }

    #[test]
    fn a_padded_declaration_is_the_same_material() {
        let plain = jet(&[(1, 1), (2, 1)]);
        let padded = jet(&[(1, 1), (2, 1), (0, 1), (0, 1)]);
        assert_eq!(
            plain, padded,
            "trailing zeros must not read as a material change"
        );
        assert_eq!(plain.rank(), 2);
    }

    #[test]
    fn swept_is_the_exact_termwise_antiderivative() {
        // Hand figures, independent of the implementation.
        assert_eq!(jet(&[(3, 1)]).swept(&integer(2)), integer(6));
        assert_eq!(jet(&[(0, 1), (5, 1)]).swept(&integer(3)), rat(45, 2));
        assert_eq!(jet(&[(0, 1), (0, 1), (1, 1)]).swept(&integer(2)), rat(8, 3));
        assert_eq!(
            jet(&[(1, 1), (1, 1), (1, 1), (1, 1)]).swept(&Rat::one()),
            rat(25, 12)
        );
        assert_eq!(
            jet(&[(2, 1), (-3, 1), (4, 1), (-5, 1), (6, 1)]).swept(&rat(1, 2)),
            rat(721, 960)
        );
        // A span that is not a grain and a coefficient family that is not integral.
        // ∫_0^{3/5} (7/2 - 4/3 t) dt = (7/2)(3/5) - (4/3)(9/50)  = 21/10 - 6/25 = 105/50 - 12/50.
        assert_eq!(jet(&[(7, 2), (-4, 3)]).swept(&rat(3, 5)), rat(93, 50));
    }

    // --- refusals -----------------------------------------------------------------------------

    #[test]
    fn unlawful_declarations_are_refused() {
        let (boundary, _) = linear_ramp();
        assert_eq!(
            integrate_by_leaders(&boundary, &law(Rat::zero(), RideDiscipline::GrainOnly, 1)),
            Err(LeaderError::GrainNotPositive)
        );
        assert_eq!(
            integrate_by_leaders(&boundary, &law(integer(-2), RideDiscipline::GrainOnly, 1)),
            Err(LeaderError::GrainNotPositive)
        );
        assert_eq!(
            integrate_by_leaders(&boundary, &law(Rat::one(), RideDiscipline::GrainOnly, 0)),
            Err(LeaderError::WitnessDepthZero)
        );
        assert_eq!(
            MaterialBoundary::new(Vec::new()),
            Err(LeaderError::EmptyMaterial)
        );
        assert_eq!(
            RationalGerm::new(Rat::zero(), jet(&[(1, 1)])),
            Err(LeaderError::GermExtentNotPositive)
        );
        assert_eq!(
            RationalGerm::new(integer(-1), jet(&[(1, 1)])),
            Err(LeaderError::GermExtentNotPositive)
        );
        assert_eq!(LocalJet::new(Vec::new()), Err(LeaderError::EmptyJet));
        assert_eq!(
            boundary.rescale_parameter(&Rat::zero()),
            Err(LeaderError::RescaleNotPositive)
        );
    }

    #[test]
    fn the_standing_read_is_local_and_bounded_by_the_region() {
        let (boundary, _) = unaligned_piecewise();
        assert_eq!(boundary.span(), &(rat(7, 3) + rat(4, 5) + rat(3, 2)));
        assert!(boundary.standing_at(&integer(-1)).is_none());
        assert!(boundary.standing_at(boundary.span()).is_none());
        assert!(
            boundary
                .standing_at(&(boundary.span() - rat(1, 1000)))
                .is_some()
        );

        let at_zero = boundary.standing_at(&Rat::zero()).unwrap();
        assert_eq!(at_zero.germ_index, 0);
        assert_eq!(at_zero.reach, rat(7, 3));
        assert_eq!(at_zero.jet, jet(&[(0, 1), (1, 1)]));

        // Inside the first germ the jet has moved: the material boundary is not what it was.
        let advanced = boundary.standing_at(&Rat::one()).unwrap();
        assert_eq!(advanced.germ_index, 0);
        assert_eq!(advanced.reach, rat(4, 3));
        assert_eq!(advanced.jet, jet(&[(1, 1), (1, 1)]));
        assert_ne!(advanced.jet, at_zero.jet);

        // Exactly on the second germ's founding.
        let second = boundary.standing_at(&rat(7, 3)).unwrap();
        assert_eq!(second.germ_index, 1);
        assert_eq!(second.jet, jet(&[(5, 2)]));
    }

    #[test]
    fn the_running_sum_is_the_lineage_and_closes_on_the_area() {
        let (boundary, expected) = unaligned_piecewise();
        let quadrature = run(&boundary, rat(1, 3), RideDiscipline::GermBounded);
        assert_eq!(quadrature.area, expected);
        assert_eq!(quadrature.jet_aperture, 2);

        let mut running = Rat::zero();
        let mut offset = Rat::zero();
        for extension in &quadrature.extensions {
            assert_eq!(extension.base_offset, offset, "the lineage has a gap");
            assert!(
                extension.span > Rat::zero(),
                "a null extension was deposited"
            );
            running = &running + &extension.winding;
            assert_eq!(
                extension.running_sum, running,
                "the running sum is not running"
            );
            offset = &offset + &extension.span;
        }
        assert_eq!(
            offset,
            *boundary.span(),
            "the lineage did not reach the far boundary"
        );
        assert_eq!(running, expected);
        assert_eq!(
            quadrature.extensions.last().unwrap().running_sum,
            quadrature.area
        );
    }
}
