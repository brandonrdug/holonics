//! **The local mixture: a family wins where it is closest** (THE_REBUILD F0, candidate 2; the record
//! of September 28, "A number is a helix, its base is a face, and a family wins where it is
//! closest", §5; #73, #62; Lean `Compression/Landmark/Context/Population.{ctxTotal_succ_same,
//! localFace_eq, local_telescope, local_mixture_code, local_of_constant}`).
//!
//! [definition; agent-inferred] **A family whose members are families.** The local mixture
//! ([`LocalMixture`]) forwards every cell to each member and keeps, for each **gating context** `c`
//! it has met, each member's weight there: its prior times its faces' product over the cells met
//! earlier in `c`. Its face at a cell mixes the members' faces under the posterior of the context
//! the receiver is in:
//!
//! ```text
//! w_f(c) = π_f ∏_(s < t, γ(s) = c) P_f(x_s | past),      π_f = 2^(−ℓ_f)/Σ_g 2^(−ℓ_g)
//! q_t(x) = Σ_f w_f(γ(t)) P_f(x | past) / Σ_f w_f(γ(t))
//! ```
//!
//! Each context's posterior is exact Bayes over its own cells (node-local Bayes); a member's face is
//! still read from its whole past, so only the weighing is local. A context not yet met holds the
//! prior. Every face is a normalized distribution given the past whenever the members' faces are.
//! Brandon's reading (the record, §5): dormancy is spatial as well as temporal, and a family dropped
//! for having no global share returns wherever it wins locally.
//!
//! [definition; agent-inferred] **The gating ladder.** A context at depth `d` is the last `d` cells,
//! `γ_d(t) = (x_(t−1), …, x_(t−d))`, a cell before the passage read as a declared pad: `d = 0` is
//! one global context (whole-passage Bayes), `d = 1` the previous cell, `d = 2` the previous two.
//! The mixture declares a ladder of rungs over the same members, and each rung keeps its own
//! posteriors on the same members' faces. The rung the receiver chose ([`LocalMixture::choose`])
//! makes the face; the others are comparison readings that enter no face, as the boundary egg's
//! comparison hazards. The members read every cell whatever the rung, so a rung's face at a cell is
//! the same whether it made the face throughout or was chosen at an earlier cell: a choice read from
//! past cells alone keeps the code prequential, and it is charged in the mixture's declared
//! description (`⌈log₂ |ladder|⌉` bits when the ladder is swept).
//!
//! [proved-derived; formal-checked] **The code within each context.** The faces telescope, context
//! by context, to the contexts' totals (Lean `local_telescope`), `∏_(t<n) q_t = ∏_(c met)
//! Σ_f π_f L_f(c)`, so for every choice of one family per context the mixture codes within
//!
//! ```text
//! −log₂ ∏_(t<n) q_t ≤ Σ_(c met) (−log₂ π_(f_c) − log₂ L_(f_c)(c))        (local_mixture_code)
//!                    = Σ_(c met) min_f code_f(c) + Σ_(c met) log₂ M      (M members, uniform prior)
//! ```
//!
//! and at `d = 0` it is the static mixture, `q_t = fwdMix_t` (`local_of_constant`), wherever the
//! executed chart's floor (below) does not bind. The bound over the members alive at the end is read
//! by [`LocalMixture::receipt`], from each context's per-member codes (`PassageCode` enclosures, the
//! population's machinery).
//!
//! [definition; agent-inferred] **The executed chart.** An exact weight grows by a face's bits at
//! every cell, so each weight is carried as the dormancy module's [`Weight`] (a 64-bit mantissa and a
//! binary exponent), multiplied by the member's exact face and rounded **down** (a factor in
//! `(1 − 2^(−62), 1]`). A member that falls more than [`FLOOR`] octaves below its context's leader
//! is held at `2^(−K)` of the leader: dormant in that context, never dead there, and the carried
//! integers stay within `K + 64` bits of one another. The executed face
//! `q̂_t = Σ_f ŵ_f P_f/Σ_f ŵ_f` is exact and normalized, and the family is scored by it (its
//! likelihood the product of its executed faces, enclosed by `PassageCode`).
//! [established-bounded] A rounding lowers only the weight it rounds, so `q̂_t ≥ Σ_f ŵ′_f/Σ_f ŵ_f`
//! where no floor binds; a floor raises the next total by at most `M·2^(−K)` of `Σ_f ŵ_f P_f`; and a
//! comparison family's weight loses at most a factor `1 − 2^(−62)` a cell. The executed code
//! therefore lies within the bound above plus the certified drift `3·r·2^(−62) + M·φ·2^(1−K)` bits,
//! `r` the cells at which a rung rounded and `φ` those at which a floor bound
//! ([`RungReceipt::drift`]; `−log₂(1 − x) < 3x` for `x ≤ ½`, `log₂(1 + y) < 2y`). Where neither
//! binds, the executed faces are the exact ones (`the_ladder_is_exact_bayes_in_each_context`).
//! `K = 64` was declared as the chart's width (two machine words hold the aligned weights) before
//! any passage was read, and it is never tuned on cells. Because the floor also carries a switching
//! law (below), `K` is a law parameter as well as a width; the declared switching law is the fixed
//! share on the hazard ladder ([`super::dormancy`]), and the floor has not been compared with it.
//!
//! [established-bounded; agent-inferred] **The floor is dormancy in time: a member returns at the
//! price `K + log₂ M`.** After every step each living member holds at least `2^(−K)` of its context's
//! leader, so at least `2^(−K)/M` of the context's total. For any path that reads member `f_0` on
//! a context's first ticks and member `f_i` on its `i`-th later segment of ticks, the telescope over
//! each segment gives
//!
//! ```text
//! code(c) ≤ −log₂ π_(f_0) + Σ_i code_(f_i)(segment i) + k (K + log₂ M) + drift,      k switches
//! ```
//!
//! (the segment from a switch starts at a share of at least `2^(−K)/M`; the test
//! `the_floor_keeps_a_dormant_member` checks it). The floor is therefore a switching law as well as
//! a chart: where a member that fell far behind wins for a while, the mixture follows it after about
//! `K + log₂ M` bits, whereas exact Bayes would need all the bits it fell behind. At `d = 0` the
//! executed mixture can code below its best single member, which no static mixture does
//! (`Σ_f π_f L_f ≤ max_f L_f`). [open] The segment telescope in Lean is owed (#62);
//! `local_mixture_code` states the static bound.
//!
//! [definition] **A member dies exactly at zero likelihood** (the population's law): a member whose
//! face gives the received cell zero is read no more, and it holds no weight in any context from
//! the next cell (its removal only raises the faces that follow). The bound is over the members
//! alive at the end. When every living member gives the cell zero, the mixture's face is zero and
//! the mixture dies.
//!
//! [definition; agent-inferred] **Standing** ([`LocalMixture::write_standing`]): the members'
//! standings, the chosen rung's weights at each context met, the gating address (the last cells the
//! ladder reads) and the likelihood. The comparison rungs and each context's per-member codes are
//! receipts, never read by the face, so they are not standing.
//!
//! [definition] The computational object is the helical pair interaction: at each context the
//! members (navigator families) meet the receiving face, and the context's posterior weighs that
//! meeting where it happens. Of the winding guide's six objects this owner touches **faces and
//! placement** (the mixed face on the cell alphabet, placed by its context), the **tube** (each
//! context's posterior moves only at its own ticks, a clock of its own, and a member dormant there
//! keeps its floor while the passage runs on) and the **tower thread** (the ladder's contexts
//! restrict: a `d = 2` context restricts to its `d = 1` suffix and to the one context at `d = 0`).
//! The helix, the pair's slip and the cell holonomy stay attached through the members' own owners.

use std::collections::{BTreeMap, VecDeque};
use std::io::{self, Write};

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, ToPrimitive, Zero};
use rayon::prelude::*;

use super::dormancy::Weight;
use super::{
    Act, Declaration, Family, KeyReadout, Likelihood, PopulationError, Readout, Relation, Work,
    refuse,
};
use crate::compression::landmark::context::{PassageCode, ratio_code_length};
use crate::ratio::Rat;
use crate::ratio::algebraic::{ExactInterval, interval_sum};

/// [definition; agent-inferred] **The floor's octaves** `K` (module header, "The executed chart"): a
/// member held at `2^(−K)` of its context's leader is dormant there.
pub const FLOOR: u32 = 64;

/// The standing's tag.
const MAGIC: &[u8; 8] = b"HLOC\0\0\0\x01";

// -------------------------------------------------------------------------------------------
// the executed chart

/// `2^(−ℓ)` on the chart, exactly.
fn kraft_weight(description: u64) -> Result<Weight, PopulationError> {
    i64::try_from(description)
        .ok()
        .and_then(|bits| (-63i64).checked_sub(bits))
        .map(|exponent| Weight {
            mantissa: 1 << 63,
            exponent,
        })
        .ok_or_else(|| refuse("a member's description", "it fits the chart's exponent"))
}

/// `v · 2^e` kept at 64 significant bits, rounded down; `true` when a set bit was dropped.
fn kept(value: BigUint, exponent: i64) -> (Weight, bool) {
    let bits = value.bits();
    if bits == 0 {
        return (Weight::ZERO, false);
    }
    if bits <= 64 {
        let shift = 64 - bits;
        let mantissa = value.to_u64().expect("at most 64 bits") << shift;
        return (
            Weight {
                mantissa,
                exponent: exponent - shift as i64,
            },
            false,
        );
    }
    let shift = bits - 64;
    let dropped = value.trailing_zeros().is_some_and(|zeros| zeros < shift);
    let mantissa = (&value >> shift as usize).to_u64().expect("64 bits kept");
    (
        Weight {
            mantissa,
            exponent: exponent + shift as i64,
        },
        dropped,
    )
}

/// **A weight times an exact face** `a/b > 0`, rounded down to the chart: the product exact when
/// `b` is a power of two, else the quotient taken to at least 128 bits first, so the factor lies in
/// `(1 − 2^(−62), 1]`; `true` when it rounded.
fn times(weight: Weight, face: &Rat) -> (Weight, bool) {
    let numerator = face.numer().magnitude();
    let denominator = face.denom().magnitude();
    let twos = denominator.trailing_zeros().unwrap_or(0);
    let odd = denominator >> twos as usize;
    let product = BigUint::from(weight.mantissa) * numerator;
    let exponent = weight.exponent - twos as i64;
    if odd.is_one() {
        return kept(product, exponent);
    }
    let shift = (128 + odd.bits()).saturating_sub(product.bits());
    let scaled = product << shift as usize;
    let (quotient, remainder) = (&scaled / &odd, &scaled % &odd);
    let (weight, dropped) = kept(quotient, exponent - shift as i64);
    (weight, dropped || !remainder.is_zero())
}

/// Whether `a < b` on the chart (mantissas normalized, zero the least).
fn below(a: Weight, b: Weight) -> bool {
    match (a.is_zero(), b.is_zero()) {
        (_, true) => false,
        (true, false) => true,
        _ => (a.exponent, a.mantissa) < (b.exponent, b.mantissa),
    }
}

/// **A context's executed face of one class**, `Σ_f ŵ_f P_f(x)/Σ_f ŵ_f` over the living members
/// (`None` a dead member), exact: the weights aligned to the least exponent, the faces over one
/// common denominator (their greatest power of two times their distinct odd parts), one reduction.
fn mixed(weights: &[Weight], faces: &[Option<&Rat>]) -> Rat {
    let live: Vec<(Weight, &Rat)> = weights
        .iter()
        .zip(faces)
        .filter_map(|(&weight, face)| face.map(|face| (weight, face)))
        .filter(|(weight, _)| !weight.is_zero())
        .collect();
    let Some(least) = live.iter().map(|(weight, _)| weight.exponent).min() else {
        return Rat::zero();
    };
    let split = |face: &Rat| {
        let denominator = face.denom().magnitude();
        let twos = denominator.trailing_zeros().unwrap_or(0);
        (twos, denominator >> twos as usize)
    };
    let mut greatest = 0u64;
    let mut odds: Vec<BigUint> = Vec::new();
    for (_, face) in &live {
        let (twos, odd) = split(face);
        greatest = greatest.max(twos);
        if !odd.is_one() && !odds.contains(&odd) {
            odds.push(odd);
        }
    }
    let common: BigUint = odds.iter().product();
    let mut numerator = BigUint::zero();
    let mut total = BigUint::zero();
    for (weight, face) in &live {
        let aligned = BigUint::from(weight.mantissa) << (weight.exponent - least) as usize;
        let (twos, odd) = split(face);
        numerator +=
            (&aligned * face.numer().magnitude() * (&common / &odd)) << (greatest - twos) as usize;
        total += aligned;
    }
    let denominator = (total * common) << greatest as usize;
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

// -------------------------------------------------------------------------------------------
// the ladder

/// One gating context: each member's executed weight (the standing), and the receipts (each
/// member's code over the context's cells, and the rung's code there).
#[derive(Clone)]
struct Context {
    weights: Vec<Weight>,
    codes: Vec<PassageCode>,
    mixture: PassageCode,
    cells: u64,
}

impl Context {
    fn opening(opening: &[Weight]) -> Self {
        Self {
            weights: opening.to_vec(),
            codes: vec![PassageCode::new(); opening.len()],
            mixture: PassageCode::new(),
            cells: 0,
        }
    }
}

/// One rung of the gating ladder: its depth, its contexts met, and its receipts.
#[derive(Clone)]
struct Rung {
    depth: usize,
    contexts: BTreeMap<u64, Context>,
    code: PassageCode,
    roundings: u64,
    floors: u64,
    received: Rat,
}

impl Rung {
    /// **One cell at this rung** (module header): the context's executed face of the cell read
    /// before its weights move, then its Bayes step on the chart and the floor.
    fn receive(
        &mut self,
        address: u64,
        opening: &[Weight],
        faces: &[Option<Rat>],
    ) -> Result<(), PopulationError> {
        let context = self
            .contexts
            .entry(address)
            .or_insert_with(|| Context::opening(opening));
        let refs: Vec<Option<&Rat>> = faces.iter().map(Option::as_ref).collect();
        let face = mixed(&context.weights, &refs);
        self.received = face.clone();
        if face.is_zero() {
            return Ok(());
        }
        context.mixture.face(&face)?;
        self.code.face(&face)?;
        let mut rounded = false;
        let mut leader = Weight::ZERO;
        for (member, member_face) in faces.iter().enumerate() {
            let Some(member_face) = member_face else {
                continue;
            };
            if member_face.is_zero() {
                context.weights[member] = Weight::ZERO;
                continue;
            }
            let (weight, dropped) = times(context.weights[member], member_face);
            context.weights[member] = weight;
            rounded |= dropped;
            context.codes[member].face(member_face)?;
            if below(leader, weight) {
                leader = weight;
            }
        }
        let floor = Weight {
            mantissa: leader.mantissa,
            exponent: leader.exponent - i64::from(FLOOR),
        };
        let mut floored = false;
        for (member, member_face) in faces.iter().enumerate() {
            if member_face.as_ref().is_some_and(Signed::is_positive)
                && below(context.weights[member], floor)
            {
                context.weights[member] = floor;
                floored = true;
            }
        }
        self.roundings += u64::from(rounded);
        self.floors += u64::from(floored);
        context.cells += 1;
        Ok(())
    }
}

/// **The gating address** at depth `d`: the last `d` cells, most recent first, each digit `x + 1`
/// in radix `|A| + 1`, a cell before the passage the pad `0`.
fn address(past: &VecDeque<usize>, depth: usize, alphabet: usize) -> u64 {
    let radix = alphabet as u64 + 1;
    (0..depth).fold(0u64, |key, back| {
        let digit = past
            .len()
            .checked_sub(back + 1)
            .map_or(0, |at| past[at] as u64 + 1);
        key * radix + digit
    })
}

/// [definition] **A rung's receipt** (module header): its depth, the contexts met, the cells read,
/// its code `−log₂ ∏ q̂_t` over every cell (enclosed), the declared bound
/// `Σ_(c met) min_f (code_f(c) − log₂ π_f)` over the members alive (enclosed), the certified drift
/// `3·r·2^(−62) + M·φ·2^(1−K)` bits, and the cells it rounded at (`r`) and a floor bound at (`φ`).
/// [established-bounded] `code ≤ bound + drift`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RungReceipt {
    pub depth: usize,
    pub contexts: usize,
    pub cells: u64,
    pub code: ExactInterval,
    pub bound: ExactInterval,
    pub drift: Rat,
    pub roundings: u64,
    pub floors: u64,
}

// -------------------------------------------------------------------------------------------
// the mixture

/// [definition; agent-inferred] **The local mixture** (module header): declared members, their
/// Kraft priors on the chart, a ladder of gating rungs of which one makes the face, the gating
/// address, and the members' deaths.
pub struct LocalMixture {
    members: Vec<Box<dyn Family>>,
    opening: Vec<Weight>,
    descriptions: Vec<u64>,
    kraft: Rat,
    alphabet: usize,
    description: u64,
    rungs: Vec<Rung>,
    chosen: usize,
    past: VecDeque<usize>,
    reach: usize,
    dead: Vec<Option<u64>>,
    faces: Vec<Option<Rat>>,
    passage: PassageCode,
    received: u64,
    weighed: u64,
}

impl LocalMixture {
    /// **Declare the mixture** over its members (one alphabet, descriptions whose Kraft sum is at
    /// most one), a ladder of distinct gating depths whose addresses fit 64 bits, the rung that
    /// makes the face, and the mixture's own description (its declaration's charge).
    pub fn new(
        members: Vec<Box<dyn Family>>,
        ladder: &[usize],
        chosen: usize,
        description: u64,
    ) -> Result<Self, PopulationError> {
        let Some(first) = members.first() else {
            return Err(refuse("a local mixture", "it declares at least one member"));
        };
        let alphabet = first.alphabet();
        if alphabet == 0 || members.iter().any(|member| member.alphabet() != alphabet) {
            return Err(refuse(
                "a local mixture",
                "its members read one declared cell alphabet",
            ));
        }
        let descriptions: Vec<u64> = members.iter().map(|member| member.description()).collect();
        let opening = descriptions
            .iter()
            .map(|&bits| kraft_weight(bits))
            .collect::<Result<Vec<_>, _>>()?;
        let kraft: Rat = descriptions
            .iter()
            .map(|&bits| {
                usize::try_from(bits)
                    .map(|bits| Rat::new(BigInt::one(), BigInt::one() << bits))
                    .map_err(|_| refuse("a member's description", "it fits the address space"))
            })
            .sum::<Result<Rat, _>>()?;
        if kraft > Rat::one() {
            return Err(refuse(
                "a local mixture's members",
                "their Kraft sum is at most one",
            ));
        }
        let radix = alphabet as u64 + 1;
        let mut distinct = ladder.to_vec();
        distinct.sort_unstable();
        distinct.dedup();
        if ladder.is_empty()
            || distinct.len() != ladder.len()
            || ladder.iter().any(|&depth| {
                u32::try_from(depth)
                    .ok()
                    .and_then(|depth| radix.checked_pow(depth))
                    .is_none()
            })
        {
            return Err(refuse(
                "a local mixture's gating ladder",
                "it declares distinct depths whose addresses fit 64 bits",
            ));
        }
        if chosen >= ladder.len() {
            return Err(refuse(
                "a local mixture's face",
                "it is made by a declared rung",
            ));
        }
        let rungs = ladder
            .iter()
            .map(|&depth| Rung {
                depth,
                contexts: BTreeMap::new(),
                code: PassageCode::new(),
                roundings: 0,
                floors: 0,
                received: Rat::zero(),
            })
            .collect();
        let count = members.len();
        Ok(Self {
            members,
            opening,
            descriptions,
            kraft,
            alphabet,
            description,
            rungs,
            chosen,
            past: VecDeque::new(),
            reach: ladder.iter().copied().max().unwrap_or(0),
            dead: vec![None; count],
            faces: vec![None; count],
            passage: PassageCode::new(),
            received: 0,
            weighed: 0,
        })
    }

    /// **The choosing role's choice** (module header, "The gating ladder"): the rung whose
    /// posterior makes the face from the next cell on. Its code on the cells already read is
    /// unchanged; the choice is read from them alone.
    pub fn choose(&mut self, rung: usize) -> Result<(), PopulationError> {
        if rung >= self.rungs.len() {
            return Err(refuse(
                "a local mixture's face",
                "it is made by a declared rung",
            ));
        }
        self.chosen = rung;
        Ok(())
    }

    /// The rung that makes the face.
    pub fn chosen(&self) -> usize {
        self.chosen
    }

    /// The ladder's depths, in declared order.
    pub fn ladder(&self) -> Vec<usize> {
        self.rungs.iter().map(|rung| rung.depth).collect()
    }

    /// The members, in declared order.
    pub fn members(&self) -> impl Iterator<Item = &dyn Family> {
        self.members.iter().map(|member| member.as_ref())
    }

    /// Member `f`.
    pub fn member(&self, member: usize) -> Option<&dyn Family> {
        self.members.get(member).map(|member| member.as_ref())
    }

    /// The cell member `f` died at, if it died.
    pub fn died(&self, member: usize) -> Option<u64> {
        self.dead.get(member).copied().flatten()
    }

    /// Each member's face of the last received cell (none for a member already dead).
    pub fn member_faces(&self) -> &[Option<Rat>] {
        &self.faces
    }

    /// Rung `r`'s executed face of the last received cell (the face it made, or would have made).
    pub fn rung_face(&self, rung: usize) -> Option<&Rat> {
        self.rungs.get(rung).map(|rung| &rung.received)
    }

    /// The cells received.
    pub fn cells(&self) -> u64 {
        self.received
    }

    /// The context's weights where rung `r` stands now (the prior at a context not yet met).
    fn weights<'a>(&'a self, rung: &'a Rung) -> &'a [Weight] {
        let at = address(&self.past, rung.depth, self.alphabet);
        rung.contexts
            .get(&at)
            .map_or(&self.opening[..], |context| &context.weights[..])
    }

    /// **Rung `r`'s face** on the alphabet before the next cell, exact.
    pub fn face_of(&self, rung: usize) -> Result<Vec<Rat>, PopulationError> {
        let Some(rung) = self.rungs.get(rung) else {
            return Err(refuse("a local mixture's rung", "it is declared"));
        };
        let faces = self
            .members
            .iter()
            .zip(&self.dead)
            .map(|(member, dead)| match dead {
                Some(_) => Ok(None),
                None => member.face().map(Some),
            })
            .collect::<Result<Vec<Option<Vec<Rat>>>, PopulationError>>()?;
        let weights = self.weights(rung);
        Ok((0..self.alphabet)
            .map(|class| {
                let refs: Vec<Option<&Rat>> = faces
                    .iter()
                    .map(|face| face.as_ref().map(|face| &face[class]))
                    .collect();
                mixed(weights, &refs)
            })
            .collect())
    }

    /// `−log₂ π_f = ℓ_f + log₂ Σ_g 2^(−ℓ_g)`, enclosed.
    fn prior_code(&self, member: usize) -> Result<ExactInterval, PopulationError> {
        let mass = ratio_code_length(
            self.kraft.numer().magnitude(),
            self.kraft.denom().magnitude(),
        )?;
        let bits = Rat::from_integer(BigInt::from(self.descriptions[member]));
        Ok(ExactInterval::new(
            &bits - &mass.upper,
            &bits - &mass.lower,
        )?)
    }

    /// **Rung `r`'s receipt** (module header): its code, the declared bound over the contexts met and
    /// the members alive, and the certified drift.
    pub fn receipt(&self, rung: usize) -> Result<RungReceipt, PopulationError> {
        let Some(read) = self.rungs.get(rung) else {
            return Err(refuse("a local mixture's rung", "it is declared"));
        };
        let alive: Vec<usize> = (0..self.members.len())
            .filter(|&member| self.dead[member].is_none())
            .collect();
        let priors = alive
            .iter()
            .map(|&member| self.prior_code(member))
            .collect::<Result<Vec<_>, _>>()?;
        let contexts: Vec<&Context> = read.contexts.values().collect();
        let least = contexts
            .par_iter()
            .map(|context| {
                let mut least: Option<ExactInterval> = None;
                for (index, &member) in alive.iter().enumerate() {
                    let code = interval_sum(&context.codes[member].bits()?, &priors[index])?;
                    least = Some(match least {
                        None => code,
                        Some(held) => ExactInterval::new(
                            held.lower.min(code.lower),
                            held.upper.min(code.upper),
                        )?,
                    });
                }
                least.ok_or_else(|| refuse("a local mixture's bound", "a member is alive"))
            })
            .collect::<Result<Vec<_>, PopulationError>>()?;
        let mut bound = ExactInterval::point(Rat::zero());
        for code in &least {
            bound = interval_sum(&bound, code)?;
        }
        Ok(RungReceipt {
            depth: read.depth,
            contexts: read.contexts.len(),
            cells: read.contexts.values().map(|context| context.cells).sum(),
            code: read.code.bits()?,
            bound,
            drift: self.drift_of(read),
            roundings: read.roundings,
            floors: read.floors,
        })
    }

    /// A rung's certified drift, `3·r·2^(−62) + M·φ·2^(1−K)` bits (module header).
    fn drift_of(&self, rung: &Rung) -> Rat {
        Rat::new(
            BigInt::from(3u32) * BigInt::from(rung.roundings),
            BigInt::one() << 62usize,
        ) + Rat::new(
            BigInt::from(self.members.len()) * BigInt::from(rung.floors),
            BigInt::one() << (FLOOR - 1) as usize,
        )
    }

    /// **The standing, streamed** (module header, "Standing"): the tag, the alphabet, the members'
    /// count, the cells read, the chosen rung's depth and the floor; each member's death and its own
    /// native checkpoint (a tree's or the admitted receivers'), length-prefixed; the gating address;
    /// the likelihood's bounds; and the chosen rung's weights at each context met, in address order.
    /// Returns the bytes of the members' own checkpoints within it. Refused for a member without a
    /// native checkpoint codec.
    pub fn write_standing<W: Write>(&self, output: &mut W) -> io::Result<u64> {
        let word = |output: &mut W, value: u64| output.write_all(&value.to_le_bytes());
        output.write_all(MAGIC)?;
        word(output, self.alphabet as u64)?;
        word(output, self.members.len() as u64)?;
        word(output, self.received)?;
        word(output, self.rungs[self.chosen].depth as u64)?;
        word(output, u64::from(FLOOR))?;
        let mut members = 0u64;
        for (member, dead) in self.members.iter().zip(&self.dead) {
            word(output, dead.map_or(0, |cell| cell + 1))?;
            let (tag, bytes) = match member.tree_checkpoint() {
                Some(bytes) => (1u8, bytes),
                None => match member.admitted_checkpoint() {
                    Some(bytes) => (2u8, bytes.map_err(io::Error::other)?),
                    None => {
                        return Err(io::Error::other(
                            "a local mixture's member has no native standing codec",
                        ));
                    }
                },
            };
            output.write_all(&[tag])?;
            word(output, bytes.len() as u64)?;
            output.write_all(&bytes)?;
            members += bytes.len() as u64;
        }
        let depth = self.rungs[self.chosen].depth;
        let address: Vec<usize> = self.past.iter().rev().take(depth).copied().collect();
        word(output, address.len() as u64)?;
        for cell in address {
            word(output, cell as u64)?;
        }
        let (numerator, denominator, exponent) = self.passage.bounds();
        for bound in numerator.iter().chain(&denominator) {
            output.write_all(&bound.mantissa.to_le_bytes())?;
            word(output, bound.exponent)?;
        }
        word(output, exponent)?;
        word(output, self.passage.factors())?;
        let rung = &self.rungs[self.chosen];
        word(output, rung.contexts.len() as u64)?;
        for (&key, context) in &rung.contexts {
            word(output, key)?;
            for weight in &context.weights {
                word(output, weight.mantissa)?;
                output.write_all(&weight.exponent.to_le_bytes())?;
            }
        }
        Ok(members)
    }
}

impl Family for LocalMixture {
    fn branch_future(&self) -> Option<Box<dyn Family>> {
        let members = self
            .members
            .iter()
            .map(|member| member.branch_future())
            .collect::<Option<Vec<_>>>()?;
        Some(Box::new(LocalMixture {
            members,
            opening: self.opening.clone(),
            descriptions: self.descriptions.clone(),
            kraft: self.kraft.clone(),
            alphabet: self.alphabet,
            description: self.description,
            rungs: self.rungs.clone(),
            chosen: self.chosen,
            past: self.past.clone(),
            reach: self.reach,
            dead: self.dead.clone(),
            faces: self.faces.clone(),
            passage: self.passage,
            received: self.received,
            weighed: self.weighed,
        }))
    }

    fn label(&self) -> String {
        format!(
            "local mixture over {} members, gating depth {} of the ladder {:?}",
            self.members.len(),
            self.rungs[self.chosen].depth,
            self.ladder()
        )
    }

    fn alphabet(&self) -> usize {
        self.alphabet
    }

    fn description(&self) -> u64 {
        self.description
    }

    fn face(&self) -> Result<Vec<Rat>, PopulationError> {
        self.face_of(self.chosen)
    }

    /// Every living member reads the cell on the host's cores, each writing only its own state (the
    /// hardware law); then each rung, writing only its own contexts, reads its face and steps; the
    /// chosen rung's face is returned.
    fn receive(&mut self, cell: usize) -> Result<Rat, PopulationError> {
        if cell >= self.alphabet {
            return Err(PopulationError::CellOutside {
                cell,
                alphabet: self.alphabet,
            });
        }
        if self.dead.iter().all(Option::is_some) {
            return Err(PopulationError::Extinct {
                cell: self.received as usize,
            });
        }
        let faces: Vec<Option<Rat>> = self
            .members
            .par_iter_mut()
            .zip(self.dead.par_iter())
            .map(|(member, dead)| {
                if dead.is_some() {
                    return Ok(None);
                }
                let face = member.receive(cell)?;
                if face.is_negative() || face > Rat::one() {
                    return Err(refuse(
                        "a member's face of a cell",
                        "it lies in the unit interval",
                    ));
                }
                Ok(Some(face))
            })
            .collect::<Result<_, PopulationError>>()?;
        let addresses: Vec<u64> = self
            .rungs
            .iter()
            .map(|rung| address(&self.past, rung.depth, self.alphabet))
            .collect();
        let opening = &self.opening;
        self.rungs
            .par_iter_mut()
            .zip(addresses.par_iter())
            .try_for_each(|(rung, &at)| rung.receive(at, opening, &faces))?;
        let living = faces.iter().flatten().count() as u64;
        self.weighed += living * self.rungs.len() as u64;
        for (member, face) in faces.iter().enumerate() {
            if face.as_ref().is_some_and(Zero::is_zero) {
                self.dead[member] = Some(self.received);
            }
        }
        let face = self.rungs[self.chosen].received.clone();
        if face.is_positive() {
            self.passage.face(&face)?;
        }
        if self.reach > 0 {
            self.past.push_back(cell);
            if self.past.len() > self.reach {
                self.past.pop_front();
            }
        }
        self.received += 1;
        self.faces = faces;
        Ok(face)
    }

    fn admits(&self, cells: &[usize]) -> Result<(), PopulationError> {
        if let Some(&cell) = cells.iter().find(|&&cell| cell >= self.alphabet) {
            return Err(PopulationError::CellOutside {
                cell,
                alphabet: self.alphabet,
            });
        }
        for (member, dead) in self.members.iter().zip(&self.dead) {
            if dead.is_none() {
                member.admits(cells)?;
            }
        }
        Ok(())
    }

    fn owns_planned_relation(&self) -> bool {
        self.members
            .iter()
            .zip(&self.dead)
            .any(|(member, dead)| dead.is_none() && member.owns_planned_relation())
    }

    fn validate_planned_relation(&self, relation: Relation) -> Result<(), PopulationError> {
        for (member, dead) in self.members.iter().zip(&self.dead) {
            if dead.is_none() {
                member.validate_planned_relation(relation)?;
            }
        }
        Ok(())
    }

    fn commit_planned_relation(&mut self, relation: Relation) {
        for (member, dead) in self.members.iter_mut().zip(&self.dead) {
            if dead.is_none() {
                member.commit_planned_relation(relation);
            }
        }
    }

    fn likelihood(&self) -> Likelihood {
        Likelihood::Enclosed(self.passage)
    }

    /// The mixture locates no key; its members' readouts are read through
    /// [`LocalMixture::member`].
    fn readout(&self) -> Readout<'_> {
        Readout::Keys(KeyReadout {
            spaces: Vec::new(),
            survivors: Vec::new(),
            masses: Vec::new(),
            dormant: Vec::new(),
        })
    }

    /// Every rung's certified drift: a bound on the chosen rung's over any cells it made the face.
    fn drift(&self) -> Rat {
        self.rungs.iter().map(|rung| self.drift_of(rung)).sum()
    }

    /// The ladder's depths and the floor, built on the members' declarations.
    fn declaration(&self) -> Declaration {
        let mut parameters = vec![u64::from(FLOOR)];
        parameters.extend(self.rungs.iter().map(|rung| rung.depth as u64));
        Declaration::new("local mixture", parameters).with(
            self.members
                .iter()
                .map(|member| member.declaration())
                .collect(),
        )
    }

    /// The members' work, and each member's weight moved at each rung.
    fn work(&self) -> Work {
        let mut work = Work::default();
        for member in &self.members {
            work.absorb(&member.work());
        }
        work.add(Act::Weigh, self.weighed);
        work
    }
}
