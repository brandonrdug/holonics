//! **The contact's own readings: its transfer and site kind, its boost, its lock address and its
//! break** (campaign 2, Lean `HNN/Contact`, `HNN/ContactBreak`).
//!
//! [definition] A contact slips, dissipates and addresses. Its transit (`hnn::propagation`, the
//! owner of the executed two-port) is read here through what it says about the contact itself:
//!
//! ```text
//! transfer   m = 2c + p + h d + (h²/2) k ,   T = (1/m) [[m − h²k, 2hc], [−2hk, 4c − m]]
//!            tr T = (4c − h²k)/m ,   det T = (2c + h²k/2 − p − hd)/m       p = 2h/G, or 0 closed
//! kind       closed, lossless, c > 0, 4c + h²k ≠ 0:  k > 0 rotation, k = 0 null shear, k < 0 boost;
//!            the chart's hypothesis checked on every mode (2C + (h²/2)K nonsingular), else refused
//! boost      K = b diag(σ) bᵀ, σ ∈ {±1}; admitted only where M_a = 2C + (2h/G)I + hD + (h²/2)K is
//!            nonsingular, a refusal carrying its singular direction
//! lock       whole windings (m_g, m_h) over a passage: the least-denominator rate p/q in their fibre
//!            (m_g/(m_h + 1), (m_g + 1)/m_h), p ≤ m_g, q ≤ m_h; Locked within (P, Q) = the horizon,
//!            else Unlocked
//! break      R = E_a + W_a − D_a − E_a′ ,   an advance is admitted when R ≥ J = γ·(parted extent)
//! ```
//!
//! [proved-derived; implemented-exact] **The site kind.** On a contact of `k_a` directions the closed
//! lossless transit keeps the plane of every generalized mode `K v = μ C v` and acts there as the
//! scalar transfer at `(c, k) = (1, μ)` (Lean `HNN/Contact.contact_mode_transfer`), whose kind is
//! the sign of `μ` (`contact_transfer_kind_by_storage_sign`). With `C ≻ 0` the signs of the `μ` are
//! the inertia of `K` (Sylvester's law, [`crate::ratio::linear::inertia`], [proved-standard]), so the
//! contact's **kind census** is `(n₊(K), n₀(K), n₋(K))` rotations, null shears and boosts, and its
//! **kind** is its least stable mode's: a boost if any, else a null shear if any, else a rotation
//! ([`site_reading`]). The sign rule's Cayley-chart hypothesis `2 + (h²/2)μ ≠ 0` is checked at every
//! mode, as the nonsingularity of `2C + (h²/2)K`, and a contact where it fails is refused, not read.
//! Without a declared stiffness signature `K = b bᵀ ⪰ 0`, so no deposit can make a boost: the kinds
//! are rotations and null shears. A contact whose storage is not definite on its channel reads
//! [`SiteKind::Degenerate`]: the sign rule's hypothesis `c > 0` fails there (a massless direction's
//! transfer is the half-turn shear, `tr = −2`, and a direction with neither storage nor stiffness has
//! no Cayley chart). A port-loaded or damped transfer is classified by its own trace and
//! determinant ([`Transfer::site`]).
//!
//! [proved-derived; implemented-exact] **The boost** ([`certify_boost`]). A stiffness factor carries
//! its declared signature `σ` (`ConstitutionRead::contact_stiffness_signature`, campaign 1: none, so
//! `K = b bᵀ ⪰ 0` and `m_a ⪰ 1`). A negative column makes `K` indefinite, and `tick_well_defined`'s
//! `K ⪰ 0` no longer certifies the solve: the solve is certified at a cut's conductance by the exact
//! operator itself, and refused with its singular direction (Lean
//! `contact_boost_solve_or_singular_direction`); the signed form `2C + hD + (h²/2)K ⪰ 0` certifies it
//! at every conductance at once. Its storage balance is still exact
//! (`contact_signed_storage_balance`); passivity does not follow
//! (`boost_grows_at_conserved_signed_storage`), and the word releases the expanding change with its
//! other unread change at its end.
//!
//! [proved-derived; implemented-exact] **The lock address** ([`lock_address`], Lean
//! `HNN/Contact.contact_lock_address`). A contact `a = (g → h)` reads its two rings' whole windings
//! over a passage, the difference of their lift points' windings (the signed count is the flux, Lean
//! `Aeon/Clock/Epoch.signed_count_is_flux`). The rings' phases are the unresolved part at the
//! winding grain, so the rates consistent with the reading are the open fibre
//! `(m_g/(m_h + 1), (m_g + 1)/m_h)`, which holds the measured ratio `m_g/m_h`. The lock address is
//! the fibre's least-denominator rate, the least of that denominator (Lean `IsLockAddress`; the owner
//! [`simplest_between`], its Stern–Brocot descent). It exists and is unique
//! (`lockAddress_exists`, `lockAddress_unique`; past the integers the denominator alone fixes it,
//! `least_denominator_unique`), it closes at its period `q` (`lockAddress_closes`: the cycles are the
//! multiples of `q`), and it lies in the box `1 ≤ p ≤ m_g`, `1 ≤ q ≤ m_h`. It is **Locked** `(p, q)`
//! within the declared bounds and **Unlocked** otherwise, or when either ring has not wound.
//!
//! [definition; agent-inferred] **The bounds are the horizon** ([`LockDeclaration::derived`]). The
//! carry chain's horizon is `B_r = ∏_(j>r) d_j` windings of ring `r` an aeon of the joint clock (`1`
//! for the last ring): each winding of ring `r + 1` takes `d_(r+1)` steps, its predecessor's carries
//! (campaign 1's readout: ring 2 winds `13 = d_3` times and ring 3 once, every aeon). The reader reads
//! the letter of the aeon's closing tick before the carry-out restarts the windings
//! (`hnn::receiving::LetterReader::tick`), so the windings it reads reach `B_r`. The bound is the true
//! horizon, `Q = B_h` and `P = B_g` (Lean `lock_partition_finite`, `Q = H`): the greatest denominator
//! whose first return (`q` turns of ring `h`) is observable within the aeon, and by the box every
//! address of windings within the horizon lands in the family. A count past it (a ring above stepping
//! by its own lock as well as by carries) reads **Unlocked**, a lawful letter.
//!
//! [definition; agent-inferred] **The lock letters** (the receiving join's contact letter,
//! `hnn::receiving::Feature::Contact`). The addresses a contact can read form the finite family
//! `{Unlocked} ∪ {(p, q) reduced : 1 ≤ p ≤ P, 1 ≤ q ≤ Q}` (Lean
//! `Compression/Landmark/Context/Address.lock_partition_finite`, whose horizon clause is the address's period,
//! `lockAddress_closes`): a box, not the Farey family `F_Q` of `[0, 1]`, since the
//! contact `g → h` reads its rate in its declared orientation, which lies above one where ring `g`
//! winds faster (campaign 1's `0 → 1` and `1 → 2`). Its letter is `0` unlocked and `1 +` the rank
//! ordered by `(q, p)` ([`ContactLock::code`]), and a contact's reading is that letter times its
//! site kind's ([`ContactReading::letter`], `5` kinds). The rank is one to one onto the family's
//! letters ([`LockDeclaration::letters`]); the tests check it, Lean states the family.
//!
//! [definition] **The break** ([`BreakReceipt`], Lean `HNN/ContactBreak`). The contact's parting of
//! `j` matched nodes at the declared surface-storage density `γ` (`ConstitutionRead::
//! contact_surface_storage`, #31) takes the gluing work `J = γ j`; the released storage is
//! `R = E_a + W_a − D_a − E_a′` with `E_a′` the post-transit storage the parted constitution still
//! holds, and the receipt is `R − J`. Under the exact law `R` is the storage the parting removes
//! (`break_release_balance`); on the lattices it carries the transit's defects. A parted contact's
//! shared face returns its typed gluing defect ([`crate::hnn::Field::parted_holarchy`],
//! `parting_returns_gluing_defect`).
//!
//! | Lean | Rust |
//! |---|---|
//! | `HNN/Contact.{transferDen, transfer, transfer_solves, transfer_trace_det}` | [`transfer`], [`Transfer`] |
//! | `HNN/Contact.contact_transfer_kind_by_storage_sign`, `contact_mode_transfer` | [`Transfer::site`], [`site_reading`], [`site_reading_of_factors`] |
//! | `HNN/Contact.contact_boost_solve_or_singular_direction` | [`certify_boost`], [`signed_form_certifies`] |
//! | `HNN/Contact.contact_signed_storage_balance`, `boost_grows_at_conserved_signed_storage` | tests (the transit's balance at an indefinite `K`) |
//! | `HNN/Contact.{IsLockAddress, lockAddress_exists, lockAddress_unique, exists_smaller_den_between, least_denominator_unique, lockAddress_closes, contact_lock_address}` | [`lock_address`] (through [`simplest_between`]), [`ContactLock`] |
//! | `Compression/Landmark/Context/Address.lock_partition_finite` (`Q = H`, the horizon) | [`LockDeclaration::derived`] |
//! | `Compression/Landmark/Context/Address.lock_partition_finite` (the finite family the address lands in) | [`LockDeclaration::letters`], [`ContactLock::code`], [`ContactReading::letter`] |
//! | `HNN/ContactBreak.{break_release_balance, break_iff_release_covers_gluing, griffith_closed_port_case}` | [`BreakReceipt`] |
//! | `HNN/ContactBreak.parting_returns_gluing_defect` | [`crate::hnn::Field::parted_holarchy`] |

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, ToPrimitive, Zero};

use crate::hnn::HnnError;
use crate::hnn::field::{ConstitutionRead, Current, Field};
use crate::hnn::propagation::{ContactOperands, Transit, gram};
use crate::holon::element::contact_operator;
use crate::navigator::address::simplest_between;
use crate::navigator::trace::{SiteFactor, SiteKind};
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::inertia::{SymmetricForm, inertia};
use crate::ratio::linear::vector::dot;
use crate::ratio::{Rat, integer};

// -------------------------------------------------------------------------------------------
// the transfer

/// [definition] **The contact's scalar transfer** on `(u, w)` (Lean `HNN/Contact.transfer`):
/// its matrix and its denominator `m = 2c + p + hd + (h²/2)k`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Transfer {
    pub matrix: [[Rat; 2]; 2],
    pub denominator: Rat,
}

/// **The scalar transfer** at storage `c`, stiffness `k`, dissipation `d`, port term `p` (`2h/G`,
/// or `0` closed) and hop `h`. Refused when `m = 0`: no Cayley chart.
pub fn transfer(c: &Rat, k: &Rat, d: &Rat, p: &Rat, h: &Rat) -> Result<Transfer, HnnError> {
    let m = integer(2) * c + p + h * d + h * h / integer(2) * k;
    if m.is_zero() {
        return Err(HnnError::SingularTransfer);
    }
    let hh = h * h;
    let matrix = [
        [(&m - &hh * k) / &m, integer(2) * h * c / &m],
        [-(integer(2) * h * k) / &m, (integer(4) * c - &m) / &m],
    ];
    Ok(Transfer {
        matrix,
        denominator: m,
    })
}

impl Transfer {
    /// `T (u, w)`.
    pub fn apply(&self, state: [&Rat; 2]) -> [Rat; 2] {
        [
            &self.matrix[0][0] * state[0] + &self.matrix[0][1] * state[1],
            &self.matrix[1][0] * state[0] + &self.matrix[1][1] * state[1],
        ]
    }

    /// **Its two faces** `(tr T, det T)`: the site a damped or port-loaded transfer is classified
    /// by (Lean `transfer_trace_det`).
    pub fn site(&self) -> SiteFactor {
        let [[a, b], [c, d]] = &self.matrix;
        SiteFactor::new(a + d, a * d - b * c)
    }
}

// -------------------------------------------------------------------------------------------
// the site reading

/// [definition] **The contact's kind census**: its closed lossless transfer's generalized modes by
/// kind (module header).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct KindCensus {
    pub rotation: usize,
    pub null: usize,
    pub boost: usize,
}

/// [definition] **The contact's site reading**: its kind census and its kind, the least stable
/// mode's ([`SiteKind::Degenerate`] where its storage is not definite on its channel).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SiteReading {
    pub census: KindCensus,
    pub kind: SiteKind,
}

/// A symmetric form read from an exact matrix; an asymmetric one is refused by the inertia owner.
pub(crate) fn symmetric(form: &ExactRatMatrix) -> Result<SymmetricForm, HnnError> {
    SymmetricForm::from_rows(form.to_rows())
        .map_err(|refusal| HnnError::from(crate::holon::contact::ContactError::from(refusal)))
}

/// **The contact's site reading** from its storage `C_a` and signed stiffness `K_a` at the hop `h`
/// (module header): with `C_a ≻ 0` the census is the inertia of `K_a`, and the kind a boost if any
/// mode is, else a null shear if any is, else a rotation. The sign rule's Cayley-chart hypothesis
/// (Lean `contact_transfer_kind_by_storage_sign`, `transferDen(1, μ, 0, 0, h) = 2 + (h²/2)μ ≠ 0` at
/// every generalized mode `K v = μ C v`) is checked: with `C ≻ 0` it holds exactly when the closed
/// denominator `2C + (h²/2)K` is nonsingular (it sends a mode `v` to `(2 + (h²/2)μ) C v`), and a
/// contact where it fails is refused ([`HnnError::SingularTransfer`]): no kind is read there.
pub fn site_reading(
    storage: &ExactRatMatrix,
    stiffness: &ExactRatMatrix,
    step: &Rat,
) -> Result<SiteReading, HnnError> {
    if storage.rows() == 0 || !inertia(&symmetric(storage)?).is_positive_definite() {
        return Ok(SiteReading {
            census: KindCensus::default(),
            kind: SiteKind::Degenerate,
        });
    }
    let signs = inertia(&symmetric(stiffness)?);
    if signs.negative > 0 {
        // Only an indefinite stiffness can meet `2 + (h²/2)μ = 0` (`μ = −4/h²`); `K ⪰ 0` never does.
        let closed = storage
            .scaled(&integer(2))
            .add(&stiffness.scaled(&(step * step / integer(2))))?;
        if inertia(&symmetric(&closed)?).zero > 0 {
            return Err(HnnError::SingularTransfer);
        }
    }
    let census = KindCensus {
        rotation: signs.positive,
        null: signs.zero,
        boost: signs.negative,
    };
    let kind = if census.boost > 0 {
        SiteKind::Boost
    } else if census.null > 0 {
        SiteKind::Null
    } else {
        SiteKind::Rotation
    };
    Ok(SiteReading { census, kind })
}

/// The Mersenne prime `2^61 − 1`, the chart the census's rank certificate reads in.
const CENSUS_PRIME: u64 = (1 << 61) - 1;

/// **A factor's full row rank, certified in one prime chart** ([proved-standard]): `f` (`k × m`)
/// has rank `k` over ℚ when its rows, each cleared of its denominators by a nonzero integer scale,
/// have rank `k` modulo `p = 2^61 − 1`: a nonzero `k × k` minor modulo `p` is a nonzero integer
/// minor. `false` says only that this chart did not certify it (the rank is deficient, or `p`
/// divides every maximal minor), and the caller reads the exact inertia instead.
fn full_row_rank_certified(factor: &ExactRatMatrix) -> bool {
    let (k, m) = (factor.rows(), factor.columns());
    if k > m {
        return false;
    }
    let prime = BigInt::from(CENSUS_PRIME);
    let mut rows: Vec<Vec<u64>> = Vec::with_capacity(k);
    for i in 0..k {
        let Ok(row) = factor.row(i) else {
            return false;
        };
        let scale = row.iter().fold(BigInt::one(), |scale, x| {
            let common = crate::ratio::gcd(&scale, x.denom());
            &scale / common * x.denom()
        });
        rows.push(
            row.iter()
                .map(|x| {
                    let cleared = (x.numer() * (&scale / x.denom())) % &prime;
                    let reduced = if cleared.is_negative() {
                        cleared + &prime
                    } else {
                        cleared
                    };
                    reduced.to_u64().expect("a residue below the prime")
                })
                .collect(),
        );
    }
    let mul = |a: u64, b: u64| ((u128::from(a) * u128::from(b)) % u128::from(CENSUS_PRIME)) as u64;
    let inverse = |a: u64| {
        // a^(p − 2) by squaring: Fermat's little theorem in the prime chart.
        let (mut base, mut exponent, mut result) = (a, CENSUS_PRIME - 2, 1u64);
        while exponent > 0 {
            if exponent & 1 == 1 {
                result = mul(result, base);
            }
            base = mul(base, base);
            exponent >>= 1;
        }
        result
    };
    let mut column = 0;
    for pivot_row in 0..k {
        let pivot = loop {
            if column == m {
                return false;
            }
            match (pivot_row..k).find(|&r| rows[r][column] != 0) {
                Some(r) => break r,
                None => column += 1,
            }
        };
        rows.swap(pivot_row, pivot);
        let unit = inverse(rows[pivot_row][column]);
        let (upper, lower) = rows.split_at_mut(pivot_row + 1);
        let pivot_words = &upper[pivot_row];
        for row in lower.iter_mut() {
            let factor = mul(row[column], unit);
            if factor != 0 {
                for (entry, &word) in row[column..].iter_mut().zip(&pivot_words[column..]) {
                    let product = mul(factor, word);
                    *entry = (*entry + CENSUS_PRIME - product) % CENSUS_PRIME;
                }
            }
        }
        column += 1;
    }
    true
}

/// **The contact's site reading from its factors** (the census's reading at every commit): with no
/// declared stiffness signature, `C = c cᵀ ≻ 0` exactly when `c` has full row rank and
/// `K = b bᵀ ≻ 0` exactly when `b` does, and then every generalized mode is a rotation: the census
/// is `(k, 0, 0)` and the kind a rotation, the reading [`site_reading`] returns, certified in one
/// prime chart ([`full_row_rank_certified`]) without the exact inertia of the Gram matrices. Any
/// other case (a signature, or a rank the chart does not certify) is read exactly by
/// [`site_reading`].
pub fn site_reading_of_factors(
    storage: &ExactRatMatrix,
    stiffness: &ExactRatMatrix,
    signature: Option<&[bool]>,
    step: &Rat,
) -> Result<SiteReading, HnnError> {
    let signed = signature.is_some_and(|signs| signs.iter().any(|positive| !positive));
    if !signed
        && storage.rows() > 0
        && storage.rows() == stiffness.rows()
        && full_row_rank_certified(storage)
        && full_row_rank_certified(stiffness)
    {
        return Ok(SiteReading {
            census: KindCensus {
                rotation: stiffness.rows(),
                null: 0,
                boost: 0,
            },
            kind: SiteKind::Rotation,
        });
    }
    site_reading(
        &gram(storage)?,
        &signed_stiffness(stiffness, signature)?,
        step,
    )
}

// -------------------------------------------------------------------------------------------
// the boost

/// **The signed stiffness** `K = b diag(σ) bᵀ` of a factor `b` and its declared signature (`None`:
/// every column positive, `K = b bᵀ`).
pub fn signed_stiffness(
    factor: &ExactRatMatrix,
    signature: Option<&[bool]>,
) -> Result<ExactRatMatrix, HnnError> {
    let Some(signature) = signature.filter(|signs| signs.iter().any(|positive| !positive)) else {
        return gram(factor);
    };
    if signature.len() != factor.columns() {
        return Err(HnnError::Shape {
            what: "a stiffness signature (one sign per factor column)",
            expected: factor.columns(),
            found: signature.len(),
        });
    }
    let signed = ExactRatMatrix::shaped(
        factor.rows(),
        factor.columns(),
        (0..factor.rows())
            .map(|i| {
                (0..factor.columns())
                    .map(|j| {
                        let entry = factor.get(i, j).expect("in range").clone();
                        if signature[j] { entry } else { -entry }
                    })
                    .collect()
            })
            .collect(),
    )?;
    Ok(signed.multiply(&factor.transpose()?)?)
}

/// **The signed form certifies the solve at every conductance** (Lean
/// `contact_boost_solve_or_singular_direction`, part 2): `2C + hD + (h²/2)K ⪰ 0` gives
/// `⟨v, M_a v⟩ ≥ (2h/G)|v|²` for every `G > 0`.
pub fn signed_form_certifies(
    storage: &ExactRatMatrix,
    stiffness: &ExactRatMatrix,
    dissipation: &ExactRatMatrix,
    step: &Rat,
) -> Result<bool, HnnError> {
    let form = storage
        .scaled(&integer(2))
        .add(&dissipation.scaled(step))?
        .add(&stiffness.scaled(&(step * step / integer(2))))?;
    Ok(inertia(&symmetric(&form)?).negative == 0)
}

/// **A boost's solve, certified or refused with its singular direction** (Lean
/// `contact_boost_solve_or_singular_direction`, part 1): the contact's normalized operator
/// `m_a = (G/2h) M_a` at the cut's conductance is nonsingular, or its kernel's first basis vector is
/// returned in the refusal.
pub fn certify_boost(
    contact: usize,
    forms: [&ExactRatMatrix; 3],
    conductance: &Rat,
    step: &Rat,
) -> Result<(), HnnError> {
    let [storage, stiffness, dissipation] = forms;
    let operator = contact_operator(storage, stiffness, dissipation, conductance, step)?;
    match operator.kernel_basis()?.into_iter().next() {
        None => Ok(()),
        Some(direction) => Err(HnnError::SingularContact {
            contact,
            conductance: Box::new(conductance.clone()),
            direction,
        }),
    }
}

/// **Every conductance a contact can take**, read over the pair quadrances of its two rings'
/// phase configurations when the rings' screws have no pitch (so the family is finite, the
/// windings entering no quadrance); `None` when a pitch makes it infinite.
pub fn contact_conductances(field: &Field, contact: usize) -> Result<Option<Vec<Rat>>, HnnError> {
    let declared = field.contact(contact);
    let (g, h) = declared.ends();
    let (ring_g, ring_h) = (field.ring(g), field.ring(h));
    if !ring_g.winding_carry().norm_squared().is_zero()
        || !ring_h.winding_carry().norm_squared().is_zero()
    {
        return Ok(None);
    }
    let mut lift: Vec<BigInt> = vec![BigInt::zero(); field.rings().len()];
    let mut conductances: Vec<Rat> = Vec::new();
    for phase_g in 0..ring_g.period() {
        for phase_h in 0..ring_h.period() {
            lift[g] = BigInt::from(phase_g);
            lift[h] = BigInt::from(phase_h);
            let exponent = crate::hnn::propagation::contact_exponent(field, contact, &lift)?;
            if exponent.phase != 0 {
                return Err(HnnError::ExponentPhase {
                    contact,
                    phase: exponent.phase,
                    grain: field.exponent_grain(),
                });
            }
            let conductance =
                crate::ratio::exponentiated::power_of_two(&exponent.carry)? * declared.admittance();
            if !conductances.contains(&conductance) {
                conductances.push(conductance);
            }
        }
    }
    conductances.sort();
    Ok(Some(conductances))
}

// -------------------------------------------------------------------------------------------
// the lock address

/// [definition] **A contact's lock address** at the declared tolerance (module header).
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ContactLock {
    /// No lock of denominator at most `Q` lies in the measured fibre, or a ring has not wound.
    Unlocked,
    /// The reduced address `p/q`, `0 < q ≤ Q`.
    Locked {
        numerator: BigUint,
        denominator: BigUint,
    },
}

/// [definition] **The finite lock family's bound**: `Q`, the greatest denominator whose first return
/// is observable before the admitted horizon, and the numerator's bound `P` alike.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LockDeclaration {
    pub denominator: BigUint,
    pub numerator: BigUint,
}

impl LockDeclaration {
    /// **The bound derived from the field** (module header, "The bounds are the horizon"): ring `r`
    /// winds at most `B_r = ∏_(j>r) d_j` times within one aeon of the joint clock, and the letter of
    /// the aeon's closing tick is read before the windings restart, so `Q = B_h` and `P = B_g`, the
    /// horizon (Lean `lock_partition_finite`, `Q = H`).
    pub fn derived(field: &Field, contact: usize) -> Self {
        let bound = |ring: usize| -> BigUint {
            field.rings()[ring + 1..]
                .iter()
                .map(|later| BigUint::from(later.period()))
                .product()
        };
        let (g, h) = field.contact(contact).ends();
        Self {
            denominator: bound(h),
            numerator: bound(g),
        }
    }

    /// `(P, Q)` as machine words, refused past 64 bits (the partition's letters are counted and
    /// ranked on them).
    fn words(&self) -> Result<(u64, u64), HnnError> {
        let word = |bound: &BigUint| {
            bound.to_u64().ok_or(HnnError::Shape {
                what: "a lock bound within 64 bits",
                expected: u64::MAX as usize,
                found: usize::MAX,
            })
        };
        Ok((word(&self.numerator)?, word(&self.denominator)?))
    }

    /// **The lock family's letters** (module header, "The lock letters"): `1 + #{(p, q) : 1 ≤ p ≤ P,
    /// 1 ≤ q ≤ Q, gcd(p, q) = 1}`, `Unlocked` with the reduced addresses in the box (Lean
    /// `Compression/Landmark/Context/Address.lock_partition_finite`).
    pub fn letters(&self) -> Result<u64, HnnError> {
        let (p_bound, q_bound) = self.words()?;
        Ok(1 + (1..=q_bound)
            .map(|q| coprime_up_to(p_bound, q))
            .sum::<u64>())
    }
}

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

/// The distinct prime factors of `n ≥ 1`, by trial division.
fn prime_factors(mut n: u64) -> Vec<u64> {
    let mut primes = Vec::new();
    let mut d = 2u64;
    while d * d <= n {
        if n.is_multiple_of(d) {
            primes.push(d);
            while n.is_multiple_of(d) {
                n /= d;
            }
        }
        d += 1;
    }
    if n > 1 {
        primes.push(n);
    }
    primes
}

/// `#{p ∈ [1, n] : gcd(p, q) = 1}` for `q ≥ 1`, by inclusion and exclusion over the distinct
/// primes of `q`: `Σ_(d | rad q) μ(d) ⌊n/d⌋`.
fn coprime_up_to(n: u64, q: u64) -> u64 {
    let primes = prime_factors(q);
    let mut count: i128 = 0;
    for subset in 0u32..(1 << primes.len()) {
        let divisor: u64 = (0..primes.len())
            .filter(|&i| subset >> i & 1 == 1)
            .map(|i| primes[i])
            .product();
        let term = i128::from(n / divisor);
        count += if subset.count_ones() % 2 == 0 {
            term
        } else {
            -term
        };
    }
    u64::try_from(count).expect("a count of integers is nonnegative")
}

/// **The lock address of a measured winding pair** (module header; Lean
/// `HNN/Contact.contact_lock_address`): the least-denominator rate of the open fibre
/// `(m_g/(m_h + 1), (m_g + 1)/m_h)` when both rings have wound (`IsLockAddress`, unique, closing at
/// its `q`, with `p ≤ m_g`, `q ≤ m_h`), Locked when its reduced parts lie within the declared bounds.
pub fn lock_address(first: &BigInt, second: &BigInt, bound: &LockDeclaration) -> ContactLock {
    if !first.is_positive() || !second.is_positive() {
        return ContactLock::Unlocked;
    }
    let lower = Rat::new(first.clone(), second + BigInt::one());
    let upper = Rat::new(first + BigInt::one(), second.clone());
    let Ok(simplest) = simplest_between(&lower, &upper) else {
        return ContactLock::Unlocked;
    };
    let (Some(numerator), Some(denominator)) =
        (simplest.numer().to_biguint(), simplest.denom().to_biguint())
    else {
        return ContactLock::Unlocked;
    };
    if numerator.is_zero()
        || denominator > bound.denominator
        || numerator > bound.numerator
        || denominator.is_zero()
    {
        return ContactLock::Unlocked;
    }
    ContactLock::Locked {
        numerator,
        denominator,
    }
}

impl ContactLock {
    /// **Its letter in the lock family** (module header, "The lock letters"): `0` unlocked, else
    /// `1 +` its rank among the reduced addresses of the box ordered by `(q, p)`,
    /// `Σ_(q′ < q) #{p ≤ P coprime to q′} + #{p′ < p coprime to q}`. One to one onto
    /// `[0, bound.letters())`; refused for an address outside the family (not reduced, or past a
    /// bound).
    pub fn code(&self, bound: &LockDeclaration) -> Result<u64, HnnError> {
        let ContactLock::Locked {
            numerator,
            denominator,
        } = self
        else {
            return Ok(0);
        };
        let (p_bound, q_bound) = bound.words()?;
        let outside = || HnnError::Shape {
            what: "a reduced lock address (p, q) with 1 ≤ p ≤ P and 1 ≤ q ≤ Q",
            expected: usize::try_from(q_bound).unwrap_or(usize::MAX),
            found: usize::try_from(denominator).unwrap_or(usize::MAX),
        };
        let (Some(p), Some(q)) = (numerator.to_u64(), denominator.to_u64()) else {
            return Err(outside());
        };
        if p == 0 || q == 0 || p > p_bound || q > q_bound || gcd(p, q) != 1 {
            return Err(outside());
        }
        let below: u64 = (1..q).map(|earlier| coprime_up_to(p_bound, earlier)).sum();
        Ok(1 + below + coprime_up_to(p - 1, q))
    }
}

// -------------------------------------------------------------------------------------------
// the readings the receiving join consumes

/// [definition] **One contact's reading at a cell's tick**: its lock address and its site kind,
/// both read from retained state before the cell (the lift point and the constitution). It is the
/// receiving join's contact letter (`hnn::receiving::Feature::Contact`): its value in the slot is
/// [`ContactReading::letter`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContactReading {
    pub contact: usize,
    pub lock: ContactLock,
    pub kind: SiteKind,
}

/// The proved site kinds (`Compression/Landmark/SiteKind.Kind`), the kind letter's alphabet.
pub const SITE_KINDS: u64 = 5;

/// **A site kind's letter**: rotation, null, boost, reflection, degenerate.
pub fn kind_letter(kind: SiteKind) -> u64 {
    match kind {
        SiteKind::Rotation => 0,
        SiteKind::Null => 1,
        SiteKind::Boost => 2,
        SiteKind::Reflection => 3,
        SiteKind::Degenerate => 4,
    }
}

impl ContactReading {
    /// **The contact letters at a bound**: the lock family's letters times the five site kinds.
    pub fn letters(bound: &LockDeclaration) -> Result<u64, HnnError> {
        bound
            .letters()?
            .checked_mul(SITE_KINDS)
            .ok_or(HnnError::Shape {
                what: "a contact's letters within 64 bits",
                expected: u64::MAX as usize,
                found: usize::MAX,
            })
    }

    /// **Its letter**: `code(lock) · 5 + kind`, one to one onto `[0, letters(bound))`.
    pub fn letter(&self, bound: &LockDeclaration) -> Result<u64, HnnError> {
        Ok(self.lock.code(bound)? * SITE_KINDS + kind_letter(self.kind))
    }
}

/// **Every contact's site reading** from its constitution's storage and stiffness factors and
/// signature ([`site_reading_of_factors`]): the part of a contact's reading that the constitution,
/// not the clock, carries.
pub fn site_readings(
    field: &Field,
    constitution: &impl ConstitutionRead,
) -> Result<Vec<SiteReading>, HnnError> {
    (0..field.contacts().len())
        .map(|contact| {
            site_reading_of_factors(
                constitution.contact_storage(contact),
                constitution.contact_stiffness(contact),
                constitution.contact_stiffness_signature(contact),
                field.step(),
            )
        })
        .collect()
}

/// **Every contact's site kind** ([`site_readings`]' kinds).
pub fn site_kinds(
    field: &Field,
    constitution: &impl ConstitutionRead,
) -> Result<Vec<SiteKind>, HnnError> {
    Ok(site_readings(field, constitution)?
        .into_iter()
        .map(|reading| reading.kind)
        .collect())
}

/// **Every contact's reading at a cell's tick** (the readings the receiving join consumes, campaign
/// 2): each contact's lock address from its two rings' whole windings over the passage from
/// `origin` (the aeon's opening lift point, or rest when `None`) to `current`, at the field's derived
/// bound, and its site kind from its constitution's storage and signed stiffness. Read before the
/// cell from the retained lift point and constitution only; nothing of the cell enters.
pub fn contact_readings(
    field: &Field,
    constitution: &impl ConstitutionRead,
    current: &Current,
    origin: Option<&Current>,
) -> Result<Vec<ContactReading>, HnnError> {
    let windings = |ring: usize| -> Result<BigInt, HnnError> {
        let now = current.winding(field, ring)?;
        Ok(match origin {
            Some(origin) => now - origin.winding(field, ring)?,
            None => now,
        })
    };
    site_kinds(field, constitution)?
        .into_iter()
        .enumerate()
        .map(|(contact, kind)| {
            let (g, h) = field.contact(contact).ends();
            let lock = lock_address(
                &windings(g)?,
                &windings(h)?,
                &LockDeclaration::derived(field, contact),
            );
            Ok(ContactReading {
                contact,
                lock,
                kind,
            })
        })
        .collect()
}

// -------------------------------------------------------------------------------------------
// the break

/// [definition] **The break's receipt** (Lean `HNN/ContactBreak`): the stored energy before the
/// transit `E_a`, its port work `W_a`, its dissipation `D_a`, the storage the parted constitution
/// holds after it `E_a′`, the released storage `R = E_a + W_a − D_a − E_a′`, the gluing work `J`,
/// the remainder `R − J`, and whether the advance is admitted (`R ≥ J`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BreakReceipt {
    pub stored: Rat,
    pub port_work: Rat,
    pub dissipation: Rat,
    pub kept: Rat,
    pub released: Rat,
    pub gluing: Rat,
    pub remainder: Rat,
    pub parts: bool,
}

impl BreakReceipt {
    /// **The receipt of one transit** for the parting of the matched nodes `parted` (channel node
    /// positions) at surface-storage density `density`: `J = γ · #parted`; `E_a′` is the post-transit
    /// state's storage under the constitution with the parted nodes' coordinates removed from `C`
    /// and `K`. `before` is the contact's state `[u, w]` before the transit, `after` the carried one.
    pub fn read(
        contact: &ContactOperands,
        step: &Rat,
        before: [&[Rat]; 2],
        after: [&[Rat]; 2],
        transit: &Transit,
        parted: &[usize],
        density: &Rat,
    ) -> Result<Self, HnnError> {
        let width = contact.width();
        let mut kept_coordinates = vec![true; width];
        for &node in parted {
            for coordinate in [2 * node, 2 * node + 1] {
                if coordinate >= width {
                    return Err(HnnError::Shape {
                        what: "a parted node of the contact's channel",
                        expected: width / 2,
                        found: node,
                    });
                }
                kept_coordinates[coordinate] = false;
            }
        }
        let stored = contact.energy(before[0], before[1])?;
        let quarter = step * contact.conductance() / integer(4);
        let norm = |v: &[Rat]| dot(v, v);
        let (alpha, out) = (&transit.channel_in, &transit.channel_out);
        let port_work = &quarter * (norm(&alpha.0) + norm(&alpha.1) - norm(&out.0) - norm(&out.1));
        let dissipation = transit.dissipation.clone();
        let (storage, stiffness, _) = contact.forms();
        let restricted = |form: &ExactRatMatrix| -> Result<ExactRatMatrix, HnnError> {
            Ok(ExactRatMatrix::shaped(
                width,
                width,
                (0..width)
                    .map(|i| {
                        (0..width)
                            .map(|j| {
                                if kept_coordinates[i] && kept_coordinates[j] {
                                    form.get(i, j).expect("in range").clone()
                                } else {
                                    Rat::zero()
                                }
                            })
                            .collect()
                    })
                    .collect(),
            )?)
        };
        let quadratic = |form: &ExactRatMatrix, v: &[Rat]| -> Result<Rat, HnnError> {
            Ok(dot(v, &form.apply(v)?))
        };
        let kept = (quadratic(&restricted(storage)?, after[1])?
            + quadratic(&restricted(stiffness)?, after[0])?)
            / integer(2);
        let released = &stored + &port_work - &dissipation - &kept;
        let gluing = density * Rat::from_integer(BigInt::from(parted.len()));
        let remainder = &released - &gluing;
        Ok(Self {
            parts: !remainder.is_negative(),
            stored,
            port_work,
            dissipation,
            kept,
            released,
            gluing,
            remainder,
        })
    }
}
