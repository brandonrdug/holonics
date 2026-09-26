//! **The contact's own readings: its transfer and site kind, its boost, its lock address and its
//! break** (campaign 2, Lean `HNN/Contact`, `HNN/ContactBreak`).
//!
//! [definition] A contact slips, dissipates and addresses. Its transit (`hnn::propagation`, the
//! owner of the executed two-port) is read here through what it says about the contact itself:
//!
//! ```text
//! transfer   m = 2c + p + h d + (h²/2) k ,   T = (1/m) [[m − h²k, 2hc], [−2hk, 4c − m]]
//!            tr T = (4c − h²k)/m ,   det T = (2c + h²k/2 − p − hd)/m       p = 2h/G, or 0 closed
//! kind       closed, lossless, c > 0, 4c + h²k ≠ 0:  k > 0 rotation, k = 0 null shear, k < 0 boost
//! boost      K = b diag(σ) bᵀ, σ ∈ {±1}; admitted only where M_a = 2C + (2h/G)I + hD + (h²/2)K is
//!            nonsingular, a refusal carrying its singular direction
//! lock       whole windings (m_g, m_h) over a passage: the simplest rate in their fibre
//!            (m_g/(m_h + 1), (m_g + 1)/m_h) with denominator at most Q, or Unlocked
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
//! ([`site_reading`]). A contact whose storage is not definite on its channel reads
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
//! [definition; agent-inferred] **The lock address and its finite family.** A contact `a = (g → h)`
//! reads its two rings' whole windings over a passage, the difference of their lift points' windings
//! (the signed count is the flux, Lean `Aeon/Clock/Epoch.signed_count_is_flux`). The rings' phases
//! are the unresolved part at the winding grain, so the rates consistent with the reading are the
//! open fibre `(m_g/(m_h + 1), (m_g + 1)/m_h)`, which holds the measured ratio `m_g/m_h`, whose
//! reduced address the passage closes at (Lean `contact_lock_address`). The lock address is the
//! simplest rate in the fibre, the least-denominator lock (Lean `Geometry/PairResonance`, the owner
//! [`simplest_between`]); it is **Locked** `(p, q)` when `q ≤ Q`, and **Unlocked** otherwise, or when
//! either ring has not wound. `Q` is the greatest denominator whose first return (`q` turns of ring
//! `h`) is observable before the admitted horizon ([`LockDeclaration::derived`]: within one aeon of
//! the joint clock ring `h` winds fewer than `∏_(j>h) d_j` times, the carry chain's bound, so
//! `Q = ∏_(j>h) d_j − 1`, and the numerator is held to ring `g`'s bound alike).
//!
//! [definition] **The break** ([`BreakReceipt`], Lean `HNN/ContactBreak`). The contact's parting of
//! `j` matched nodes at the declared surface-storage density `γ` (`ConstitutionRead::
//! contact_surface_storage`, #31) takes the gluing work `J = γ j`; the released storage is
//! `R = E_a + W_a − D_a − E_a′` with `E_a′` the post-transit storage the parted constitution still
//! holds, and the receipt is `R − J`. Under the exact law `R` is the storage the parting removes
//! (`break_release_balance`); on the lattices it carries the transit's defects. A parted contact's
//! shared face returns its typed gluing defect ([`crate::hnn::Field::parted_holon`],
//! `parting_returns_gluing_defect`).
//!
//! | Lean | Rust |
//! |---|---|
//! | `HNN/Contact.{transferDen, transfer, transfer_solves, transfer_trace_det}` | [`transfer`], [`Transfer`] |
//! | `HNN/Contact.contact_transfer_kind_by_storage_sign`, `contact_mode_transfer` | [`Transfer::site`], [`site_reading`] |
//! | `HNN/Contact.contact_boost_solve_or_singular_direction` | [`certify_boost`], [`signed_form_certifies`] |
//! | `HNN/Contact.contact_signed_storage_balance`, `boost_grows_at_conserved_signed_storage` | tests (the transit's balance at an indefinite `K`) |
//! | `HNN/Contact.contact_lock_address`; `Geometry/PairResonance` | [`lock_address`], [`ContactLock`] |
//! | `HNN/ContactBreak.{break_release_balance, break_iff_release_covers_gluing, griffith_closed_port_case}` | [`BreakReceipt`] |
//! | `HNN/ContactBreak.parting_returns_gluing_defect` | [`crate::hnn::Field::parted_holon`] |

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};

use crate::hnn::HnnError;
use crate::hnn::field::{ConstitutionRead, Current, Field};
use crate::hnn::propagation::{ContactOperands, Transit, contact_operator, gram};
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

/// **The contact's site reading** from its storage `C_a` and signed stiffness `K_a` (module
/// header): with `C_a ≻ 0` the census is the inertia of `K_a`, and the kind a boost if any mode is,
/// else a null shear if any is, else a rotation.
pub fn site_reading(
    storage: &ExactRatMatrix,
    stiffness: &ExactRatMatrix,
) -> Result<SiteReading, HnnError> {
    if storage.rows() == 0 || !inertia(&symmetric(storage)?).is_positive_definite() {
        return Ok(SiteReading {
            census: KindCensus::default(),
            kind: SiteKind::Degenerate,
        });
    }
    let signs = inertia(&symmetric(stiffness)?);
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
/// is observable before the admitted horizon, and the numerator's bound alike.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LockDeclaration {
    pub denominator: BigUint,
    pub numerator: BigUint,
}

impl LockDeclaration {
    /// **The bound derived from the field** (module header): ring `r` winds fewer than
    /// `B_r = ∏_(j>r) d_j` times within one aeon of the joint clock, so the first return of `q` turns
    /// of the contact's second ring is observable within the aeon when `q ≤ B_h − 1`, and the first
    /// ring's `p` turns when `p ≤ B_g − 1`.
    pub fn derived(field: &Field, contact: usize) -> Self {
        let bound = |ring: usize| -> BigUint {
            let horizon: BigUint = field.rings()[ring + 1..]
                .iter()
                .map(|later| BigUint::from(later.period()))
                .product();
            if horizon.is_zero() {
                BigUint::zero()
            } else {
                horizon - BigUint::one()
            }
        };
        let (g, h) = field.contact(contact).ends();
        Self {
            denominator: bound(h),
            numerator: bound(g),
        }
    }
}

/// **The lock address of a measured winding pair** (module header): the simplest rate in the open
/// fibre `(m_g/(m_h + 1), (m_g + 1)/m_h)` when both rings have wound, Locked when its reduced parts
/// lie within the declared bounds.
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

// -------------------------------------------------------------------------------------------
// the readings the receiving join consumes

/// [definition] **One contact's reading at a cell's tick**: its lock address and its site kind,
/// both read from retained state before the cell (the lift point and the constitution).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContactReading {
    pub contact: usize,
    pub lock: ContactLock,
    pub kind: SiteKind,
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
    (0..field.contacts().len())
        .map(|contact| {
            let (g, h) = field.contact(contact).ends();
            let lock = lock_address(
                &windings(g)?,
                &windings(h)?,
                &LockDeclaration::derived(field, contact),
            );
            let storage = gram(constitution.contact_storage(contact))?;
            let stiffness = signed_stiffness(
                constitution.contact_stiffness(contact),
                constitution.contact_stiffness_signature(contact),
            )?;
            Ok(ContactReading {
                contact,
                lock,
                kind: site_reading(&storage, &stiffness)?.kind,
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
