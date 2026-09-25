//! The boost as the Doppler ratio, dilation as an aeon rate, the twin, and the Wigner rotation.

use num_traits::{One, Signed, Zero};

use crate::aeon::{Aeon, ClosedForm, FiniteComplex, Form, Step, rate};
use crate::compression::landmark::{doppler_chart, rational_square_root};
use crate::geometry::{RatMat3, RatVec3};
use crate::ratio::surprisal::SymbolicSurprisal;
use crate::ratio::{Presentation, Rat, integer};

use super::SpacetimeError;

/// [definition] **A displacement in the light-cone chart** `u = t − x`, `v = t + x` (Lean
/// `Physics/Spacetime/Boost.LightCone`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LightCone {
    pub u: Rat,
    pub v: Rat,
}

impl LightCone {
    /// The displacement of `(t, x)` (Lean `ofTX`).
    pub fn of_tx(t: &Rat, x: &Rat) -> Self {
        Self { u: t - x, v: t + x }
    }

    /// `t = (u + v)/2`.
    pub fn time(&self) -> Rat {
        (&self.u + &self.v) / integer(2)
    }

    /// `x = (v − u)/2`.
    pub fn space(&self) -> Rat {
        (&self.v - &self.u) / integer(2)
    }

    /// The interval `uv = t² − x²` (Lean `interval`).
    pub fn interval(&self) -> Rat {
        &self.u * &self.v
    }

    /// **The Minkowski pairing** `−(a_u b_v + a_v b_u)/2 = −a_t b_t + a_x b_x` (Lean `pairing`).
    pub fn pairing(&self, other: &Self) -> Rat {
        -(&self.u * &other.v + &self.v * &other.u) / integer(2)
    }

    /// The displacement scaled by `τ`.
    pub fn scaled(&self, factor: &Rat) -> Self {
        Self {
            u: factor * &self.u,
            v: factor * &self.v,
        }
    }

    /// Two displacements added.
    pub fn plus(&self, other: &Self) -> Self {
        Self {
            u: &self.u + &other.u,
            v: &self.v + &other.v,
        }
    }
}

/// [definition] **The boost as the undivided Doppler pair** `(k, k⁻¹)`: `(u, v) ↦ (ku, k⁻¹v)`, with
/// `k > 0` (Lean `Boost.boost`). `γ = (k + k⁻¹)/2` and `γβ = (k − k⁻¹)/2` without a logarithm, on
/// the hyperbola of the owner `CompositeMassEnergy.multiplicativeScale_lorentz_identity`; rapidity is
/// the ratio's log chart.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DopplerBoost {
    ratio: Rat,
}

impl DopplerBoost {
    /// A boost of Doppler ratio `k`, refused unless `k > 0`.
    pub fn new(ratio: Rat) -> Result<Self, SpacetimeError> {
        if !ratio.is_positive() {
            return Err(SpacetimeError::Coefficient {
                what: "a Doppler ratio",
                value: ratio,
                requirement: "positive",
            });
        }
        Ok(Self { ratio })
    }

    /// [proved-derived; implemented-exact] **The boost of a velocity** `|β| < 1`, through the
    /// landmark owner's Doppler chart: `k² = D(β) = (1 + β)/(1 − β)` ([`doppler_chart`]; Lean
    /// `Boost.doppler_betaOf`), refused outside the open cone or when `D(β)` is not the square of a
    /// rational ratio.
    pub fn from_velocity(velocity: &Rat) -> Result<Self, SpacetimeError> {
        let chart = doppler_chart(velocity, &Rat::one())?;
        let ratio = rational_square_root(&chart).ok_or(SpacetimeError::Coefficient {
            what: "the Doppler chart (1 + β)/(1 − β)",
            value: chart.clone(),
            requirement: "the square of a rational Doppler ratio",
        })?;
        Self::new(ratio)
    }

    pub fn ratio(&self) -> &Rat {
        &self.ratio
    }

    /// `γ = (k + k⁻¹)/2` (Lean `gammaOf`).
    pub fn gamma(&self) -> Rat {
        (&self.ratio + self.ratio.recip()) / integer(2)
    }

    /// `γβ = (k − k⁻¹)/2` (Lean `gammaBetaOf`).
    pub fn gamma_beta(&self) -> Rat {
        (&self.ratio - self.ratio.recip()) / integer(2)
    }

    /// `β = (k² − 1)/(k² + 1)` (Lean `betaOf`).
    pub fn beta(&self) -> Rat {
        let square = &self.ratio * &self.ratio;
        (&square - Rat::one()) / (square + Rat::one())
    }

    /// [proved-derived; implemented-exact] **Collinear composition multiplies the Doppler ratios**
    /// (Lean `boost_mul`); read through the landmark owner's Doppler chart `D(β) = k²`, it is that
    /// owner's velocity addition (Lean `velocity_addition`, from `FixedPoint.doppler_vadd`).
    pub fn compose(&self, other: &Self) -> Self {
        Self {
            ratio: &self.ratio * &other.ratio,
        }
    }

    /// The reverse boost `k⁻¹`.
    pub fn inverse(&self) -> Self {
        Self {
            ratio: self.ratio.recip(),
        }
    }

    /// `(u, v) ↦ (ku, k⁻¹v)`: preserves the pairing and the interval (Lean `boost_pairing`,
    /// `boost_interval`).
    pub fn apply(&self, event: &LightCone) -> LightCone {
        LightCone {
            u: &self.ratio * &event.u,
            v: self.ratio.recip() * &event.v,
        }
    }

    /// The rapidity `log₂ k` as an exact form: its additive chart, summed under composition.
    pub fn rapidity_log2(&self) -> Result<SymbolicSurprisal, SpacetimeError> {
        SymbolicSurprisal::log2_of_ratio(&self.ratio).map_err(|_| SpacetimeError::Coefficient {
            what: "a Doppler ratio",
            value: self.ratio.clone(),
            requirement: "positive",
        })
    }

    /// The boost along `x` on `(t, x, y)` (Lean `Wigner.boostX`).
    pub fn along_x(&self) -> RatMat3 {
        let (g, s, z) = (self.gamma(), self.gamma_beta(), Rat::zero());
        RatMat3::new([
            [g.clone(), s.clone(), z.clone()],
            [s, g, z.clone()],
            [z.clone(), z, Rat::one()],
        ])
    }

    /// The boost along `y` on `(t, x, y)` (Lean `Wigner.boostY`).
    pub fn along_y(&self) -> RatMat3 {
        let (g, s, z) = (self.gamma(), self.gamma_beta(), Rat::zero());
        RatMat3::new([
            [g.clone(), z.clone(), s.clone()],
            [z.clone(), Rat::one(), z.clone()],
            [s, z, g],
        ])
    }
}

/// [definition] **The unit velocity** `U(k) = (k⁻¹, k)` of the receiver of Doppler ratio `k` (Lean
/// `receiverVelocity`), `(γ, γβ)` in the `(t, x)` chart.
pub fn receiver_velocity(boost: &DopplerBoost) -> LightCone {
    LightCone {
        u: boost.ratio.recip(),
        v: boost.ratio.clone(),
    }
}

/// [definition] **The receiver's clock reading** `t_R(Δ) = ⟨ω_R | Δ⟩ = −⟨U, Δ⟩` (Lean
/// `clockReading`).
pub fn clock_reading(receiver: &LightCone, displacement: &LightCone) -> Rat {
    -receiver.pairing(displacement)
}

/// [proved-derived; implemented-exact] **Time dilation as the rate of two aeon clocks** (Lean
/// `dilation_is_rate`, `inertialClock_reading`, `time_dilation`). Each receiver's inertial clock is
/// the exact clock of its potential `−⟨U, x⟩` on the event complex; on the aeon `0 → τU(k_moving)`,
/// here its one passage, it reads `−⟨U, τU(k_moving)⟩`. The owner's [`rate`] of the reader against
/// the moving receiver is `(τγ(k_reader/k_moving) : τ)`.
pub fn time_dilation(
    reader: &DopplerBoost,
    moving: &DopplerBoost,
    proper_time: &Rat,
) -> Result<Presentation, SpacetimeError> {
    let complex = FiniteComplex::graph(2, &[0], &[1])?;
    let aeon = Aeon::new(&complex, 0, vec![Step::along(0)])?;
    let displacement = receiver_velocity(moving).scaled(proper_time);
    let clock = |receiver: &DopplerBoost| {
        ClosedForm::new(
            &complex,
            Form::new(vec![clock_reading(
                &receiver_velocity(receiver),
                &displacement,
            )]),
        )
    };
    Ok(rate(&clock(reader)?, &clock(moving)?, &aeon)?)
}

/// [definition] **The twin's readings**: the traveller's proper time `2τ` out along `U(k)` and back
/// along `U(k⁻¹)`, and the stay-at-home proper time read from the same displacement.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TwinReading {
    pub traveller: Rat,
    /// `√(interval)` of the joint displacement, read from it.
    pub home: Rat,
    /// The interval of the joint displacement, `home²`.
    pub home_interval: Rat,
}

/// [proved-derived; implemented-exact] **The twin** (Lean `twin_interval`, `one_lt_gammaOf`): the
/// joint displacement `τU(k) + τU(k⁻¹)` has interval `(2γτ)²`, a rational square, and the
/// stay-at-home proper time is its square root, read from the displacement: `2γτ ≥ 2τ`, strictly
/// for `k ≠ 1`. A negative proper time is refused.
pub fn twin(boost: &DopplerBoost, proper_time: &Rat) -> Result<TwinReading, SpacetimeError> {
    if proper_time.is_negative() {
        return Err(SpacetimeError::Coefficient {
            what: "a proper time",
            value: proper_time.clone(),
            requirement: "nonnegative",
        });
    }
    let out = receiver_velocity(boost).scaled(proper_time);
    let back = receiver_velocity(&boost.inverse()).scaled(proper_time);
    let home_interval = out.plus(&back).interval();
    let home =
        rational_square_root(&home_interval).ok_or(SpacetimeError::NotARationalProperTime {
            interval: home_interval.clone(),
        })?;
    Ok(TwinReading {
        traveller: integer(2) * proper_time,
        home,
        home_interval,
    })
}

/// An event `(t, x, y)` of the velocity hyperboloid.
type Event3 = [Rat; 3];

fn event(vector: &RatVec3) -> Event3 {
    [vector.x.clone(), vector.y.clone(), vector.z.clone()]
}

/// The Minkowski pairing on `(t, x, y)` (Lean `Wigner.pairing3`).
fn pairing3(a: &Event3, b: &Event3) -> Rat {
    -(&a[0] * &b[0]) + &a[1] * &b[1] + &a[2] * &b[2]
}

/// The tangent at `vertex` toward `toward`, `X + ⟨V, X⟩V` (Lean `Wigner.tangent`).
fn tangent(vertex: &Event3, toward: &Event3) -> Event3 {
    let along = pairing3(vertex, toward);
    std::array::from_fn(|i| &toward[i] + &along * &vertex[i])
}

/// The oriented area `det[V, a, b]` (Lean `Wigner.orientedArea`).
fn oriented_area(vertex: &Event3, a: &Event3, b: &Event3) -> Rat {
    RatMat3::new([vertex.clone(), a.clone(), b.clone()]).determinant()
}

/// An interior angle at `vertex` of the rays toward `a` and `b`, scaled by the length of the ray
/// toward `b`: `(|t_b| cos, |t_b| sin)` with `sin ≥ 0`, and `|t_a|`. `None` when the ray toward
/// `a` is degenerate or its length is not rational.
fn scaled_angle(vertex: &Event3, a: &Event3, b: &Event3) -> Option<(Rat, Rat, Rat)> {
    let (ta, tb) = (tangent(vertex, a), tangent(vertex, b));
    let length = rational_square_root(&pairing3(&ta, &ta))?;
    if length.is_zero() {
        return None;
    }
    Some((
        pairing3(&ta, &tb) / &length,
        oriented_area(vertex, &ta, &tb).abs() / &length,
        length,
    ))
}

/// [definition] **The velocity triangle** `O → P → W` of two perpendicular boosts, read from its
/// vertices (Lean `Wigner.restVertex`, `vertexP`, `vertexW`, `rest_vertex_angle`,
/// `far_vertex_angle`, `right_angle_at_P`): its interior angles `α` (at `O`) and `β` (at `W`) scaled
/// by `S = |t_OW| = |t_WO|`, with nonnegative sines for every positive Doppler ratio
/// (`vertexAngles_nonneg`), and its orientation `σ = sign det[O, P, W]` (`orientation`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VelocityTriangle {
    /// `S² = ⟨t_OW, t_OW⟩ = γ₁²γ₂² − 1`.
    pub scale_sq: Rat,
    pub sin_alpha: Rat,
    pub cos_alpha: Rat,
    pub sin_beta: Rat,
    pub cos_beta: Rat,
    /// `sign det[O, P, W]`, `±1`.
    pub orientation: Rat,
}

impl VelocityTriangle {
    /// `S² sin(α + β)`, which is `S² cos θ` (Lean `wigner_angle_is_defect`).
    pub fn defect_cos_scaled(&self) -> Rat {
        &self.sin_alpha * &self.cos_beta + &self.cos_alpha * &self.sin_beta
    }

    /// `−σ S² cos(α + β)`, which is `S² sin θ`: the rotation turns opposite to the loop's
    /// orientation.
    pub fn defect_sin_scaled(&self) -> Rat {
        -(&self.orientation * (&self.cos_alpha * &self.cos_beta - &self.sin_alpha * &self.sin_beta))
    }

    /// [proved-derived; implemented-exact] **The triangle read from its vertices**: the tangents at
    /// each vertex, their pairings and oriented areas. `None` for a degenerate triangle (a unit
    /// ratio, no boost). Refused unless the angle at `P` is right (Lean `right_angle_at_P`) and
    /// the hypotenuse reads alike from both ends.
    fn of_vertices(
        rest: &Event3,
        near: &Event3,
        far: &Event3,
    ) -> Result<Option<Self>, SpacetimeError> {
        if !pairing3(&tangent(near, rest), &tangent(near, far)).is_zero() {
            return Err(SpacetimeError::NotARotation);
        }
        let (Some((cos_alpha, sin_alpha, _)), Some((cos_beta, sin_beta, _))) =
            (scaled_angle(rest, near, far), scaled_angle(far, near, rest))
        else {
            return Ok(None);
        };
        let from_rest = tangent(rest, far);
        let from_far = tangent(far, rest);
        let scale_sq = pairing3(&from_rest, &from_rest);
        if scale_sq != pairing3(&from_far, &from_far) {
            return Err(SpacetimeError::NotARotation);
        }
        let area = oriented_area(rest, near, far);
        let orientation = if area.is_negative() {
            -Rat::one()
        } else {
            Rat::one()
        };
        Ok(Some(Self {
            scale_sq,
            sin_alpha,
            cos_alpha,
            sin_beta,
            cos_beta,
            orientation,
        }))
    }
}

/// [definition] **The Thomas–Wigner return of a loop of boosts**: the composite, its pure boost,
/// the loop's return and the rotation read from it, with the velocity triangle read from the
/// composite's vertices (`None` when degenerate).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WignerRotation {
    /// `boostX k₁ · boostY k₂`.
    pub composite: RatMat3,
    /// `B(w)`, the pure boost to the composite velocity.
    pub pure_boost: RatMat3,
    /// `B(w)⁻¹ · boostX k₁ · boostY k₂`.
    pub loop_return: RatMat3,
    pub cos: Rat,
    pub sin: Rat,
    pub triangle: Option<VelocityTriangle>,
}

/// The pure boost with first column `(γ, pₓ, p_y)` (Lean `Wigner.pureBoost`).
fn pure_boost(gamma: &Rat, px: &Rat, py: &Rat) -> RatMat3 {
    let one_plus = gamma + Rat::one();
    RatMat3::new([
        [gamma.clone(), px.clone(), py.clone()],
        [
            px.clone(),
            Rat::one() + px * px / &one_plus,
            px * py / &one_plus,
        ],
        [
            py.clone(),
            px * py / &one_plus,
            Rat::one() + py * py / &one_plus,
        ],
    ])
}

/// [proved-derived; implemented-exact] **The Thomas–Wigner rotation of perpendicular boosts** (Lean
/// `wigner_decomposition`, `pureBoost_inverse`, `loop_returns_rotation`, `wigner_angle_is_defect`).
/// The composite's first column is the composite velocity; the loop's return is computed by exact
/// matrix products and refused unless it is a rotation of the spatial plane, whose angle is read
/// from it: `cos θ = (γ₁ + γ₂)/(1 + γ₁γ₂)`, `sin θ = −γβ₁γβ₂/(1 + γ₁γ₂)`. The velocity triangle is
/// read from the vertices `O = e₀`, `P = boostX k₁ e₀` and `W = composite · e₀`.
pub fn wigner_rotation(
    first: &DopplerBoost,
    second: &DopplerBoost,
) -> Result<WignerRotation, SpacetimeError> {
    let composite = first.along_x().multiply(&second.along_y());
    let (gamma, px, py) = (
        composite.rows[0][0].clone(),
        composite.rows[1][0].clone(),
        composite.rows[2][0].clone(),
    );
    let pure = pure_boost(&gamma, &px, &py);
    let inverse = pure_boost(&gamma, &-px.clone(), &-py.clone());
    let loop_return = inverse.multiply(&composite);
    let r = &loop_return.rows;
    let (cos, sin) = (r[1][1].clone(), r[2][1].clone());
    let is_rotation = r[0][0] == Rat::one()
        && [&r[0][1], &r[0][2], &r[1][0], &r[2][0]]
            .iter()
            .all(|entry| entry.is_zero())
        && r[2][2] == cos
        && r[1][2] == -sin.clone()
        && &cos * &cos + &sin * &sin == Rat::one();
    if !is_rotation {
        return Err(SpacetimeError::NotARotation);
    }
    let rest = RatVec3::new(Rat::one(), Rat::zero(), Rat::zero());
    let triangle = VelocityTriangle::of_vertices(
        &event(&rest),
        &event(&first.along_x().apply(&rest)),
        &event(&composite.apply(&rest)),
    )?;
    Ok(WignerRotation {
        composite,
        pure_boost: pure,
        loop_return,
        cos,
        sin,
        triangle,
    })
}
