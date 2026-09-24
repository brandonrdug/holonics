//! The local helical-pair adapter.
//!
//! A `ScrewPair` owns the geometry.  This module only embeds its two-parameter relative
//! velocity into the existing checked interaction owners:
//!
//! ```text
//! J_pair = [v_a | -v_b]
//! u_pair = C z
//! M_medium = Cᵀ J_pairᵀ D J_pair C
//! ```
//!
//! The pair rate, the medium state and the resident current remain distinct charts.  In
//! particular, `C z` is not silently identified with a physical configuration velocity.
//!
//! [proved-derived; implemented-exact] **The pair contact is a core resistive element on relative
//! slip** (`Holon/Conformance.lean::pairContact_resistive`): the flow is the slip `f = J_pair C v`
//! and the effort the traction `e = −w D f`. Its power `⟨e, f⟩ = −w⟨f, D f⟩` is minus the
//! assembled contact form at `v`, and [`HelicalPairInteraction::contact_element`] certifies `w D`
//! passive through the core. The whole pair unit is the core Holon of its interaction
//! ([`HolonicInteraction::holon`]).

use holonics::element::ResistiveRelation;
use holonics::port::Bond;
use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use relational_geometry::{PairQuadranceJet, Rat, ScrewPair};
use thiserror::Error;

use super::{
    Carrier, Clock, ContactDissipation, ContactFace, ExactRatMatrix, HolonicInteraction,
    InteractionRefusal, Medium, MediumContact, Perspective, SourceCurrent, SymmetricForm,
};

/// The units carried by the pair adapter.  They are labels for the declared frame and parameter
/// ports; no conversion or clock is inferred from a spelling.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairUnits {
    frame: String,
    parameters: [String; 2],
}

impl PairUnits {
    pub fn declared(frame: impl Into<String>, parameters: [String; 2]) -> Self {
        Self {
            frame: frame.into(),
            parameters,
        }
    }

    pub fn frame(&self) -> &str {
        &self.frame
    }

    pub fn parameters(&self) -> &[String; 2] {
        &self.parameters
    }
}

/// Refusal returned by the pair adapter.  The interaction owners retain their own refusal
/// vocabulary; geometry and matrix construction remain visible to the caller as separate arms.
#[derive(Debug, Error)]
pub enum HelicalRefusal {
    #[error(transparent)]
    Interaction(#[from] InteractionRefusal),
    #[error(transparent)]
    Linear(#[from] holonics::exact_linear::ExactLinearError),
    #[error("the pair response has extent {found}, but a spatial slip has extent 3")]
    ResponseExtent { found: usize },
    #[error("the pair rate port must have 2 rows, found {found}")]
    RatePortRows { found: usize },
    #[error("a rate port with {columns} ambient columns needs an explicit left/right block split")]
    AmbientSplitRequired { columns: usize },
    #[error(
        "the declared left/right blocks have widths {left} and {right}, but the rate port has {columns} columns"
    )]
    AmbientSplitMismatch {
        left: usize,
        right: usize,
        columns: usize,
    },
    #[error("a medium block has zero width")]
    EmptyMediumBlock,
    /// The Holon core refused the contact element.
    #[error(transparent)]
    Holon(#[from] holonics::holon::HolonError),
}

/// A covector over the full fixed-generator pair feature `(Delta,Q,DQ)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairFeatureCovector {
    pub delta: [Rat; 3],
    pub quadrance: Rat,
    pub gradient: [Rat; 2],
}

impl PairFeatureCovector {
    pub fn new(delta: [Rat; 3], quadrance: Rat, gradient: [Rat; 2]) -> Self {
        Self {
            delta,
            quadrance,
            gradient,
        }
    }
}

/// The lock reading keeps the signed and stationary cases outside the positive Farey address
/// chart.  A zero rate is a stationary reading, never `LockAddress(0/0)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PairLockReading {
    NotLocked,
    PositiveAddress {
        numerator: BigInt,
        denominator: BigInt,
        address: relational_geometry::LockAddress,
    },
    SignedOrStationary {
        numerator: BigInt,
        denominator: BigInt,
    },
}

/// A `ScrewPair` joined to the existing exact contact and interaction owners.
#[derive(Clone, Debug)]
pub struct HelicalPairInteraction {
    pair: ScrewPair,
    jet: PairQuadranceJet,
    pair_slip: ExactRatMatrix,
    rate_port: ExactRatMatrix,
    effective_slip: ExactRatMatrix,
    units: PairUnits,
    clock: Clock,
    interaction: HolonicInteraction,
}

impl HelicalPairInteraction {
    /// Build a local pair interaction. `rate_port` is the explicit `C: z ↦ (ṡ,ṫ)` map.
    /// `response` is the spatial `D_f` over the three slip coordinates and `weight` is `w_f`.
    /// Their positivity is checked by `ContactFace::declared`.
    #[allow(clippy::too_many_arguments)]
    pub fn declared(
        lineage: impl Into<String>,
        pair: ScrewPair,
        rate_port: ExactRatMatrix,
        response: SymmetricForm,
        weight: Rat,
        clock: Clock,
        units: PairUnits,
    ) -> Result<Self, HelicalRefusal> {
        if rate_port.columns() != 2 {
            return Err(HelicalRefusal::AmbientSplitRequired {
                columns: rate_port.columns(),
            });
        }
        Self::declared_with_blocks(
            lineage, pair, rate_port, 1, 1, response, weight, clock, units,
        )
    }

    /// Build the same adapter with an explicit ambient split.  The two medium blocks concatenate
    /// to the columns of `C`; this is required whenever the resident state has more than the two
    /// pair-rate coordinates.
    #[allow(clippy::too_many_arguments)]
    pub fn declared_with_blocks(
        lineage: impl Into<String>,
        pair: ScrewPair,
        rate_port: ExactRatMatrix,
        left_width: usize,
        right_width: usize,
        response: SymmetricForm,
        weight: Rat,
        clock: Clock,
        units: PairUnits,
    ) -> Result<Self, HelicalRefusal> {
        let lineage = lineage.into();
        if response.extent() != 3 {
            return Err(HelicalRefusal::ResponseExtent {
                found: response.extent(),
            });
        }
        if rate_port.rows() != 2 {
            return Err(HelicalRefusal::RatePortRows {
                found: rate_port.rows(),
            });
        }
        if left_width == 0 || right_width == 0 {
            return Err(HelicalRefusal::EmptyMediumBlock);
        }
        super::bounded(
            "the pair's left medium width",
            left_width,
            super::DECLARED_MODE_CEILING,
        )?;
        super::bounded(
            "the pair's right medium width",
            right_width,
            super::DECLARED_MODE_CEILING,
        )?;
        let ambient =
            left_width
                .checked_add(right_width)
                .ok_or(InteractionRefusal::WorkOverflows {
                    what: "the pair's ambient chart",
                })?;
        super::bounded(
            "the pair's ambient chart",
            ambient,
            super::DECLARED_MODE_CEILING,
        )?;
        if ambient != rate_port.columns() {
            return Err(HelicalRefusal::AmbientSplitMismatch {
                left: left_width,
                right: right_width,
                columns: rate_port.columns(),
            });
        }

        let first = pair.first();
        let second = pair.second();
        let first_velocity = first.generator().velocity(first.initial());
        let second_velocity = second.generator().velocity(second.initial());
        super::bounded(
            "the pair's ambient rate port",
            rate_port.columns(),
            super::DECLARED_MODE_CEILING,
        )?;
        super::bounded_product(
            "the pair's effective slip map",
            &[3, rate_port.columns()],
            super::DECLARED_ASSEMBLY_CEILING,
        )?;
        let pair_slip = ExactRatMatrix::shaped(
            3,
            2,
            vec![
                vec![first_velocity.x.clone(), -&second_velocity.x],
                vec![first_velocity.y.clone(), -&second_velocity.y],
                vec![first_velocity.z.clone(), -&second_velocity.z],
            ],
        )?;
        let effective_slip = pair_slip.multiply(&rate_port)?;
        let jet = PairQuadranceJet::at(
            first.generator(),
            first.initial(),
            second.generator(),
            second.initial(),
        );

        // The actual interaction face is J_pair C, so HolonicInteraction::joint_dissipation
        // assembles the requested Cᵀ Jᵀ D J C form through its existing
        // ContactFace/MediumContact path.  The split is explicit because C's ambient columns
        // are not intrinsically two pair coordinates.
        let one = Rat::from_integer(1.into());
        let left_storage = SymmetricForm::from_diagonal(vec![one.clone(); left_width]);
        let right_storage = SymmetricForm::from_diagonal(vec![one; right_width]);
        let left_structure = ExactRatMatrix::zero(left_width, left_width)?;
        let right_structure = ExactRatMatrix::zero(right_width, right_width)?;
        let media = vec![
            Medium::declared(
                format!("{lineage}|first"),
                left_storage,
                left_structure,
                Vec::new(),
            )?,
            Medium::declared(
                format!("{lineage}|second"),
                right_storage,
                right_structure,
                Vec::new(),
            )?,
        ];
        let face = ContactFace::declared(
            format!("{lineage}|pair-face"),
            effective_slip.clone(),
            response,
            weight,
        )?;
        let contact = MediumContact::declared(
            format!("{lineage}|contact"),
            Carrier::Medium(0),
            Carrier::Medium(1),
            face,
        )?;
        let source = SourceCurrent::declared(
            format!("{lineage}|source"),
            Carrier::Medium(0),
            ExactRatMatrix::shaped(
                left_width,
                1,
                (0..left_width)
                    .map(|row| {
                        vec![if row == 0 {
                            Rat::from_integer(1.into())
                        } else {
                            Rat::zero()
                        }]
                    })
                    .collect(),
            )?,
            vec![format!("{lineage}|input")],
        )?;
        let perspective = Perspective::over_joint(
            format!("{lineage}|receiver"),
            ExactRatMatrix::identity(rate_port.columns())?,
            (0..rate_port.columns())
                .map(|column| format!("{lineage}|ambient[{column}]"))
                .collect(),
        )?;
        let interaction = HolonicInteraction::declared(
            lineage,
            source,
            media,
            vec![contact],
            Vec::new(),
            None,
            perspective,
        )?;

        Ok(Self {
            pair,
            jet,
            pair_slip,
            rate_port,
            effective_slip,
            units,
            clock,
            interaction,
        })
    }

    pub fn pair(&self) -> &ScrewPair {
        &self.pair
    }

    pub fn jet(&self) -> &PairQuadranceJet {
        &self.jet
    }

    /// `J_pair=[v_a|-v_b]`, in the declared frame and spatial units.
    pub fn pair_slip(&self) -> &ExactRatMatrix {
        &self.pair_slip
    }

    /// The explicit rate-port map `C` from medium state to pair rates.
    pub fn rate_port(&self) -> &ExactRatMatrix {
        &self.rate_port
    }

    /// The face map carried by `HolonicInteraction`: `J_pair C`.
    pub fn effective_slip(&self) -> &ExactRatMatrix {
        &self.effective_slip
    }

    pub fn units(&self) -> &PairUnits {
        &self.units
    }

    pub fn clock(&self) -> &Clock {
        &self.clock
    }

    /// Return the actual public interaction owner, including its checked medium contact.
    pub fn interaction(&self) -> &HolonicInteraction {
        &self.interaction
    }

    pub fn into_interaction(self) -> HolonicInteraction {
        self.interaction
    }

    /// The assembled medium form is exactly `CᵀJᵀDJC`.
    pub fn contact_dissipation(&self) -> Result<ContactDissipation, HelicalRefusal> {
        Ok(self.interaction.joint_dissipation()?)
    }

    /// **The pair contact as the core resistive relation** `R = w D` on the three slip
    /// coordinates, certified passive (`Holon/Element.lean::PortHolon.passive`).
    pub fn contact_element(&self) -> Result<ResistiveRelation, HelicalRefusal> {
        let face = self.pair_face();
        let response = face.response();
        let resistance = ExactRatMatrix::shaped(
            3,
            3,
            (0..3)
                .map(|row| {
                    (0..3)
                        .map(|column| face.weight() * response.at(row, column))
                        .collect()
                })
                .collect(),
        )?;
        Ok(ResistiveRelation::new(resistance)?)
    }

    /// **The contact bond at a medium motion** `v`: flow the slip `f = J_pair C v`, effort the
    /// traction `e = −w D f` (`Holon/Conformance.lean::pairContact_resistive`). Its power is
    /// `−⟨v, M_contact v⟩`.
    pub fn contact_bond(&self, motion: &[Rat]) -> Result<Bond, HelicalRefusal> {
        let element = self.contact_element()?;
        let slip = self.pair_face().slip_of(motion)?;
        let traction = element
            .resistance()
            .apply(&slip)?
            .into_iter()
            .map(|value| -value)
            .collect();
        Ok(Bond::new(slip, traction)?)
    }

    fn pair_face(&self) -> &ContactFace {
        self.interaction
            .contacts()
            .first()
            .expect("the pair interaction declares exactly one contact")
            .face()
    }

    /// The kinematic no-slip kernel of `J_pair C` in the medium chart.
    pub fn no_slip_kernel(&self) -> Result<Vec<Vec<Rat>>, HelicalRefusal> {
        Ok(self.contact_dissipation()?.zero_slip_kernel()?)
    }

    /// The material zero-power kernel of `D J_pair C`; it can be larger than no-slip for PSD D.
    pub fn material_kernel(&self) -> Result<Vec<Vec<Rat>>, HelicalRefusal> {
        Ok(self.contact_dissipation()?.kernel_basis()?)
    }

    pub fn material_is_definite(&self) -> bool {
        self.interaction
            .contacts()
            .first()
            .is_some_and(|contact| contact.face().is_dissipative())
    }

    /// Whether the declared material is definite on the attainable pair slips.  This is weaker
    /// than `material_is_definite`: a globally singular `D` can still have no null direction in
    /// `im(J_pair C)`, while a singular response blind to an attainable slip cannot synchronize
    /// zero power with no-slip.
    pub fn material_power_implies_no_slip(&self) -> Result<bool, HelicalRefusal> {
        let dissipation = self.contact_dissipation()?;
        Ok(dissipation.signature().positive == self.effective_slip.rank()?)
    }

    /// Pull a covector through `(Delta,Q,DQ)` at fixed generators:
    /// `Jᵀ lambda_Delta + lambda_Q DQ + (D²Q)ᵀ lambda_DQ`.
    pub fn feature_pullback(&self, covector: &PairFeatureCovector) -> [Rat; 2] {
        let mut result = [Rat::zero(), Rat::zero()];
        for (column, value) in result.iter_mut().enumerate() {
            for row in 0..3 {
                *value += self.pair_slip.get(row, column).expect("pair slip shape")
                    * &covector.delta[row];
            }
            *value += &covector.quadrance * &self.jet.gradient()[column];
            for row in 0..2 {
                *value += &self.jet.hessian()[row][column] * &covector.gradient[row];
            }
        }
        result
    }

    /// Preserve the positive Farey address only when the supplied nonzero ratio is positive and
    /// actually locks this pair. Signed and stationary rate relations remain explicit readings.
    pub fn lock_reading(&self, numerator: BigInt, denominator: BigInt) -> PairLockReading {
        if !relational_geometry::pair_lock(&self.pair, &numerator, &denominator) {
            return PairLockReading::NotLocked;
        }
        if numerator.is_positive() && denominator.is_positive() {
            if let Ok(address) =
                relational_geometry::LockAddress::from_ratio(&numerator, &denominator)
            {
                return PairLockReading::PositiveAddress {
                    numerator,
                    denominator,
                    address,
                };
            }
        }
        PairLockReading::SignedOrStationary {
            numerator,
            denominator,
        }
    }
}

#[cfg(test)]
#[path = "helical/tests.rs"]
mod tests;
