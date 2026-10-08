//! One retained current for execution and its exact/charted receiving views (Refs #73 #62).
//!
//! The source navigator lift and the absolute carried crossing are distinct clocks. A section
//! receiver declares its station entrance at the live lift; it does not advance that lift. The
//! existing execution port alone advances it through an ingested Encoded passage.

use super::*;
use crate::hnn::field::FieldMaterial;
use crate::holon::HolonState;

fn coefficients(change: &EndChange) -> impl Iterator<Item = &Rat> {
    change.storage.iter().chain(change.arrivals.iter().flatten())
        .chain(change.states.iter().flatten())
        .chain(change.resonators.iter().flatten().flatten()).flatten()
}

impl Resident {
    /// The actual coupled current's enclosure, at the same crossing as `carried()`.
    /// None supplies no counterfactual accuracy claim. It never substitutes a work residual.
    pub fn carry_error(&self) -> Option<&EndChange> {
        self.carried_error.as_ref()
    }

    /// A receiving view opens the shared current with no absorption. Its constructor admits
    /// this future; the absolute crossing index already distinguishes complete and partial words.
    pub fn reception_opening(&self) -> WordOpening {
        match &self.carried {
            Some(carry) => WordOpening::Received {
                carry: carry.clone(), absorption: Absorption::Nothing,
            },
            None => WordOpening::Rest,
        }
    }

    pub(crate) fn admit_exact_current(&self) -> Result<(), HnnError> {
        self.admit_no_participating_world()?;
        if self.held_contact_variation.is_some() {
            return Err(HnnError::Unadmitted {
                reason: "this consumer has no transport or rebase for the held contact material variation",
            });
        }
        self.admit_exact_current_point()
    }

    pub(crate) fn admit_no_participating_world(&self) -> Result<(), HnnError> {
        if self.participating_world.is_some() {
            return Err(HnnError::Unadmitted {
                reason: "this view has no participating World transport, derivative or passage serialization",
            });
        }
        Ok(())
    }

    pub fn participating_world(&self) -> Option<&crate::hnn::physical::action::BoundJointWorld> {
        self.participating_world.as_ref()
    }

    pub(crate) fn participating_world_mut(&mut self)
        -> Result<&mut crate::hnn::physical::action::BoundJointWorld, HnnError>
    {
        self.participating_world.as_mut().ok_or(HnnError::Unadmitted {
            reason: "an actual retained participating World precedes native action execution",
        })
    }

    pub(crate) fn bind_participating_world(&mut self,
        world: crate::hnn::physical::action::BoundJointWorld) -> Result<(), HnnError>
    {
        self.admit_exact_current()?;
        self.admit_receiving_chart(world.common_chart())?;
        if !self.pending.is_empty() || !self.staged.is_empty()
            || self.opens != Opens::OnMotion || self.field.sources().len() != 1
        {
            return Err(HnnError::Unadmitted {
                reason: "one retained World on a continuing source current without pending returns",
            });
        }
        let source = self.field.sources()[0];
        let wave = vec![Rat::zero(); self.field.ring(source).width()];
        world.admit(world.common_chart(), &wave, self.field.ring(source).admittance(),
            self.field.step(), self.carried.as_ref().map_or(0, |c| c.ticks))?;
        let ops = crate::hnn::propagation::Operands::exact_at_cut(&self.field,
            &self.constitution, &self.current)?;
        if ops.resonators()[source].is_some() {
            return Err(HnnError::Unadmitted {
                reason: "the actual World return requires a nonloaded source storage port",
            });
        }
        self.participating_world = Some(world);
        Ok(())
    }

    pub(crate) fn admit_exact_current_point(&self) -> Result<(), HnnError> {
        if self.carried_error.as_ref().is_some_and(|e| coefficients(e).any(|x| !x.is_zero())) {
            return Err(HnnError::Unadmitted {
                reason: "this current carries an enclosure whose transport this consumer does not admit",
            });
        }
        Ok(())
    }

    /// Admit a prospective fixed-material differential on the existing current.
    /// No physical coordinate is reset; the derivative before this declaration is not claimed.
    pub fn begin_held_contact_variation(&mut self,
        budget: crate::hnn::word::variation::VariationBudget,
    ) -> Result<crate::hnn::word::variation::VariationReading,HnnError> {
        self.begin_contact_variation(budget,false)
    }

    /// Admit continuing sensitivity through actual contact publications. Applied increments
    /// are declared exterior controls of the realized factor-translation action, with P=I;
    /// the learner's selection/rounding policy is not differentiated. No primal state resets.
    pub fn begin_continuing_contact_variation(&mut self,
        budget:crate::hnn::word::variation::VariationBudget,
    ) -> Result<crate::hnn::word::variation::VariationReading,HnnError> {
        self.begin_contact_variation(budget,true)
    }

    fn begin_contact_variation(&mut self,
        budget:crate::hnn::word::variation::VariationBudget,translations:bool,
    ) -> Result<crate::hnn::word::variation::VariationReading,HnnError> {
        self.admit_exact_current()?;
        if self.opens != Opens::OnMotion || !self.pending.is_empty() || !self.staged.is_empty() {
            return Err(HnnError::Unadmitted {
                reason:"the held contact variation starts on a continuing current without pending or staged returns",
            });
        }
        let held = crate::hnn::word::variation::HeldContactVariation::begin(
            &self.field,&self.constitution,&self.current,self.carried.as_ref(),budget)?;
        let held = if translations { held.with_realized_translations()? } else { held };
        let reading = held.reading().clone();
        self.held_contact_variation = Some(held);
        Ok(reading)
    }

    pub fn held_contact_variation(&self) -> Option<&crate::hnn::word::variation::HeldContactVariation> {
        self.held_contact_variation.as_ref()
    }

    /// Explicitly end this differential future while keeping the physical current. Starting
    /// another prospective domain later grants no derivative through this discarded one.
    pub fn end_held_contact_variation(&mut self) -> Option<crate::hnn::word::variation::VariationReading> {
        self.held_contact_variation.take().map(|held| held.reading().clone())
    }

    pub(crate) fn admit_receiving_view(&self, field: &Field) -> Result<(), HnnError> {
        if field != &self.field || self.opens != Opens::OnMotion {
            return Err(HnnError::Unadmitted {
                reason: "a physical receiving view keeps the same field and continuing admitted future",
            });
        }
        Ok(())
    }

    pub(crate) fn admit_receiving_chart(&self, chart: &Encoded) -> Result<(), HnnError> {
        if !chart.is_empty() || self.receiving_chart.as_ref().is_some_and(|old| old != chart) {
            return Err(HnnError::Unadmitted {
                reason: "the receiving view keeps the complete cell-free producing chart",
            });
        }
        Ok(())
    }

    pub(crate) fn receiving_chart(&self) -> Option<&Encoded> { self.receiving_chart.as_ref() }

    /// Publish an actual affine observer translation at the already published blind crossing.
    /// It executes no second Word and preserves every current/tangent value and clock.
    /// The receiving-only consumer supplies native deposited material; the full propagation
    /// and canonical-state equality is checked before its exceptional publication is admitted.
    pub(crate) fn publish_receiving_translation(
        &mut self, material:Constitution, point:HolonState<ReceptionCarry>, chart:&Encoded,
    ) -> Result<Option<crate::hnn::word::variation::VariationReading>,HnnError> {
        if self.carried.as_ref()!=Some(&point.configuration) {
            return Err(HnnError::Unadmitted {
                reason:"an observer translation keeps the already executed full blind current",
            });
        }
        let old_ops = crate::hnn::propagation::Operands::exact_at_cut(&self.field,&self.constitution,&self.current)?;
        let new_ops = crate::hnn::propagation::Operands::exact_at_cut(&self.field,&material,&self.current)?;
        if old_ops != new_ops
            || crate::hnn::word::PowerForm::read(&self.field,&self.constitution,&self.current)?
                != crate::hnn::word::PowerForm::read(&self.field,&material,&self.current)?
        {
            return Err(HnnError::Unadmitted {
                reason:"an observer translation changes no producing propagation or physical power form",
            });
        }
        let variation = self.held_contact_variation.as_ref().map(|held|
            held.rebound_receiving(&self.field,&self.current,&material,&point.configuration)
        ).transpose()?;
        let reading = variation.as_ref().map(|held| held.reading().clone());
        self.publish_reception_with_variation_kind(Some(material),point,None,None,chart,variation,true)?;
        Ok(reading)
    }

    /// The native return publishes a library Holon point, with its real producing commit.
    /// This is the wave/descriptor configuration chart; it is not a proof that the continuous
    /// Field::holarchy storage chart includes the arriving-wave delay coordinates (#62).
    ///
    /// All fallible reads use detached candidate charts/ledger. A receiving-view code length is
    /// never added to the Reference ledger: only its one bounded Arrived operand is reread there.
    pub(crate) fn publish_reception(
        &mut self,
        material: Option<Constitution>,
        point: HolonState<ReceptionCarry>,
        charts: Option<Charts>,
        error: Option<EndChange>,
        chart: &Encoded,
    ) -> Result<(), HnnError> {
        self.publish_reception_with_variation(material,point,charts,error,chart,None)
    }

    pub(crate) fn publish_reception_with_variation(
        &mut self,
        material: Option<Constitution>,
        point: HolonState<ReceptionCarry>,
        charts: Option<Charts>,
        error: Option<EndChange>,
        chart: &Encoded,
        variation: Option<crate::hnn::word::variation::HeldContactVariation>,
    ) -> Result<(), HnnError> {
        self.publish_reception_with_variation_kind(material,point,charts,error,chart,variation,false)
    }

    fn publish_reception_with_variation_kind(
        &mut self,
        material: Option<Constitution>,
        point: HolonState<ReceptionCarry>,
        charts: Option<Charts>,
        error: Option<EndChange>,
        chart: &Encoded,
        variation: Option<crate::hnn::word::variation::HeldContactVariation>,
        receiving_translation:bool,
    ) -> Result<(), HnnError> {
        self.admit_receiving_chart(chart)?;
        // The invariant belongs to this owner even when a future caller omits its preflight.
        // No unimplemented transport/absorption can silently turn a nonzero box into an exact
        // point. A supported charted producer returns its new box explicitly.
        if error.is_none() { self.admit_exact_current_point()?; }
        let next = material.unwrap_or_else(|| self.constitution.clone());
        match (&self.held_contact_variation,&variation) {
            (None,None) => {},
            (Some(old),Some(new)) if error.is_none()
                && (receiving_translation || next == self.constitution || old.action()==
                    crate::hnn::word::variation::ContactVariationAction::RealizedFactorTranslation)
                && new.matches(&next,&point.configuration)
                && new.coordinates() == old.coordinates()
                && new.action() == old.action()
                && (if receiving_translation { old.reading().words==new.reading().words }
                    else { old.reading().words.checked_add(1)==Some(new.reading().words) }) => {},
            _ => return Err(HnnError::Unadmitted {
                reason:"publication must transport/rebase the held differential at its actual material, clock and parameter identity",
            }),
        }
        if point.commit != next.commit() || !point.configuration.fits(&self.field) {
            return Err(HnnError::ContinuingState {
                what: "the returned Holon point and its producing material/field",
            });
        }
        let carry = &point.configuration;
        for (a, state) in carry.change.states.iter().enumerate() {
            let factor = FieldMaterial::contact_storage(&next, a);
            let capacity = factor.multiply(&factor.transpose()?)?;
            if capacity.apply(&state[1])? != carry.momenta[a] {
                return Err(HnnError::HeldMomentum { contact: a });
            }
            let exponent = contact_exponent(&self.field, a, self.current.lift())?;
            if exponent.phase != 0 ||
                power_of_two(&exponent.carry)? * self.field.contact(a).admittance() != carry.conductances[a]
            {
                return Err(HnnError::ContinuingState {
                    what: "the returned current keeps its actual port reference frame",
                });
            }
        }
        for (g, (state, momentum)) in carry.change.resonators.iter()
            .zip(&carry.resonator_momenta).enumerate()
        {
            if let (Some([_, rate]), Some(momentum)) = (state, momentum) {
                let resonator = next.resonator(g).ok_or(HnnError::Resonator {
                    ring: g, what: "a returned loaded current has its producing material",
                })?;
                if resonator.forms().0.apply(rate)? != *momentum {
                    return Err(HnnError::Resonator {
                        ring: g, what: "a returned loaded current keeps its canonical momentum",
                    });
                }
            }
        }
        if let Some(error) = &error {
            let shaped = ReceptionCarry { change: error.clone(), ..carry.clone() };
            if !shaped.fits(&self.field)
                || coefficients(error).any(|x| x < &Rat::zero())
                || error.resonator_phases != carry.change.resonator_phases {
                return Err(HnnError::ContinuingState {
                    what: "the current and nonnegative enclosure have the same native shape and pump frame",
                });
            }
        }
        let moved = next != self.constitution;
        if moved && self.stop.is_some() {
            return Err(HnnError::DepositsStopped { commit: self.constitution.commit() });
        }
        let mut next_charts = charts.unwrap_or_else(|| self.charts.clone());
        let mut next_tally = self.tally.clone();
        let mut next_ledger = self.ledger.clone();
        if moved {
            if let Some(arrived) = &self.arrived {
                let (reread, readings) = arrived.code_length(&self.field, &next, &mut next_charts)?;
                next_tally.read(&readings);
                next_ledger.deposit(reread)?;
            }
        }
        self.constitution = next;
        self.carried = Some(point.configuration);
        self.carried_error = error;
        self.held_contact_variation = variation;
        self.receiving_chart = Some(chart.clone());
        self.charts = next_charts;
        self.tally = next_tally;
        self.ledger = next_ledger;
        if moved { self.forget_kept_reads(); }
        Ok(())
    }

    pub(crate) fn carry_error_bits(&self) -> u64 {
        self.carried_error.as_ref().map_or(0, |e| coefficients(e)
            .filter(|x| !x.is_zero()).map(|x| x.numer().bits() + x.denom().bits()).sum())
    }

    /// A native receiver stages its chart operations before publication.
    pub(crate) fn reception_charts(&self) -> Charts { self.charts.clone() }
}

impl Reference {
    /// Construct the common resident on an explicitly declared receiving opening.
    /// This is the existing mount/continued-mount law, including its gluing and shape checks.
    pub(crate) fn mount_receiving(
        field: &Field, current: &Current, material: Constitution, opening: WordOpening,
    ) -> Result<Resident, HnnError> {
        let reference = Self::campaign_one();
        match opening {
            WordOpening::Rest => reference.mount_with(field, current, material),
            WordOpening::Received { carry, absorption: Absorption::Nothing } =>
                reference.mount_carried(field, current, material, carry),
            WordOpening::Received { .. } => Err(HnnError::Unadmitted {
                reason: "this receiving view admits the continuing opening without absorption",
            }),
        }
    }
}
