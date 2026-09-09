//! Cold, source-qualified finite-response comparison. This is an exact rational observer,
//! not a native update or a choice of one source from its retained uncertainty family.
use super::*;
use crate::ExactInterval;
use num_traits::{Signed, Zero};

#[derive(Debug, Serialize)]
pub struct NativeFiniteMaterialResponse {
    pub outgoing: NativeFieldCurrentBall,
    pub material: NativeFieldCurrentBall,
    /// Observed minus predicted, with both complex quadratures retained.
    pub difference: NativeFieldCurrentBall,
    pub half_squared_difference: ExactInterval,
}

#[derive(Debug, Serialize)]
pub struct NativeMaterialContactStepComparison {
    pub source: NativeFieldLineage,
    pub receiving: NativeFieldLineage,
    pub application_cut: usize,
    pub realization: NativeContactRealization,
    pub gradient_metric: NativeMaterialPullbackMetric,
    pub producing_contacts: usize,
    pub current_contacts: usize,
    pub source_input: NativeFieldCurrentBall,
    /// Actual entering source current, extended by zero at contacts born afterwards.
    /// This declared diagnostic excitation does not reset the continuing ecology's interior.
    pub internal_input: NativeFieldCurrentBall,
    pub observed: NativeFieldCurrentBall,
    pub original_material: NativeFieldCurrentBall,
    /// All three comparisons use the CURRENT material operator, with its retained radius.
    pub producing_contacts_with_current_material: NativeFiniteMaterialResponse,
    pub before: NativeFiniteMaterialResponse,
    pub after: NativeFiniteMaterialResponse,
    pub strictly_improves: bool,
    pub strictly_worsens: bool,
}

fn l1(values: &[ExactComplexWaveCurrent]) -> Rat {
    values
        .iter()
        .map(|v| v.real.abs() + v.imaginary.abs())
        .sum()
}

fn evaluate(
    contacts: &NativeOperativeContactReading,
    source: &NativeFieldCurrentBall,
    internal: &NativeFieldCurrentBall,
    material: &NativeFieldMaterialTransportState,
    observed: &NativeFieldCurrentBall,
) -> Result<NativeFiniteMaterialResponse, Error> {
    let input = &internal.center[..contacts.contacts.len()];
    let exact = PairedJunctionLinearization::at(contacts.contacts.clone(), &source.center, input)
        .map_err(|e| Error::Arithmetic(e.to_string()))?;
    // The paired scattering operator is unitary. Its map variation is bounded by 2||delta D||,
    // via the two resolvents of the skew-adjoint block I+[0,-D;D†,0], each of norm at most one.
    let output_radius = &source.radius
        + &internal.radius
        + Rat::from_integer(2.into())
            * &contacts.contacts_radius
            * (l1(&source.center) + l1(input));
    let outgoing = NativeFieldCurrentBall {
        center: exact.outgoing().to_vec(),
        radius: output_radius,
    };
    project_material(outgoing, material, observed)
}

fn project_material(
    outgoing: NativeFieldCurrentBall,
    material: &NativeFieldMaterialTransportState,
    observed: &NativeFieldCurrentBall,
) -> Result<NativeFiniteMaterialResponse, Error> {
    let matrix_norm: Rat = material.coefficients.iter().map(|row| l1(row)).sum();
    let predicted = NativeFieldCurrentBall {
        center: material
            .coefficients
            .iter()
            .map(|row| {
                row.iter()
                    .zip(&outgoing.center)
                    .fold(ExactComplexWaveCurrent::zero(), |sum, (m, x)| {
                        sum.add(&m.multiply(x))
                    })
            })
            .collect(),
        radius: &material.radius * l1(&outgoing.center)
            + (matrix_norm + &material.radius) * &outgoing.radius,
    };
    let difference = NativeFieldCurrentBall {
        center: observed
            .center
            .iter()
            .zip(&predicted.center)
            .map(|(y, z)| y.subtract(z))
            .collect(),
        radius: &observed.radius + &predicted.radius,
    };
    let square: Rat = difference
        .center
        .iter()
        .map(ExactComplexWaveCurrent::norm_square)
        .sum();
    let cross = Rat::from_integer(2.into()) * l1(&difference.center) * &difference.radius;
    let two = Rat::from_integer(2.into());
    let interval = ExactInterval::new(
        (&square - &cross).max(Rat::zero()) / &two,
        (&square + &cross + &difference.radius * &difference.radius) / two,
    )
    .map_err(|e| Error::Arithmetic(e.to_string()))?;
    Ok(NativeFiniteMaterialResponse {
        outgoing,
        material: predicted,
        difference,
        half_squared_difference: interval,
    })
}

#[derive(Debug, Serialize)]
pub struct NativeRetainedMaterialRelation {
    pub source: NativeFieldLineage,
    pub receiving: NativeFieldLineage,
    pub inspection_cut: usize,
    pub observed: NativeFieldCurrentBall,
    pub original_material: NativeFieldCurrentBall,
    pub current: NativeFiniteMaterialResponse,
}

impl<'c> NativeConstitutiveField<'c> {
    /// Read the current material operator on the original retained outgoing source family.
    /// This checks retention in that operator; it does not reenact the whole ecology or select
    /// one current from the source family. No relation or occurrence is added.
    pub fn inspect_retained_material_relation(
        &self,
        receiving: usize,
    ) -> Result<NativeRetainedMaterialRelation, Error> {
        if self.material_transport_source() != Some(NativeMaterialTransportSource::OperativeLinear)
        {
            return Err(Error::Rest(
                "material retention comparison requires the operative linear chart".into(),
            ));
        }
        let event = self
            .history
            .get(receiving)
            .ok_or(Error::ForeignOccurrence)?;
        let source = event
            .lineage
            .observed_source()
            .ok_or(Error::ForeignOccurrence)?;
        let source_lineage = &self.history[source].lineage;
        if source_lineage.frame != self.frame.view.ordinal {
            return Err(Error::Rest(
                "material retention comparison requires a common source/current frame".into(),
            ));
        }
        let outgoing = self
            .inspect_operative_reflection(source)?
            .ok_or(Error::Uncertain)?
            .outgoing;
        let observed = self
            .inspect_material_transport(receiving)?
            .ok_or(Error::Uncertain)?
            .observed;
        let original_material = self
            .inspect_material_transport(source)?
            .ok_or(Error::Uncertain)?
            .forward;
        let matrix = self
            .inspect_material_transport_state()?
            .ok_or(Error::Uncertain)?;
        Ok(NativeRetainedMaterialRelation {
            source: source_lineage.clone(),
            receiving: event.lineage.clone(),
            inspection_cut: self.history.len(),
            current: project_material(outgoing, &matrix, &observed)?,
            observed,
            original_material,
        })
    }

    /// Inspect the actual staged deposit at a declared replay of its retained source excitation.
    /// The old source input is extended by zero at later contacts; current material is held fixed.
    /// Complete error families are bounded, while exact rational centres are reference calculations.
    /// No occurrence, source capability, coefficient or continuing current is changed.
    pub fn inspect_material_contact_step(
        &self,
        response: &NativeMaterialContactResponse<'c>,
        realization: NativeContactRealization,
    ) -> Result<NativeMaterialContactStepComparison, Error> {
        let returned = self.prepare_material_contact_return(response, realization)?;
        if self.material_transport_source() != Some(NativeMaterialTransportSource::OperativeLinear)
        {
            return Err(Error::Rest(
                "finite contact comparison currently requires the operative linear material chart"
                    .into(),
            ));
        }
        let source = response.query.source.occurrence;
        if response.query.source.frame != self.frame.view.ordinal {
            return Err(Error::Rest(
                "finite contact comparison requires a common source/current frame".into(),
            ));
        }
        let op = self.junction.as_ref().unwrap().operative.as_ref().unwrap();
        if source < op.activated_at {
            return Err(Error::ForeignOccurrence);
        }
        let surface = self.relation.surface;
        let read = |s: &ResidentSection<'c>| wides(&surface.detach_section(s, 64)?.intervals);
        let scale = BigInt::one() << op.grain;
        let rat = |x: i128| Rat::new(x.into(), scale.clone());
        let old_count = op
            .births
            .iter()
            .filter(|birth| birth.receiving < source)
            .count();
        let (input, input_bounds) = if source == op.activated_at {
            (op.initial.b.clone(), op.initial.bounds.clone())
        } else {
            self.history[source - 1].with_resident(surface, |h| {
                let state = h.operative.as_ref().ok_or(Error::Uncertain)?;
                Ok((state.b.clone(), state.bounds.clone()))
            })?
        };
        let input = read(&input)?;
        let mut internal = NativeFieldCurrentBall {
            center: input[..2 * old_count]
                .chunks_exact(2)
                .map(|v| ExactComplexWaveCurrent::new(rat(v[0]), rat(v[1])))
                .collect(),
            radius: rat(read(&input_bounds)?[1]),
        };
        // These returns occurred after the preceding emission and before this source entered.
        for deposit in op.returns.iter().filter(|r| r.at_cut == source) {
            if let Some(delta) = &deposit.b {
                for (value, delta) in internal.center.iter_mut().zip(read(delta)?.chunks_exact(2)) {
                    *value = value.add(&ExactComplexWaveCurrent::new(rat(delta[0]), rat(delta[1])));
                }
            }
            internal.radius += rat(read(&deposit.bounds)?[1]);
        }
        internal
            .center
            .resize(op.births.len(), ExactComplexWaveCurrent::zero());
        let source_input = self
            .inspect_operative_reflection(source)?
            .ok_or(Error::Uncertain)?
            .source;
        let observed = self
            .inspect_material_transport(response.query.receiving.occurrence)?
            .ok_or(Error::Uncertain)?
            .observed;
        let original_material = self
            .inspect_material_transport(source)?
            .ok_or(Error::Uncertain)?
            .forward;
        let material = self
            .inspect_material_transport_state()?
            .ok_or(Error::Uncertain)?;
        let view = NativeOperativeContactStaging {
            field: self,
            origin: op.origin.clone(),
            grain: op.grain,
            births: op.births.clone(),
            sections: op.sections.clone(),
            returns: op.returns.clone(),
        };
        let proposed = view.stage_return(returned)?;
        let producing = super::super::inspect_sections(
            self,
            op.grain,
            &op.births[..response.query.contacts],
            &response._producing,
            0,
        )?;
        let before = evaluate(
            &view.inspect()?,
            &source_input,
            &internal,
            &material,
            &observed,
        )?;
        let after = evaluate(
            &proposed.inspect()?,
            &source_input,
            &internal,
            &material,
            &observed,
        )?;
        Ok(NativeMaterialContactStepComparison {
            source: response.query.source.clone(),
            receiving: response.query.receiving.clone(),
            application_cut: response.at_cut,
            realization,
            gradient_metric: response.query.metric(),
            producing_contacts: response.query.contacts,
            current_contacts: op.births.len(),
            original_material,
            observed: observed.clone(),
            producing_contacts_with_current_material: evaluate(
                &producing,
                &source_input,
                &internal,
                &material,
                &observed,
            )?,
            strictly_improves: after.half_squared_difference.upper
                < before.half_squared_difference.lower,
            strictly_worsens: after.half_squared_difference.lower
                > before.half_squared_difference.upper,
            source_input,
            internal_input: internal,
            before,
            after,
        })
    }
}
