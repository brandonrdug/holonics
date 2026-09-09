//! Exterior exact derivation over actually retained field passages. No native state is changed.
use super::*;
use crate::exact_linear::{ContextualFactorization, ExactRatMatrix};
use num_traits::{One, Zero};

#[derive(Debug, Serialize, PartialEq, Eq)]
pub enum NativeContextContrastStatus {
    DifferentSourceFaces,
    NoReturnedContrast,
    ZeroSourceNeedsFullRelation,
    ContextContrastCertifiedNonzero,
    ContextContrastUnresolved,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::embedding_fiber::ResidentReadout;
    #[test]
    #[ignore = "requires CUDA; source equality, pre-return context and oriented targets derive a lifted contrast without exact source inversion"]
    fn bounded_pair_agrees_with_exact_lift_and_keeps_context_chronology() {
        let readout = ResidentReadout::new().unwrap();
        let surface = ResidentSurface::on(&readout).unwrap();
        let seed = vec![NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        }];
        let mut body = NativeConstitutiveField::found_with_enclosed_junction(
            &surface,
            seed,
            ResidentGrain(72),
        )
        .unwrap();
        body.enable_material_transport_source(NativeMaterialTransportSource::HomogeneousMoment)
            .unwrap();
        let first = body
            .advance_resident(&mut NativeFieldOccurrence::entering(vec![
                NativePhaseCurrent::unit(),
            ]))
            .unwrap();
        let anchor = body.retain_source(&first.source).unwrap();
        for p in [
            NativePhaseCurrent::new(0, 1, 1).unwrap(),
            NativePhaseCurrent::new(-1, 0, 1).unwrap(),
            NativePhaseCurrent::new(-1, 0, 1).unwrap(),
        ] {
            body.advance_resident(&mut NativeFieldOccurrence::through_anchor(&anchor, vec![p]))
                .unwrap();
        }
        let before = body.census();
        let pair = body.inspect_contextual_pair([1, 2]).unwrap();
        assert_eq!(
            pair.status,
            NativeContextContrastStatus::ContextContrastCertifiedNonzero
        );
        assert_eq!(pair.source_occurrences, [0, 0]);
        assert_eq!(pair.context_occurrences, [0, 1]);
        assert_eq!(
            pair.returned_difference,
            vec![ExactComplexWaveCurrent::new(
                Rat::from_integer((-1).into()),
                Rat::from_integer((-1).into())
            )]
        );
        let exact = body.inspect_contextual_lift(&[1, 2]).unwrap();
        let ContextualFactorization::Lifted(l) = exact.factorization else {
            panic!("actual context must lift")
        };
        assert_eq!(l.demonstrated_context_rank, 1);
        let delta = exact
            .context
            .apply(&[Rat::from_integer((-1).into()), Rat::one()])
            .unwrap();
        assert!(delta.iter().any(|x| !x.is_zero()));
        assert_eq!(
            body.inspect_contextual_pair([2, 3]).unwrap().status,
            NativeContextContrastStatus::NoReturnedContrast
        );
        assert_eq!(body.occurrence_count(), 4);
        assert_eq!(body.census().deed_launches, before.deed_launches);
    }
}
#[derive(Debug, Serialize)]
pub struct NativeContextContrastInspection {
    pub receiving_occurrences: [usize; 2],
    pub source_occurrences: [usize; 2],
    pub context_occurrences: [usize; 2],
    /// Oriented passage combination: second minus first, never a source identity.
    pub occurrence_combination: [i64; 2],
    pub source_difference: Vec<ExactComplexWaveCurrent>,
    pub returned_difference: Vec<ExactComplexWaveCurrent>,
    /// Original generating expressions and separate uncertainty; no exact context is selected.
    pub context_expressions: [NativeCurrentHistorySourceReading; 2],
    pub numerical_context_difference_norm_square: Rat,
    pub context_difference_error: Rat,
    pub status: NativeContextContrastStatus,
}

#[derive(Debug, Serialize)]
pub struct NativeContextualLiftInspection {
    pub receiving_occurrences: Vec<usize>,
    pub source_occurrences: Vec<usize>,
    pub context_occurrences: Vec<usize>,
    pub internal_births: Vec<usize>,
    pub source: ExactRatMatrix,
    pub context: ExactRatMatrix,
    pub returned: ExactRatMatrix,
    pub factorization: ContextualFactorization,
}
fn invalid(e: impl std::fmt::Display) -> ConstitutiveFibreError {
    ConstitutiveFibreError::Rest(format!("contextual lift inspection: {e}"))
}
fn real_columns(
    columns: &[Vec<ExactComplexWaveCurrent>],
) -> Result<ExactRatMatrix, ConstitutiveFibreError> {
    // Both quadratures are preserved; the hypothesis is rational-real local linearity.
    // No imaginary multiple is relabelled as an additional observed occurrence.
    let rows = columns.first().map_or(0, |c| 2 * c.len());
    let values = columns
        .iter()
        .map(|c| {
            c.iter()
                .flat_map(|z| [z.real.clone(), z.imaginary.clone()])
                .collect::<Vec<_>>()
        })
        .collect();
    ExactRatMatrix::shaped(columns.len(), rows, values)
        .and_then(|v| v.transpose())
        .map_err(invalid)
}
impl NativeConstitutiveField<'_> {
    /// Two actual observations with a common nonzero source have a one-dimensional source
    /// kernel. If their bounded context difference excludes zero, each compatible actual
    /// context admits D(alpha*(c1-c0))=alpha*(y1-y0). The unknown context and all other map
    /// directions remain free. This exterior check needs no exact historical-current inverse.
    pub fn inspect_contextual_pair(
        &self,
        receiving: [usize; 2],
    ) -> Result<NativeContextContrastInspection, ConstitutiveFibreError> {
        if !self.relation.usable || self.pending.is_some() {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        if receiving[0] >= receiving[1] {
            return Err(ConstitutiveFibreError::Shape);
        }
        let source = receiving.map(|at| self.history.get(at).and_then(|h| h.lineage.observed_source()));
        let [Some(s0), Some(s1)] = source else {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        };
        let contexts = [
            receiving[0]
                .checked_sub(1)
                .ok_or(ConstitutiveFibreError::ForeignOccurrence)?,
            receiving[1] - 1,
        ];
        let read = |at| -> Result<NativeCurrentHistorySourceReading, ConstitutiveFibreError> {
            match self.material_transport_source() {
                Some(NativeMaterialTransportSource::HomogeneousMoment) => self
                    .inspect_moment_material_transport(at)?
                    .map(|r| r.source)
                    .ok_or_else(|| invalid("missing moment source")),
                Some(NativeMaterialTransportSource::Contextual | NativeMaterialTransportSource::BilinearContextual) => self
                    .inspect_contextual_material_transport(at)?
                    .and_then(|r| r.context)
                    .ok_or_else(|| invalid("missing contextual source")),
                Some(NativeMaterialTransportSource::CompleteCurrent) => self
                    .inspect_complete_material_transport(at)?
                    .map(|r| r.numerical_source)
                    .ok_or_else(|| invalid("missing complete source")),
                _ => Err(invalid("retained complete-source expression required")),
            }
        };
        let a = read(contexts[0])?;
        let b = read(contexts[1])?;
        let square = &a.numerical_norm_square + &b.numerical_norm_square
            - a.numerical_pairing(&b).real * Rat::from_integer(2.into());
        if square < Rat::zero() {
            return Err(invalid("negative numerical contrast norm"));
        }
        let error = &a.source_radius + &b.source_radius;
        let source0 = self.root_junction_source(s0)?;
        let source1 = self.root_junction_source(s1)?;
        let source_difference = source1
            .iter()
            .zip(&source0)
            .map(|(b, a)| b.subtract(a))
            .collect::<Vec<_>>();
        let target0 = self.inspect_incoming(receiving[0])?;
        let target1 = self.inspect_incoming(receiving[1])?;
        let returned_difference = target1
            .iter()
            .zip(target0)
            .map(|(b, a)| b.current().subtract(&a.current()))
            .collect::<Vec<_>>();
        let nonzero = |v: &ExactComplexWaveCurrent| v != &ExactComplexWaveCurrent::zero();
        let status = if source_difference.iter().any(nonzero) {
            NativeContextContrastStatus::DifferentSourceFaces
        } else if !returned_difference.iter().any(nonzero) {
            NativeContextContrastStatus::NoReturnedContrast
        } else if !source0.iter().any(nonzero) {
            NativeContextContrastStatus::ZeroSourceNeedsFullRelation
        } else if square > &error * &error {
            NativeContextContrastStatus::ContextContrastCertifiedNonzero
        } else {
            NativeContextContrastStatus::ContextContrastUnresolved
        };
        Ok(NativeContextContrastInspection {
            receiving_occurrences: receiving,
            source_occurrences: [s0, s1],
            context_occurrences: contexts,
            occurrence_combination: [-1, 1],
            source_difference,
            returned_difference,
            context_expressions: [a, b],
            numerical_context_difference_norm_square: square,
            context_difference_error: error,
            status,
        })
    }
    /// Derive S,C,Y from completed receiving occurrences. S is the original two-branch
    /// field source in its root chart; C is outgoing PLUS every born internal current in
    /// the receiving predecessor, before the incoming target arrives. Y is that actual incoming
    /// current. This contemporary relation never rewrites the original prediction. This cold decoder
    /// is never an ingress, learner, or replacement for a numerical enclosure in production.
    pub fn inspect_contextual_lift(
        &self,
        receiving_occurrences: &[usize],
    ) -> Result<NativeContextualLiftInspection, ConstitutiveFibreError> {
        if !self.relation.usable || self.pending.is_some() {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        if receiving_occurrences.is_empty()
            || receiving_occurrences.windows(2).any(|w| w[0] >= w[1])
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let sources = receiving_occurrences
            .iter()
            .map(|at| {
                self.history
                    .get(*at)
                    .and_then(|h| h.lineage.observed_source())
                    .ok_or(ConstitutiveFibreError::ForeignOccurrence)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let contexts = receiving_occurrences
            .iter()
            .map(|at| {
                at.checked_sub(1)
                    .ok_or(ConstitutiveFibreError::ForeignOccurrence)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let until = *contexts.iter().max().expect("nonempty contexts");
        let trace = self.decode_junction_residual_trace(until)?;
        let contacts = (0..=until)
            .filter(|at| self.history[*at].lineage.observed_source().is_some())
            .map(|at| {
                self.junction_contact(at)
                    .map(|d| (at, d.expect("linked contact")))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let mut source = Vec::new();
        let mut context = Vec::new();
        let mut returned = Vec::new();
        let zero = vec![ExactComplexWaveCurrent::zero(); 3 * self.nodes()];
        for ((&at, &source_at), &context_at) in
            receiving_occurrences.iter().zip(&sources).zip(&contexts)
        {
            source.push(self.root_junction_source(source_at)?);
            let mut x = trace[context_at].outgoing.clone();
            for (birth, d) in &contacts {
                if *birth > context_at {
                    x.push(ExactComplexWaveCurrent::zero());
                    continue;
                }
                let prior = if *birth == 0 {
                    &zero
                } else {
                    &trace[*birth - 1].potential_prefix
                };
                let mut b = ExactComplexWaveCurrent::zero();
                for ((d, now), before) in
                    d.iter().zip(&trace[context_at].potential_prefix).zip(prior)
                {
                    b = b.add(&d.conjugate().multiply(&now.subtract(before)));
                }
                x.push(b.scaled(
                    &(if context_at % 2 == 0 {
                        Rat::one()
                    } else {
                        -Rat::one()
                    }),
                ));
            }
            context.push(x);
            returned.push(
                self.inspect_incoming(at)?
                    .iter()
                    .map(|p| p.current())
                    .collect(),
            );
        }
        let source = real_columns(&source)?;
        let context = real_columns(&context)?;
        let returned = real_columns(&returned)?;
        let factorization = source
            .contextual_factorization(&context, &returned)
            .map_err(invalid)?;
        Ok(NativeContextualLiftInspection {
            receiving_occurrences: receiving_occurrences.to_vec(),
            source_occurrences: sources,
            context_occurrences: contexts,
            internal_births: contacts.iter().map(|(at, _)| *at).collect(),
            source,
            context,
            returned,
            factorization,
        })
    }
}
