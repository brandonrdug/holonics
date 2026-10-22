//! Smooth physical contact-ray bounds, separate from represented endpoint defects (Refs #62 #73).
//!
//! These bounds concern the unrounded physical relation at a fixed source/opening. They are
//! neither derivatives of chart selection nor an admission for a represented material update.
//! In particular, composing this envelope does not supply the missing represented defect floor.

use super::{EndChange, Word};
use crate::hnn::HnnError;
use crate::hnn::propagation::Operands;
use crate::holon::deposition::{schur_norms, sqrt_ceiling};
use crate::ratio::{Rat, linear::ExactRatMatrix};
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

fn int(n: usize) -> Rat {
    Rat::from_integer(BigInt::from(n))
}
fn square(x: &Rat) -> Rat {
    x * x
}
fn norm(m: &ExactRatMatrix) -> Rat {
    let (c, r) = schur_norms(m);
    sqrt_ceiling(&(c * r), 64)
}
pub(crate) fn vector_norm(v: &[Rat]) -> Rat {
    sqrt_ceiling(&v.iter().map(square).sum(), 64)
}
pub(crate) fn state_norm(o: &Operands, s: &EndChange) -> Result<Rat, HnnError> {
    if s.states.len() != o.contacts().len() || s.resonators.len() != o.resonators().len() {
        return Err(HnnError::Unadmitted {
            reason: "native ray norm keeps the complete contact/loaded shape",
        });
    }
    let mut power = s
        .storage
        .iter()
        .chain(s.arrivals.iter().flatten())
        .flatten()
        .map(square)
        .sum::<Rat>();
    for (s, c) in s.states.iter().zip(o.contacts()) {
        power += s[0]
            .iter()
            .map(|x| square(&(x / (o.step() * c.conductance()))))
            .sum::<Rat>();
        power += s[1]
            .iter()
            .map(|x| square(&(x / c.conductance())))
            .sum::<Rat>();
    }
    for (s, r) in s.resonators.iter().zip(o.resonators()) {
        match (s, r) {
            (Some(s), Some(r)) => {
                power += s[0]
                    .iter()
                    .map(|x| square(&(x / (o.step() * r.admittance()))))
                    .sum::<Rat>();
                power += s[1]
                    .iter()
                    .map(|x| square(&(x / r.admittance())))
                    .sum::<Rat>();
            }
            (None, _) => {}
            _ => {
                return Err(HnnError::Unadmitted {
                    reason: "native ray norm has no undeclared loaded state",
                });
            }
        }
    }
    Ok(sqrt_ceiling(&power, 64))
}

/// Finite scalar readings issued at the ACTUAL original intermediate, before its Word is
/// consumed. No direction, substitute state, Word tape or exterior source history is retained.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct OriginalContactStage {
    pub(crate) input_norm: Rat,
    pub(crate) input_error: Rat,
    pub(crate) solve_residual: Rat,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct OriginalPathStages {
    opening_norm: Rat,
    contacts: Vec<Vec<OriginalContactStage>>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct OriginalPairStages {
    declaration: std::sync::Arc<()>,
    lattice: crate::hnn::chart::WordLattice,
    opened_at: usize,
    full_ticks: usize,
    actual: OriginalPathStages,
    fresh: OriginalPathStages,
    physical_ticks: Vec<Rat>,
    fixed_ticks: Vec<Rat>,
}
impl OriginalPairStages {
    pub(crate) fn issue(word: &Word<'_>) -> Result<Self, HnnError> {
        let o = word.operands();
        if o.lattice().is_none()
            || word.native_declaration_id.is_none()
            || !word.source_returns().is_empty()
        {
            return Err(HnnError::Unadmitted {
                reason: "represented native ray stages require the original native no-World producing Word",
            });
        }
        let column = word.response().ok_or(HnnError::Unadmitted {
            reason: "native material stages require the same executed fresh path",
        })?;
        let original = word
            .response_opening_exact
            .as_ref()
            .ok_or(HnnError::Unadmitted {
                reason: "native ray keeps its complete decoded original opening",
            })?;
        let actual = super::trajectory::TrajectoryView::actual(word);
        let fresh =
            super::trajectory::TrajectoryView::column(word, &column.records, &column.resonances)?;
        let full = word
            .recorded()
            .len()
            .checked_sub(usize::from(word.is_ended()))
            .ok_or(HnnError::CountOverflow)?;
        let mut physical_ticks = Vec::with_capacity(full);
        let mut fixed_ticks = Vec::with_capacity(full);
        for t in 0..full {
            let (a, b) = crate::hnn::prediction::charted::ResponseTube::physical_tick_norms(
                o,
                word.opened_at() + t,
            )?;
            physical_ticks.push(a);
            fixed_ticks.push(b);
        }
        let issue_path = |view: &super::trajectory::TrajectoryView<'_, '_>,
                          exact: &EndChange,
                          end: &EndChange|
         -> Result<OriginalPathStages, HnnError> {
            let mut tube =
                crate::hnn::prediction::charted::ResponseTube::open(o, exact, &view.point(0)?)?;
            let mut contacts = Vec::with_capacity(full);
            for t in 0..full {
                let point = view.point(t)?;
                let record = &view.recorded()[t];
                contacts.push(tube.material_contact_stages(
                    &point,
                    &record.anchors,
                    &record.rates,
                )?);
                let after = if t + 1 < view.recorded().len() {
                    view.point(t + 1)?
                } else {
                    end.clone()
                };
                tube.advance(&point, &after, word.opened_at() + t)?;
                super::work::reached(super::work::Event::ResponseCertificateTick);
            }
            Ok(OriginalPathStages {
                opening_norm: state_norm(o, exact)?,
                contacts,
            })
        };
        let result = Self {
            declaration: word
                .native_declaration_id
                .clone()
                .expect("admitted native declaration"),
            lattice: *o.lattice().expect("admitted represented declaration"),
            opened_at: word.opened_at(),
            full_ticks: full,
            actual: issue_path(&actual, original, &word.end_change())?,
            fresh: issue_path(&fresh, column.original_opening(), &column.end)?,
            physical_ticks,
            fixed_ticks,
        };
        // These transient certificate operands share the existing finite native work extent.
        // They are not a new retained-state codec or an exemption from its input limits.
        let limit = super::action::NativeWorkBudget::V1;
        let mut total = 0u64;
        for q in result
            .actual
            .contacts
            .iter()
            .chain(&result.fresh.contacts)
            .flatten()
            .flat_map(|s| [&s.input_norm, &s.input_error, &s.solve_residual])
            .chain([&result.actual.opening_norm, &result.fresh.opening_norm])
            .chain(&result.physical_ticks)
            .chain(&result.fixed_ticks)
        {
            let bits = q
                .numer()
                .bits()
                .checked_add(q.denom().bits())
                .ok_or(HnnError::CountOverflow)?;
            total = total.checked_add(bits).ok_or(HnnError::CountOverflow)?;
            if q.numer().bits() > limit.integer_bits
                || q.denom().bits() > limit.integer_bits
                || total > limit.aggregate_bits
            {
                return Err(HnnError::Unadmitted {
                    reason: "native material-ray stage readings exceed their declared finite operand extent",
                });
            }
        }
        Ok(result)
    }
    pub(super) fn admit_declaration(
        &self,
        o: &Operands,
        id: &std::sync::Arc<()>,
    ) -> Result<(), HnnError> {
        // The private native declaration authenticated complete operands AND decoded opening
        // before execution. Keep that identity, without duplicating its entire matrix packet.
        if o.lattice() != Some(&self.lattice) || !std::sync::Arc::ptr_eq(&self.declaration, id) {
            return Err(HnnError::Unadmitted {
                reason: "native material stages cannot substitute another complete prepared opening or operator producer",
            });
        }
        Ok(())
    }
}

/// Upper bounds for a stage and its first two material derivatives on one declared closed ray.
/// All entries are Euclidean operator norms in the *same* normalized physical state chart.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct StageEnvelope {
    pub norm: Rat,
    pub first: Rat,
    pub second: Rat,
}
impl StageEnvelope {
    pub(super) fn identity() -> Self {
        Self {
            norm: Rat::one(),
            first: Rat::zero(),
            second: Rat::zero(),
        }
    }
    pub(super) fn fixed(norm: Rat) -> Result<Self, HnnError> {
        if norm < Rat::zero() {
            return Err(HnnError::Unadmitted {
                reason: "a fixed physical stage norm is nonnegative",
            });
        }
        Ok(Self {
            norm,
            first: Rat::zero(),
            second: Rat::zero(),
        })
    }
    /// Append a stage. The right sides all use the OLD envelope; no in-place recurrence aliasing.
    pub(super) fn then(&self, stage: &Self) -> Self {
        Self {
            norm: &stage.norm * &self.norm,
            first: &stage.norm * &self.first + &stage.first * &self.norm,
            second: &stage.norm * &self.second
                + int(2) * &stage.first * &self.first
                + &stage.second * &self.norm,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct FormEnvelope {
    value: Rat,
    first: Rat,
    second: Rat,
}
impl FormEnvelope {
    fn of(
        base: &ExactRatMatrix,
        direction: &ExactRatMatrix,
        eta_max: &Rat,
    ) -> Result<Self, HnnError> {
        if base.rows() != direction.rows()
            || base.columns() != direction.columns()
            || eta_max < &Rat::zero()
        {
            return Err(HnnError::Unadmitted {
                reason: "a Gram-factor envelope keeps one factor shape and a nonnegative declared ray extent",
            });
        }
        let v = norm(direction);
        let f = norm(base) + eta_max * &v;
        // F F* on F(eta)=F0+eta V. A signature is not silently admitted here: m>=I
        // below requires the actual positive Gram families of the physical contact.
        Ok(Self {
            value: square(&f),
            first: int(2) * &f * &v,
            second: int(2) * square(&v),
        })
    }
    fn domain(
        base: &ExactRatMatrix,
        extent: &ExactRatMatrix,
        direction: &ExactRatMatrix,
    ) -> Result<Self, HnnError> {
        if base.rows() != extent.rows() || base.columns() != extent.columns() {
            return Err(HnnError::Unadmitted {
                reason: "native physical ray extent has its original factor shape",
            });
        }
        let mut result = Self::of(base, direction, &Rat::zero())?;
        let v = norm(direction);
        let f = norm(base) + norm(extent);
        result.value = square(&f);
        result.first = int(2) * f * v;
        Ok(result)
    }
}

struct ContactEnvelope {
    stage: StageEnvelope,
    j: Rat,
    q0: Rat,
    q1: Rat,
    mu1: Rat,
}
impl ContactEnvelope {
    fn of(forms: [FormEnvelope; 3], h: &Rat, g: &Rat) -> Result<Self, HnnError> {
        if h <= &Rat::zero() || g <= &Rat::zero() {
            return Err(HnnError::NonpositiveDeclaration);
        }
        let [c, k, d] = forms;
        let mu = |c: &Rat, k: &Rat, d: &Rat| g / h * c + g / int(2) * d + g * h / int(4) * k;
        let q = |order: usize, c: &Rat, k: &Rat| {
            sqrt_ceiling(
                &(if order == 0 {
                    int(2) * square(h)
                } else {
                    Rat::zero()
                } + square(&square(h)) * square(g) * square(k)
                    + int(4) * square(g) * square(c)),
                64,
            )
        };
        let q0 = q(0, &c.value, &k.value);
        let q1 = q(1, &c.first, &k.first);
        let q2 = q(2, &c.second, &k.second);
        let mu1 = mu(&c.first, &k.first, &d.first);
        let mu2 = mu(&c.second, &k.second, &d.second);
        let j = sqrt_ceiling(&(int(13) / (int(4) * square(h))), 64);
        let stage = StageEnvelope {
            norm: Rat::one() + &j * &q0,
            first: &j * (&mu1 * &q0 + &q1),
            second: &j * ((int(2) * square(&mu1) + mu2) * &q0 + int(2) * &mu1 * &q1 + q2),
        };
        Ok(Self {
            stage,
            j,
            q0,
            q1,
            mu1,
        })
    }
    fn forcing_error(&self, chi: &Rat, point: &OriginalContactStage) -> Rat {
        &self.j * chi * (&self.q1 + (int(2) + chi) * &self.mu1 * &self.q0) * &point.input_norm
            + &self.j * (Rat::one() + chi) * &self.mu1 * &point.solve_residual
    }
}

/// The transit owner's exact decomposition, in z=(alpha_g,alpha_h,u/(hG),w/G):
/// L=D0+J m^-1 P, P=[hI,-hI,-h²GK,2GC], ||J||²=13/(4h²).
/// This is a pure certificate calculation, not a second transit or a native operation.
pub(super) fn contact_envelope(
    base: [&ExactRatMatrix; 3],
    direction: [&ExactRatMatrix; 3],
    eta_max: &Rat,
    h: &Rat,
    g: &Rat,
) -> Result<StageEnvelope, HnnError> {
    if h <= &Rat::zero() || g <= &Rat::zero() {
        return Err(HnnError::Unadmitted {
            reason: "a physical contact-ray envelope keeps positive producing hop and conductance",
        });
    }
    let forms = [
        FormEnvelope::of(base[0], direction[0], eta_max)?,
        FormEnvelope::of(base[1], direction[1], eta_max)?,
        FormEnvelope::of(base[2], direction[2], eta_max)?,
    ];
    // Positive Gram C/K/D imply m>=I uniformly; no chart inverse or rounded endpoint
    // is used as a substitute for this physical inverse bound.
    Ok(ContactEnvelope::of(forms, h, g)?.stage)
}

/// One queried direction on the original factor chart. `extent` is the jointly declared
/// range of ALL factors; it never changes the material tangent's zero held opening.
pub(crate) type ContactDirections = Vec<[ExactRatMatrix; 3]>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PhysicalRayReading {
    pub stored_pairing: Rat,
    pub surrogate_pairing: Rat,
    pub reverse_discrepancy: Rat,
    pub class_error_charge: Rat,
    pub response_error_charge: Rat,
    pub lower: Rat,
    pub response_squared: Rat,
    pub tangent_queries: usize,
    /// Actual/fresh stage error norms before and after local forcing. Exterior evidence only.
    pub stage_error_norms: Vec<(bool, usize, Rat, Rat)>,
    pub surrogate_response: Vec<Vec<Rat>>,
    pub response_component_error: Vec<Vec<Rat>>,
}
impl PhysicalRayReading {
    fn values(&self) -> impl Iterator<Item = &Rat> {
        [
            &self.stored_pairing,
            &self.surrogate_pairing,
            &self.reverse_discrepancy,
            &self.class_error_charge,
            &self.response_error_charge,
            &self.lower,
            &self.response_squared,
        ]
        .into_iter()
        .chain(
            self.stage_error_norms
                .iter()
                .flat_map(|(_, _, a, b)| [a, b]),
        )
        .chain(self.surrogate_response.iter().flatten())
        .chain(self.response_component_error.iter().flatten())
    }
}
/// This transient proof owns only scalar original-stage readings and the ALREADY returned
/// per-contact original u/w/midpoint operands. It owns no Word, new observation or state history.
#[derive(Clone, Debug)]
pub(crate) struct PhysicalContactProof {
    stages: OriginalPairStages,
    actual: Vec<Vec<OriginalPrimalTransit>>,
    fresh: Vec<Vec<OriginalPrimalTransit>>,
    reads: Vec<(Vec<Rat>, Vec<Rat>)>,
    errors: Vec<Vec<Rat>>,
    cache: std::sync::Arc<std::sync::Mutex<Vec<(ContactDirections, PhysicalRayReading)>>>,
}
#[derive(Clone, Debug)]
struct OriginalPrimalTransit {
    tick: usize,
    displacement: Vec<Rat>,
    rate: Vec<Rat>,
    midpoint: Vec<Rat>,
}
impl PhysicalContactProof {
    pub(crate) fn issue(
        o: &Operands,
        stages: &OriginalPairStages,
        back: &crate::hnn::port::WordReturn,
        errors: &[Vec<Rat>],
    ) -> Result<Self, HnnError> {
        if back.transits.len() != o.contacts().len() {
            return Err(HnnError::Unadmitted {
                reason: "native physical proof has every original contact return",
            });
        }
        let mut actual = Vec::new();
        let mut fresh = Vec::new();
        let n = stages.full_ticks;
        // Preflight every copied operand BEFORE clones. The already-reconciled reverse
        // cotangents need not be duplicated: only their original primal u/w/omega are used.
        admit_extent(
            back.transits
                .iter()
                .flatten()
                .flat_map(|t| t.displacement.iter().chain(&t.rate).chain(&t.midpoint))
                .chain(back.reads.iter().flat_map(|(f, g)| f.iter().chain(g)))
                .chain(errors.iter().flatten()),
        )?;
        for returned in &back.transits {
            if returned.len() != n.checked_mul(2).ok_or(HnnError::CountOverflow)? {
                return Err(HnnError::Unadmitted {
                    reason: "native physical proof preserves two separately labeled original return lanes",
                });
            }
            let (a, f) = returned.split_at(n);
            for lane in [a, f] {
                if lane
                    .iter()
                    .map(|t| t.tick)
                    .collect::<std::collections::BTreeSet<_>>()
                    != (0..n).collect()
                {
                    return Err(HnnError::Unadmitted {
                        reason: "native material tangent keeps each original absolute stage order",
                    });
                }
            }
            let copied = |lane: &[crate::hnn::port::TransitTick]| {
                lane.iter()
                    .map(|t| OriginalPrimalTransit {
                        tick: t.tick,
                        displacement: t.displacement.clone(),
                        rate: t.rate.clone(),
                        midpoint: t.midpoint.clone(),
                    })
                    .collect()
            };
            actual.push(copied(a));
            fresh.push(copied(f));
        }
        Ok(Self {
            stages: stages.clone(),
            actual,
            fresh,
            reads: back.reads.clone(),
            errors: errors.to_vec(),
            cache: std::sync::Arc::new(std::sync::Mutex::new(Vec::new())),
        })
    }
    fn directions(
        o: &Operands,
        theta: &crate::hnn::constitution::Constitution,
        d: &ContactDirections,
    ) -> Result<(), HnnError> {
        use crate::hnn::field::ConstitutionRead;
        if d.len() != o.contacts().len() {
            return Err(HnnError::Unadmitted {
                reason: "native material ray keeps every original contact",
            });
        }
        for (a, (c, d)) in o.contacts().iter().zip(d).enumerate() {
            if theta
                .contact_stiffness_signature(a)
                .is_some_and(|s| s.iter().any(|s| !s))
            {
                return Err(HnnError::Unadmitted {
                    reason: "represented physical native ray admits ordinary positive Gram contact factors only",
                });
            }
            let bases = [
                theta.contact_storage(a),
                theta.contact_stiffness(a),
                theta.contact_dissipation(a),
            ];
            for (b, v) in bases.iter().zip(d) {
                if b.rows() != v.rows() || b.columns() != v.columns() || b.rows() != c.width() {
                    return Err(HnnError::Unadmitted {
                        reason: "native factor direction has its original admitted Gram chart",
                    });
                }
            }
        }
        Ok(())
    }
    /// Arm A: physical-reference derivative at the original fixed opening, paired with the
    /// ORIGINAL represented return. Neither endpoint rounding nor an unsplit teacher is inferred.
    pub(crate) fn query(
        &self,
        witness: &super::native_prediction::NativeContactWitness,
        o: &Operands,
        direction: &ContactDirections,
        extent: &ContactDirections,
        eps: &[Vec<Rat>],
    ) -> Result<PhysicalRayReading, HnnError> {
        use crate::hnn::field::ConstitutionRead;
        let theta = &witness.producing;
        super::work::reached(super::work::Event::MaterialRayQuery);
        Self::directions(o, theta, direction)?;
        Self::directions(o, theta, extent)?;
        if self.stages.opened_at != witness.opened_at
            || witness.reads != self.reads
            || eps != self.errors
            || witness.reads.len() != eps.len()
            || eps.iter().any(|e| e.iter().any(|e| e < &Rat::zero()))
        {
            return Err(HnnError::Unadmitted {
                reason: "physical native query retains original cut, station order and return error",
            });
        }
        let map =
            theta
                .receiving_map(witness.phases.ring())
                .ok_or(HnnError::MissingReceivingMap {
                    ring: witness.phases.ring(),
                })?;
        let width = o.rings()[witness.phases.ring()].width();
        if map.columns() != 2 * width
            || witness
                .reads
                .iter()
                .zip(eps)
                .any(|((_, g), e)| g.len() != map.rows() || e.len() * 2 != g.len())
        {
            return Err(HnnError::Unadmitted {
                reason: "native physical query includes all paired real/phase rows",
            });
        }
        admit_extent(
            direction
                .iter()
                .chain(extent)
                .flatten()
                .flat_map(|m| m.entries()),
        )?;
        let cached = self
            .cache
            .lock()
            .map_err(|_| HnnError::Unadmitted {
                reason: "native immutable ray cache is available",
            })?
            .iter()
            .find(|(d, _)| d == direction)
            .map(|(_, r)| r.clone());
        if let Some(mut reading) = cached {
            reading.response_squared = self.uniform_response(witness, o, direction, extent)?;
            reading.tangent_queries = 0;
            return Ok(reading);
        }
        let bases = (0..o.contacts().len())
            .map(|a| {
                [
                    theta.contact_storage(a),
                    theta.contact_stiffness(a),
                    theta.contact_dissipation(a),
                ]
            })
            .collect::<Vec<_>>();
        let point_envelopes = bases
            .iter()
            .zip(direction)
            .zip(o.contacts())
            .map(|((b, v), c)| {
                ContactEnvelope::of(
                    [
                        FormEnvelope::of(b[0], &v[0], &Rat::zero())?,
                        FormEnvelope::of(b[1], &v[1], &Rat::zero())?,
                        FormEnvelope::of(b[2], &v[2], &Rat::zero())?,
                    ],
                    o.step(),
                    c.conductance(),
                )
            })
            .collect::<Result<Vec<_>, HnnError>>()?;
        let forms = bases
            .iter()
            .zip(direction)
            .map(|(b, v)| {
                let form = |i: usize| -> Result<ExactRatMatrix, HnnError> {
                    Ok(b[i]
                        .multiply(&v[i].transpose()?)?
                        .add(&v[i].multiply(&b[i].transpose()?)?)?)
                };
                Ok([form(0)?, form(1)?, form(2)?])
            })
            .collect::<Result<Vec<_>, HnnError>>()?;
        let run =
            |path: &OriginalPathStages,
             records: &[Vec<OriginalPrimalTransit>]|
             -> Result<(Vec<(Vec<Rat>, Vec<Rat>)>, Vec<(usize, Rat, Rat)>), HnnError> {
                let mut tangent = zero_state(o, self.stages.opened_at);
                let mut tube =
                    crate::hnn::prediction::charted::ResponseTube::open(o, &tangent, &tangent)?;
                let mut out = Vec::new();
                let mut trace = Vec::new();
                for t in 0..=self.stages.full_ticks {
                    let junction = super::linear::junctions(o, &tangent)?;
                    if witness.phases.epochs().any(|j| j == t) {
                        let centers = junction
                            .iter()
                            .map(|j| j.anchor.clone())
                            .collect::<Vec<_>>();
                        let local = tube.anchors(&tangent, &centers)?;
                        out.push((
                            centers[witness.phases.ring()].clone(),
                            local[witness.phases.ring()].clone(),
                        ));
                    }
                    if t == self.stages.full_ticks {
                        break;
                    }
                    let mut next = super::linear::tick(o, &tangent, self.stages.opened_at + t)?;
                    tube.advance(&tangent, &next, self.stages.opened_at + t)?;
                    let hom = state_norm(o, tube.radius())?;
                    for (a, c) in o.contacts().iter().enumerate() {
                        if direction[a]
                            .iter()
                            .all(|m| m.entries().iter().all(Zero::is_zero))
                        {
                            continue;
                        }
                        let record = records[a].iter().find(|r| r.tick == t).ok_or(
                            HnnError::Unadmitted {
                                reason: "native tangent forcing uses the original returned stage",
                            },
                        )?;
                        let (f, to) = c.ends();
                        let zf = vec![Rat::zero(); o.rings()[f].width()];
                        let zt = vec![Rat::zero(); o.rings()[to].width()];
                        let zs = vec![Rat::zero(); c.width()];
                        let forced = crate::hnn::propagation::transit_variation(
                            c,
                            o.step(),
                            &zf,
                            &zt,
                            &zs,
                            &zs,
                            &record.displacement,
                            &record.rate,
                            &record.midpoint,
                            &forms[a],
                        )?;
                        for (x, d) in next.arrivals[a][0].iter_mut().zip(forced.arrive_from) {
                            *x += d;
                        }
                        for (x, d) in next.arrivals[a][1].iter_mut().zip(forced.arrive_to) {
                            *x += d;
                        }
                        for (x, d) in next.states[a][0].iter_mut().zip(forced.displacement) {
                            *x += d;
                        }
                        for (x, d) in next.states[a][1].iter_mut().zip(forced.rate) {
                            *x += d;
                        }
                        let chi = sqrt_ceiling(&int(c.width()), 64)
                            * c.chart().map_or_else(Rat::zero, |c| c.certificate.clone());
                        let stage = &path.contacts[t][a];
                        let e = &point_envelopes[a].stage.first * &stage.input_error
                            + point_envelopes[a].forcing_error(&chi, stage);
                        tube.add_material_contact_error(a, &e)?;
                    }
                    trace.push((t, hom, state_norm(o, tube.radius())?));
                    tangent = next;
                    super::work::reached(super::work::Event::MaterialRayTick);
                }
                Ok((out, trace))
            };
        let (actual, actual_trace) = run(&self.stages.actual, &self.actual)?;
        let (fresh, fresh_trace) = run(&self.stages.fresh, &self.fresh)?;
        if actual.len() != witness.reads.len() || fresh.len() != actual.len() {
            return Err(HnnError::Unadmitted {
                reason: "physical ray reads every original receiving station once",
            });
        }
        let mut stored = Rat::zero();
        for step in witness.deposit.factors() {
            let (a, f, g) = match &step.gradient {
                crate::hnn::constitution::FactorGradient::Storage { contact, gradient } => {
                    (*contact, 0, gradient)
                }
                crate::hnn::constitution::FactorGradient::Stiffness { contact, gradient } => {
                    (*contact, 1, gradient)
                }
                crate::hnn::constitution::FactorGradient::Dissipation { contact, gradient } => {
                    (*contact, 2, gradient)
                }
                _ => {
                    return Err(HnnError::Unadmitted {
                        reason: "physical contact query includes reached C/K/D only",
                    });
                }
            };
            stored += g
                .entries()
                .iter()
                .zip(direction[a][f].entries())
                .map(|(g, d)| g * d)
                .sum::<Rat>();
        }
        let mut paired = Rat::zero();
        let mut class_charge = Rat::zero();
        let mut response_charge = Rat::zero();
        let mut surrogate_response = Vec::new();
        let mut response_component_error = Vec::new();
        for (j, ((a, ea), (s, es))) in actual.iter().zip(&fresh).enumerate() {
            let feature = s
                .iter()
                .cloned()
                .chain(a.iter().zip(s).map(|(a, s)| a - s))
                .collect::<Vec<_>>();
            let v = map
                .apply(&feature)?
                .into_iter()
                .map(|x| -x)
                .collect::<Vec<_>>();
            let mut row_errors = Vec::new();
            for row in 0..map.rows() {
                let coefficients = map.row(row)?;
                let rc = &coefficients[width..];
                let rs = coefficients[..width]
                    .iter()
                    .zip(rc)
                    .map(|(s, c)| s - c)
                    .collect::<Vec<_>>();
                let ev = rc.iter().zip(ea).map(|(c, e)| c.abs() * e).sum::<Rat>()
                    + rs.iter().zip(es).map(|(c, e)| c.abs() * e).sum::<Rat>();
                row_errors.push(ev.clone());
                let eg = if row % 2 == 0 {
                    eps[j][row / 2].clone()
                } else {
                    Rat::zero()
                };
                let g = &witness.reads[j].1[row];
                paired += g * &v[row];
                class_charge += &eg * v[row].abs();
                response_charge += (g.abs() + eg) * ev;
            }
            surrogate_response.push(v);
            response_component_error.push(row_errors);
        }
        let response_squared = self.uniform_response(witness, o, direction, extent)?;
        let discrepancy = (&stored - &paired).abs();
        let lower = &stored - &discrepancy - &class_charge - &response_charge;
        let reading = PhysicalRayReading {
            stored_pairing: stored,
            surrogate_pairing: paired,
            reverse_discrepancy: discrepancy,
            class_error_charge: class_charge,
            response_error_charge: response_charge,
            lower,
            response_squared,
            tangent_queries: 2,
            stage_error_norms: actual_trace
                .into_iter()
                .map(|(t, a, b)| (true, t, a, b))
                .chain(fresh_trace.into_iter().map(|(t, a, b)| (false, t, a, b)))
                .collect(),
            surrogate_response,
            response_component_error,
        };
        let mut cache = self.cache.lock().map_err(|_| HnnError::Unadmitted {
            reason: "native immutable ray cache is available",
        })?;
        let retained = cache
            .iter()
            .flat_map(|(d, _)| d.iter().flatten().flat_map(|m| m.entries()))
            .chain(cache.iter().flat_map(|(_, r)| r.values()))
            .chain(direction.iter().flatten().flat_map(|m| m.entries()))
            .chain(reading.values());
        admit_extent(retained)?;
        cache.push((direction.clone(), reading.clone()));
        Ok(reading)
    }

    fn uniform_response(
        &self,
        witness: &super::native_prediction::NativeContactWitness,
        o: &Operands,
        direction: &ContactDirections,
        extent: &ContactDirections,
    ) -> Result<Rat, HnnError> {
        use crate::hnn::field::ConstitutionRead;
        let theta = &witness.producing;
        let map =
            theta
                .receiving_map(witness.phases.ring())
                .ok_or(HnnError::MissingReceivingMap {
                    ring: witness.phases.ring(),
                })?;
        let width = o.rings()[witness.phases.ring()].width();
        let bases = (0..o.contacts().len())
            .map(|a| {
                [
                    theta.contact_storage(a),
                    theta.contact_stiffness(a),
                    theta.contact_dissipation(a),
                ]
            })
            .collect::<Vec<_>>();
        let domain_envelopes = bases
            .iter()
            .zip(direction)
            .zip(extent)
            .zip(o.contacts())
            .map(|(((b, v), d), c)| {
                ContactEnvelope::of(
                    [
                        FormEnvelope::domain(b[0], &d[0], &v[0])?,
                        FormEnvelope::domain(b[1], &d[1], &v[1])?,
                        FormEnvelope::domain(b[2], &d[2], &v[2])?,
                    ],
                    o.step(),
                    c.conductance(),
                )
            })
            .collect::<Result<Vec<_>, HnnError>>()?;
        let mut parallel = StageEnvelope::identity();
        parallel.first = Rat::zero();
        parallel.second = Rat::zero();
        for c in &domain_envelopes {
            parallel.norm = parallel.norm.max(c.stage.norm.clone());
            parallel.first = parallel.first.max(c.stage.first.clone());
            parallel.second = parallel.second.max(c.stage.second.clone());
        }
        let rc = ExactRatMatrix::new(map.to_rows().iter().map(|r| r[width..].to_vec()).collect())?;
        let rs = ExactRatMatrix::new(
            map.to_rows()
                .iter()
                .map(|r| {
                    r[..width]
                        .iter()
                        .zip(&r[width..])
                        .map(|(s, c)| s - c)
                        .collect()
                })
                .collect(),
        )?;
        let projection = sqrt_ceiling(
            &o.exact_weights(witness.phases.ring())
                .iter()
                .map(square)
                .sum(),
            64,
        );
        let mut envelope = StageEnvelope::identity();
        let mut response_squared = Rat::zero();
        for t in 0..=self.stages.full_ticks {
            if witness.phases.epochs().any(|j| j == t) {
                let response = &projection
                    * &envelope.first
                    * (norm(&rc) * &self.stages.actual.opening_norm
                        + norm(&rs) * &self.stages.fresh.opening_norm);
                response_squared += square(&response);
            }
            if t < self.stages.full_ticks {
                envelope = envelope
                    .then(&StageEnvelope::fixed(self.stages.fixed_ticks[t].clone())?)
                    .then(&parallel);
            }
        }
        admit_extent([&response_squared])?;
        Ok(response_squared)
    }
}

fn admit_extent<'a>(values: impl IntoIterator<Item = &'a Rat>) -> Result<(), HnnError> {
    let policy = super::action::NativeWorkBudget::V1;
    let mut used = 0u64;
    for q in values {
        let n = q.numer().bits();
        let d = q.denom().bits();
        used = used
            .checked_add(n)
            .and_then(|x| x.checked_add(d))
            .ok_or(HnnError::CountOverflow)?;
        if n > policy.integer_bits || d > policy.integer_bits || used > policy.aggregate_bits {
            return Err(HnnError::Unadmitted {
                reason: "native ray certificate obeys its explicit finite rational/cache extent",
            });
        }
    }
    Ok(())
}

fn zero_state(o: &Operands, tick: usize) -> EndChange {
    EndChange {
        storage: o
            .rings()
            .iter()
            .map(|r| vec![Rat::zero(); r.width()])
            .collect(),
        arrivals: o
            .contacts()
            .iter()
            .map(|c| {
                let (a, b) = c.ends();
                [
                    vec![Rat::zero(); o.rings()[a].width()],
                    vec![Rat::zero(); o.rings()[b].width()],
                ]
            })
            .collect(),
        states: o
            .contacts()
            .iter()
            .map(|c| [vec![Rat::zero(); c.width()], vec![Rat::zero(); c.width()]])
            .collect(),
        resonators: o
            .resonators()
            .iter()
            .map(|r| {
                r.as_ref()
                    .map(|r| [vec![Rat::zero(); r.width()], vec![Rat::zero(); r.width()]])
            })
            .collect(),
        resonator_phases: o
            .resonators()
            .iter()
            .map(|r| r.as_ref().map(|r| r.phase_at(tick.saturating_sub(1))))
            .collect(),
    }
}

#[cfg(test)]
mod represented_material_ray_data {
    use super::*;
    use crate::ratio::rat;

    // Independent scalar inverse differentiation, including simultaneous C/K/D changes.
    fn scalar_maps(f: [Rat; 3], v: [Rat; 3], eta: &Rat, h: &Rat, g: &Rat) -> [ExactRatMatrix; 3] {
        let value = std::array::from_fn::<_, 3, _>(|i| &f[i] + eta * &v[i]);
        let a = value.map(|x| square(&x));
        let a1 = std::array::from_fn::<_, 3, _>(|i| int(2) * (&f[i] + eta * &v[i]) * &v[i]);
        let a2 = v.map(|x| int(2) * square(&x));
        let m = Rat::one() + g / h * &a[0] + g / int(2) * &a[2] + g * h / int(4) * &a[1];
        let m1 = g / h * &a1[0] + g / int(2) * &a1[2] + g * h / int(4) * &a1[1];
        let m2 = g / h * &a2[0] + g / int(2) * &a2[2] + g * h / int(4) * &a2[1];
        let x = m.recip();
        let x1 = -&m1 * square(&x);
        let x2 = int(2) * square(&m1) * &x * &x * &x - m2 * square(&x);
        let p = [h.clone(), -h, -square(h) * g * &a[1], int(2) * g * &a[0]];
        let p1 = [
            Rat::zero(),
            Rat::zero(),
            -square(h) * g * &a1[1],
            int(2) * g * &a1[0],
        ];
        let p2 = [
            Rat::zero(),
            Rat::zero(),
            -square(h) * g * &a2[1],
            int(2) * g * &a2[0],
        ];
        let j = [-h.recip(), h.recip(), Rat::one() / (int(2) * h), h.recip()];
        std::array::from_fn(|order| {
            ExactRatMatrix::new(
                (0..4)
                    .map(|i| {
                        (0..4)
                            .map(|k| {
                                let correction = match order {
                                    0 => &x * &p[k],
                                    1 => &x1 * &p[k] + &x * &p1[k],
                                    _ => &x2 * &p[k] + int(2) * &x1 * &p1[k] + &x * &p2[k],
                                };
                                &j[i] * correction
                                    + if order == 0 && i == k {
                                        if i == 3 { -Rat::one() } else { Rat::one() }
                                    } else {
                                        Rat::zero()
                                    }
                            })
                            .collect()
                    })
                    .collect(),
            )
            .unwrap()
        })
    }
    #[test]
    fn physical_contact_envelope_covers_inverse_and_both_derivatives_on_declared_ray() {
        let f = [rat(3, 4), rat(2, 3), rat(1, 5)];
        let v = [rat(-2, 7), rat(1, 4), rat(-3, 11)];
        let bases = f
            .each_ref()
            .map(|x| ExactRatMatrix::new(vec![vec![x.clone()]]).unwrap());
        let directions = v
            .each_ref()
            .map(|x| ExactRatMatrix::new(vec![vec![x.clone()]]).unwrap());
        let h = rat(2, 3);
        let g = rat(5, 2);
        let end = rat(3, 2);
        let e = contact_envelope(bases.each_ref(), directions.each_ref(), &end, &h, &g).unwrap();
        for n in 0..=24 {
            let eta = &end * rat(n, 24);
            for (m, bound) in scalar_maps(f.clone(), v.clone(), &eta, &h, &g)
                .iter()
                .zip([&e.norm, &e.first, &e.second])
            {
                // Frobenius is independent of the Schur norm used to construct factor bounds.
                assert!(m.entries().iter().map(square).sum::<Rat>() <= int(4) * square(bound));
                for input in [
                    vec![rat(1, 1), rat(-2, 3), rat(4, 5), rat(-3, 7)],
                    vec![rat(0, 1), rat(0, 1), rat(1, 1), rat(0, 1)],
                ] {
                    assert!(
                        m.apply(&input).unwrap().iter().map(square).sum::<Rat>()
                            <= square(bound) * input.iter().map(square).sum::<Rat>()
                    );
                }
            }
        }
        assert!(contact_envelope(bases.each_ref(), directions.each_ref(), &-end, &h, &g).is_err());
    }
    #[test]
    fn composed_stage_uses_simultaneous_old_first_derivative() {
        let a = StageEnvelope {
            norm: int(2),
            first: int(3),
            second: int(5),
        };
        let b = StageEnvelope {
            norm: int(7),
            first: int(11),
            second: int(13),
        };
        assert_eq!(
            a.then(&b),
            StageEnvelope {
                norm: int(14),
                first: int(43),
                second: int(127)
            }
        );
        assert_eq!(StageEnvelope::identity().then(&a), a);
        assert!(StageEnvelope::fixed(-Rat::one()).is_err());
    }
    #[test]
    fn original_midpoint_and_inverse_error_charge_cover_material_forcing_and_feedback() {
        let h = rat(2, 3);
        let g = rat(5, 2);
        let f = [rat(3, 4), rat(2, 3), rat(1, 5)];
        let v = [rat(-2, 7), rat(1, 4), rat(-3, 11)];
        let bases = f
            .each_ref()
            .map(|x| ExactRatMatrix::new(vec![vec![x.clone()]]).unwrap());
        let directions = v
            .each_ref()
            .map(|x| ExactRatMatrix::new(vec![vec![x.clone()]]).unwrap());
        let e = ContactEnvelope::of(
            std::array::from_fn(|i| {
                FormEnvelope::of(&bases[i], &directions[i], &Rat::zero()).unwrap()
            }),
            &h,
            &g,
        )
        .unwrap();
        let c = square(&f[0]);
        let k = square(&f[1]);
        let d = square(&f[2]);
        let c1 = int(2) * &f[0] * &v[0];
        let k1 = int(2) * &f[1] * &v[1];
        let d1 = int(2) * &f[2] * &v[2];
        let m = Rat::one() + &g / &h * c + &g / int(2) * d + &g * &h / int(4) * k.clone();
        let m1 = &g / &h * &c1 + &g / int(2) * d1 + &g * &h / int(4) * &k1;
        let input = [rat(1, 3), rat(-2, 5), rat(3, 7), rat(-4, 9)];
        let p = &h * (&input[0] - &input[1]) - square(&h) * &g * k * &input[2]
            + int(2) * &g * square(&f[0]) * &input[3];
        let p1 = -square(&h) * &g * k1 * &input[2] + int(2) * &g * c1 * &input[3];
        let exact = m.recip();
        for inverse in [exact.clone(), &exact + rat(1, 1 << 20)] {
            let chi = (Rat::one() - &m * &inverse).abs();
            for feedback in [Rat::zero(), rat(-3, 1024), rat(5, 2048)] {
                let zeta = &inverse * &p + &feedback;
                let true_force = &exact * (&p1 - &m1 * &exact * &p);
                let surrogate = &inverse * (&p1 - &m1 * zeta);
                let point = OriginalContactStage {
                    input_norm: vector_norm(&input),
                    input_error: Rat::zero(),
                    solve_residual: feedback.abs(),
                };
                let charge = e.forcing_error(&chi, &point);
                assert!(square(&e.j) * square(&(true_force - surrogate)) <= square(&charge));
                if chi.is_zero() && feedback.is_zero() {
                    assert_eq!(charge, Rat::zero());
                }
                if !feedback.is_zero() {
                    assert!(charge > Rat::zero());
                }
            }
        }
    }
    #[test]
    fn point_radius_and_reverse_parity_are_not_material_certificates() {
        // Producing state is exactly 1/2 for every M; response derivative is -M/2.
        for m in [1, 3, 127] {
            let value = rat(1, 2);
            let derivative = -rat(m, 2);
            assert_eq!(value, rat(1, 2));
            assert!(derivative.abs() >= rat(1, 2));
        }
        let stored = rat(3, 8);
        let tangent_pair = rat(1, 4);
        let sigma = (&stored - &tangent_pair).abs();
        assert_eq!(&stored - sigma, tangent_pair);
        // The positive g/response cross term cannot be omitted in a robust lower bound.
        let g = rat(2, 3);
        let eg = rat(1, 17);
        let v = rat(3, 5);
        let ev = rat(1, 19);
        let lower = &g * &v - &eg * v.abs() - (g.abs() + &eg) * &ev;
        for dg in [-eg.clone(), eg.clone()] {
            for dv in [-ev.clone(), ev.clone()] {
                assert!((&g + &dg) * (&v + dv) >= lower);
            }
        }
        assert!(admit_extent([&Rat::new(BigInt::one() << 65_537usize, BigInt::one())]).is_err());
    }
    #[test]
    fn component_tangent_radius_preserves_remote_support_and_encloses_existing_linear_action() {
        use crate::hnn::tests::support::{contact, small_field};
        use crate::hnn::{Constitution, Current};
        let calls = super::super::work::process_native_calls();
        let field = small_field(
            &[2, 3, 5],
            vec![contact(0, 1, 2, 0), contact(1, 2, 2, 0)],
            2,
        );
        let theta =
            Constitution::initial(&field, crate::hnn::constitution::CAMPAIGN_ONE_BUDGET).unwrap();
        let ops = Operands::exact_at_cut(&field, &theta, &Current::at_rest(&field)).unwrap();
        let zero = zero_state(&ops, 0);
        let mut tube =
            crate::hnn::prediction::charted::ResponseTube::open(&ops, &zero, &zero).unwrap();
        let epsilon = rat(1, 1024);
        tube.add_material_contact_error(0, &epsilon).unwrap();
        assert!(
            tube.add_material_contact_error(0, &-epsilon.clone())
                .is_err()
        );
        let anchors = super::super::linear::junctions(&ops, &zero)
            .unwrap()
            .into_iter()
            .map(|j| j.anchor)
            .collect::<Vec<_>>();
        assert!(
            tube.anchors(&zero, &anchors).unwrap()[2]
                .iter()
                .all(Zero::is_zero),
            "a local error is not instantly present at a remote receiver"
        );
        let mut point = zero.clone();
        point.arrivals[0][1][0] = epsilon;
        let image = super::super::linear::tick(&ops, &point, 0).unwrap();
        let zero_image = super::super::linear::tick(&ops, &zero, 0).unwrap();
        tube.advance(&zero, &zero_image, 0).unwrap();
        let actual = super::super::linear::junctions(&ops, &image).unwrap();
        let center = super::super::linear::junctions(&ops, &zero_image)
            .unwrap()
            .into_iter()
            .map(|j| j.anchor)
            .collect::<Vec<_>>();
        let bound = tube.anchors(&zero_image, &center).unwrap();
        assert!(actual[2].anchor.iter().any(|x| !x.is_zero()));
        for (value, error) in actual[2].anchor.iter().zip(&bound[2]) {
            assert!(value.abs() <= *error);
        }
        assert_eq!(
            super::super::work::process_native_calls(),
            calls,
            "coefficient/data control opens no Word, response or return"
        );
    }
}
