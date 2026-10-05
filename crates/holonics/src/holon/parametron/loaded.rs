//! The loaded quartic element and its **executed** mixed kick/drift scheme.
//!
//! `N=C+h(D+Y⁻¹I)`, `Nω=Cw+he−h(Ku+∇Q(u))`, `F(u,w)=(u+hω,ω)`.
//! Positive storage and an exact signed energy balance do not imply stability: with
//! `C=K=D=0`, `h=Y=β=1`, this is `u ↦ u−u³`, hence `2 ↦ −6`.
//!
//! A domain certificate is about this finite map, not the continuous equation or a
//! linear Floquet multiplier. On `B_G(c,r)`, `G ⪰ gI`, `r² ≤ g ε²`, the quartic
//! Hessian differs from its value at the centre by at most
//! `δ=3β(2Uε+ε²)`, where `U ≥ |c_u|`. With `A=[−h²X;−hX]`,
//! `aI ⪰ AᵀG_next A`, Young's inequality gives the sufficient exact test
//!
//! `(1+s) J_cᵀG_next J_c + (1+1/s) aδ²/g G ⪯ λ²G`.
//!
//! The actual centre residual must also satisfy `|F(c)−c_next|_G_next ≤ η`
//! and `η+λr ≤ r_next`. Cyclic domains with `∏λ < 1` certify a contracting
//! period map. The certificates store material and domain geometry, not an event tape.
//! Charted solves, lattice splitting and their retained fibres need an additional
//! envelope; these smooth certificates never certify them implicitly.

use num_traits::{One, Signed, Zero};

use super::SymmetricQuartic;
use crate::holon::dirac::DiracStructure;
use crate::holon::element::ResistiveRelation;
use crate::holon::law::{Advance, EnergyBalance, HolonLaw, ReferenceHolon, Scheme};
use crate::holon::port::Bond;
use crate::holon::{Holon, HolonError, HolonState, PortCounts, PortHolon};
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::inertia::{SymmetricForm, inertia};
use crate::ratio::linear::vector::{add, at, block_diagonal, dot, matrix, scale, sub};
use crate::ratio::{Rat, integer};

fn failed(what: &'static str) -> HolonError {
    HolonError::ConformanceFailed { what }
}

fn nonnegative_form(m: &ExactRatMatrix) -> Result<(), HolonError> {
    let form = SymmetricForm::from_rows(m.to_rows())?;
    if inertia(&form).negative != 0 {
        return Err(failed("the declared quadratic inequality"));
    }
    Ok(())
}

fn positive_form(m: &ExactRatMatrix) -> Result<(), HolonError> {
    let form = SymmetricForm::from_rows(m.to_rows())?;
    let signs = inertia(&form);
    if signs.negative != 0 || signs.zero != 0 {
        return Err(failed("a domain metric must be positive definite"));
    }
    Ok(())
}

/// The material and participating wave port; `K` may be signed under a pump.
/// `C` and `D` are certified nonnegative. A singular `C` needs no inverse.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoadedParametron {
    capacity: ExactRatMatrix,
    stiffness: ExactRatMatrix,
    dissipation: ExactRatMatrix,
    saturation: SymmetricQuartic,
    admittance: Rat,
}

impl LoadedParametron {
    pub fn new(
        capacity: ExactRatMatrix,
        stiffness: ExactRatMatrix,
        dissipation: ExactRatMatrix,
        saturation: SymmetricQuartic,
        admittance: Rat,
    ) -> Result<Self, HolonError> {
        let n = capacity.rows();
        if n == 0
            || !n.is_multiple_of(2)
            || [&capacity, &stiffness, &dissipation]
                .iter()
                .any(|m| m.rows() != n || m.columns() != n)
        {
            return Err(failed("loaded realified parametron material shape"));
        }
        if !admittance.is_positive() {
            return Err(failed("a positive wave-port admittance"));
        }
        nonnegative_form(&capacity)?;
        nonnegative_form(&dissipation)?;
        SymmetricForm::from_rows(stiffness.to_rows())?;
        Ok(Self {
            capacity,
            stiffness,
            dissipation,
            saturation,
            admittance,
        })
    }

    pub fn width(&self) -> usize {
        self.capacity.rows()
    }
    pub fn saturation(&self) -> &SymmetricQuartic {
        &self.saturation
    }
    pub fn stiffness(&self) -> &ExactRatMatrix {
        &self.stiffness
    }

    pub fn operator(&self, h: &Rat) -> Result<ExactRatMatrix, HolonError> {
        if !h.is_positive() {
            return Err(HolonError::NonpositiveStep);
        }
        Ok(self
            .capacity
            .add(&self.dissipation.scaled(h))?
            .add(&ExactRatMatrix::identity(self.width())?.scaled(&(h / &self.admittance)))?)
    }

    pub fn energy(&self, state: &[Rat]) -> Result<Rat, HolonError> {
        self.check_state(state)?;
        let n = self.width();
        Ok((dot(&state[..n], &self.stiffness.apply(&state[..n])?)
            + dot(&state[n..], &self.capacity.apply(&state[n..])?))
            / integer(2)
            + self
                .saturation
                .energy(&state[..n])
                .map_err(|_| failed("quartic storage shape"))?)
    }

    fn check_state(&self, state: &[Rat]) -> Result<(), HolonError> {
        if state.len() != 2 * self.width() {
            return Err(HolonError::Shape {
                what: "loaded (displacement, rate)",
                expected: 2 * self.width(),
                found: state.len(),
            });
        }
        Ok(())
    }

    pub fn right(&self, h: &Rat, state: &[Rat], drive: &[Rat]) -> Result<Vec<Rat>, HolonError> {
        if !h.is_positive() {
            return Err(HolonError::NonpositiveStep);
        }
        self.check_state(state)?;
        if drive.len() != self.width() {
            return Err(HolonError::Shape {
                what: "loaded drive",
                expected: self.width(),
                found: drive.len(),
            });
        }
        let n = self.width();
        let force = add(
            &self.stiffness.apply(&state[..n])?,
            &self
                .saturation
                .effort(&state[..n])
                .map_err(|_| failed("quartic effort shape"))?,
        );
        Ok(sub(
            &add(&self.capacity.apply(&state[n..])?, &scale(h, drive)),
            &scale(h, &force),
        ))
    }

    /// The power-neutral interconnection needs **no C inverse**. With `ω=−f_u`,
    /// `e_w=Cω`, `f_R=f_P=ω`, `e_u=Cf_w+e_R+e_P`, its power vanishes.
    /// The wave port has `e_P=e−ω/Y`; its pairing equals `(Y/4)(|e|²−|out|²)`.
    pub fn holon(&self) -> Result<Holon, HolonError> {
        let n = self.width();
        let total = 4 * n;
        let flow = matrix(total, total, |i, j| {
            if i < n && j < n {
                at(&self.capacity, i, j)
            } else if (n..2 * n).contains(&i) && (n..2 * n).contains(&j) {
                -at(&self.capacity, i - n, j - n)
            } else if i >= 2 * n && (j == i || j == (i % n)) {
                Rat::one()
            } else {
                Rat::zero()
            }
        })?;
        let effort = matrix(total, total, |i, j| {
            if i < n && j == n + i {
                Rat::one()
            } else if (n..2 * n).contains(&i) && j == i - n {
                Rat::one()
            } else if (n..2 * n).contains(&i) && (j == n + i || j == 2 * n + i) {
                -Rat::one()
            } else {
                Rat::zero()
            }
        })?;
        let storage =
            SymmetricForm::from_rows(block_diagonal(&self.stiffness, &self.capacity)?.to_rows())?;
        let port = PortHolon::new(
            DiracStructure::kernel_form(&flow, &effort)?,
            PortCounts {
                storage: 2 * n,
                resistive: n,
                external: n,
                active: 0,
            },
            storage,
            ResistiveRelation::new(self.dissipation.clone())?,
        )?;
        Holon::new(port)?.with_loaded_parametron(self.clone())
    }

    pub fn law(&self, h: Rat) -> Result<ReferenceHolon, HolonError> {
        ReferenceHolon::new(self.holon()?, h, Scheme::QuarticKickDrift)
    }

    /// Read the actual rate, including its equation residual. The exact `advance`
    /// admits the returned bond; a numerical caller must bound this residual separately.
    pub fn executed(
        &self,
        h: &Rat,
        state: &HolonState,
        drive: &[Rat],
        rate: &[Rat],
    ) -> Result<Advance, HolonError> {
        self.right(h, &state.configuration, drive)?;
        let n = self.width();
        if rate.len() != n {
            return Err(failed("loaded executed rate shape"));
        }
        let u = &state.configuration[..n];
        let w = &state.configuration[n..];
        let drift = scale(h, rate);
        let next_u = add(u, &drift);
        let next = [next_u, rate.to_vec()].concat();
        let change = sub(rate, w);
        let force = add(
            &self.stiffness.apply(u)?,
            &self
                .saturation
                .effort(u)
                .map_err(|_| failed("quartic effort shape"))?,
        );
        let port_effort = sub(drive, &scale(&(Rat::one() / &self.admittance), rate));
        let flow = [
            scale(&integer(-1), rate),
            scale(&(-Rat::one() / h), &change),
            rate.to_vec(),
            rate.to_vec(),
        ]
        .concat();
        let effort = [
            force,
            self.capacity.apply(rate)?,
            scale(&integer(-1), &self.dissipation.apply(rate)?),
            port_effort.clone(),
        ]
        .concat();
        let integration = dot(&drift, &self.stiffness.apply(&drift)?) / integer(2)
            + self
                .saturation
                .drift_defect(u, &drift)
                .map_err(|_| failed("quartic drift shape"))?
            - dot(&change, &self.capacity.apply(&change)?) / integer(2);
        let balance = EnergyBalance::closed(
            self.energy(&next)? - self.energy(&state.configuration)?,
            h * dot(rate, &self.dissipation.apply(rate)?),
            h * dot(rate, &port_effort),
            Rat::zero(),
            Rat::zero(),
            integration,
        );
        let next_state = state
            .committed(next)
            .map_err(|_| failed("loaded material clock overflow"))?;
        Ok(Advance {
            state: next_state,
            bond: Bond::new(flow, effort)?,
            balance,
        })
    }

    /// The derivative of the finite map at its producing state, not its ODE generator.
    pub fn jacobian(
        &self,
        h: &Rat,
        inverse: &ExactRatMatrix,
        state: &[Rat],
    ) -> Result<ExactRatMatrix, HolonError> {
        if !h.is_positive() {
            return Err(HolonError::NonpositiveStep);
        }
        self.check_state(state)?;
        let n = self.width();
        if inverse.rows() != n || inverse.columns() != n {
            return Err(failed("the finite-map solve has the declared extent"));
        }
        let l = self.stiffness.add(
            &self
                .saturation
                .hessian(&state[..n])
                .map_err(|_| failed("quartic Hessian shape"))?,
        )?;
        let xl = inverse.multiply(&l)?;
        let xc = inverse.multiply(&self.capacity)?;
        Ok(matrix(2 * n, 2 * n, |i, j| match (i < n, j < n) {
            (true, true) => (if i == j { Rat::one() } else { Rat::zero() }) - h * h * at(&xl, i, j),
            (true, false) => h * at(&xc, i, j - n),
            (false, true) => -h * at(&xl, i - n, j),
            (false, false) => at(&xc, i - n, j - n),
        })?)
    }
}

/// A proposed local domain. Every numerical bound here is checked against the actual map.
/// The centre is a proposed period point, not an answer or a supplied stable multiplier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DomainProposal {
    pub centre: Vec<Rat>,
    pub drive: Vec<Rat>,
    pub metric: ExactRatMatrix,
    pub radius: Rat,
    pub metric_lower: Rat,
    pub euclidean_radius: Rat,
    pub lipschitz: Rat,
    pub centre_residual: Rat,
    pub young: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DomainStep {
    law: ReferenceHolon,
    proposal: DomainProposal,
    hessian_variation: Rat,
    jacobian: ExactRatMatrix,
    centre_residual_squared: Rat,
}

impl DomainStep {
    fn certify(
        law: &ReferenceHolon,
        p: &DomainProposal,
        next: &DomainProposal,
    ) -> Result<Self, HolonError> {
        let element = law
            .holon()
            .loaded_parametron()
            .ok_or(failed("a domain needs the actual quartic law"))?;
        let n = element.width();
        if p.metric.rows() != 2 * n
            || p.metric.columns() != 2 * n
            || next.metric.rows() != 2 * n
            || next.metric.columns() != 2 * n
            || p.centre.len() != 2 * n
            || next.centre.len() != 2 * n
        {
            return Err(failed("period domain extent"));
        }
        if !p.radius.is_positive()
            || !p.metric_lower.is_positive()
            || !p.euclidean_radius.is_positive()
            || !p.young.is_positive()
            || !p.lipschitz.is_positive()
            || p.centre_residual.is_negative()
        {
            return Err(failed("positive domain bounds"));
        }
        positive_form(&p.metric)?;
        positive_form(&next.metric)?;
        let id = ExactRatMatrix::identity(2 * n)?;
        nonnegative_form(&p.metric.subtract(&id.scaled(&p.metric_lower))?)?;
        if &p.radius * &p.radius > &p.metric_lower * &p.euclidean_radius * &p.euclidean_radius {
            return Err(failed("the Euclidean enclosure of the input metric ball"));
        }
        let h = law.step();
        let x = element.operator(h)?.inverse()?;
        let j = element.jacobian(h, &x, &p.centre)?;
        let a_map = matrix(2 * n, n, |i, k| {
            if i < n {
                -h * h * at(&x, i, k)
            } else {
                -h * at(&x, i - n, k)
            }
        })?;
        let a_gram = a_map
            .transpose()?
            .multiply(&next.metric)?
            .multiply(&a_map)?;
        // For this symmetric PSD form its absolute row norm bounds its spectral norm.
        let a: Rat = a_gram
            .to_rows()
            .iter()
            .map(|row| row.iter().map(|v| v.abs()).sum::<Rat>())
            .max()
            .unwrap_or_else(Rat::zero);
        nonnegative_form(&ExactRatMatrix::identity(n)?.scaled(&a).subtract(&a_gram)?)?;
        let u: Rat = p.centre[..n].iter().map(|v| v.abs()).sum();
        let eps = &p.euclidean_radius;
        let delta =
            integer(3) * element.saturation.coefficient() * (integer(2) * u * eps + eps * eps);
        let nominal = j.transpose()?.multiply(&next.metric)?.multiply(&j)?;
        let variation =
            (Rat::one() + Rat::one() / &p.young) * a * &delta * &delta / &p.metric_lower;
        let margin = p
            .metric
            .scaled(&(&p.lipschitz * &p.lipschitz - variation))
            .subtract(&nominal.scaled(&(Rat::one() + &p.young)))?;
        nonnegative_form(&margin).map_err(|_| failed("the nonlinear domain Jacobian bound"))?;
        let advanced = law.advance(&HolonState::new(p.centre.clone()), &p.drive)?;
        let residual = sub(&advanced.state.configuration, &next.centre);
        let residual_squared = dot(&residual, &next.metric.apply(&residual)?);
        if residual_squared > &p.centre_residual * &p.centre_residual
            || &p.centre_residual + &p.lipschitz * &p.radius > next.radius
        {
            return Err(failed("the actual centre residual and domain inclusion"));
        }
        Ok(Self {
            law: law.clone(),
            proposal: p.clone(),
            hessian_variation: delta,
            jacobian: j,
            centre_residual_squared: residual_squared,
        })
    }

    pub fn contains(&self, state: &[Rat]) -> Result<bool, HolonError> {
        if state.len() != self.proposal.centre.len() {
            return Err(failed("domain state extent"));
        }
        let v = sub(state, &self.proposal.centre);
        Ok(dot(&v, &self.proposal.metric.apply(&v)?)
            <= &self.proposal.radius * &self.proposal.radius)
    }
    pub fn hessian_variation(&self) -> &Rat {
        &self.hessian_variation
    }
    /// The constitutive law whose finite map this domain certifies.
    pub fn law(&self) -> &ReferenceHolon {
        &self.law
    }
    pub fn jacobian(&self) -> &ExactRatMatrix {
        &self.jacobian
    }
    pub fn centre_residual_squared(&self) -> &Rat {
        &self.centre_residual_squared
    }
}

/// The composition of the **declared executed laws**, with cyclic domains.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PeriodicDomain {
    steps: Vec<DomainStep>,
    contraction: Rat,
}

impl PeriodicDomain {
    pub fn certify(
        laws: &[ReferenceHolon],
        proposals: &[DomainProposal],
    ) -> Result<Self, HolonError> {
        if laws.is_empty() || laws.len() != proposals.len() {
            return Err(failed("a nonempty declared period"));
        }
        let mut steps = Vec::with_capacity(laws.len());
        let mut contraction = Rat::one();
        for i in 0..laws.len() {
            let base = laws[0]
                .holon()
                .loaded_parametron()
                .ok_or(failed("a quartic period law"))?;
            let material = laws[i]
                .holon()
                .loaded_parametron()
                .ok_or(failed("a quartic period law"))?;
            if laws[i].step() != laws[0].step()
                || material.capacity != base.capacity
                || material.dissipation != base.dissipation
                || material.saturation != base.saturation
                || material.admittance != base.admittance
            {
                return Err(failed(
                    "the period changes stiffness only; other material changes need their holding law",
                ));
            }
            steps.push(DomainStep::certify(
                &laws[i],
                &proposals[i],
                &proposals[(i + 1) % laws.len()],
            )?);
            contraction *= &proposals[i].lipschitz;
        }
        if contraction >= Rat::one() {
            return Err(failed("strict contraction over the actual period"));
        }
        Ok(Self { steps, contraction })
    }
    pub fn period(&self) -> usize {
        self.steps.len()
    }
    pub fn contraction(&self) -> &Rat {
        &self.contraction
    }
    pub fn step(&self, phase: usize) -> Result<&DomainStep, HolonError> {
        self.steps
            .get(phase)
            .ok_or(failed("a phase inside the declared period"))
    }
    pub fn advance(&self, phase: usize, state: &HolonState) -> Result<Advance, HolonError> {
        let here = self.step(phase)?;
        if !here.contains(&state.configuration)? {
            return Err(failed("the input lies in its certified domain"));
        }
        let mut advanced = here.law.advance(state, &here.proposal.drive)?;
        let previous = &self.steps[(phase + self.period() - 1) % self.period()];
        let current_material = here
            .law
            .holon()
            .loaded_parametron()
            .ok_or(failed("quartic period material"))?;
        let previous_material = previous
            .law
            .holon()
            .loaded_parametron()
            .ok_or(failed("quartic period material"))?;
        let pump = current_material.energy(&state.configuration)?
            - previous_material.energy(&state.configuration)?;
        advanced.balance = EnergyBalance::closed(
            &advanced.balance.stored_change + &pump,
            advanced.balance.dissipated.clone(),
            advanced.balance.port.clone(),
            advanced.balance.active.clone(),
            &advanced.balance.deposition_work + pump,
            advanced.balance.discretization_defect.clone(),
        );
        if !self.steps[(phase + 1) % self.period()].contains(&advanced.state.configuration)? {
            return Err(failed(
                "the executed successor lies in the next certified domain",
            ));
        }
        Ok(advanced)
    }

    /// Execute the admitted period composition, checking each intermediate domain.
    /// Only the continuing point is carried; no per-step state sequence is retained.
    pub fn period_map(&self, phase: usize, state: &HolonState) -> Result<HolonState, HolonError> {
        self.step(phase)?;
        let mut current = state.clone();
        for offset in 0..self.period() {
            current = self
                .advance((phase + offset) % self.period(), &current)?
                .state;
        }
        Ok(current)
    }
}

/// A half-turn sheet read **only after** certifying its actual contracting period domain.
/// The phase class is the declared period's phase index; amplitude is enclosed as a square.
/// This is not the linear bank's ray/threshold face and is not a full source phase-lift class.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PeriodicLock {
    domain: PeriodicDomain,
    phase: usize,
    sheet: i8,
    amplitude_squared: [Rat; 2],
}

impl PeriodicLock {
    pub fn read(domain: PeriodicDomain, phase: usize, axis: usize) -> Result<Self, HolonError> {
        let step = domain.step(phase)?;
        let n = step.proposal.centre.len() / 2;
        if axis >= n {
            return Err(failed("a displacement axis for the sheet"));
        }
        let p = &step.proposal;
        let centre = &p.centre[axis];
        let eps = &p.euclidean_radius;
        if centre.abs() <= *eps {
            return Err(failed("the domain must separate the two half-turn sheets"));
        }
        let lower = (centre.abs() - eps) * (centre.abs() - eps);
        let upper = p.centre[..n]
            .iter()
            .map(|c| (c.abs() + eps) * (c.abs() + eps))
            .sum();
        let sheet = if centre.is_positive() { 1 } else { -1 };
        Ok(Self {
            domain,
            phase,
            sheet,
            amplitude_squared: [lower, upper],
        })
    }
    pub fn sheet(&self) -> i8 {
        self.sheet
    }
    pub fn phase_class(&self) -> usize {
        self.phase
    }
    pub fn amplitude_squared(&self) -> &[Rat; 2] {
        &self.amplitude_squared
    }
    pub fn domain(&self) -> &PeriodicDomain {
        &self.domain
    }
    pub fn advance(&self, state: &HolonState) -> Result<HolonState, HolonError> {
        self.domain.period_map(self.phase, state)
    }
}
