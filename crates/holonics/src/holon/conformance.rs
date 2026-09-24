//! **Conformance: the checks every Holon implementation passes.**
//!
//! [definition] Generic checks over [`HolonLaw`]: Tellegen on a Dirac structure
//! (`Holon/Dirac.tellegen`, `Holon/Dirac.IsDirac.power_eq_zero`); an exact advance
//! (`Holon/Law.advance_law`: residual zero, step bond admitted); a run whose aggregated
//! balance closes; interconnection closure and additivity (`Holon/Law.PortHolon.interconnect`,
//! `Holon/Law.storageEnergy_blocks`, `Holon/Law.dissipation_blocks`); the passive
//! coholon reading (`Holon/Law.passive_reading`); restriction and pullback
//! (`Holon/Restriction.pushforwardD_isDirac`, `Holon/Law.pullback_law`).
//!
//! [definition] The witnesses mirror `Holon/Conformance`: the medium
//! (`Holon/Conformance.medium_rate_agrees`), diffusion
//! (`Holon/Conformance.diffusion_dissipates`), the linear SSM
//! (`Holon/Conformance.ssm_port_output`), the pair contact
//! (`Holon/Conformance.pairContact_resistive`), the pumped LC loop
//! (`Holon/Conformance.lc_pump_work`), Maxwell on the triangle
//! (`Holon/Conformance.maxwell_gauss`, `Holon/Conformance.maxwell_balance`) and the
//! `so(3)` Lie–Poisson truncation (`Holon/Conformance.hat_casimir`,
//! `Holon/Conformance.navierStokes_balance`); the deposition witnesses mirror
//! `Holon/Deposition`. A resident realization owes the chart square "exact reference value ∈
//! returned ball" against these checks.
//!
//! [definition; agent-inferred] The Lie–Poisson witness freezes the modulated structure at the
//! current state, `Ω = hat(x_k)`: every frozen structure is skew, so each word is Dirac and
//! balances exactly, and with `G = 1` the energy is the Casimir `|x|²/2`, preserved exactly. The
//! Casimir for general `G` needs the midpoint-modulated structure `hat(x̄)`, a nonlinear implicit
//! step that is not implemented here.

use crate::ratio::Rat;
use num_traits::Zero;

use crate::holon::dirac::DiracStructure;
use crate::holon::element::storage_energy;
use crate::holon::law::{Advance, EnergyBalance, HolonLaw};
use crate::holon::restriction::PortMap;
use crate::holon::{HolonError, HolonState};
use crate::ratio::linear::vector::dot;

/// Tellegen on a structure: every basis pair pairs to zero and `D^⊥ = D`. Returns the pairings
/// checked.
pub fn check_tellegen(structure: &DiracStructure) -> Result<usize, HolonError> {
    let checked = structure.tellegen()?;
    if structure.form().orthogonal()? != *structure.form() {
        return Err(HolonError::ConformanceFailed {
            what: "a Dirac structure equals its orthogonal",
        });
    }
    Ok(checked)
}

/// One advance whose balance closes exactly and whose step bond is admitted.
pub fn check_exact_advance<L: HolonLaw>(
    law: &L,
    state: &HolonState,
    input: &[Rat],
) -> Result<Advance, HolonError> {
    let advance = law.advance(state, input)?;
    if !advance.balance.is_exact() {
        return Err(HolonError::ConformanceFailed {
            what: "the energy balance residual is zero",
        });
    }
    if !law.holon().port_holon().dirac().contains(&advance.bond)? {
        return Err(HolonError::NotAdmitted);
    }
    Ok(advance)
}

/// `commits` exact advances under one input; returns the reached state and the summed balance
/// (only the aggregate is retained).
pub fn check_run<L: HolonLaw>(
    law: &L,
    state: &HolonState,
    input: &[Rat],
    commits: u64,
) -> Result<(HolonState, EnergyBalance), HolonError> {
    let zero = Rat::zero();
    let mut total = EnergyBalance {
        stored_change: zero.clone(),
        dissipated: zero.clone(),
        port: zero.clone(),
        active: zero.clone(),
        deposition_work: zero.clone(),
        discretization_defect: zero.clone(),
        residual: zero,
    };
    let mut current = state.clone();
    for _ in 0..commits {
        let advance = check_exact_advance(law, &current, input)?;
        let b = advance.balance;
        total.stored_change += b.stored_change;
        total.dissipated += b.dissipated;
        total.port += b.port;
        total.active += b.active;
        total.deposition_work += b.deposition_work;
        total.discretization_defect += b.discretization_defect;
        total.residual += b.residual;
        current = advance.state;
    }
    Ok((current, total))
}

/// **Interaction closure and additivity**: the joined law is a Holon (its structure is Dirac), its
/// energy at the concatenated state is the sum of the parts' energies, its advance is exact, and
/// its dissipation is the sum of the parts' dissipations on their resistive flows.
pub fn check_interaction<L: HolonLaw>(
    a: &L,
    b: &L,
    joined: &[(usize, usize)],
    state_a: &[Rat],
    state_b: &[Rat],
    input: &[Rat],
) -> Result<(L, Advance), HolonError> {
    let composite = a.interact(b, joined)?;
    let port_holon = composite.holon().port_holon();
    check_tellegen(port_holon.dirac())?;
    let mut configuration = state_a.to_vec();
    configuration.extend(state_b.iter().cloned());
    let parts = a.holon().port_holon().storage_energy(state_a)?
        + b.holon().port_holon().storage_energy(state_b)?;
    if port_holon.storage_energy(&configuration)? != parts {
        return Err(HolonError::ConformanceFailed {
            what: "energy is additive over an interconnection",
        });
    }
    let advance = check_exact_advance(&composite, &HolonState::new(configuration), input)?;
    let resistive = port_holon.split(&advance.bond)?.resistive;
    let split = a.holon().port_holon().counts().resistive;
    let (flow_a, flow_b) = resistive.flow().split_at(split);
    let sum = a.holon().dissipation(flow_a)? + b.holon().dissipation(flow_b)?;
    if composite.holon().dissipation(resistive.flow())? != sum {
        return Err(HolonError::ConformanceFailed {
            what: "dissipation is additive over an interconnection",
        });
    }
    Ok((composite, advance))
}

/// **Restriction and pullback**: the restricted structure is Dirac and a pulled-back effort carries
/// the same power against a flow as the coarse effort against the pushed flow.
pub fn check_restriction<L: HolonLaw>(
    law: &L,
    map: &PortMap,
    flow: &[Rat],
    coarse_effort: &[Rat],
) -> Result<DiracStructure, HolonError> {
    let restricted = law.restrict(map)?;
    check_tellegen(&restricted)?;
    let pulled = law.pullback(map, coarse_effort)?;
    if dot(&pulled, flow) != dot(coarse_effort, &map.push_flow(flow)?) {
        return Err(HolonError::ConformanceFailed {
            what: "the pullback preserves power",
        });
    }
    Ok(restricted)
}

/// The stored energy at a state under the storage in force.
pub fn energy_at<L: HolonLaw>(law: &L, state: &HolonState) -> Result<Rat, HolonError> {
    storage_energy(law.holon().storage_at(state.commit), &state.configuration)
}

#[cfg(test)]
mod tests {
    use num_traits::{One, Signed};

    use super::*;
    use crate::geometry::complex::CellComplex;
    use crate::holon::deposition::{
        DepositLedger, divergent_state, indefinite_block, project_passive,
    };
    use crate::holon::element::{ActiveRelation, Pump, PumpSchedule, ResistiveRelation};
    use crate::holon::law::{ReferenceHolon, Scheme, active_receiver};
    use crate::holon::port::Bond;
    use crate::holon::{Holon, PortCounts, PortHolon};
    use crate::navigator::Clock;
    use crate::ratio::integer;
    use crate::ratio::linear::ExactRatMatrix;
    use crate::ratio::linear::inertia::SymmetricForm;
    use crate::ratio::linear::vector::{
        from_blocks, integer_matrix, ints, is_zero, matrix, quad, sub,
    };
    use crate::ratio::rat;

    fn form(rows: &[Vec<i64>]) -> SymmetricForm {
        SymmetricForm::from_integers(rows).unwrap()
    }

    fn diagonal(values: &[i64]) -> SymmetricForm {
        SymmetricForm::from_diagonal(ints(values))
    }

    fn medium_law(
        omega: &ExactRatMatrix,
        m: &ExactRatMatrix,
        g: SymmetricForm,
        b: &ExactRatMatrix,
        step: Rat,
    ) -> ReferenceHolon {
        let port_holon = PortHolon::medium(omega, m, g, b, false).unwrap();
        ReferenceHolon::new(Holon::new(port_holon).unwrap(), step, Scheme::Midpoint).unwrap()
    }

    fn zero(rows: usize, columns: usize) -> ExactRatMatrix {
        ExactRatMatrix::zero(rows, columns).unwrap()
    }

    // ---------------------------------------------------------------------------------------
    // Tellegen on every constructor

    #[test]
    fn tellegen_holds_on_every_dirac_constructor() {
        let gyrator = integer_matrix(&[&[0, -1], &[1, 0]]).unwrap();
        let triangle = integer_matrix(&[&[-1, 1, 0], &[0, -1, 1], &[1, 0, -1]]).unwrap();
        let skew = DiracStructure::skew_graph(&gyrator).unwrap();
        let kirchhoff = DiracStructure::kirchhoff(&triangle).unwrap();
        let (kernel, _) = crate::holon::dirac::KernelForm::from_incidence(&triangle).unwrap();
        let declared = DiracStructure::kernel_form(
            &kernel.flow_matrix().unwrap(),
            &kernel.effort_matrix().unwrap(),
        )
        .unwrap();
        let coholon = DiracStructure::passive_coholon(3).unwrap();
        let joined = skew.interconnect(&skew, &[(1, 0)]).unwrap();
        let composed = kirchhoff
            .interconnect(&coholon, &[])
            .unwrap()
            .compose(&DiracStructure::passive_coholon(1).unwrap(), &[0])
            .unwrap();
        let pushed = kirchhoff
            .pushforward(&integer_matrix(&[&[1, 1, 0], &[0, 1, -1]]).unwrap())
            .unwrap();
        let relabelled = kirchhoff.relabel(&[1, 2, 0]).unwrap();
        let curved = CellComplex::new(vec![3, 3], vec![triangle.transpose().unwrap()])
            .unwrap()
            .connection(vec![integer(2), integer(1), rat(-1, 3)])
            .unwrap()
            .kirchhoff()
            .unwrap();
        for structure in [
            &skew,
            &kirchhoff,
            &declared,
            &coholon,
            &joined,
            &composed,
            &pushed,
            &relabelled,
            &curved,
        ] {
            assert!(check_tellegen(structure).unwrap() > 0);
        }
    }

    // ---------------------------------------------------------------------------------------
    // Exact power balance: residual zero

    /// `Holon/Conformance.medium_rate_agrees` in its discrete form.
    #[test]
    fn the_medium_balances_exactly() {
        let law = medium_law(
            &integer_matrix(&[&[0, 2], &[-2, 0]]).unwrap(),
            &integer_matrix(&[&[1, 0], &[0, 3]]).unwrap(),
            form(&[vec![2, 1], vec![1, 1]]),
            &integer_matrix(&[&[1], &[-1]]).unwrap(),
            rat(1, 2),
        );
        let (_, total) = check_run(&law, &HolonState::new(ints(&[1, -2])), &ints(&[3]), 5).unwrap();
        assert!(total.residual.is_zero());
        assert!(total.dissipated.is_positive());
        assert!(total.discretization_defect.is_zero());
    }

    /// `Holon/Conformance.diffusion_dissipates`, `Holon/Conformance.diffusion_witness`.
    #[test]
    fn diffusion_dissipates_exactly() {
        let law = medium_law(
            &zero(1, 1),
            &integer_matrix(&[&[1]]).unwrap(),
            diagonal(&[1]),
            &zero(1, 0),
            integer(1),
        );
        let advance = check_exact_advance(&law, &HolonState::new(ints(&[1])), &[]).unwrap();
        assert_eq!(advance.state.configuration, vec![rat(1, 3)]);
        assert_eq!(advance.balance.dissipated, rat(4, 9));
        assert_eq!(advance.balance.stored_change, rat(-4, 9));
    }

    /// `Holon/Conformance.ssm_port_output`: the collocated output is the external port flow.
    #[test]
    fn the_linear_ssm_output_is_the_port_flow() {
        let b = integer_matrix(&[&[1, 0], &[2, -1]]).unwrap();
        let g = form(&[vec![3, 1], vec![1, 2]]);
        let law = medium_law(
            &integer_matrix(&[&[0, -1], &[1, 0]]).unwrap(),
            &integer_matrix(&[&[1, 0], &[0, 0]]).unwrap(),
            g.clone(),
            &b,
            rat(1, 3),
        );
        let state = HolonState::new(ints(&[2, -1]));
        let u = ints(&[1, 4]);
        let advance = check_exact_advance(&law, &state, &u).unwrap();
        let kinds = law.kinds(&advance).unwrap();
        let effort = kinds.storage.effort().to_vec();
        assert_eq!(
            kinds.external.flow(),
            b.transpose().unwrap().apply(&effort).unwrap()
        );
        assert_eq!(
            advance.balance.port,
            rat(1, 3) * dot(&u, kinds.external.flow())
        );
    }

    /// `Holon/Conformance.pairContact_resistive`: slip `f = Jv`, traction `e = −Df`.
    #[test]
    fn the_pair_contact_is_a_resistive_element() {
        let j = integer_matrix(&[&[1, -1]]).unwrap();
        let d = integer_matrix(&[&[2]]).unwrap();
        let v = ints(&[3, 1]);
        let slip = j.apply(&v).unwrap();
        let contact = Bond::new(
            slip.clone(),
            crate::ratio::linear::vector::neg(&d.apply(&slip).unwrap()),
        )
        .unwrap();
        let face = j
            .transpose()
            .unwrap()
            .multiply(&d)
            .unwrap()
            .multiply(&j)
            .unwrap();
        assert_eq!(contact.power(), -quad(&face, &v).unwrap());
        assert!(contact.power() <= Rat::zero());
        // As a Holon: f_S = −Jᵀ e_R, f_R = J e_S, e_R = −D f_R, so ẋ = −JᵀDJ ē.
        let structure = from_blocks(
            &zero(2, 2),
            &j.transpose().unwrap().scaled(&integer(-1)),
            &j,
            &zero(1, 1),
        )
        .unwrap();
        let port_holon = PortHolon::new(
            DiracStructure::skew_graph(&structure).unwrap(),
            PortCounts {
                storage: 2,
                resistive: 1,
                external: 0,
                active: 0,
            },
            diagonal(&[1, 2]),
            ResistiveRelation::new(d).unwrap(),
        )
        .unwrap();
        let law = ReferenceHolon::new(
            Holon::new(port_holon).unwrap(),
            integer(1),
            Scheme::Midpoint,
        )
        .unwrap();
        let advance = check_exact_advance(&law, &HolonState::new(v), &[]).unwrap();
        let effort = law.kinds(&advance).unwrap().storage.effort().to_vec();
        assert_eq!(advance.balance.dissipated, quad(&face, &effort).unwrap());
        assert!(advance.balance.dissipated.is_positive());
    }

    /// `Holon/Conformance.lc_pump_work`: the pumped LC loop is lossless and its energy
    /// changes by the pump work only.
    #[test]
    fn the_pumped_lc_loop_changes_energy_by_pump_work_only() {
        let lc_exchange = integer_matrix(&[&[0, 1], &[-1, 0]]).unwrap();
        let port_holon = PortHolon::medium(
            &lc_exchange,
            &zero(2, 2),
            diagonal(&[1, 1]),
            &zero(2, 0),
            false,
        )
        .unwrap();
        let pump = Pump {
            schedule: PumpSchedule::new(vec![diagonal(&[1, 1]), diagonal(&[2, 1])]).unwrap(),
            clock: Clock::ring(rat(1, 2), 2).unwrap(),
        };
        let holon = Holon::new(port_holon).unwrap().with_pump(pump).unwrap();
        let law = ReferenceHolon::new(holon, rat(1, 2), Scheme::Midpoint).unwrap();
        let start = HolonState::new(ints(&[1, 0]));
        let (end, total) = check_run(&law, &start, &[], 6).unwrap();
        assert!(total.dissipated.is_zero() && total.port.is_zero() && total.active.is_zero());
        assert_eq!(total.stored_change, total.deposition_work);
        assert!(!total.deposition_work.is_zero());
        assert_eq!(
            energy_at(&law, &end).unwrap() - energy_at(&law, &start).unwrap(),
            total.stored_change
        );
    }

    /// `Holon/Conformance.maxwell_gauss`, `Holon/Conformance.maxwell_balance` on the
    /// triangle with its face (`Holon/Conformance.triangle_face_complex`).
    #[test]
    fn maxwell_on_the_triangle_balances_and_keeps_gauss() {
        let d0 = integer_matrix(&[&[-1, 1, 0], &[0, -1, 1], &[1, 0, -1]]).unwrap();
        let complex = CellComplex::new(
            vec![3, 3, 1],
            vec![
                d0.transpose().unwrap(),
                integer_matrix(&[&[1], &[1], &[1]]).unwrap(),
            ],
        )
        .unwrap();
        let d1 = complex.coboundary(1).unwrap().unwrap();
        let maxwell_skew = from_blocks(
            &zero(3, 3),
            &d1.transpose().unwrap(),
            &d1.scaled(&integer(-1)),
            &zero(1, 1),
        )
        .unwrap();
        let g = diagonal(&[1, 2, 1, 3]);
        let state = HolonState::new(ints(&[1, 0, -2, 1]));
        // Lossless: the edge field's discrete divergence does not move.
        let lossless = medium_law(
            &maxwell_skew,
            &zero(4, 4),
            g.clone(),
            &zero(4, 0),
            rat(1, 2),
        );
        let advance = check_exact_advance(&lossless, &state, &[]).unwrap();
        let delta = sub(&advance.state.configuration, &state.configuration);
        let divergence = complex
            .incidence()
            .unwrap()
            .transpose()
            .unwrap()
            .apply(&delta[..3])
            .unwrap();
        assert!(is_zero(&divergence));
        assert!(advance.balance.stored_change.is_zero());
        // Ohmic loss on one edge with a source: Joule loss plus source power.
        let ohmic = ExactRatMatrix::from_diagonal(ints(&[1, 0, 0, 0])).unwrap();
        let source = integer_matrix(&[&[1], &[0], &[0], &[0]]).unwrap();
        let lossy = medium_law(&maxwell_skew, &ohmic, g, &source, rat(1, 2));
        let advance = check_exact_advance(&lossy, &state, &ints(&[2])).unwrap();
        assert!(advance.balance.dissipated.is_positive());
    }

    fn hat(x: &[Rat]) -> ExactRatMatrix {
        matrix(3, 3, |r, c| match (r, c) {
            (0, 1) => -x[2].clone(),
            (0, 2) => x[1].clone(),
            (1, 0) => x[2].clone(),
            (1, 2) => -x[0].clone(),
            (2, 0) => -x[1].clone(),
            (2, 1) => x[0].clone(),
            _ => Rat::zero(),
        })
        .unwrap()
    }

    /// `Holon/Conformance.hat_casimir`, `Holon/Conformance.navierStokes_balance`.
    #[test]
    fn the_so3_lie_poisson_witness_balances_and_keeps_its_casimir() {
        let x = ints(&[1, 2, 3]);
        assert!(dot(&x, &hat(&x).apply(&ints(&[4, -1, 2])).unwrap()).is_zero());
        // Euler with G = 1: energy is the Casimir |x|²/2, preserved exactly word by word.
        let mut state = HolonState::new(x.clone());
        for _ in 0..3 {
            let law = medium_law(
                &hat(&state.configuration),
                &zero(3, 3),
                diagonal(&[1, 1, 1]),
                &zero(3, 0),
                rat(1, 2),
            );
            let advance = check_exact_advance(&law, &state, &[]).unwrap();
            assert!(advance.balance.stored_change.is_zero());
            state = HolonState::new(advance.state.configuration);
        }
        assert_eq!(dot(&state.configuration, &state.configuration), dot(&x, &x));
        // Navier–Stokes with G = diag(1,2,3) and viscosity: the energy drops by the dissipation.
        let law = medium_law(
            &hat(&x),
            &ExactRatMatrix::from_diagonal(vec![rat(1, 10); 3]).unwrap(),
            diagonal(&[1, 2, 3]),
            &zero(3, 0),
            rat(1, 4),
        );
        let advance = check_exact_advance(&law, &HolonState::new(x), &[]).unwrap();
        assert_eq!(
            advance.balance.stored_change,
            -advance.balance.dissipated.clone()
        );
        assert!(advance.balance.dissipated.is_positive());
    }

    /// `Holon/Element.backwardEuler_defect_witness`.
    #[test]
    fn backward_euler_carries_its_defect() {
        let port_holon = PortHolon::medium(
            &zero(1, 1),
            &zero(1, 1),
            diagonal(&[1]),
            &integer_matrix(&[&[1]]).unwrap(),
            false,
        )
        .unwrap();
        let law = ReferenceHolon::new(
            Holon::new(port_holon).unwrap(),
            integer(1),
            Scheme::BackwardEuler,
        )
        .unwrap();
        let advance = check_exact_advance(&law, &HolonState::new(ints(&[0])), &ints(&[1])).unwrap();
        assert_eq!(advance.state.configuration, ints(&[1]));
        assert_eq!(advance.balance.discretization_defect, rat(-1, 2));
        assert_eq!(advance.balance.port, integer(1));
        assert_eq!(advance.balance.stored_change, rat(1, 2));
    }

    // ---------------------------------------------------------------------------------------
    // Interaction, receivers

    /// `Holon/Conformance.two_media_witness` with a real shared port: two resistive media
    /// joined at their inputs (flows opposite, efforts equal) form a Holon whose word is exact and
    /// whose energy and dissipation are additive.
    #[test]
    fn a_holon_of_holons_is_a_holon() {
        let one = |g: i64| {
            medium_law(
                &zero(1, 1),
                &integer_matrix(&[&[1]]).unwrap(),
                diagonal(&[g]),
                &integer_matrix(&[&[1]]).unwrap(),
                integer(1),
            )
        };
        let (composite, advance) =
            check_interaction(&one(2), &one(3), &[(0, 0)], &ints(&[3]), &ints(&[-2]), &[]).unwrap();
        assert_eq!(composite.holon().port_holon().counts().external, 0);
        assert_eq!(
            composite
                .holon()
                .port_holon()
                .storage_energy(&ints(&[1, 1]))
                .unwrap(),
            integer(1) + rat(3, 2)
        );
        // The shared port forces opposite storage efforts at the midpoint (the constraint
        // `2x_A + 3x_B = 0`; the state starts on it, so the word dissipates).
        let effort = composite.kinds(&advance).unwrap().storage.effort().to_vec();
        assert_eq!(&effort[0] + &effort[1], Rat::zero());
        assert!(advance.balance.dissipated.is_positive());
    }

    /// `Holon/Law.passive_reading`.
    #[test]
    fn a_passive_coholon_reads_with_zero_power() {
        let law = medium_law(
            &zero(2, 2),
            &zero(2, 2),
            form(&[vec![2, 1], vec![1, 1]]),
            &zero(2, 0),
            integer(1),
        );
        let reading = law
            .receive(
                &HolonState::new(ints(&[1, 1])),
                &integer_matrix(&[&[1, -1]]).unwrap(),
            )
            .unwrap();
        assert_eq!(reading.value, ints(&[1]));
        assert!(reading.power.is_zero());
    }

    /// `Holon/Law.active_receiver_law`.
    #[test]
    fn an_active_receiver_dissipates_the_interface_power() {
        let g = ResistiveRelation::new(integer_matrix(&[&[2, 1], &[1, 1]]).unwrap()).unwrap();
        let reading = active_receiver(&g, &ints(&[1, 2]), &ints(&[0, -1])).unwrap();
        assert_eq!(
            &reading.holon_power + &reading.receiver_power,
            -reading.dissipation.clone()
        );
        assert_eq!(reading.dissipation, integer(17));
    }

    // ---------------------------------------------------------------------------------------
    // Restriction

    #[test]
    fn a_port_restriction_of_the_medium_passes_the_restriction_check() {
        let law = medium_law(
            &integer_matrix(&[&[0, 1], &[-1, 0]]).unwrap(),
            &integer_matrix(&[&[1, 0], &[0, 0]]).unwrap(),
            diagonal(&[1, 1]),
            &integer_matrix(&[&[1], &[0]]).unwrap(),
            integer(1),
        );
        // Restrict the five ports (σ σ ρ ρ π) to the storage and input ports summed.
        let map = PortMap::new(integer_matrix(&[&[1, 1, 0, 0, 0], &[0, 0, 0, 0, 1]]).unwrap());
        check_restriction(&law, &map, &ints(&[1, -2, 3, 0, 5]), &ints(&[2, -1])).unwrap();
    }

    // ---------------------------------------------------------------------------------------
    // Deposition

    fn learned_law(learned: &ExactRatMatrix) -> ReferenceHolon {
        let port_holon = PortHolon::medium(
            &zero(2, 2),
            &zero(2, 2),
            diagonal(&[1, 1]),
            &zero(2, 0),
            true,
        )
        .unwrap();
        let holon = Holon::new(port_holon)
            .unwrap()
            .with_active(ActiveRelation::new(learned.clone()).unwrap())
            .unwrap();
        ReferenceHolon::new(holon, integer(1), Scheme::Midpoint).unwrap()
    }

    /// `Holon/Deposition.normal_law_divergence_witness`,
    /// `Holon/Deposition.projected_committed_energy_bound`.
    #[test]
    fn the_indefinite_normal_law_grows_ninefold_and_the_projection_restores_the_bound() {
        let identity = diagonal(&[1, 1]);
        // Unprojected: the committed state is (3ⁿ, 0) and the energy grows ×9 per commit.
        let law = learned_law(&indefinite_block());
        let mut state = HolonState::new(divergent_state(0));
        let mut ledger = DepositLedger::new(energy_at(&law, &state).unwrap());
        for n in 1..=3u32 {
            let advance = check_exact_advance(&law, &state, &[]).unwrap();
            assert_eq!(advance.state.configuration, divergent_state(n));
            assert_eq!(
                energy_at(&law, &advance.state).unwrap(),
                integer(9) * energy_at(&law, &state).unwrap()
            );
            assert!(advance.balance.active.is_positive());
            let reading = ledger
                .commit(
                    &identity,
                    &identity,
                    &Rat::zero(),
                    energy_at(&law, &advance.state).unwrap(),
                )
                .unwrap();
            assert!(!reading.holds);
            state = advance.state;
        }
        // Projected: the word is passive and the bound ∏(1 + ε_k) E₀ holds at every commit.
        let projected = project_passive(&indefinite_block()).unwrap().projected;
        let law = learned_law(&projected);
        let mut state = HolonState::new(ints(&[1, 1]));
        let mut ledger = DepositLedger::new(energy_at(&law, &state).unwrap());
        for _ in 0..4 {
            let advance = check_exact_advance(&law, &state, &[]).unwrap();
            assert!(advance.balance.active <= Rat::zero());
            let reading = ledger
                .commit(
                    &identity,
                    &identity,
                    &Rat::zero(),
                    energy_at(&law, &advance.state).unwrap(),
                )
                .unwrap();
            assert!(reading.holds);
            state = advance.state;
        }
    }

    /// `Holon/Deposition.commit_balance` with a real deposit, and the ledger's `ε_k`.
    #[test]
    fn the_commit_balance_is_word_plus_deposition_work() {
        let law = learned_law(
            &project_passive(&integer_matrix(&[&[1, 2], &[0, -3]]).unwrap())
                .unwrap()
                .projected,
        );
        let before = diagonal(&[1, 1]);
        let after = form(&[vec![3, 1], vec![1, 2]]);
        let state = HolonState::new(ints(&[2, -1]));
        let learned = law.holon().active().relation().clone();
        let advance = law.commit(&state, &[], &before, &learned, &after).unwrap();
        assert!(advance.balance.is_exact());
        assert_eq!(
            advance.balance.stored_change,
            advance.balance.word_change() + advance.balance.deposition_work.clone()
        );
        // after ⪯ (1 + ε) before with ε = 3 (eigenvalues of `after` are (5 ± √5)/2 < 4).
        let mut ledger = DepositLedger::new(storage_energy(&before, &state.configuration).unwrap());
        let reading = ledger
            .commit(
                &before,
                &after,
                &integer(3),
                storage_energy(&after, &advance.state.configuration).unwrap(),
            )
            .unwrap();
        assert!(reading.holds);
        assert_eq!(ledger.product(), &integer(4));
        assert!(ledger.commits() == 1 && Rat::one() < *ledger.product());
    }
}
