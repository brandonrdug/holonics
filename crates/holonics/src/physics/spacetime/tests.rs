//! One test per law and one per counterexample of the spacetime instance.

use std::collections::BTreeSet;

use num_traits::{One, Zero};

use super::*;
use crate::aeon::Form;
use crate::compression::landmark::{doppler_chart, velocity_addition};
use crate::geometry::{RatMat3, RatVec3};
use crate::holarchy::Grain;
use crate::physics::fluid::cells::{CubicalComplex, GridCell, reflect_across_face};
use crate::physics::fluid::control_volume::{
    AffineFlow, ControlVolume, NewtonianMaterial, pressure_part, trace,
};
use crate::physics::thermal::ThermalCell;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::{Rat, integer, rat};

fn doppler(k: Rat) -> DopplerBoost {
    DopplerBoost::new(k).unwrap()
}

fn gradient_matrix() -> RatMat3 {
    gradient()
}

fn gradient() -> RatMat3 {
    RatMat3::new([
        [integer(1), integer(2), Rat::zero()],
        [Rat::zero(), integer(-1), integer(3)],
        [integer(1), Rat::zero(), integer(2)],
    ])
}

/// A constituted K3 cell: a unit control volume, a thermal cell of energy `6`, a Newtonian material
/// `μ = 1/2`, `λ = 1/3` at pressure `3/2`, the flow gradient above and a heat flux.
fn k3_state() -> (ConstitutedState, AffineFlow, ControlVolume) {
    let volume = ControlVolume::new(GridCell::unit_cube(3).unwrap()).unwrap();
    let thermal = ThermalCell::new(integer(2), integer(6)).unwrap();
    let flow = AffineFlow {
        velocity: RatVec3::zero(),
        gradient: gradient(),
    };
    let state = ConstitutedState::of_cells(
        &volume,
        integer(10),
        &thermal,
        rat(3, 2),
        NewtonianMaterial::new(rat(1, 2), rat(1, 3)),
        &flow,
        RatVec3::new(rat(1, 4), rat(-1, 5), Rat::zero()),
    );
    (state, flow, volume)
}

fn zero4() -> Vector4 {
    std::array::from_fn(|_| Rat::zero())
}

/// Lean `StressEnergy.sourceMap_symmetric`, `sourceMap_restReading`: the K3 cell's source is
/// symmetric, its rest observer reads `ε = ρ₀ + U/V`, and its mixed entries are the heat flux.
#[test]
fn the_source_map_is_symmetric_and_reads_its_energy_density() {
    let (state, _, _) = k3_state();
    let t = source_map(&state);
    assert!(t.is_symmetric());
    let rest: Vector4 = [Rat::one(), Rat::zero(), Rat::zero(), Rat::zero()];
    assert_eq!(t.observer_bilinear(&rest, &rest), integer(16));
    assert_eq!(t.at(0, 1), &rat(1, 4));
    assert_eq!(t.at(2, 0), &rat(-1, 5));
    assert_eq!(t.at(1, 2), &-state.cauchy().rows[0][1].clone());
}

/// Lean `sourceMap_perfect`: without viscosity or heat flux the source is `diag(ε, p, p, p)`.
#[test]
fn without_viscosity_or_heat_the_source_is_a_perfect_fluid() {
    let (mut state, _, _) = k3_state();
    state.material = NewtonianMaterial::new(Rat::zero(), Rat::zero());
    state.heat_flux = RatVec3::zero();
    let t = source_map(&state);
    for mu in 0..4 {
        for nu in 0..4 {
            let expected = match (mu, nu) {
                (0, 0) => integer(16),
                (m, n) if m == n => rat(3, 2),
                _ => Rat::zero(),
            };
            assert_eq!(t.at(mu, nu), &expected, "entry ({mu}, {nu})");
        }
    }
}

/// Lean `sourceMap_spatialTrace`: the spatial trace is the bulk-viscous pressure
/// `3p − (2μ + 3λ) tr G`.
#[test]
fn the_spatial_trace_is_the_bulk_viscous_pressure() {
    let (state, flow, _) = k3_state();
    let expected = integer(3) * rat(3, 2)
        - (integer(2) * rat(1, 2) + integer(3) * rat(1, 3)) * trace(&flow.gradient);
    assert_eq!(source_map(&state).spatial_trace(), expected);
}

/// Lean `sourceMap_boostedEnergy`: the unit timelike observer `(5/3, 4/3, 0, 0)` reads
/// `25ε/9 − 40q₁/9 + 16T¹¹/9`.
#[test]
fn a_boosted_observer_mixes_energy_heat_and_stress() {
    let (state, _, _) = k3_state();
    let t = source_map(&state);
    let boosted: Vector4 = [rat(5, 3), rat(4, 3), Rat::zero(), Rat::zero()];
    assert!(ReceiverWorldline::new(boosted.clone(), [zero4(), zero4(), zero4(), zero4()]).is_ok());
    let expected = rat(25, 9) * state.energy_density() - rat(40, 9) * &state.heat_flux.x
        + rat(16, 9) * t.at(1, 1);
    assert_eq!(t.observer_bilinear(&boosted, &boosted), expected);
}

/// Lean `comoving_observerDivergence`, joined to the K3 heat port: the comoving receiver's current
/// has divergence `f⁰ − p tr G + Φ`, and its deformation term less the pressure work is the viscous
/// heat the fluid's control volume hands to the thermal port, computed there from face tractions.
#[test]
fn the_comoving_deformation_is_pressure_work_plus_viscous_heat() {
    let (state, flow, volume) = k3_state();
    let receiver = ReceiverWorldline::comoving(&flow, &RatVec3::zero()).unwrap();
    let force: Vector4 = [rat(1, 5), integer(7), integer(-2), rat(1, 3)];
    let current = observer_current(&source_map(&state), &receiver, &force);
    let pressure_work = -state.pressure.clone() * trace(&flow.gradient);
    let heat = state.material.dissipation(&flow.gradient);
    assert_eq!(current.force_power, rat(1, 5));
    assert_eq!(current.deformation, &pressure_work + &heat);
    assert_eq!(current.divergence, rat(1, 5) + &pressure_work + &heat);
    let cell = volume.cell_return(&integer(1), &flow, &state.pressure, &state.material);
    assert_eq!(
        &current.deformation - &pressure_work,
        cell.heat.rate().clone()
    );
    assert_eq!(
        &current.deformation - &pressure_work,
        cell.mechanical_deficit()
    );
}

/// Lean `rigid_comoving_reads_force`, `observerCurrentDivergence_killing`: a rigidly rotating
/// comoving receiver is Killing and reads the force alone.
#[test]
fn a_rigid_receiver_reads_the_force_alone() {
    let (mut state, _, _) = k3_state();
    let rotation = RatMat3::new([
        [Rat::zero(), integer(2), integer(-1)],
        [integer(-2), Rat::zero(), integer(3)],
        [integer(1), integer(-3), Rat::zero()],
    ]);
    state.gradient = rotation.clone();
    let flow = AffineFlow {
        velocity: RatVec3::zero(),
        gradient: rotation,
    };
    let receiver = ReceiverWorldline::comoving(&flow, &RatVec3::zero()).unwrap();
    assert!(receiver.is_killing());
    let force: Vector4 = [rat(2, 7), integer(1), integer(1), integer(1)];
    let current = observer_current(&source_map(&state), &receiver, &force);
    assert!(current.deformation.is_zero());
    assert_eq!(current.divergence, rat(2, 7));
}

/// [counterexample] Lean `expanding_receiver_reads_pressure_work`: a force-free source read by a
/// uniformly expanding receiver has current divergence `−3`, the pressure work.
#[test]
fn an_expanding_receiver_reads_pressure_work() {
    let state = ConstitutedState {
        rest_energy: integer(1),
        internal_energy: Rat::zero(),
        pressure: integer(1),
        material: NewtonianMaterial::new(Rat::zero(), Rat::zero()),
        gradient: RatMat3::identity(),
        heat_flux: RatVec3::zero(),
    };
    let flow = AffineFlow {
        velocity: RatVec3::zero(),
        gradient: RatMat3::identity(),
    };
    let receiver = ReceiverWorldline::comoving(&flow, &RatVec3::zero()).unwrap();
    let current = observer_current(&source_map(&state), &receiver, &zero4());
    assert_eq!(current.divergence, integer(-3));
}

/// [counterexample] Lean `sheared_receiver_reads_viscous_heat`: a force-free viscous source read by
/// a sheared receiver has current divergence `+1`, the viscous heat.
#[test]
fn a_sheared_receiver_reads_viscous_heat() {
    let shear = RatMat3::from_i64([[0, 1, 0], [0, 0, 0], [0, 0, 0]]);
    let state = ConstitutedState {
        rest_energy: integer(1),
        internal_energy: Rat::zero(),
        pressure: Rat::zero(),
        material: NewtonianMaterial::new(integer(1), Rat::zero()),
        gradient: shear.clone(),
        heat_flux: RatVec3::zero(),
    };
    let flow = AffineFlow {
        velocity: RatVec3::zero(),
        gradient: shear,
    };
    let receiver = ReceiverWorldline::comoving(&flow, &RatVec3::zero()).unwrap();
    let current = observer_current(&source_map(&state), &receiver, &zero4());
    assert_eq!(current.divergence, integer(1));
}

/// [counterexample] A receiver's velocity must be a future-directed unit timelike vector.
#[test]
fn a_receiver_must_be_unit_timelike_and_future_directed() {
    let zero = [zero4(), zero4(), zero4(), zero4()];
    let slow: Vector4 = [integer(1), rat(1, 2), Rat::zero(), Rat::zero()];
    assert!(matches!(
        ReceiverWorldline::new(slow, zero.clone()),
        Err(SpacetimeError::NotUnitTimelike { .. })
    ));
    let past: Vector4 = [integer(-1), Rat::zero(), Rat::zero(), Rat::zero()];
    assert_eq!(
        ReceiverWorldline::new(past, zero),
        Err(SpacetimeError::PastDirected)
    );
}

/// [counterexample] A receiver's gradient must preserve its unit norm, `U^ν ∂_μ u_ν = 0`: at rest,
/// `∂_x u_t = 1` is the gradient of no unit timelike field and is refused; the comoving receiver of a
/// flow that moves at the event is refused.
#[test]
fn a_receiver_gradient_must_preserve_the_unit_norm() {
    let rest: Vector4 = [Rat::one(), Rat::zero(), Rat::zero(), Rat::zero()];
    let mut gradient = [zero4(), zero4(), zero4(), zero4()];
    gradient[1][0] = Rat::one();
    assert_eq!(
        ReceiverWorldline::new(rest, gradient),
        Err(SpacetimeError::GradientNotUnitPreserving { row: 1 })
    );
    let moving = AffineFlow {
        velocity: RatVec3::new(Rat::one(), Rat::zero(), Rat::zero()),
        gradient: gradient_matrix(),
    };
    assert!(matches!(
        ReceiverWorldline::comoving(&moving, &RatVec3::zero()),
        Err(SpacetimeError::FlowNotAtRest { .. })
    ));
}

/// Lean `StressEnergy.observerBilinear_transport`, `boosted_reads_transported`, `boostT_lorentz`,
/// `boostedObserver_eq`, `sourceMap_boosted_transport`: a moving receiver with a nonzero,
/// `u`-orthogonal gradient, the comoving one carried by the boost `k = 2`, reads the transported
/// source, force and gradient with the same force power, deformation and divergence; the boosted
/// observer `Λe₀` reads `T` as the rest observer reads `Λ⁻¹TΛ⁻ᵀ`.
#[test]
fn a_boosted_receiver_reads_the_transported_source_alike() {
    let (state, flow, _) = k3_state();
    let t = source_map(&state);
    let rest_receiver = ReceiverWorldline::comoving(&flow, &RatVec3::zero()).unwrap();
    let force: Vector4 = [rat(1, 5), integer(7), integer(-2), rat(1, 3)];
    let rest = observer_current(&t, &rest_receiver, &force);
    let boost = LorentzMap::boost_x(&doppler(integer(2)));
    assert_eq!(LorentzMap::new(boost.matrix().clone()), Ok(boost.clone()));
    let moving = rest_receiver.transported(&boost).unwrap();
    assert!(
        moving
            .gradient()
            .iter()
            .flatten()
            .any(|entry| !entry.is_zero())
    );
    assert!(!moving.velocity()[1].is_zero());
    let carried = observer_current(&boost.tensor(&t), &moving, &boost.vector(&force));
    assert_eq!(carried.force_power, rest.force_power);
    assert_eq!(carried.deformation, rest.deformation);
    assert_eq!(carried.divergence, rest.divergence);
    let three = LorentzMap::boost_x(&doppler(integer(3)));
    let observer = three.vector(&[Rat::one(), Rat::zero(), Rat::zero(), Rat::zero()]);
    assert_eq!(observer, [rat(5, 3), rat(4, 3), Rat::zero(), Rat::zero()]);
    assert_eq!(
        t.observer_bilinear(&observer, &observer),
        three.inverse().tensor(&t).at(0, 0).clone()
    );
    let mut skew = boost.matrix().clone();
    skew[0][1] = Rat::zero();
    assert_eq!(LorentzMap::new(skew), Err(SpacetimeError::NotLorentz));
}

/// Lean `StressEnergy.trace_reversal`, `traceReversed_zero_zero`, `sourceMap_traceReversed`,
/// `perfectFluid_traceReversed`, `dust_newtonian_source`: the trace reversal is an involution, so the
/// field equation `Ric − ½(tr Ric)η = κT` is `Ric = κT̄`; `T̄⁰⁰ = (ε + Σ Tⁱⁱ)/2`, `(ε + 3p)/2` on a
/// perfect fluid and `ε/2` on dust; at `κ = 8πG` dust reads `R₀₀ = 4πGρ` (with `πG` a rational
/// stand-in `u`: `8u · ρ/2 = 4uρ`).
#[test]
fn trace_reversal_gives_the_newtonian_coupling() {
    let (state, _, _) = k3_state();
    let t = source_map(&state);
    assert_eq!(
        t.trace_reversed().at(0, 0),
        &((state.energy_density() + t.spatial_trace()) / integer(2))
    );
    let kappa = integer(8) * rat(3, 7);
    let ricci = t.trace_reversed().scaled(&kappa);
    assert_eq!(ricci.trace_reversed(), t.scaled(&kappa));
    let (rho, pressure) = (integer(5), rat(1, 2));
    let mut perfect = state.clone();
    perfect.material = NewtonianMaterial::new(Rat::zero(), Rat::zero());
    perfect.heat_flux = RatVec3::zero();
    perfect.rest_energy = rho.clone();
    perfect.internal_energy = Rat::zero();
    perfect.pressure = pressure.clone();
    assert_eq!(
        source_map(&perfect).trace_reversed().at(0, 0),
        &((&rho + integer(3) * &pressure) / integer(2))
    );
    perfect.pressure = Rat::zero();
    let dust = source_map(&perfect);
    assert_eq!(dust.trace_reversed().at(0, 0), &(&rho / integer(2)));
    assert_eq!(
        dust.trace_reversed().scaled(&kappa).at(0, 0),
        &(integer(4) * rat(3, 7) * &rho)
    );
}

/// The unit square of the plane chart as a cubical complex.
fn unit_square() -> CubicalComplex {
    CubicalComplex::of_tops(&[GridCell::unit_cube(2).unwrap()]).unwrap()
}

/// Lean `discrete_bianchi`, `grid_field_conserves`, `square_field_current`: the square's field has a
/// nonzero Einstein side (its boundary loop) whose boundary vanishes.
#[test]
fn the_discrete_bianchi_identity_is_the_boundary_of_a_boundary() {
    let square = unit_square();
    let einstein = cell_einstein(square.complex(), 1, &[integer(1)]).unwrap();
    assert!(einstein.einstein.iter().any(|entry| !entry.is_zero()));
    assert!(einstein.bianchi.iter().all(Rat::is_zero));
}

/// Lean `conservation_return`, `conservation_return_eq`, `cell_field_conserves`: with the derived
/// Bianchi identity and a metric cycle, `κ∂j = −∂𝓡`; the field equation's source is conserved, and a
/// perturbed source's defect is exactly the residual's divergence.
#[test]
fn the_conservation_return_relates_source_and_residual() {
    let square = unit_square();
    let field = cell_einstein(square.complex(), 1, &[integer(3)]).unwrap();
    let metric = cell_einstein(square.complex(), 1, &[integer(1)])
        .unwrap()
        .einstein;
    let (lambda, kappa) = (rat(1, 2), integer(2));
    // The source solving `G + Λg = κj`.
    let source: Vec<Rat> = field
        .einstein
        .iter()
        .zip(&metric)
        .map(|(g, m)| (g + &lambda * m) / &kappa)
        .collect();
    let solved = conservation_return(
        &field.divergence,
        &field.einstein,
        &metric,
        &source,
        &lambda,
        &kappa,
    )
    .unwrap();
    assert!(solved.residual.iter().all(Rat::is_zero));
    assert!(solved.is_conserved());
    let mut perturbed = source.clone();
    perturbed[0] += integer(1);
    let defect = conservation_return(
        &field.divergence,
        &field.einstein,
        &metric,
        &perturbed,
        &lambda,
        &kappa,
    )
    .unwrap();
    assert!(!defect.is_conserved());
    for (source_div, residual_div) in defect
        .source_divergence
        .iter()
        .zip(&defect.residual_divergence)
    {
        assert_eq!(&kappa * source_div, -residual_div.clone());
    }
}

/// [counterexample] Lean `field_equation_without_bianchi`: over a divergence that does not annihilate
/// the Einstein side, the return is refused with the Bianchi defect.
#[test]
fn without_the_bianchi_port_the_source_is_not_conserved() {
    let identity = ExactRatMatrix::identity(1).unwrap();
    let refused = conservation_return(
        &identity,
        &[integer(1)],
        &[Rat::zero()],
        &[integer(1)],
        &Rat::zero(),
        &integer(1),
    );
    assert_eq!(
        refused,
        Err(SpacetimeError::NoBianchi {
            defect: vec![integer(1)]
        })
    );
    assert_eq!(
        conservation_return(
            &identity,
            &[Rat::zero()],
            &[integer(1)],
            &[Rat::zero()],
            &integer(1),
            &integer(1)
        ),
        Err(SpacetimeError::MetricNotCompatible {
            defect: vec![integer(1)]
        })
    );
}

/// [counterexample] Lean `segment_current_not_conserved`: a current that is not a boundary, one unit
/// segment, has nonzero boundary.
#[test]
fn a_current_that_is_not_a_boundary_is_not_conserved() {
    let segment = CubicalComplex::of_tops(&[GridCell::unit_cube(1).unwrap()]).unwrap();
    let boundary = segment
        .complex()
        .boundary(1)
        .unwrap()
        .apply(&[integer(1)])
        .unwrap();
    assert!(boundary.iter().any(|entry| !entry.is_zero()));
}

/// Lean `potential_field_block_flux_zero`, `potential_field_total_flux_zero`, through
/// `Holarchy/View.shared_face_cancels`: on the square joined to its reflection, a current that is
/// the coboundary of a potential has zero flux through every block at both grains; a single-edge
/// current does not.
#[test]
fn a_potential_sourced_current_has_no_flux_at_any_grain() {
    let reflection = reflect_across_face(2, 0, true).unwrap();
    let holarchy = reflection.join().unwrap();
    let complex = reflection.glued.complex();
    let potential: Vec<Rat> = (0..complex.cells(0) as i64)
        .map(|v| rat(v * v + 1, 3))
        .collect();
    let current: Vec<Rat> = pressure_part(complex, &potential)
        .unwrap()
        .into_iter()
        .map(|entry| entry / integer(5))
        .collect();
    let fine = Grain::new(vec![BTreeSet::from([0]), BTreeSet::from([1])]);
    let coarse = Grain::new(vec![BTreeSet::from([0, 1])]);
    for grain in [&fine, &coarse] {
        assert!(
            holarchy
                .interface_flux(grain, &current)
                .unwrap()
                .iter()
                .all(Rat::is_zero)
        );
    }
    let unit_on = |edge: usize| -> Vec<Rat> {
        (0..complex.cells(1))
            .map(|e| if e == edge { Rat::one() } else { Rat::zero() })
            .collect()
    };
    // The shared face cancels once: its fine fluxes are opposite, its whole's flux is zero.
    let shared = unit_on(reflection.shared_face);
    let split = holarchy.interface_flux(&fine, &shared).unwrap();
    assert_eq!(split[0], -split[1].clone());
    assert!(!split[0].is_zero());
    assert!(holarchy.interface_flux(&coarse, &shared).unwrap()[0].is_zero());
    // A current on an outer edge is not a coboundary: the whole reads its flux at every grain.
    let outer = (0..complex.cells(1))
        .find(|e| *e != reflection.shared_face)
        .unwrap();
    let whole = holarchy.interface_flux(&coarse, &unit_on(outer)).unwrap()[0].clone();
    let fine_total: Rat = holarchy
        .interface_flux(&fine, &unit_on(outer))
        .unwrap()
        .into_iter()
        .sum();
    assert!(!whole.is_zero());
    assert_eq!(whole, fine_total);
}

/// Lean `Boost.boost_pairing`, `boost_interval`, `boost_mul`, `boost_tx`, `doppler_betaOf`,
/// `velocity_addition`; `CompositeMassEnergy.multiplicativeScale_lorentz_identity`,
/// `rational_boost_parameters`; `Compression/Landmark/FixedPoint.doppler_vadd`: the boost is the
/// Doppler ratio, and its velocity addition is the landmark owner's Doppler chart.
#[test]
fn the_boost_is_the_doppler_ratio() {
    let (a, b) = (doppler(integer(3)), doppler(rat(5, 2)));
    assert_eq!((a.gamma(), a.beta()), (rat(5, 3), rat(4, 5)));
    assert_eq!(
        a.gamma() * a.gamma() - a.gamma_beta() * a.gamma_beta(),
        Rat::one()
    );
    let (e, f) = (
        LightCone::of_tx(&integer(2), &rat(1, 3)),
        LightCone::of_tx(&integer(-1), &integer(4)),
    );
    assert_eq!(a.apply(&e).pairing(&a.apply(&f)), e.pairing(&f));
    assert_eq!(a.apply(&e).interval(), e.interval());
    assert_eq!(a.apply(&b.apply(&e)), a.compose(&b).apply(&e));
    let ab = a.compose(&b);
    let chart = |boost: &DopplerBoost| doppler_chart(&boost.beta(), &Rat::one()).unwrap();
    assert_eq!(chart(&a), a.ratio() * a.ratio());
    assert_eq!(chart(&ab), chart(&a) * chart(&b));
    assert_eq!(DopplerBoost::from_velocity(&ab.beta()).unwrap(), ab);
    assert_eq!(
        velocity_addition(&b.beta(), &Rat::one())
            .unwrap()
            .act(&a.beta()),
        Ok(ab.beta())
    );
    let moved = a.apply(&e);
    assert_eq!(
        moved.time(),
        a.gamma() * e.time() - a.gamma_beta() * e.space()
    );
    assert_eq!(
        moved.space(),
        a.gamma() * e.space() - a.gamma_beta() * e.time()
    );
    assert_eq!(
        ab.rapidity_log2().unwrap(),
        a.rapidity_log2().unwrap().plus(&b.rapidity_log2().unwrap())
    );
}

/// Lean `time_dilation`, `dilation_is_rate`, `clockReading_self`: the owner's aeon rate of two
/// inertial clocks is `(τγ(k₁/k₂) : τ)`, a function of the relative Doppler ratio only.
#[test]
fn time_dilation_is_the_rate_of_two_aeon_clocks() {
    let tau = rat(7, 2);
    let rest_reads_moving =
        time_dilation(&doppler(integer(1)), &doppler(integer(3)), &tau).unwrap();
    assert_eq!(rest_reads_moving.numerator(), &(rat(5, 3) * &tau));
    assert_eq!(rest_reads_moving.denominator(), &tau);
    let relative = time_dilation(&doppler(integer(2)), &doppler(integer(6)), &tau).unwrap();
    assert!(relative.projectively_equal(&rest_reads_moving));
    let own = time_dilation(&doppler(integer(3)), &doppler(integer(3)), &tau).unwrap();
    assert_eq!(own.numerator(), own.denominator());
}

/// Lean `twin_interval`, `one_lt_gammaOf`: the stay-at-home twin ages `2γτ`, read from the joint
/// displacement, the traveller `2τ`; equal only at `k = 1`. A negative proper time is refused.
#[test]
fn the_stay_at_home_twin_ages_more() {
    let reading = twin(&doppler(integer(3)), &integer(1)).unwrap();
    assert_eq!(reading.traveller, integer(2));
    assert_eq!(reading.home, rat(10, 3));
    assert_eq!(reading.home_interval, &reading.home * &reading.home);
    assert!(reading.home > reading.traveller);
    let still = twin(&doppler(integer(1)), &integer(1)).unwrap();
    assert_eq!(still.home, still.traveller);
    assert!(matches!(
        twin(&doppler(integer(3)), &integer(-2)),
        Err(SpacetimeError::Coefficient { .. })
    ));
}

/// Lean `wigner_decomposition`, `loop_returns_rotation`, `rest_vertex_angle`, `far_vertex_angle`,
/// `right_angle_at_P`, `vertexAngles_on_circle`, `wigner_angle_is_defect`, `wigner_two_three`: at
/// `k₁ = 2`, `k₂ = 3` the loop returns the rotation `(35/37, −12/37)`, the composite is its pure boost
/// times it, and the angle is the defect of the velocity triangle read from its vertices.
#[test]
fn the_wigner_rotation_is_the_defect_of_the_velocity_triangle() {
    let wigner = wigner_rotation(&doppler(integer(2)), &doppler(integer(3))).unwrap();
    assert_eq!(
        (wigner.cos.clone(), wigner.sin.clone()),
        (rat(35, 37), rat(-12, 37))
    );
    assert_eq!(
        wigner.pure_boost.multiply(&wigner.loop_return),
        wigner.composite
    );
    let t = wigner.triangle.as_ref().unwrap();
    assert_eq!(t.scale_sq, rat(481, 144));
    assert_eq!(
        (t.sin_alpha.clone(), t.cos_alpha.clone()),
        (rat(4, 3), rat(5, 4))
    );
    assert_eq!(
        (t.sin_beta.clone(), t.cos_beta.clone()),
        (rat(3, 4), rat(5, 3))
    );
    assert_eq!(t.orientation, Rat::one());
    assert_eq!(
        &t.sin_alpha * &t.sin_alpha + &t.cos_alpha * &t.cos_alpha,
        t.scale_sq
    );
    assert_eq!(
        &t.sin_beta * &t.sin_beta + &t.cos_beta * &t.cos_beta,
        t.scale_sq
    );
    assert_eq!(&wigner.cos * &t.scale_sq, t.defect_cos_scaled());
    assert_eq!(&wigner.sin * &t.scale_sq, t.defect_sin_scaled());
}

/// [counterexample] Lean `vertexAngles_nonneg`, `orientation`: a ratio below one boosts the other
/// way; the triangle's interior angles keep nonnegative sines and its orientation turns, so the
/// rotation turns with it. At `k₁ = 1/7`, `k₂ = 9/4` the orientation is `−1` and the defect law
/// holds; a unit ratio has no triangle.
#[test]
fn a_reversed_boost_turns_the_orientation_not_the_sines() {
    let wigner = wigner_rotation(&doppler(rat(1, 7)), &doppler(rat(9, 4))).unwrap();
    let t = wigner.triangle.as_ref().unwrap();
    assert_eq!(t.orientation, -Rat::one());
    for value in [&t.sin_alpha, &t.cos_alpha, &t.sin_beta, &t.cos_beta] {
        assert!(*value >= Rat::zero());
    }
    assert_eq!(&wigner.cos * &t.scale_sq, t.defect_cos_scaled());
    assert_eq!(&wigner.sin * &t.scale_sq, t.defect_sin_scaled());
    let flat = wigner_rotation(&doppler(integer(1)), &doppler(integer(3))).unwrap();
    assert_eq!(flat.triangle, None);
    assert_eq!((flat.cos, flat.sin), (Rat::one(), Rat::zero()));
}

/// [counterexample] Lean `boostX_mul_boostX`: collinear boosts compose to the boost of the product
/// ratio, with no rotation.
#[test]
fn collinear_boosts_carry_no_rotation() {
    let (a, b) = (doppler(integer(2)), doppler(integer(3)));
    assert_eq!(a.along_x().multiply(&b.along_x()), a.compose(&b).along_x());
}

/// Lean `NonClosedClock.inertial_clock_silent`: an inertial (exact) clock reads nothing on the
/// cycle and has no production time.
#[test]
fn the_inertial_clock_reads_nothing_on_the_cycle() {
    let square = square_complex().unwrap();
    let potential = [integer(0), rat(3, 2), integer(-4), rat(1, 7)];
    let exact = Form::new(
        [(0, 1), (1, 2), (2, 3), (3, 0)]
            .iter()
            .map(|(s, t)| &potential[*t] - &potential[*s])
            .collect(),
    );
    let reading = read_on_cycle(&square, &exact).unwrap();
    assert!(reading.loop_reading.is_zero());
    assert!(reading.is_clock);
    assert!(reading.production.values().iter().all(Rat::is_zero));
}

/// Lean `sagnac_reading`, `rectangle_area`, `sagnac_is_curvature_flux`, `sagnac_is_production`,
/// `sagnac_not_closed`: a rotating clock reads `2ΩA` on the loop, its curvature flux, all of it
/// production time, and it is not a clock.
#[test]
fn sagnac_is_production_time() {
    let square = square_complex().unwrap();
    let (a, b, omega) = (integer(3), rat(1, 2), rat(2, 5));
    let corners = [
        (Rat::zero(), Rat::zero()),
        (a.clone(), Rat::zero()),
        (a.clone(), b.clone()),
        (Rat::zero(), b.clone()),
    ];
    let reading = read_on_cycle(&square, &sagnac_clock(&omega, &corners)).unwrap();
    let expected = integer(2) * &omega * &a * &b;
    assert_eq!(reading.loop_reading, expected);
    assert_eq!(reading.curvature, vec![expected.clone()]);
    assert_eq!(reading.production_reading, expected);
    assert!(!reading.is_clock);
}

/// Lean `static_reading`, `static_is_production`, `static_not_closed`, `redshift_rate`: a static
/// clock with a lapse gradient reads `(N₁ − N₂)Δt` on the loop, as production time; the owner's rate
/// of the two static receivers is `(N₁Δt : N₂Δt)`, projectively `(N₁ : N₂)`, and a zero interval,
/// the undetermined `(0 : 0)`, is refused.
#[test]
fn the_redshift_is_production_time_and_a_rate_ratio() {
    let square = square_complex().unwrap();
    let (near, far, tick) = (rat(3, 2), integer(1), integer(4));
    let reading = read_on_cycle(&square, &static_clock(&near, &far, &tick)).unwrap();
    assert_eq!(reading.loop_reading, (&near - &far) * &tick);
    assert_eq!(reading.production_reading, reading.loop_reading);
    assert!(!reading.is_clock);
    let redshift = redshift_rate(&near, &far, &tick).unwrap();
    assert_eq!(redshift.numerator(), &(&near * &tick));
    assert_eq!(redshift.denominator(), &(&far * &tick));
    assert!(redshift.projectively_equal(&crate::ratio::Presentation::new(near.clone(), far)));
    assert_eq!(
        redshift_rate(&near, &integer(1), &Rat::zero()),
        Err(SpacetimeError::Aeon(Box::new(
            crate::aeon::AeonError::Undetermined
        )))
    );
}

/// [counterexample] With equal lapses the static clock is closed: no redshift, no production.
#[test]
fn an_equal_lapse_clock_is_closed() {
    let square = square_complex().unwrap();
    let reading =
        read_on_cycle(&square, &static_clock(&rat(3, 2), &rat(3, 2), &integer(4))).unwrap();
    assert!(reading.loop_reading.is_zero());
    assert!(reading.is_clock);
    assert!(reading.production_reading.is_zero());
}
