//! Tests for the neck station. Every value is exact over `Q`; no float decides anything and no
//! fixture is read from disk.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;

use super::*;
use crate::continuing_tube::HolonomyVerdict;
use crate::jet_staircase::JetChart;
use crate::rational_polynomial::RationalPolynomial;

fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn ratio(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn vector(values: &[i64]) -> Vec<Rat> {
    values.iter().map(|value| integer(*value)).collect()
}

fn sections(areas: &[i64]) -> Vec<GeometricSection> {
    areas
        .iter()
        .map(|area| GeometricSection::declare(integer(*area), "m^2").expect("the section stands"))
        .collect()
}

/// The pinhole profile: the section narrows to one and widens back, with the flux constant.
fn pinhole_profile() -> TubeProfile {
    TubeProfile::declare(
        "test|pinhole",
        vector(&[0, 1, 2, 3, 4]),
        sections(&[4, 2, 1, 2, 4]),
        vector(&[1, 2, 4, 2, 1]),
        vector(&[0, 0, 0, 0]),
    )
    .expect("the profile stands")
}

// ---------------------------------------------------------------------------------------------
// 1. three widths, three types, related only through a declared law
// ---------------------------------------------------------------------------------------------

#[test]
fn the_three_widths_meet_only_through_a_declared_constitutive_link() {
    let geometric = GeometricSection::declare(integer(8), "m^2").expect("the section stands");
    let bundle = RayBundle::declare("test|bundle", ratio(1, 2), ratio(1, 4), Rat::one())
        .expect("the bundle stands");
    let train = optical_train(&bundle, &[]).expect("the train stands");
    let receiver = ReceiverUncertaintyWidth::declare(
        train.stations()[0].receiver_width.clone(),
        "test|height-receiver",
    );
    let analytic = analytic_width_of_denominator(&RationalPolynomial::new(vector(&[4, 0, 1])))
        .expect("the width returns");
    let widths = WidthTriple {
        geometric,
        receiver: Some(receiver),
        analytic: Some(analytic),
    };

    // The receiver diameter is `receiver_release`'s own: the box half-height is 1/2, so the
    // supremum diameter is 1.
    assert_eq!(
        widths.receiver.as_ref().unwrap().width().diameter(),
        &Rat::one()
    );
    // The analytic squared half-width of `x² + 4` is 4: the poles are at `±2i`. No square root.
    assert_eq!(widths.analytic.as_ref().unwrap().squared_half_width(), &integer(4));

    // Nothing relates them without a declaration, and a declaration returns a residual.
    let link = ConstitutiveLink::declare(
        "test|link",
        "the paraxial regime, |theta| <= 1/4",
        WidthFace::Geometric,
        WidthFace::ReceiverUncertainty,
        ratio(1, 8),
    )
    .expect("the link stands");
    let residual = check_constitutive_link(&link, &widths).expect("both faces are present");
    assert_eq!(residual.predicted, Rat::one(), "1/8 · 8");
    assert_eq!(residual.observed, Rat::one());
    assert!(residual.residual.is_zero());
    assert_eq!(residual.domain, "the paraxial regime, |theta| <= 1/4");

    // A link whose target face the triple does not carry returns nothing rather than a value.
    let bare = WidthTriple {
        geometric: GeometricSection::declare(integer(8), "m^2").expect("the section stands"),
        receiver: None,
        analytic: None,
    };
    assert!(check_constitutive_link(&link, &bare).is_none());
}

#[test]
fn a_link_from_a_face_to_itself_and_a_negative_section_are_refused_by_name() {
    assert!(matches!(
        ConstitutiveLink::declare(
            "test|identity",
            "anywhere",
            WidthFace::Analytic,
            WidthFace::Analytic,
            Rat::one()
        ),
        Err(NeckRefusal::LinkIsIdentity)
    ));
    assert!(matches!(
        GeometricSection::declare(-Rat::one(), "m^2"),
        Err(NeckRefusal::NegativeSection { .. })
    ));
    // Zero is admitted: that is a closed neck, not a refusal.
    let closed = GeometricSection::declare(Rat::zero(), "m^2").expect("zero is a section");
    assert!(closed.is_closed());
}

#[test]
fn the_analytic_width_is_a_squared_rational_and_names_what_it_did_not_decide() {
    // A pole on the real axis: the strip has closed and the squared half-width is zero.
    let on_axis = analytic_width_of_denominator(&RationalPolynomial::new(vector(&[-1, 0, 1])))
        .expect("the width returns");
    assert_eq!(on_axis.squared_half_width(), &Rat::zero());
    assert!(matches!(
        on_axis.attaining(),
        AnalyticCertificate::RationalPoleOnAxis { .. }
    ));
    assert!(on_axis.is_complete());

    // `(x² + 4)·(x⁴ + 1)²`: the squarefree factor at multiplicity one is the quadratic, whose
    // conjugate pair decides the width; the quartic at multiplicity two is left undecided rather
    // than approximated.
    let mixed = RationalPolynomial::new(vector(&[4, 0, 1, 0, 8, 0, 2, 0, 4, 0, 1]));
    let reading = analytic_width_of_denominator(&mixed).expect("the width returns");
    assert_eq!(reading.squared_half_width(), &integer(4));
    assert!(matches!(
        reading.attaining(),
        AnalyticCertificate::ConjugatePair { .. }
    ));
    assert_eq!(reading.undecided().len(), 1, "the quartic is not decided");
    assert!(!reading.is_complete());

    // `x² − 2`: no rational names √2, but the discriminant's sign alone puts both roots on the
    // real axis. The strip has closed; this is decided, not left undecided.
    let irrational = analytic_width_of_denominator(&RationalPolynomial::new(vector(&[-2, 0, 1])))
        .expect("the width returns");
    assert_eq!(irrational.squared_half_width(), &Rat::zero());
    assert!(matches!(
        irrational.attaining(),
        AnalyticCertificate::RealQuadraticRoots { .. }
    ));
    assert!(irrational.is_complete());

    // A non-monic conjugate pair: `2x² + 8` has roots `±2i`, squared half-width `4`.
    let scaled = analytic_width_of_denominator(&RationalPolynomial::new(vector(&[8, 0, 2])))
        .expect("the width returns");
    assert_eq!(scaled.squared_half_width(), &integer(4));

    // A constant denominator has no pole at all, and that is refused by name.
    assert!(matches!(
        analytic_width_of_denominator(&RationalPolynomial::new(vec![Rat::one()])),
        Err(NeckRefusal::NoPoleToRead)
    ));
}

// ---------------------------------------------------------------------------------------------
// 2. convergence into the pinhole and divergence out of it, from one law
// ---------------------------------------------------------------------------------------------

#[test]
fn a_sourceless_tube_conserves_flux_and_the_density_rises_into_the_neck() {
    let profile = pinhole_profile();
    assert_eq!(profile.fluxes(), vector(&[4, 4, 4, 4, 4]));
    assert_eq!(profile.neck_index(), 2);
    assert_eq!(profile.reopening(), Some((3, Rat::one())));

    let reading = profile.speedup().expect("a sourceless tube has the reading");
    assert!(reading.flux_is_constant);
    assert_eq!(reading.flux, integer(4));
    assert_eq!(reading.implied_density, vector(&[1, 2, 4, 2, 1]));
    assert_eq!(reading.neck, 2);
    assert!(reading.rises_into_the_neck);
    assert!(reading.falls_after_the_neck);

    // `j_i = Φ / A_i` exactly, and it is the declared density: the law and the declaration agree.
    for station in 0..profile.station_count() {
        assert_eq!(
            &reading.implied_density[station],
            &profile.current_density()[station]
        );
    }

    // And the junction reading agrees: nothing is owed at any control volume.
    let balance = profile.station_balance().expect("the balance returns");
    assert_eq!(balance.gaps, 4);
    assert!(balance.is_balanced());
    assert!(balance.verdict.is_balanced());
    assert!(balance.residual.iter().all(Zero::is_zero));
}

#[test]
fn a_source_returns_the_per_station_residual_instead_of_a_speed_up() {
    // The same geometry with one gap injecting: the flux is no longer constant and the owner
    // returns the residual rather than asserting anything.
    let profile = TubeProfile::declare(
        "test|sourced",
        vector(&[0, 1, 2, 3, 4]),
        sections(&[4, 2, 1, 2, 4]),
        vector(&[1, 2, 4, 2, 1]),
        vec![Rat::zero(), Rat::one(), Rat::zero(), Rat::zero()],
    )
    .expect("the profile stands");

    assert!(matches!(
        profile.speedup(),
        Err(NeckRefusal::SpeedupNeedsNoSource { at: 1, .. })
    ));

    let balance = profile.station_balance().expect("the balance returns");
    assert_eq!(balance.residual, vec![
        Rat::zero(),
        -Rat::one(),
        Rat::zero(),
        Rat::zero()
    ]);
    assert!(!balance.is_balanced());
    assert!(!balance.verdict.is_balanced());
    match &balance.verdict {
        JunctionVerdict::Unbalanced { residual, offending, .. } => {
            assert_eq!(offending.len(), 1, "one control volume is owed");
            assert_eq!(residual.len(), 4, "and the whole cochain comes back");
        }
        other => panic!("the sourced tube is unbalanced: {other:?}"),
    }

    // A source that the flux actually carries balances: `Φ` steps up by exactly `σ`.
    let matched = TubeProfile::declare(
        "test|matched",
        vector(&[0, 1, 2]),
        sections(&[2, 1, 2]),
        vector(&[2, 5, 5, ]),
        vec![Rat::one(), integer(5)],
    )
    .expect("the profile stands");
    assert_eq!(matched.fluxes(), vector(&[4, 5, 10]));
    let matched_balance = matched.station_balance().expect("the balance returns");
    assert_eq!(matched_balance.residual, vector(&[0, 0]));
    assert!(matched_balance.is_balanced());
    assert!(matched_balance.verdict.is_balanced());
}

#[test]
fn the_neck_reading_is_open_pinhole_or_closed_at_the_declared_grain() {
    let profile = pinhole_profile();
    // A grain coarser than the section: the receiver cannot resolve it, and the section is a
    // point at that grain while the interior still carries plurality.
    match profile.neck_reading(&integer(2), &ratio(1, 3)) {
        NeckReading::Pinhole {
            station,
            section,
            grain,
            interior_plurality,
        } => {
            assert_eq!(station, 2);
            assert_eq!(section, Rat::one());
            assert_eq!(grain, integer(2));
            assert_eq!(interior_plurality, ratio(1, 3));
        }
        other => panic!("a grain of 2 cannot resolve a section of 1: {other:?}"),
    }
    // A finer grain resolves it and the tube is open there.
    assert_eq!(profile.neck_reading(&ratio(1, 4), &Rat::zero()).arm(), "open");

    // A zero section is closed, and the flux through it comes back rather than being assumed zero.
    let closed = TubeProfile::declare(
        "test|closed",
        vector(&[0, 1, 2]),
        sections(&[4, 0, 4]),
        vector(&[1, 7, 1]),
        vector(&[0, 0]),
    )
    .expect("the profile stands");
    match closed.neck_reading(&Rat::one(), &Rat::zero()) {
        NeckReading::Closed { station, flux } => {
            assert_eq!(station, 1);
            assert!(flux.is_zero(), "a zero section carries zero flux exactly");
        }
        other => panic!("a zero section is closed: {other:?}"),
    }
    assert!(matches!(
        closed.speedup(),
        Err(NeckRefusal::ZeroSectionHasNoDensity { at: 1 })
    ));
}

#[test]
fn a_malformed_profile_is_refused_by_name() {
    assert!(matches!(
        TubeProfile::declare("t", vector(&[0]), sections(&[1]), vector(&[1]), Vec::new()),
        Err(NeckRefusal::TooFewStations { declared: 1 })
    ));
    assert!(matches!(
        TubeProfile::declare(
            "t",
            vector(&[0, 1, 2]),
            sections(&[1, 1]),
            vector(&[1, 1, 1]),
            vector(&[0, 0])
        ),
        Err(NeckRefusal::ProfileShapeMismatch { .. })
    ));
    assert!(matches!(
        TubeProfile::declare(
            "t",
            vector(&[0, 2, 1]),
            sections(&[1, 1, 1]),
            vector(&[1, 1, 1]),
            vector(&[0, 0])
        ),
        Err(NeckRefusal::StationsNotIncreasing { at: 2 })
    ));
    let oversize = (0..STATION_CEILING as i64 + 2).collect::<Vec<_>>();
    assert!(matches!(
        TubeProfile::declare(
            "t",
            vector(&oversize),
            Vec::new(),
            Vec::new(),
            Vec::new()
        ),
        Err(NeckRefusal::StationsBeyondCeiling { .. })
    ));
}

// ---------------------------------------------------------------------------------------------
// 3. parametric orientation
// ---------------------------------------------------------------------------------------------

#[test]
fn the_reading_is_covariant_under_reparametrization_and_flips_under_reversal() {
    let profile = pinhole_profile();
    // Reparametrize by `s ↦ s³ + s`, strictly increasing on the declared stations.
    let moved = profile
        .reparametrized(vector(&[0, 2, 10, 30, 68]))
        .expect("the reparametrization stands");
    assert_eq!(moved.neck_index(), profile.neck_index());
    assert_eq!(moved.fluxes(), profile.fluxes());
    assert_eq!(moved.sections(), profile.sections());
    assert_eq!(
        moved.speedup().expect("reading").implied_density,
        profile.speedup().expect("reading").implied_density
    );
    // A reparametrization that is not increasing is refused by the same declaration check.
    assert!(matches!(
        profile.reparametrized(vector(&[0, 2, 1, 3, 4])),
        Err(NeckRefusal::StationsNotIncreasing { .. })
    ));

    // Reversal: the neck reflects, the sections reverse, the flux changes sign.
    let reversed = profile.reversed().expect("the reversal stands");
    assert_eq!(reversed.neck_index(), 2, "the neck reflects to 4 − 2 = 2");
    assert_eq!(reversed.fluxes(), vector(&[-4, -4, -4, -4, -4]));
    assert_eq!(
        reversed.sections().iter().map(|s| s.area().clone()).collect::<Vec<_>>(),
        vector(&[4, 2, 1, 2, 4])
    );
    assert!(profile.reversal_orientation().reverses());
    // Reversing twice returns the original reading up to the station coordinate.
    let twice = reversed.reversed().expect("the reversal stands");
    assert_eq!(twice.fluxes(), profile.fluxes());
    assert_eq!(twice.current_density(), profile.current_density());
    assert_eq!(twice.stations(), profile.stations());
}

// ---------------------------------------------------------------------------------------------
// 4. the neck is a station of the existing tube
// ---------------------------------------------------------------------------------------------

#[test]
fn the_holonomy_around_the_neck_is_the_existing_tubes_own_reading() {
    // A sealed tube: the circuit out to the neck and back returns the face it left.
    let sealed = NeckTube::sealed(pinhole_profile()).expect("the tube stands");
    let verdict = sealed
        .holonomy_around_the_neck(0, integer(4))
        .expect("the reading returns");
    assert!(holonomy_is_identity(&verdict));
    assert!(matches!(verdict, HolonomyVerdict::Identity(_)));

    // A signed source cancels on the round trip: the reversible part is holonomy-free.
    let sourced = TubeProfile::declare(
        "test|sourced-tube",
        vector(&[0, 1, 2, 3, 4]),
        sections(&[4, 2, 1, 2, 4]),
        vector(&[1, 2, 4, 2, 1]),
        vec![Rat::zero(), integer(3), Rat::zero(), Rat::zero()],
    )
    .expect("the profile stands");
    let reversible = NeckTube::sealed(sourced).expect("the tube stands");
    assert!(holonomy_is_identity(
        &reversible
            .holonomy_around_the_neck(0, integer(4))
            .expect("the reading returns")
    ));

    // A dissipative wall does not: the round trip loses twice the wall's exchange, and that
    // defect is the chain's irreversibility read as tube holonomy.
    let lossy = NeckTube::declare(
        pinhole_profile(),
        vec![Rat::zero(), Rat::one(), Rat::zero(), Rat::zero()],
    )
    .expect("the tube stands");
    match lossy
        .holonomy_around_the_neck(0, integer(4))
        .expect("the reading returns")
    {
        HolonomyVerdict::Defect(defect) => {
            assert_eq!(defect.entered(), &integer(4));
            assert_eq!(defect.returned(), &integer(2), "4 − 2·1");
            assert_eq!(defect.circuit(), &[0usize, 2, 0]);
        }
        other => panic!("a dissipative wall has holonomy: {other:?}"),
    }
}

/// The receiver uncertainty width is `receiver_release`'s own, taken over `continuing_tube`'s
/// two-axis horizon `(h, k)` — the longitudinal station and the grain index, which is not the
/// time/entropy pair.
#[test]
fn the_receiver_width_at_a_neck_is_the_two_axis_width_over_the_declared_horizon() {
    let receiver = FluxReading::declare("test|flux-receiver");
    // A sealed tube carries the flux unchanged, so everything the horizon reaches is one face and
    // the width is exactly zero: release at that receiver, over the whole declared horizon.
    let sealed = NeckTube::sealed(pinhole_profile()).expect("the tube stands");
    let sealed_width = neck_two_axis_width(
        &sealed,
        0,
        Horizon::declare(4, 0).expect("the horizon stands"),
        integer(4),
        &receiver,
    )
    .expect("the reading returns");
    assert!(sealed_width.width().is_zero());
    assert!(sealed_width.releases_at(&Rat::zero()));
    assert!(sealed_width.domain().contains("h = 4"));

    // A dissipative wall spreads the reached faces, and the width is the exact spread.
    let lossy = NeckTube::declare(
        pinhole_profile(),
        vec![Rat::zero(), Rat::one(), Rat::zero(), Rat::zero()],
    )
    .expect("the tube stands");
    let lossy_width = neck_two_axis_width(
        &lossy,
        0,
        Horizon::declare(4, 0).expect("the horizon stands"),
        integer(4),
        &receiver,
    )
    .expect("the reading returns");
    assert_eq!(lossy_width.width().diameter(), &Rat::one());
    assert!(!lossy_width.releases_at(&Rat::zero()));

    // A width and a section are different quantities: they meet only through a declared link.
    let widths = WidthTriple {
        geometric: pinhole_profile().sections()[2].clone(),
        receiver: Some(lossy_width),
        analytic: None,
    };
    let link = ConstitutiveLink::declare(
        "test|width-link",
        "the sealed-wall regime",
        WidthFace::Geometric,
        WidthFace::ReceiverUncertainty,
        Rat::zero(),
    )
    .expect("the link stands");
    let residual = check_constitutive_link(&link, &widths).expect("both faces are present");
    assert_eq!(residual.residual, Rat::one(), "the wall's loss is the residual");
}

#[test]
fn a_negative_wall_loss_and_a_wrong_length_declaration_are_refused_by_name() {
    assert!(matches!(
        NeckTube::declare(
            pinhole_profile(),
            vec![Rat::zero(), -Rat::one(), Rat::zero(), Rat::zero()]
        ),
        Err(NeckRefusal::NegativeWallLoss { .. })
    ));
    assert!(matches!(
        NeckTube::declare(pinhole_profile(), vec![Rat::zero()]),
        Err(NeckRefusal::ProfileShapeMismatch { .. })
    ));
}

// ---------------------------------------------------------------------------------------------
// 5. the optical instance
// ---------------------------------------------------------------------------------------------

/// A `2f`–`2f` imaging train: a point source, two units of free space, a unit-focal thin lens and
/// two more units. `B` vanishes at the last station, which is the image.
fn imaging_train() -> OpticalTrain {
    let bundle =
        RayBundle::point_source("test|point", ratio(1, 10), Rat::one()).expect("the bundle stands");
    let elements = vec![
        (
            "object-to-lens".to_owned(),
            RayTransfer::free_space(&integer(2)).expect("free space"),
            Rat::one(),
        ),
        (
            "lens".to_owned(),
            RayTransfer::thin_lens(&Rat::one()).expect("the lens"),
            Rat::one(),
        ),
        (
            "lens-to-image".to_owned(),
            RayTransfer::free_space(&integer(2)).expect("free space"),
            Rat::one(),
        ),
    ];
    optical_train(&bundle, &elements).expect("the train stands")
}

#[test]
fn the_focus_is_where_the_b_element_vanishes_and_etendue_survives_it() {
    let train = imaging_train();
    assert_eq!(train.stations().len(), 4);

    // The object point and its image are exactly the two stations where the transverse extent is
    // zero; in between the bundle is wide.
    assert_eq!(train.foci(), vec![0, 3]);
    assert_eq!(train.focus(), Some(0));
    assert_eq!(
        train.stations()[1].transverse_half_extent,
        ratio(2, 10),
        "two units of free propagation of a 1/10 angular spread"
    );
    assert!(train.stations()[2].transverse_half_extent.is_positive());
    assert!(train.stations()[3].transverse_half_extent.is_zero());

    // The image station's `B` element is exactly zero, and its `A` is −1: an inverted unit image.
    let image = train.stations()[3].transfer.matrix();
    assert!(image.get(0, 1).expect("B").is_zero());
    assert_eq!(image.get(0, 0).expect("A"), &-Rat::one());

    // Plural inside: the angular half-extent is still 1/10 at the focus.
    assert_eq!(train.plural_at(3), Some(true));
    assert_eq!(train.stations()[3].angular_half_extent, ratio(1, 10));

    // And `receiver_release`'s own width of the height reading is zero there: release, at that
    // receiver's grain, with the plurality retained.
    assert!(train.stations()[3].receiver_width.is_zero());
    assert!(train.stations()[3].receiver_width.releasable_at(&Rat::zero()));
    assert!(!train.stations()[1].receiver_width.is_zero());

    // Étendue is conserved through the neck: every element is unimodular in one medium.
    assert!(train.etendue_conserved());
    for station in train.stations() {
        assert!(station.transfer.is_unimodular());
        assert_eq!(station.etendue_invariant, Rat::one());
    }
}

#[test]
fn a_refracting_interface_is_not_unimodular_and_conserves_the_reduced_etendue() {
    let bundle = RayBundle::declare("test|slab", ratio(1, 2), ratio(1, 4), Rat::one())
        .expect("the bundle stands");
    let interface = RayTransfer::refracting_interface(&Rat::one(), &ratio(3, 2))
        .expect("the interface stands");
    assert_eq!(interface.determinant(), &ratio(2, 3));
    assert!(!interface.is_unimodular());

    let train = optical_train(
        &bundle,
        &[
            ("glass".to_owned(), interface, ratio(3, 2)),
            (
                "inside".to_owned(),
                RayTransfer::free_space(&Rat::one()).expect("free space"),
                ratio(3, 2),
            ),
        ],
    )
    .expect("the train stands");

    // `n · det` is the entry index at every station, across the interface and after it.
    assert!(train.etendue_conserved());
    for station in train.stations() {
        assert_eq!(station.etendue_invariant, Rat::one());
    }
    // The literal phase-space area is `n₁/n₂` times the entry area, and the reduced area `n·area`
    // is unchanged: that is the same statement read on the enclosure.
    assert!(train.reduced_area_conserved());
    assert_eq!(train.stations()[0].phase_area, ratio(1, 2));
    assert_eq!(train.stations()[1].phase_area, ratio(1, 3));

    // Declaring that same matrix as unimodular is refused by name.
    let matrix = train.stations()[1].transfer.matrix().clone();
    assert!(matches!(
        RayTransfer::unimodular("test|forced", matrix),
        Err(NeckRefusal::RayTransferNotUnimodular { .. })
    ));
}

#[test]
fn degenerate_optical_declarations_are_refused_by_name() {
    assert!(matches!(
        RayTransfer::thin_lens(&Rat::zero()),
        Err(NeckRefusal::ZeroFocalLength)
    ));
    assert!(matches!(
        RayTransfer::refracting_interface(&Rat::zero(), &Rat::one()),
        Err(NeckRefusal::NonPositiveIndex { .. })
    ));
    assert!(matches!(
        RayTransfer::declare(
            "test|wrong-shape",
            ExactRatMatrix::identity(3).expect("identity")
        ),
        Err(NeckRefusal::RayTransferNotTwoByTwo {
            rows: 3,
            columns: 3
        })
    ));
    assert!(matches!(
        RayBundle::declare("test|negative", -Rat::one(), Rat::one(), Rat::one()),
        Err(NeckRefusal::NegativeBundleExtent {
            which: "half-height",
            ..
        })
    ));
    assert!(matches!(
        RayBundle::declare("test|point-ray", Rat::zero(), Rat::zero(), Rat::one()),
        Err(NeckRefusal::DegenerateBundle)
    ));
}

#[test]
fn composing_two_transfers_multiplies_their_determinants() {
    let lens = RayTransfer::thin_lens(&integer(3)).expect("the lens");
    let interface =
        RayTransfer::refracting_interface(&integer(2), &integer(5)).expect("the interface");
    let composed = lens.then(&interface).expect("the composite stands");
    assert_eq!(composed.determinant(), &ratio(2, 5));
    // And the composite really is `interface · lens`, applied in that order to a ray.
    let ray = vec![Rat::one(), integer(4)];
    let stepwise = interface
        .matrix()
        .apply(&lens.matrix().apply(&ray).expect("applies"))
        .expect("applies");
    assert_eq!(composed.matrix().apply(&ray).expect("applies"), stepwise);
}

// ---------------------------------------------------------------------------------------------
// 6. the neck invariants, assembled over one source
// ---------------------------------------------------------------------------------------------

#[test]
fn the_jet_order_at_the_neck_is_one_for_a_lens_and_higher_for_a_cusp() {
    let chart = JetChart::unit("test|section");
    // `A(s) = 1 + s`: a simple zero of `A − A_min` at the neck. A lens pinhole.
    let simple = FiniteJet::from_integers(chart.clone(), &[1, 1, 0]).expect("the jet stands");
    let reading = jet_order_at_neck(&simple, &Rat::one(), "A(s) − A_min");
    assert_eq!(reading.order, Some(1));
    assert_eq!(reading.read_to, 2);

    // `A(s) = 1 + s³`: a cusp, order three.
    let cusp = FiniteJet::from_integers(chart.clone(), &[1, 0, 0, 5]).expect("the jet stands");
    assert_eq!(jet_order_at_neck(&cusp, &Rat::one(), "A(s) − A_min").order, Some(3));

    // Flat to the declared order: undecided, and the reading says so with the order it read to.
    let flat = FiniteJet::from_integers(chart, &[1, 0, 0]).expect("the jet stands");
    let undecided = jet_order_at_neck(&flat, &Rat::one(), "A(s) − A_min");
    assert_eq!(undecided.order, None);
    assert_eq!(undecided.read_to, 2);
}

#[test]
fn the_growth_exponent_at_a_pinch_is_the_iwasawa_owners_own_reading() {
    // `Λ/(p)` at two consecutive levels: the growth exponent does not decrease as the level rises.
    let presentation = LambdaPresentation::principal(vec![BigInt::from(2)])
        .expect("the presentation stands");
    let coarse = pinch_growth(&presentation, 2, 1).expect("the reading returns");
    let fine = pinch_growth(&presentation, 2, 2).expect("the reading returns");
    assert_eq!(coarse.prime, 2);
    assert_eq!(coarse.level, 1);
    assert!(
        fine.growth_exponent >= coarse.growth_exponent,
        "the order of M/ω_n M does not shrink as the level rises: {} then {}",
        coarse.growth_exponent,
        fine.growth_exponent
    );
    assert!(coarse.growth_exponent > 0);
}

#[test]
fn the_linking_at_a_declared_embedding_is_the_topological_owners_own_reading() {
    let left = ClosedPolygon::declared(
        "test|neck-left",
        vec![
            [integer(2), Rat::zero(), Rat::zero()],
            [Rat::zero(), integer(2), Rat::zero()],
            [integer(-2), Rat::zero(), Rat::zero()],
            [Rat::zero(), integer(-2), Rat::zero()],
        ],
    )
    .expect("the left curve stands");
    let right = ClosedPolygon::declared(
        "test|neck-right",
        vec![
            [integer(4), Rat::zero(), Rat::zero()],
            [integer(2), Rat::zero(), integer(2)],
            [Rat::zero(), Rat::zero(), Rat::zero()],
            [integer(2), Rat::zero(), integer(-2)],
        ],
    )
    .expect("the right curve stands");
    let direction =
        ProjectionDirection::declared([Rat::one(), integer(2), integer(3)]).expect("admissible");
    let linking = neck_linking(&left, &right, &direction).expect("the reading returns");
    assert_eq!(linking.abs(), 1, "the Hopf link, through the neck");
}

#[test]
fn the_neck_invariants_assemble_over_one_source_and_name_what_is_open() {
    let profile = pinhole_profile();
    let station = profile.neck_index();
    let chart = JetChart::unit("test|section");
    let section_jet = FiniteJet::from_integers(chart, &[1, 1, 0]).expect("the jet stands");
    let sealed = NeckTube::sealed(profile.clone()).expect("the tube stands");
    let holonomy = sealed
        .holonomy_around_the_neck(0, integer(4))
        .expect("the reading returns");

    let complete = NeckInvariants {
        lineage: "test|pinhole".to_owned(),
        station,
        widths: WidthTriple {
            geometric: profile.sections()[station].clone(),
            receiver: Some(ReceiverUncertaintyWidth::declare(
                imaging_train().stations()[3].receiver_width.clone(),
                "test|height-receiver at the image",
            )),
            analytic: Some(
                analytic_width_of_denominator(&RationalPolynomial::new(vector(&[4, 0, 1])))
                    .expect("the width returns"),
            ),
        },
        holonomy_is_identity: Some(holonomy_is_identity(&holonomy)),
        linking: Some(1),
        growth: Some(
            pinch_growth(
                &LambdaPresentation::principal(vec![BigInt::from(2)]).expect("presentation"),
                2,
                1,
            )
            .expect("the reading returns"),
        ),
        jet_order: jet_order_at_neck(&section_jet, &Rat::one(), "A(s) − A_min"),
        domains: BTreeMap::from([
            ("geometric".to_owned(), "m^2 along the tube".to_owned()),
            (
                "receiver".to_owned(),
                "the height reading's supremum diameter".to_owned(),
            ),
            (
                "analytic".to_owned(),
                "squared distance from the real axis".to_owned(),
            ),
        ]),
    };
    assert!(complete.open_invariants().is_empty(), "every reading present");
    assert_eq!(complete.jet_order.order, Some(1));
    assert_eq!(complete.widths.geometric.area(), &Rat::one());

    // A reading that took only the geometry names the five it did not take, with the owner each
    // would compose. An absent reading is an open fibre, not a refusal.
    let partial = NeckInvariants {
        lineage: "test|partial".to_owned(),
        station,
        widths: WidthTriple {
            geometric: profile.sections()[station].clone(),
            receiver: None,
            analytic: None,
        },
        holonomy_is_identity: None,
        linking: None,
        growth: None,
        jet_order: jet_order_at_neck(&section_jet, &Rat::one(), "A(s) − A_min"),
        domains: BTreeMap::new(),
    };
    let open = partial.open_invariants();
    assert_eq!(open.len(), 5);
    assert!(open.iter().any(|(name, _)| *name == "analytic width"));
    assert!(
        open.iter()
            .any(|(_, owner)| *owner == "continuing_tube::check_circuit_holonomy")
    );
}

#[test]
fn a_neck_certificate_names_its_receiver_scope_and_gates_nothing() {
    let certificate = NeckCertificate {
        receiver_scope: "test|height-receiver at the image plane".to_owned(),
        statement: "the transverse half-extent is zero at station 3".to_owned(),
        station: 3,
    };
    assert_eq!(certificate.station, 3);
    assert!(certificate.receiver_scope.contains("height-receiver"));
    // The certificate carries a scope and a statement, and this owner offers no function that
    // consumes one to permit or forbid a generated face. The reading below is taken without it.
    let train = imaging_train();
    assert!(train.stations()[3].transverse_half_extent.is_zero());
}
