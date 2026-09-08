use super::*;
use crate::{
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::ResidentConstitutiveCurrent,
    phase_current::resident::{
        ResidentPhaseCurrentView, compare_enclosed_resident, convolve_enclosed_resident,
    },
    resident_section::{ResidentGrain, ResidentSection, ResidentSectionRest, ResidentSurface},
};
use num_rational::BigRational as Rat;
use num_traits::Zero;

fn seed(nodes: usize) -> Vec<NativeJunctionSeed> {
    vec![
        NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        };
        nodes
    ]
}

fn mount<'c>(surface: &'c ResidentSurface<'c>, values: &[i64]) -> ResidentSection<'c> {
    surface
        .mount_section_rest(
            &ResidentSectionRest::found(
                1,
                values.len(),
                ResidentGrain(0),
                64,
                values.iter().map(|value| (*value, *value)).collect(),
            )
            .unwrap(),
        )
        .unwrap()
}

fn point<'section, 'chart>(
    section: &'section ResidentSection<'chart>,
    raw_extent: usize,
    receiver: u64,
    lineage: u64,
) -> ResidentPhaseCurrentView<'section, 'chart> {
    ResidentPhaseCurrentView::new(
        ResidentConstitutiveCurrent::rational(section).unwrap(),
        PhaseCurrentReceiverId(receiver),
        PhaseCurrentLineageId(lineage),
        Rat::zero(),
        Rat::new(1.into(), 100.into()),
        4,
        raw_extent,
    )
    .unwrap()
}

#[test]
#[ignore = "requires native GPU; resident complete-current return and temporal receiver port"]
fn resident_return_keeps_cold_equivalence_and_temporal_carrier_resident() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(1), ResidentGrain(72))
            .unwrap();
    body.enable_material_transport_source(NativeMaterialTransportSource::CompleteCurrent)
        .unwrap();
    let first = body
        .advance_resident(&mut NativeFieldOccurrence::entering(vec![
            NativePhaseCurrent::unit(),
        ]))
        .unwrap();
    let anchor = body.retain_source(&first.source).unwrap();
    for _ in 0..2 {
        body.advance_resident(&mut NativeFieldOccurrence::through_anchor(
            &anchor,
            vec![NativePhaseCurrent::unit()],
        ))
        .unwrap();
    }
    body.advance_resident(&mut NativeFieldOccurrence::entering(vec![
        NativePhaseCurrent::new(-9, 0, 10).unwrap(),
    ]))
    .unwrap();
    let mut sources = Vec::new();
    for _ in 0..3 {
        let next = body
            .advance_resident(&mut NativeFieldOccurrence::entering(vec![
                NativePhaseCurrent::zero(),
            ]))
            .unwrap();
        if body.occurrence_count() >= 6 {
            sources.push(body.retain_source(&next.source).unwrap());
        }
    }
    body.advance_resident(&mut NativeFieldOccurrence::through_anchor(
        &sources[0],
        vec![NativePhaseCurrent::unit()],
    ))
    .unwrap();

    let before = surface.census();
    let resident = body
        .read_complete_material_source_resident(&sources[0])
        .unwrap();
    let after = surface.census();
    assert_eq!(after.section_read_outs, before.section_read_outs);
    assert_eq!(after.egress_section_octets, before.egress_section_octets);
    assert_eq!(resident.source_occurrence(), 5);
    assert_eq!(resident.producing_cut(), 5);
    assert_eq!(resident.current_cut(), 7);
    assert_eq!(resident.provenance().occurrence, 5);

    let cold = resident.inspect().unwrap();
    let old_api = body.read_complete_material_source(&sources[0]).unwrap();
    assert_eq!(cold, old_api);

    let response = resident
        .temporal_view(
            PhaseCurrentReceiverId(10),
            PhaseCurrentLineageId(11),
            Rat::zero(),
            Rat::new(1.into(), 100.into()),
            4,
        )
        .unwrap();
    assert_eq!(response.raw_extent(), 1);
    let source_section = mount(&surface, &[1, 0, 1]);
    let observed_section = mount(&surface, &[1, 0, 1]);
    let source = point(&source_section, 1, 20, 21);
    let observed = point(&observed_section, 1, 40, 31);
    let before_temporal = surface.census();
    let prediction = convolve_enclosed_resident(
        &surface,
        source,
        response,
        PhaseCurrentReceiverId(40),
        PhaseCurrentLineageId(41),
    )
    .unwrap();
    let difference = compare_enclosed_resident(
        &surface,
        prediction.view(),
        observed,
        PhaseCurrentLineageId(42),
    )
    .unwrap();
    assert_eq!(difference.view().raw_extent(), 1);
    let after_temporal = surface.census();
    assert_eq!(
        after_temporal.section_read_outs,
        before_temporal.section_read_outs
    );
    assert_eq!(
        after_temporal.egress_section_octets,
        before_temporal.egress_section_octets
    );

    let preserved = resident
        .temporal_view(
            PhaseCurrentReceiverId(10),
            PhaseCurrentLineageId(11),
            Rat::zero(),
            Rat::new(1.into(), 100.into()),
            4,
        )
        .unwrap()
        .inspect(&surface)
        .unwrap();
    body.advance_resident(&mut NativeFieldOccurrence::through_anchor(
        &sources[0],
        vec![NativePhaseCurrent::unit()],
    ))
    .unwrap();
    let after_later = resident
        .temporal_view(
            PhaseCurrentReceiverId(10),
            PhaseCurrentLineageId(11),
            Rat::zero(),
            Rat::new(1.into(), 100.into()),
            4,
        )
        .unwrap()
        .inspect(&surface)
        .unwrap();
    assert_eq!(preserved, after_later);
}

#[test]
#[ignore = "requires native GPU; mode component and unfolding views retain cuts without readout"]
fn material_mode_temporal_views_retain_component_identity_and_cuts() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(1), ResidentGrain(72))
            .unwrap();
    body.enable_material_transport_source(NativeMaterialTransportSource::CompleteCurrent)
        .unwrap();
    let input = |phase: NativePhaseCurrent| {
        let mut values = vec![NativePhaseCurrent::zero()];
        values[0] = phase;
        values
    };
    let first = body
        .advance_resident(&mut NativeFieldOccurrence::entering(input(
            NativePhaseCurrent::unit(),
        )))
        .unwrap();
    let anchor = body.retain_source(&first.source).unwrap();
    for _ in 0..2 {
        body.advance_resident(&mut NativeFieldOccurrence::through_anchor(
            &anchor,
            input(NativePhaseCurrent::unit()),
        ))
        .unwrap();
    }
    body.advance_resident(&mut NativeFieldOccurrence::entering(input(
        NativePhaseCurrent::new(-9, 0, 10).unwrap(),
    )))
    .unwrap();
    for _ in 0..2 {
        body.advance_resident(&mut NativeFieldOccurrence::entering(input(
            NativePhaseCurrent::zero(),
        )))
        .unwrap();
    }
    let last = body
        .advance_resident(&mut NativeFieldOccurrence::entering(input(
            NativePhaseCurrent::zero(),
        )))
        .unwrap();
    let at = last.lineage.occurrence;
    let later_anchor = body.retain_source(&last.source).unwrap();
    let mode = body.condense_shared_drive_mode(1, 2).unwrap();
    body.advance_resident(&mut NativeFieldOccurrence::through(
        last.source,
        input(NativePhaseCurrent::new(0, 1, 1).unwrap()),
    ))
    .unwrap();
    let returned = body.read_material_mode_using(at, &mode).unwrap();
    let before_views = surface.census();
    let full_view = returned
        .temporal_view(
            NativeMaterialModeComponent::CurrentFull,
            PhaseCurrentReceiverId(50),
            PhaseCurrentLineageId(51),
            Rat::zero(),
            Rat::new(1.into(), 100.into()),
            4,
        )
        .unwrap();
    assert!(matches!(
        full_view.component(),
        NativeMaterialModeComponent::CurrentFull
    ));
    assert_eq!(full_view.source_occurrence(), at);
    assert_eq!(full_view.producing_operator_at(), at);
    assert_eq!(full_view.current_operator_at(), body.occurrence_count() - 1);
    assert_eq!(full_view.view().raw_extent(), 1);
    let producing_view = returned
        .temporal_view(
            NativeMaterialModeComponent::ProducingFull,
            PhaseCurrentReceiverId(50),
            PhaseCurrentLineageId(51),
            Rat::zero(),
            Rat::new(1.into(), 100.into()),
            4,
        )
        .unwrap();
    let current_view = returned
        .temporal_view(
            NativeMaterialModeComponent::CurrentMode,
            PhaseCurrentReceiverId(50),
            PhaseCurrentLineageId(51),
            Rat::zero(),
            Rat::new(1.into(), 100.into()),
            4,
        )
        .unwrap();
    let after_views = surface.census();
    assert_eq!(
        after_views.section_read_outs,
        before_views.section_read_outs
    );
    assert_eq!(
        after_views.egress_section_octets,
        before_views.egress_section_octets
    );
    let reading = returned.inspect().unwrap();
    assert!(
        reading
            .current_full
            .center
            .iter()
            .any(|value| value != &ExactComplexWaveCurrent::zero())
    );
    assert_eq!(
        full_view.view().inspect(&surface).unwrap(),
        reading.current_full
    );
    assert_eq!(
        producing_view.view().inspect(&surface).unwrap(),
        reading.producing_full
    );
    assert_eq!(
        current_view.view().inspect(&surface).unwrap(),
        reading.current_mode
    );
    assert!(
        reading
            .current_mode
            .center
            .iter()
            .any(|value| value != &ExactComplexWaveCurrent::zero())
    );
    let source_section = mount(&surface, &[1, 0, 1]);
    let before_prediction = surface.census();
    let prediction = convolve_enclosed_resident(
        &surface,
        point(&source_section, 1, 50, 60),
        full_view.view(),
        PhaseCurrentReceiverId(70),
        PhaseCurrentLineageId(71),
    )
    .unwrap();
    let after_prediction = surface.census();
    assert_eq!(
        after_prediction.section_read_outs,
        before_prediction.section_read_outs
    );
    assert_eq!(
        after_prediction.egress_section_octets,
        before_prediction.egress_section_octets
    );
    assert!(
        prediction
            .view()
            .inspect(&surface)
            .unwrap()
            .contains(&reading.current_full.center)
    );
    let before_unfold = surface.census();
    let unfolding = returned.unfold_current(2).unwrap();
    let unfolded = unfolding
        .temporal_view(
            PhaseCurrentReceiverId(52),
            PhaseCurrentLineageId(53),
            Rat::zero(),
            Rat::new(1.into(), 100.into()),
            4,
        )
        .unwrap();
    assert_eq!(unfolded.steps(), 2);
    assert_eq!(unfolded.receiving_occurrences(), [1, 2]);
    assert_eq!(unfolded.view().raw_extent(), 1);
    let after_unfold = surface.census();
    assert_eq!(
        after_unfold.section_read_outs,
        before_unfold.section_read_outs
    );
    assert_eq!(
        after_unfold.egress_section_octets,
        before_unfold.egress_section_octets
    );
    body.advance_resident(&mut NativeFieldOccurrence::through_anchor(
        &later_anchor,
        input(NativePhaseCurrent::unit()),
    ))
    .unwrap();
    assert_eq!(
        full_view.view().inspect(&surface).unwrap(),
        reading.current_full
    );
}
