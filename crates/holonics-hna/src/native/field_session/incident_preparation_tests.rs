use super::*;
use crate::native::{FieldSessionSpec, FieldSourceChart, FieldTextCodec};
use holonic_engine::codec_recovery::Symbol;

fn spec() -> FieldSessionSpec {
    FieldSessionSpec {
        symbols: vec!["a".into(), "b".into()],
        section_symbols: 3,
        context_symbols: 1,
        region_offsets: Vec::new(),
        source_chart: FieldSourceChart::TensorCondition,
        geometry: None,
        incident: None,
        generator: None,
        codec: FieldTextCodec::UnicodeScalars,
        fractional_bits: 48,
    }
}

fn preparation() -> IncidentPreparation {
    let cells = vec![
        IncidentSourceCell {
            region: 0,
            part_ordinal: 0,
            cell: 0,
            symbol: Symbol(0),
            symbol_index: 0,
        },
        IncidentSourceCell {
            region: 0,
            part_ordinal: 0,
            cell: 1,
            symbol: Symbol(1),
            symbol_index: 1,
        },
    ];
    IncidentPreparation {
        regions: vec![IncidentSourceRegion {
            origin: IncidentSourceOrigin::Direct {
                role: "request".into(),
                context_index: 0,
            },
            parts: vec![IncidentSourcePart {
                ordinal: 0,
                pointer: "/text".into(),
                kind: "agent-text".into(),
                cell_range: 0..2,
            }],
            cells: cells.clone(),
        }],
        contacts: vec![IncidentContact {
            from_cell: 0,
            to_cell: 1,
            kind: IncidentContactKind::IntraPart,
        }],
        source_cells: cells,
        held_mask: vec![true, true, false],
        context_extent: 0,
        request_extent: 2,
        source_extent: 2,
        response_aperture: 1,
    }
}

#[test]
fn direct_multi_part_regions_reset_part_cell_ordinals() {
    let mut packet = preparation();
    packet.regions[0].parts = vec![
        IncidentSourcePart {
            ordinal: 0,
            pointer: "/first".into(),
            kind: "direct-text".into(),
            cell_range: 0..1,
        },
        IncidentSourcePart {
            ordinal: 1,
            pointer: "/second".into(),
            kind: "direct-text".into(),
            cell_range: 1..2,
        },
    ];
    packet.regions[0].cells[0].cell = 0;
    packet.regions[0].cells[0].part_ordinal = 0;
    packet.regions[0].cells[1].cell = 0;
    packet.regions[0].cells[1].part_ordinal = 1;
    packet.source_cells = packet.regions[0].cells.clone();
    packet.validate(&spec()).unwrap();
}

#[test]
fn direct_origin_and_join_are_retained_without_event_ids() {
    let packet = preparation();
    assert!(matches!(
        packet.regions[0].origin,
        IncidentSourceOrigin::Direct { .. }
    ));
    let contact = IncidentContactKind::DirectJoin {
        from_region: 0,
        to_region: 1,
        context_index: 1,
    };
    assert!(matches!(contact, IncidentContactKind::DirectJoin { .. }));
}

#[test]
fn ordered_cells_retain_symbol_ordinals_and_aperture_mask() {
    let packet = preparation();
    packet.validate(&spec()).unwrap();
    assert_eq!(packet.source_cells[0].symbol_index, 0);
    assert_eq!(packet.source_cells[1].symbol_index, 1);
    assert_eq!(packet.held_mask, vec![true, true, false]);
}

#[test]
fn validation_refuses_non_unicode_or_overlapping_free_extent() {
    let mut packet = preparation();
    let mut non_unicode = spec();
    non_unicode.codec = FieldTextCodec::Utf8Nibbles;
    assert!(packet.validate(&non_unicode).is_err());
    packet.response_aperture = 2;
    packet.held_mask.push(false);
    assert!(packet.validate(&spec()).is_err());
}
