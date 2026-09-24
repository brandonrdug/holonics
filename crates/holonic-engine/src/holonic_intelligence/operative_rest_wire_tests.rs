use std::io::{self, Cursor, Read};

use super::*;
use crate::resident_section::ResidentGrain;

fn section() -> ResidentSectionRest {
    ResidentSectionRest::found(1, 1, ResidentGrain(0), 1, vec![(1, 1)]).unwrap()
}

fn ecology() -> NativeFullOperatorEcology {
    let node = |at: u32, primitive, inputs: &[u32], coefficients: &[u32]| NativeOperatorNode {
        ordinal: at,
        layer: (at < 3).then_some(0),
        primitive,
        inputs: inputs.iter().copied().map(NativeCarrierOrdinal).collect(),
        output: NativeCarrierOrdinal(at),
        coefficients: coefficients
            .iter()
            .copied()
            .map(NativeTensorOrdinal)
            .collect(),
    };
    let scale = NativeScaleConstraint::Rational {
        numerator: 1,
        denominator: 1,
    };
    NativeFullOperatorEcology {
        schema: NATIVE_FULL_OPERATOR_ECOLOGY_SCHEMA.to_owned(),
        shared_carrier_extent: 1,
        coefficient_populations: (0..3)
            .map(|at| NativeCoefficientPopulation {
                ordinal: NativeTensorOrdinal(at),
                shape: vec![1, 1],
                coefficient_population: 1,
            })
            .collect(),
        carriers: (0..8)
            .map(|at| NativeCarrierChart {
                ordinal: NativeCarrierOrdinal(at),
                axes: vec![NativeCarrierAxis::Occurrence, NativeCarrierAxis::Fixed(1)],
            })
            .collect(),
        operations: vec![
            node(
                0,
                NativeOperationPrimitive::Lookup {
                    scale: scale.clone(),
                },
                &[],
                &[0],
            ),
            node(1, NativeOperationPrimitive::Contract, &[0], &[1]),
            node(2, NativeOperationPrimitive::Add, &[0, 1], &[]),
            node(3, NativeOperationPrimitive::Contract, &[2], &[2]),
            node(
                4,
                NativeOperationPrimitive::Scale { by: scale.clone() },
                &[3],
                &[],
            ),
            node(5, NativeOperationPrimitive::Tanh, &[4], &[]),
            node(6, NativeOperationPrimitive::Scale { by: scale }, &[5], &[]),
            node(7, NativeOperationPrimitive::Emit, &[6], &[]),
        ],
        layers: vec![NativeLayerTopology {
            ordinal: 0,
            attention: NativeAttentionTopology::Local,
            kv_standing: NativeKvStanding::Own,
            first_operation: 0,
            operation_population: 3,
        }],
        coefficient_obstructions: vec![],
    }
}

fn overlay() -> NativeOverlayRest {
    NativeOverlayRest {
        rows: 1,
        width: 1,
        rank: 1,
        u: vec![7],
        v: vec![-3],
        u_exponent: 0,
        v_exponent: 0,
        u_octaves: 4,
        v_octaves: 2,
    }
}

fn base_rest() -> ExtractedOperatorRest {
    let header = ExtractedOperatorRestHeader {
        schema: NATIVE_SESSION_REST_SCHEMA.to_owned(),
        ecology: ecology(),
        operation_at: 0,
        generation: 8,
        chronology: (0..8).collect(),
        grain: 0,
        row_population: Some(1),
        cycle_complete: true,
        previous_context: Some(vec![0]),
        aperture: None,
        terminal_seal: true,
        progress: None,
        interruption: None,
    };
    let tiled = NativeTiledRest {
        carrier: NativeCarrierOrdinal(7),
        rows: 1,
        width: 1,
        grain: 0,
        sections: vec![section()],
    };
    ExtractedOperatorRest {
        header,
        carriers: [(NativeCarrierOrdinal(0), section())].into_iter().collect(),
        checkpoints: BTreeMap::new(),
        terminal_carrier: Some(tiled),
        overlay: [(NativeTensorOrdinal(0), vec![overlay()])]
            .into_iter()
            .collect(),
        passage: None,
        reuse: None,
    }
}

fn encoded(rest: &ExtractedOperatorRest) -> Vec<u8> {
    let mut bytes = Vec::new();
    rest.write_to(&mut bytes).unwrap();
    bytes
}

struct Fragmented {
    inner: Cursor<Vec<u8>>,
    width: usize,
}

impl Read for Fragmented {
    fn read(&mut self, out: &mut [u8]) -> io::Result<usize> {
        let take = out.len().min(self.width);
        self.inner.read(&mut out[..take])
    }
}

#[test]
fn roundtrip_preserves_sections_terminal_and_exact_overlay_words() {
    let rest = base_rest();
    let bytes = encoded(&rest);
    let decoded =
        ExtractedOperatorRest::read_from(&mut Cursor::new(bytes.clone()), bytes.len() as u64)
            .unwrap();
    assert_eq!(decoded, rest);
    assert!(bytes.windows(8).any(|window| window == 7i64.to_le_bytes()));
}

#[test]
fn fragmented_read_roundtrips_and_every_truncation_refuses() {
    let rest = base_rest();
    let bytes = encoded(&rest);
    let mut fragmented = Fragmented {
        inner: Cursor::new(bytes.clone()),
        width: 1,
    };
    assert_eq!(
        ExtractedOperatorRest::read_from(&mut fragmented, bytes.len() as u64).unwrap(),
        rest
    );
    for length in 0..bytes.len() {
        assert!(
            ExtractedOperatorRest::read_from(
                &mut Cursor::new(bytes[..length].to_vec()),
                length as u64
            )
            .is_err(),
            "truncated prefix {length} unexpectedly decoded"
        );
    }
}

#[test]
fn trailing_bytes_and_hostile_length_refuse() {
    let rest = base_rest();
    let bytes = encoded(&rest);
    let mut trailing = bytes.clone();
    trailing.push(0);
    assert!(
        ExtractedOperatorRest::read_from(&mut Cursor::new(trailing), (bytes.len() + 1) as u64)
            .is_err()
    );
    let magic = b"HNA-SESSION-REST\x01".len();
    let mut hostile = bytes;
    hostile[magic..magic + 8].copy_from_slice(&u64::MAX.to_le_bytes());
    assert!(ExtractedOperatorRest::read_from(&mut Cursor::new(hostile), magic as u64 + 8).is_err());
}

#[test]
fn malformed_operator_extents_and_missing_ports_refuse_before_device_access() {
    let mut rest = base_rest();
    rest.header.ecology.layers[0].first_operation = u32::MAX;
    assert!(rest.validate().is_err());
    let mut rest = base_rest();
    rest.header.ecology.layers[0].operation_population = u32::MAX;
    assert!(rest.validate().is_err());
    let mut rest = base_rest();
    rest.header.ecology.operations[1].inputs.clear();
    assert!(rest.validate().is_err());
}
