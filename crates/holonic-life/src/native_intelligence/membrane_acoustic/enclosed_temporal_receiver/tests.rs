use super::*;
use holonic_engine::ExactComplexWaveCurrent;
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use num_traits::{One, Zero};
use std::io::Cursor;

fn q(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn ball() -> NativeFieldCurrentBall {
    NativeFieldCurrentBall {
        center: vec![
            ExactComplexWaveCurrent::new(q(1, 3), q(-5, 7)),
            ExactComplexWaveCurrent::new(q(-2, 9), q(4, 11)),
        ],
        radius: q(2, 5),
    }
}

#[test]
fn non_dyadic_representative_round_trips_global_radius() {
    let source = ball();
    let projection = NativeAcousticEnclosedTemporalPcm16Projection::found(
        PhaseCurrentReceiverId(7),
        PhaseCurrentLineageId(9),
        Rat::zero(),
        q(1, 16_000),
        16_000,
        Rat::one(),
        &source,
    )
    .unwrap();
    let reconstructed = projection.reconstructed_enclosure().unwrap();
    assert_eq!(reconstructed, source);
    let compatible = vec![
        ExactComplexWaveCurrent::new(q(1, 3) + q(1, 10), q(-5, 7)),
        ExactComplexWaveCurrent::new(q(-2, 9), q(4, 11)),
    ];
    assert!(reconstructed.contains(&compatible));
    let outside_global_ball = vec![
        ExactComplexWaveCurrent::new(q(1, 3) + q(1, 4), q(-5, 7) + q(1, 4)),
        ExactComplexWaveCurrent::new(q(-2, 9) + q(1, 4), q(4, 11) + q(1, 4)),
    ];
    assert!(!reconstructed.contains(&outside_global_ball));
}

#[test]
fn clipping_is_representative_only_and_radius_survives() {
    let source = NativeFieldCurrentBall {
        center: vec![
            ExactComplexWaveCurrent::new(q(40_000, 1), q(-40_000, 1)),
            ExactComplexWaveCurrent::zero(),
        ],
        radius: q(3, 11),
    };
    let projection = NativeAcousticEnclosedTemporalPcm16Projection::found(
        PhaseCurrentReceiverId(1),
        PhaseCurrentLineageId(2),
        Rat::zero(),
        q(1, 44_100),
        44_100,
        Rat::one(),
        &source,
    )
    .unwrap();
    assert_eq!(projection.frames[0].pcm, [i16::MAX, i16::MIN]);
    assert_eq!(projection.clipped_sample_population, 2);
    assert_eq!(projection.reconstructed_enclosure().unwrap(), source);
    let reader = hound::WavReader::new(Cursor::new(projection.wav_bytes().unwrap())).unwrap();
    assert_eq!(reader.spec().channels, 2);
    assert_eq!(reader.duration(), 2);
}

#[test]
fn altered_radius_or_representative_receipt_is_refused() {
    let mut projection = NativeAcousticEnclosedTemporalPcm16Projection::found(
        PhaseCurrentReceiverId(1),
        PhaseCurrentLineageId(2),
        Rat::zero(),
        q(1, 8_000),
        8_000,
        q(2, 3),
        &ball(),
    )
    .unwrap();
    projection.radius = -Rat::one();
    assert!(projection.validate().is_err());

    let mut projection = NativeAcousticEnclosedTemporalPcm16Projection::found(
        PhaseCurrentReceiverId(1),
        PhaseCurrentLineageId(2),
        Rat::zero(),
        q(1, 8_000),
        8_000,
        Rat::one(),
        &ball(),
    )
    .unwrap();
    projection.frames[0].remainder.real += Rat::one();
    assert!(projection.validate().is_err());

    let mut projection = NativeAcousticEnclosedTemporalPcm16Projection::found(
        PhaseCurrentReceiverId(1),
        PhaseCurrentLineageId(2),
        Rat::zero(),
        q(1, 8_000),
        8_000,
        Rat::one(),
        &ball(),
    )
    .unwrap();
    projection.frames[0].clipped[0] = true;
    assert!(projection.validate().is_err());

    let mut projection = NativeAcousticEnclosedTemporalPcm16Projection::found(
        PhaseCurrentReceiverId(1),
        PhaseCurrentLineageId(2),
        Rat::zero(),
        q(1, 8_000),
        8_000,
        Rat::one(),
        &ball(),
    )
    .unwrap();
    projection.schema.push_str("-altered");
    assert!(projection.validate().is_err());
}

#[test]
fn positive_nonunit_gain_preserves_native_radius_and_invalid_chart_is_refused() {
    let source = ball();
    let projection = NativeAcousticEnclosedTemporalPcm16Projection::found(
        PhaseCurrentReceiverId(1),
        PhaseCurrentLineageId(2),
        Rat::zero(),
        q(1, 8_000),
        8_000,
        q(3, 2),
        &source,
    )
    .unwrap();
    assert_eq!(projection.reconstructed_enclosure().unwrap(), source);
    assert_eq!(projection.radius, q(2, 5));

    assert!(
        NativeAcousticEnclosedTemporalPcm16Projection::found(
            PhaseCurrentReceiverId(1),
            PhaseCurrentLineageId(2),
            Rat::zero(),
            q(1, 8_000),
            0,
            Rat::one(),
            &source,
        )
        .is_err()
    );
    assert!(
        NativeAcousticEnclosedTemporalPcm16Projection::found(
            PhaseCurrentReceiverId(1),
            PhaseCurrentLineageId(2),
            Rat::zero(),
            q(1, 8_000),
            16_000,
            Rat::one(),
            &source,
        )
        .is_err()
    );
    assert!(
        NativeAcousticEnclosedTemporalPcm16Projection::found(
            PhaseCurrentReceiverId(1),
            PhaseCurrentLineageId(2),
            Rat::zero(),
            q(1, 8_000),
            8_000,
            Rat::zero(),
            &source,
        )
        .is_err()
    );
}
