use holonics::hna::{
    native::{
        mathematical::{BilinearConstructionWire, BilinearTargetWire},
        MathematicalRequest, RationalWire,
    },
    HnaStreamCommand, HnaStreamRequest, HNA_STREAM_REQUEST_SCHEMA,
};
use serde_json::Value;
use std::process::Command;
use tempfile::tempdir;

fn row(values: &[i64]) -> Vec<RationalWire> {
    values
        .iter()
        .map(|value| RationalWire::integer(*value))
        .collect()
}

fn rows(values: &[&[i64]]) -> Vec<Vec<RationalWire>> {
    values.iter().map(|value| row(value)).collect()
}

fn wire(request: MathematicalRequest) -> String {
    let request = HnaStreamRequest {
        schema: HNA_STREAM_REQUEST_SCHEMA.into(),
        command: HnaStreamCommand::MathematicalRequest { request },
    };
    serde_json::to_string(&request).expect("request JSON")
}

#[test]
#[ignore = "requires CUDA; verifies the actual mathematical process boundary"]
fn mathematical_session_process_constructs_applies_recharts_and_recovers() {
    let temporary = tempdir().expect("temporary directory");
    let input = temporary.path().join("mathematical.jsonl");
    let construct = MathematicalRequest::ConstructBilinear {
        target: BilinearTargetWire {
            left_extent: 2,
            right_extent: 2,
            coefficients: rows(&[&[1, 0, 0, -1], &[0, 1, 1, 0]]),
        },
        construction: BilinearConstructionWire::Search {
            left_forms: rows(&[&[1, 0], &[0, 1], &[1, 1], &[1, -1]]),
            right_forms: rows(&[&[1, 0], &[0, 1], &[1, 1], &[1, -1]]),
            min_products: 1,
            max_products: 3,
            max_candidates: 1000,
        },
    };
    let mut requests = vec![wire(construct)];
    // 1/3 is intentionally non-dyadic; it must remain an exact rational at the native boundary.
    requests.push(wire(MathematicalRequest::Apply {
        operator: 0,
        left: vec![
            RationalWire {
                numerator: "1".into(),
                denominator: "3".into(),
            },
            RationalWire::integer(2),
        ],
        right: Some(row(&[4, 5])),
        retain_product: false,
    }));
    requests.push(wire(MathematicalRequest::Apply {
        operator: 0,
        left: row(&[2, 3]),
        right: Some(row(&[4, 5])),
        retain_product: true,
    }));
    requests.push(wire(MathematicalRequest::BindReceiver {
        operator: 0,
        coefficients: rows(&[&[1, 0, 0, 0], &[0, 1, 1, 0], &[0, 0, 0, 1]]),
    }));
    requests.push(wire(MathematicalRequest::ReadProduct {
        operator: 1,
        product: 0,
    }));
    requests.push(wire(MathematicalRequest::ComposeReceiver {
        operator: 1,
        matrix: rows(&[&[0, 1, 0]]),
    }));
    requests.push(wire(MathematicalRequest::ReadProduct {
        operator: 2,
        product: 0,
    }));
    // An invalid receiver must be reported as a refusal while the same process remains usable.
    requests.push(wire(MathematicalRequest::ReadProduct {
        operator: 99,
        product: 0,
    }));
    requests.push(wire(MathematicalRequest::ReadProduct {
        operator: 2,
        product: 0,
    }));
    std::fs::write(&input, requests.join("\n") + "\n").expect("input JSONL");

    let output = Command::new(env!("CARGO_BIN_EXE_holonics"))
        .args(["hna", "mathematical-session", "--input"])
        .arg(&input)
        .output()
        .expect("mathematical session process");
    assert!(
        output.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let events: Vec<Value> = String::from_utf8(output.stdout)
        .expect("stdout UTF-8")
        .lines()
        .map(|line| serde_json::from_str(line).expect("stream event JSON"))
        .collect();
    assert_eq!(events.len(), 9);
    assert!(events
        .iter()
        .all(|event| event["schema"] == "org.holonics.hna.stream-event.v1"));
    assert_eq!(events[0]["event"], "mathematical-return");
    assert_eq!(events[1]["event"], "mathematical-return");
    assert_eq!(events[1]["value"]["output"][0]["numerator"], "-26");
    assert_eq!(events[1]["value"]["output"][0]["denominator"], "3");
    assert_eq!(events[1]["value"]["output"][1]["numerator"], "29");
    assert_eq!(events[1]["value"]["output"][1]["denominator"], "3");
    assert_eq!(events[4]["value"]["source_products_recomputed"], false);
    assert_eq!(events[4]["value"]["output"][0]["numerator"], "8");
    assert_eq!(events[4]["value"]["output"][1]["numerator"], "22");
    assert_eq!(events[4]["value"]["output"][2]["numerator"], "15");
    assert_eq!(events[7]["event"], "refused");
    assert_eq!(events[8]["event"], "mathematical-return");
    assert_eq!(events[8]["value"]["output"][0]["numerator"], "22");

    let receipt: Value = String::from_utf8(output.stderr)
        .expect("stderr UTF-8")
        .lines()
        .last()
        .map(|line| serde_json::from_str(line).expect("process receipt JSON"))
        .expect("process receipt");
    assert_eq!(
        receipt["schema"],
        "org.holonics.hna.mathematical-stream-process.v1"
    );
    assert_eq!(receipt["disposition"], "input-exhausted");
    assert!(receipt["stream_error"].is_null());
    assert_eq!(receipt["transport_sequence"], 9);
    assert!(receipt["inspect"].is_object());
}
