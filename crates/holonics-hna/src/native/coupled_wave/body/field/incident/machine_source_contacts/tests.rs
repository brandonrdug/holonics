use super::*;

#[test]
fn contact_kind_wire_roundtrip_retains_direction_and_semantics() {
    let contact = GeneratorSourceContact {
        from: 2,
        to: 5,
        kind: GeneratorSourceContactKind::RecordedReply,
    };
    let encoded = serde_json::to_string(&contact).unwrap();
    let decoded: GeneratorSourceContact = serde_json::from_str(&encoded).unwrap();
    assert_eq!(decoded, contact);
}
