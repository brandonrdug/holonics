use super::*;

#[test]
fn response_aperture_refuses_overflow_without_trimming() {
    assert!(validate_response_len(4, 4).is_ok());
    assert!(validate_response_len(4, 5).is_err());
    assert!(validate_response_len(4, 0).is_err());
}
