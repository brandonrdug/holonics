/// Validate the exterior syntax of a SHA-256 digest.
///
/// This checks only the fixed-width ASCII hexadecimal receiver face; it does not
/// calculate or compare a digest.
pub fn is_sha256_digest(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

#[cfg(test)]
mod tests {
    use super::is_sha256_digest;

    #[test]
    fn accepts_lowercase_hex() {
        assert!(is_sha256_digest(&"0123456789abcdef".repeat(4)));
    }

    #[test]
    fn accepts_uppercase_hex() {
        assert!(is_sha256_digest(&"0123456789ABCDEF".repeat(4)));
    }

    #[test]
    fn rejects_invalid_length() {
        assert!(!is_sha256_digest(&"a".repeat(63)));
        assert!(!is_sha256_digest(&"a".repeat(65)));
    }

    #[test]
    fn rejects_non_hex() {
        let mut value = "a".repeat(64);
        value.replace_range(17..18, "g");
        assert!(!is_sha256_digest(&value));
    }
}
