use super::schema::*;

pub(super) fn validate_codec_descriptor(
    source: &SourceAssetIdentity,
    descriptor: &ExteriorCodecDescriptor,
) -> Result<(), RestError> {
    if descriptor.tokenizer_json_sha256 != source.tokenizer_sha256 {
        return Err(RestError::CodecIdentityMismatch {
            kind: "tokenizer",
            source: source.tokenizer_sha256.clone(),
            artifact: descriptor.tokenizer_json_sha256.clone(),
        });
    }
    if descriptor.tokenizer_json_len == 0 {
        return Err(RestError::CodecDigestMismatch {
            kind: "tokenizer",
            expected: "non-zero descriptor length".into(),
            actual: "0".into(),
        });
    }
    match (
        descriptor.tokenizer_config_sha256.as_deref(),
        descriptor.tokenizer_config_json_len,
    ) {
        (Some(digest), Some(length)) => {
            if length == 0 {
                return Err(RestError::CodecDigestMismatch {
                    kind: "tokenizer-config",
                    expected: "non-zero descriptor length".into(),
                    actual: "0".into(),
                });
            }
            if digest != source.tokenizer_config_sha256 {
                return Err(RestError::CodecIdentityMismatch {
                    kind: "tokenizer-config",
                    source: source.tokenizer_config_sha256.clone(),
                    artifact: digest.to_owned(),
                });
            }
        }
        (None, None) if source.tokenizer_config_sha256.is_empty() => {}
        (None, None) => {
            return Err(RestError::CodecIdentityMismatch {
                kind: "tokenizer-config",
                source: source.tokenizer_config_sha256.clone(),
                artifact: "descriptor absent".into(),
            });
        }
        _ => {
            return Err(RestError::CodecDigestMismatch {
                kind: "tokenizer-config",
                expected: "paired descriptor digest and length".into(),
                actual: "unpaired descriptor fields".into(),
            });
        }
    }
    Ok(())
}

pub(super) fn validate_codec(
    source: &SourceAssetIdentity,
    descriptor: &ExteriorCodecDescriptor,
    artifact: &ExteriorCodecArtifact,
) -> Result<(), RestError> {
    validate_codec_descriptor(source, descriptor)?;
    let tokenizer_actual = digest_bytes(&artifact.tokenizer_json);
    if tokenizer_actual != descriptor.tokenizer_json_sha256
        || artifact.tokenizer_json.len() as u64 != descriptor.tokenizer_json_len
    {
        return Err(RestError::CodecDigestMismatch {
            kind: "tokenizer",
            expected: format!(
                "{}:{}",
                descriptor.tokenizer_json_sha256, descriptor.tokenizer_json_len
            ),
            actual: format!("{}:{}", tokenizer_actual, artifact.tokenizer_json.len()),
        });
    }
    if tokenizer_actual != source.tokenizer_sha256 {
        return Err(RestError::CodecIdentityMismatch {
            kind: "tokenizer",
            source: source.tokenizer_sha256.clone(),
            artifact: tokenizer_actual,
        });
    }
    match (
        artifact.tokenizer_config_json.as_deref(),
        descriptor.tokenizer_config_sha256.as_deref(),
        descriptor.tokenizer_config_json_len,
    ) {
        (Some(bytes), Some(expected), Some(expected_len)) => {
            let actual = digest_bytes(bytes);
            if actual != expected || bytes.len() as u64 != expected_len {
                return Err(RestError::CodecDigestMismatch {
                    kind: "tokenizer-config",
                    expected: format!("{expected}:{expected_len}"),
                    actual: format!("{actual}:{}", bytes.len()),
                });
            }
            if actual != source.tokenizer_config_sha256 {
                return Err(RestError::CodecIdentityMismatch {
                    kind: "tokenizer-config",
                    source: source.tokenizer_config_sha256.clone(),
                    artifact: actual,
                });
            }
        }
        (None, None, None) => {}
        _ => {
            return Err(RestError::CodecDigestMismatch {
                kind: "tokenizer-config",
                expected: "paired bytes, digest, and length".into(),
                actual: "unpaired descriptor/artifact fields".into(),
            });
        }
    }
    Ok(())
}
