use sha2::{Digest, Sha256};

use super::types::ProductionEcologyError;

pub(super) fn encode_components(
    magic: &[u8; 8],
    components: &[Vec<u8>],
) -> Result<Vec<u8>, ProductionEcologyError> {
    let count = u32::try_from(components.len()).map_err(|_| ProductionEcologyError::Extent)?;
    let mut bytes = Vec::new();
    bytes.extend_from_slice(magic);
    bytes.extend_from_slice(&count.to_le_bytes());
    for component in components {
        bytes.extend_from_slice(&(component.len() as u64).to_le_bytes());
        bytes.extend_from_slice(component);
    }
    Ok(bytes)
}

pub(super) fn decode_components(
    magic: &[u8; 8],
    bytes: &[u8],
    expected: usize,
) -> Result<Vec<Vec<u8>>, ProductionEcologyError> {
    if bytes.len() < 12 || &bytes[..8] != magic {
        return Err(ProductionEcologyError::Wire(
            "component magic moved".to_owned(),
        ));
    }
    let count = u32::from_le_bytes(
        bytes[8..12]
            .try_into()
            .map_err(|_| ProductionEcologyError::Wire("component count moved".to_owned()))?,
    ) as usize;
    if count != expected {
        return Err(ProductionEcologyError::Wire(
            "component population moved".to_owned(),
        ));
    }
    let mut cursor = 12_usize;
    let mut returned = Vec::with_capacity(count);
    for _ in 0..count {
        let tail = cursor
            .checked_add(8)
            .ok_or(ProductionEcologyError::Extent)?;
        let length = u64::from_le_bytes(
            bytes
                .get(cursor..tail)
                .ok_or_else(|| ProductionEcologyError::Wire("component length absent".to_owned()))?
                .try_into()
                .map_err(|_| ProductionEcologyError::Wire("component length moved".to_owned()))?,
        );
        cursor = tail;
        let length = usize::try_from(length).map_err(|_| ProductionEcologyError::Extent)?;
        let tail = cursor
            .checked_add(length)
            .ok_or(ProductionEcologyError::Extent)?;
        returned.push(
            bytes
                .get(cursor..tail)
                .ok_or_else(|| ProductionEcologyError::Wire("component body absent".to_owned()))?
                .to_vec(),
        );
        cursor = tail;
    }
    if cursor != bytes.len() {
        return Err(ProductionEcologyError::Wire(
            "component wire carries an unaddressed tail".to_owned(),
        ));
    }
    Ok(returned)
}

pub(super) fn digest(bytes: &[u8]) -> String {
    hex(Sha256::digest(bytes))
}

pub(super) fn hex(bytes: impl AsRef<[u8]>) -> String {
    bytes
        .as_ref()
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}

pub(super) fn digest_text(text: &str) -> bool {
    text.len() == 64 && text.bytes().all(|octet| octet.is_ascii_hexdigit())
}
