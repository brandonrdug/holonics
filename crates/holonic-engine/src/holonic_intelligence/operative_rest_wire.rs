//! Streaming exterior chart for native session state. Arrays are integer codewords, not JSON
//! number populations. Frame lengths are caller-declared resource boundaries, not semantic IDs.

use super::*;
use crate::resident_section::ResidentSectionRest;
use serde::{de::DeserializeOwned, Serialize};
use std::{
    collections::BTreeMap,
    io::{Read, Take, Write},
};

const MAGIC: &[u8] = b"HNA-SESSION-REST\x01";
const END: &[u8] = b"HNA-REST-END\x01";
const CHUNK: usize = 64 * 1024;

#[cfg(test)]
#[path = "operative_rest_wire_tests.rs"]
mod tests;

type Error = NativeSessionRestError;

fn malformed(message: &str) -> Error {
    Error::Malformed(message.into())
}
fn number(out: &mut impl Write, value: usize) -> Result<(), Error> {
    out.write_all(
        &u64::try_from(value)
            .map_err(|_| malformed("wire extent"))?
            .to_le_bytes(),
    )?;
    Ok(())
}
fn count(input: &mut Take<impl Read>, minimum_octets: u64) -> Result<usize, Error> {
    let mut bytes = [0; 8];
    input.read_exact(&mut bytes)?;
    let value = u64::from_le_bytes(bytes);
    if minimum_octets > 0 && value > input.limit() / minimum_octets {
        return Err(malformed("count exceeds its complete wire frame"));
    }
    usize::try_from(value).map_err(|_| malformed("host extent"))
}
fn ordinal(out: &mut impl Write, value: u32) -> Result<(), Error> {
    out.write_all(&value.to_le_bytes())?;
    Ok(())
}
fn read_ordinal(input: &mut impl Read) -> Result<u32, Error> {
    let mut bytes = [0; 4];
    input.read_exact(&mut bytes)?;
    Ok(u32::from_le_bytes(bytes))
}
fn flag(out: &mut impl Write, value: bool) -> Result<(), Error> {
    out.write_all(&[u8::from(value)])?;
    Ok(())
}
fn read_flag(input: &mut impl Read) -> Result<bool, Error> {
    let mut byte = [0];
    input.read_exact(&mut byte)?;
    match byte[0] {
        0 => Ok(false),
        1 => Ok(true),
        _ => Err(malformed("non-Boolean option marker")),
    }
}
fn blob(out: &mut impl Write, bytes: &[u8]) -> Result<(), Error> {
    number(out, bytes.len())?;
    out.write_all(bytes)?;
    Ok(())
}
fn read_blob(input: &mut Take<impl Read>) -> Result<Vec<u8>, Error> {
    let length = count(input, 1)?;
    let mut bytes = Vec::new();
    let mut chunk = vec![0; CHUNK.min(length)];
    // Allocate only after those bytes have actually arrived, so a truncated hostile count
    // does not first demand its whole claimed population from the host allocator.
    while bytes.len() < length {
        let take = chunk.len().min(length - bytes.len());
        input.read_exact(&mut chunk[..take])?;
        bytes
            .try_reserve(take)
            .map_err(|error| malformed(&error.to_string()))?;
        bytes.extend_from_slice(&chunk[..take]);
    }
    Ok(bytes)
}
fn json(out: &mut impl Write, value: &impl Serialize) -> Result<(), Error> {
    blob(out, &serde_json::to_vec(value)?)
}
fn read_json<T: DeserializeOwned>(input: &mut Take<impl Read>) -> Result<T, Error> {
    Ok(serde_json::from_slice(&read_blob(input)?)?)
}

fn words(out: &mut impl Write, values: &[i64]) -> Result<(), Error> {
    number(out, values.len())?;
    #[cfg(target_endian = "little")]
    {
        // SAFETY: i64 is fully initialized and has no padding. This immutable byte view
        // covers precisely the borrowed codewords and cannot escape this write call.
        let bytes = unsafe {
            std::slice::from_raw_parts(values.as_ptr().cast::<u8>(), std::mem::size_of_val(values))
        };
        out.write_all(bytes)?;
    }
    #[cfg(target_endian = "big")]
    for value in values {
        out.write_all(&value.to_le_bytes())?;
    }
    Ok(())
}
fn read_words(input: &mut Take<impl Read>) -> Result<Vec<i64>, Error> {
    let length = count(input, 8)?;
    let mut values = Vec::new();
    let mut chunk = vec![0; CHUNK.min(length.saturating_mul(8))];
    while values.len() < length {
        let take = (chunk.len() / 8).min(length - values.len());
        input.read_exact(&mut chunk[..take * 8])?;
        values
            .try_reserve(take)
            .map_err(|error| malformed(&error.to_string()))?;
        for bytes in chunk[..take * 8].chunks_exact(8) {
            values.push(i64::from_le_bytes(bytes.try_into().expect("eight bytes")));
        }
    }
    Ok(values)
}
fn section(out: &mut impl Write, value: &ResidentSectionRest) -> Result<(), Error> {
    blob(out, &value.canonical_bytes().map_err(Error::Malformed)?)
}
fn read_section(input: &mut Take<impl Read>) -> Result<ResidentSectionRest, Error> {
    ResidentSectionRest::read(&read_blob(input)?).map_err(Error::Malformed)
}
fn sections(
    out: &mut impl Write,
    map: &BTreeMap<NativeCarrierOrdinal, ResidentSectionRest>,
) -> Result<(), Error> {
    number(out, map.len())?;
    for (key, value) in map {
        ordinal(out, key.0)?;
        section(out, value)?;
    }
    Ok(())
}
fn read_sections(
    input: &mut Take<impl Read>,
) -> Result<BTreeMap<NativeCarrierOrdinal, ResidentSectionRest>, Error> {
    let length = count(input, 12)?;
    let mut map = BTreeMap::new();
    for _ in 0..length {
        let key = NativeCarrierOrdinal(read_ordinal(input)?);
        if map.contains_key(&key) {
            return Err(malformed("duplicate section address"));
        }
        map.insert(key, read_section(input)?);
    }
    Ok(map)
}
fn overlays(
    out: &mut impl Write,
    map: &BTreeMap<NativeTensorOrdinal, Vec<NativeOverlayRest>>,
) -> Result<(), Error> {
    number(out, map.len())?;
    for (key, atoms) in map {
        ordinal(out, key.0)?;
        number(out, atoms.len())?;
        for atom in atoms {
            json(
                out,
                &(
                    atom.rows,
                    atom.width,
                    atom.rank,
                    atom.u_exponent,
                    atom.v_exponent,
                    atom.u_octaves,
                    atom.v_octaves,
                ),
            )?;
            words(out, &atom.u)?;
            words(out, &atom.v)?;
        }
    }
    Ok(())
}
fn read_overlays(
    input: &mut Take<impl Read>,
) -> Result<BTreeMap<NativeTensorOrdinal, Vec<NativeOverlayRest>>, Error> {
    let length = count(input, 12)?;
    let mut map = BTreeMap::new();
    for _ in 0..length {
        let key = NativeTensorOrdinal(read_ordinal(input)?);
        if map.contains_key(&key) {
            return Err(malformed("duplicate overlay population"));
        }
        let n = count(input, 24)?;
        let mut atoms = Vec::new();
        for _ in 0..n {
            let (rows, width, rank, u_exponent, v_exponent, u_octaves, v_octaves) =
                read_json(input)?;
            let atom = NativeOverlayRest {
                rows,
                width,
                rank,
                u_exponent,
                v_exponent,
                u_octaves,
                v_octaves,
                u: read_words(input)?,
                v: read_words(input)?,
            };
            atom.validate()?;
            atoms.push(atom);
        }
        map.insert(key, atoms);
    }
    Ok(map)
}
fn tiled(out: &mut impl Write, value: &Option<NativeTiledRest>) -> Result<(), Error> {
    flag(out, value.is_some())?;
    if let Some(value) = value {
        json(out, &(value.carrier, value.rows, value.width, value.grain))?;
        number(out, value.sections.len())?;
        for held in &value.sections {
            section(out, held)?;
        }
    }
    Ok(())
}
fn read_tiled(input: &mut Take<impl Read>) -> Result<Option<NativeTiledRest>, Error> {
    if !read_flag(input)? {
        return Ok(None);
    }
    let (carrier, rows, width, grain) = read_json(input)?;
    let length = count(input, 8)?;
    let mut sections = Vec::new();
    for _ in 0..length {
        sections.push(read_section(input)?);
    }
    Ok(Some(NativeTiledRest {
        carrier,
        rows,
        width,
        grain,
        sections,
    }))
}

impl NativeFullSessionRest {
    pub fn write_to(&self, out: &mut impl Write) -> Result<(), Error> {
        self.validate()?;
        out.write_all(MAGIC)?;
        json(out, &self.header)?;
        sections(out, &self.carriers)?;
        sections(out, &self.checkpoints)?;
        tiled(out, &self.terminal_carrier)?;
        tiled(out, &self.terminal_reacted)?;
        flag(out, self.terminal_contracted.is_some())?;
        if let Some(pairs) = &self.terminal_contracted {
            number(out, pairs.len())?;
            for (lo, hi) in pairs {
                out.write_all(&lo.to_le_bytes())?;
                out.write_all(&hi.to_le_bytes())?;
            }
        }
        flag(out, self.terminal_presented.is_some())?;
        if let Some(value) = &self.terminal_presented {
            section(out, value)?;
        }
        overlays(out, &self.overlay)?;
        flag(out, self.passage.is_some())?;
        if let Some(passage) = &self.passage {
            json(out, &passage.aperture)?;
            overlays(out, &passage.pending)?;
            json(out, &passage.returns)?;
        }
        flag(out, self.reuse.is_some())?;
        if let Some(reuse) = &self.reuse {
            json(out, &reuse.census)?;
            // Entries are a sequence so duplicate keys cannot silently overwrite one another.
            number(out, reuse.numerical.len())?;
            for (key, value) in &reuse.numerical {
                ordinal(out, key.0)?;
                json(out, value)?;
            }
            sections(out, &reuse.standing)?;
        }
        out.write_all(END)?;
        Ok(())
    }

    /// Decode precisely one caller-bounded frame. No declared length is trusted as an allocation
    /// request before its bytes arrive. Extra bytes inside this frame and missing bytes refuse.
    pub fn read_from(input: &mut impl Read, octets: u64) -> Result<Self, Error> {
        let mut input = input.take(octets);
        let mut magic = vec![0; MAGIC.len()];
        input.read_exact(&mut magic)?;
        if magic != MAGIC {
            return Err(malformed("session wire magic/version"));
        }
        let header = read_json(&mut input)?;
        let carriers = read_sections(&mut input)?;
        let checkpoints = read_sections(&mut input)?;
        let terminal_carrier = read_tiled(&mut input)?;
        let terminal_reacted = read_tiled(&mut input)?;
        let terminal_contracted = if read_flag(&mut input)? {
            let n = count(&mut input, 16)?;
            let mut pairs = Vec::new();
            for _ in 0..n {
                let mut lo = [0; 8];
                let mut hi = [0; 8];
                input.read_exact(&mut lo)?;
                input.read_exact(&mut hi)?;
                pairs.push((i64::from_le_bytes(lo), i64::from_le_bytes(hi)));
            }
            Some(pairs)
        } else {
            None
        };
        let terminal_presented = if read_flag(&mut input)? {
            Some(read_section(&mut input)?)
        } else {
            None
        };
        let overlay = read_overlays(&mut input)?;
        let passage = if read_flag(&mut input)? {
            Some(NativePassageRest {
                aperture: read_json(&mut input)?,
                pending: read_overlays(&mut input)?,
                returns: read_json(&mut input)?,
            })
        } else {
            None
        };
        let reuse = if read_flag(&mut input)? {
            let census = read_json(&mut input)?;
            let n = count(&mut input, 12)?;
            let mut numerical = BTreeMap::new();
            for _ in 0..n {
                let key = NativeCarrierOrdinal(read_ordinal(&mut input)?);
                if numerical.contains_key(&key) {
                    return Err(malformed("duplicate numerical address"));
                }
                numerical.insert(key, read_json(&mut input)?);
            }
            Some(NativeForwardReuseRest {
                census,
                numerical,
                standing: read_sections(&mut input)?,
            })
        } else {
            None
        };
        let mut end = vec![0; END.len()];
        input.read_exact(&mut end)?;
        if end != END || input.limit() != 0 {
            return Err(malformed("session frame end/trailing bytes"));
        }
        let rest = Self {
            header,
            carriers,
            checkpoints,
            terminal_carrier,
            terminal_reacted,
            terminal_contracted,
            terminal_presented,
            overlay,
            passage,
            reuse,
        };
        rest.validate()?;
        Ok(rest)
    }
}
