//! The exterior container codec: RFC 1951 DEFLATE and the ZIP member directory a `.npz` is.
//!
//! [definition] A `.npz` occurrence is a ZIP archive of `.npy` members, and every member NumPy
//! writes is deflated. This is an **exterior serialized chart** in the sense of AGENTS.md: it
//! carries no mathematics of its own, and nothing here decides a coordinate, a contact or a
//! grade. It exists so that [`super::numpy`] can reach the bytes of a member without a caller
//! first shelling out to an extractor, which is exactly the "reachable from no library" defect
//! item **B2** names.
//!
//! Everything is integer and total. There is no float, no `unsafe` and no panic path. **No
//! allocation is ever sized by a field the container declares**: a central directory's
//! `uncompressed` extent is unauthenticated testimony read before a single octet has been
//! decompressed or checksummed, so it is first bounded by [`MAXIMUM_DECLARED_EXTENT`] and by what
//! [`MAXIMUM_DEFLATE_EXPANSION`] permits the payload actually present to produce, and the output
//! then grows incrementally under that bound rather than being reserved from the declaration.
//! Every malformed input returns [`super::IntakeRefusal`] naming what failed.
//!
//! The decoder is the canonical-Huffman walk of RFC 1951 §3.2.2: counts per code length and the
//! symbols in code order, decoded one bit at a time, so no oversized lookup table is built and a
//! truncated stream is a refusal at the bit that runs out rather than an index out of range.
//!
//! Each member's CRC-32 is recomputed and compared against the directory's. A container codec
//! that does not check its own checksum is testimony about nothing.

use super::IntakeRefusal;

/// The end-of-central-directory signature, `PK\x05\x06`.
const END_OF_CENTRAL_DIRECTORY: [u8; 4] = [0x50, 0x4b, 0x05, 0x06];
/// The central-directory file-header signature, `PK\x01\x02`.
const CENTRAL_FILE_HEADER: [u8; 4] = [0x50, 0x4b, 0x01, 0x02];
/// The local file-header signature, `PK\x03\x04`.
const LOCAL_FILE_HEADER: [u8; 4] = [0x50, 0x4b, 0x03, 0x04];

/// The absolute ceiling on an uncompressed extent a member may declare, one gibioctet.
///
/// [definition] The declared extent is an unauthenticated `u32` read out of the central directory
/// before anything has been decompressed or checksummed. A ceiling is what keeps a member that
/// declares `0xffff_fffe` from being a resource declaration rather than a description.
pub const MAXIMUM_DECLARED_EXTENT: usize = 1 << 30;

/// The most octets one compressed octet can lawfully produce under RFC 1951.
///
/// [definition] A dynamic-Huffman block can encode a 258-octet match in two bits, and 258 octets
/// per two bits is 1032 octets per octet. No conforming stream exceeds that ratio, so a member
/// declaring more than `1032 · (compressed + 1)` octets has declared an extent its own payload
/// cannot honour — which is knowable, exactly, before any allocation.
pub const MAXIMUM_DEFLATE_EXPANSION: usize = 1032;

/// How much output is reserved up front. Beyond this the output grows incrementally, so a declared
/// extent never becomes a reservation even when it is inside [`declared_extent_bound`].
const OUTPUT_RESERVE: usize = 1 << 16;

/// The largest uncompressed extent `compressed` octets of deflate payload can lawfully produce.
///
/// This is the smaller of the absolute ceiling and the expansion the payload present permits. Both
/// are needed: the ratio alone admits a gibioctet from a mebioctet of payload, and the ceiling
/// alone admits four gibioctets declared by a payload of two hundred octets.
pub fn declared_extent_bound(compressed: usize) -> usize {
    compressed
        .saturating_add(1)
        .saturating_mul(MAXIMUM_DEFLATE_EXPANSION)
        .min(MAXIMUM_DECLARED_EXTENT)
}

/// One member of a ZIP container, already inflated and CRC-checked.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArchiveMember {
    /// The member's name inside the container.
    pub name: String,
    /// The stored compression method: `0` stored, `8` deflate.
    pub method: u16,
    /// The declared CRC-32, which [`read_zip_members`] has already verified.
    pub crc32: u32,
    /// The member's bytes.
    pub bytes: Vec<u8>,
}

/// Read every member of a ZIP container, inflating and CRC-checking each one.
///
/// Members are returned in central-directory order, which is the order the writer deposited them.
pub fn read_zip_members(
    archive_lineage: &str,
    data: &[u8],
) -> Result<Vec<ArchiveMember>, IntakeRefusal> {
    let refusal = |detail: String| IntakeRefusal::MalformedArchive {
        archive: archive_lineage.to_owned(),
        detail,
    };
    let directory_at = locate_end_of_central_directory(data)
        .ok_or_else(|| refusal("no end-of-central-directory record".to_owned()))?;
    let end = &data[directory_at..];
    if end.len() < 22 {
        return Err(refusal("the end-of-central-directory record is truncated".to_owned()));
    }
    let entries = u16::from_le_bytes([end[10], end[11]]) as usize;
    let directory_offset = u32::from_le_bytes([end[16], end[17], end[18], end[19]]) as usize;
    if directory_offset > data.len() {
        return Err(refusal(format!(
            "the central directory offset {directory_offset} leaves the {} octet container",
            data.len()
        )));
    }

    let mut members = Vec::with_capacity(entries);
    let mut cursor = directory_offset;
    for entry in 0..entries {
        if cursor + 46 > data.len() {
            return Err(refusal(format!("central directory entry {entry} is truncated")));
        }
        if data[cursor..cursor + 4] != CENTRAL_FILE_HEADER {
            return Err(refusal(format!(
                "central directory entry {entry} carries no PK\\x01\\x02 signature"
            )));
        }
        let method = u16::from_le_bytes([data[cursor + 10], data[cursor + 11]]);
        let crc32 = u32::from_le_bytes([
            data[cursor + 16],
            data[cursor + 17],
            data[cursor + 18],
            data[cursor + 19],
        ]);
        let compressed = u32::from_le_bytes([
            data[cursor + 20],
            data[cursor + 21],
            data[cursor + 22],
            data[cursor + 23],
        ]) as usize;
        let uncompressed = u32::from_le_bytes([
            data[cursor + 24],
            data[cursor + 25],
            data[cursor + 26],
            data[cursor + 27],
        ]) as usize;
        let name_octets = u16::from_le_bytes([data[cursor + 28], data[cursor + 29]]) as usize;
        let extra_octets = u16::from_le_bytes([data[cursor + 30], data[cursor + 31]]) as usize;
        let comment_octets = u16::from_le_bytes([data[cursor + 32], data[cursor + 33]]) as usize;
        let local_offset = u32::from_le_bytes([
            data[cursor + 42],
            data[cursor + 43],
            data[cursor + 44],
            data[cursor + 45],
        ]) as usize;
        let name_at = cursor + 46;
        if name_at + name_octets > data.len() {
            return Err(refusal(format!("central directory entry {entry} has a truncated name")));
        }
        let name = String::from_utf8(data[name_at..name_at + name_octets].to_vec())
            .map_err(|error| refusal(format!("member name {entry} is not UTF-8: {error}")))?;
        cursor = name_at + name_octets + extra_octets + comment_octets;

        // The local header repeats the name and extra fields with its own lengths; the payload
        // begins after them, never at the central directory's extra length.
        if local_offset + 30 > data.len() {
            return Err(refusal(format!("{name}: the local header leaves the container")));
        }
        if data[local_offset..local_offset + 4] != LOCAL_FILE_HEADER {
            return Err(refusal(format!("{name}: no PK\\x03\\x04 local signature")));
        }
        let local_name_octets =
            u16::from_le_bytes([data[local_offset + 26], data[local_offset + 27]]) as usize;
        let local_extra_octets =
            u16::from_le_bytes([data[local_offset + 28], data[local_offset + 29]]) as usize;
        let payload_at = local_offset + 30 + local_name_octets + local_extra_octets;
        let payload_end = payload_at
            .checked_add(compressed)
            .ok_or_else(|| refusal(format!("{name}: the payload extent overflows")))?;
        if payload_end > data.len() {
            return Err(refusal(format!("{name}: the payload leaves the container")));
        }
        let payload = &data[payload_at..payload_end];
        let bytes = match method {
            0 => payload.to_vec(),
            8 => inflate(&name, payload, uncompressed)?,
            other => {
                return Err(refusal(format!(
                    "{name}: compression method {other} is not stored or deflate"
                )));
            }
        };
        if bytes.len() != uncompressed {
            return Err(refusal(format!(
                "{name}: {} octets were recovered where the directory declares {uncompressed}",
                bytes.len()
            )));
        }
        let measured = crc32_of(&bytes);
        if measured != crc32 {
            return Err(refusal(format!(
                "{name}: the recovered CRC-32 {measured:#010x} disagrees with the declared \
                 {crc32:#010x}"
            )));
        }
        members.push(ArchiveMember {
            name,
            method,
            crc32,
            bytes,
        });
    }
    Ok(members)
}

fn locate_end_of_central_directory(data: &[u8]) -> Option<usize> {
    if data.len() < 22 {
        return None;
    }
    // The record is 22 octets plus a comment of at most 65,535.
    let earliest = data.len().saturating_sub(22 + 65_535);
    (earliest..=data.len() - 22)
        .rev()
        .find(|at| data[*at..*at + 4] == END_OF_CENTRAL_DIRECTORY)
}

// -------------------------------------------------------------------------------------------
// RFC 1951
// -------------------------------------------------------------------------------------------

struct BitReader<'a> {
    data: &'a [u8],
    at: usize,
    bit: u32,
}

impl<'a> BitReader<'a> {
    fn new(data: &'a [u8]) -> Self {
        Self { data, at: 0, bit: 0 }
    }

    /// `count` bits, least significant first, as RFC 1951 §3.1.1 packs them.
    fn take(&mut self, count: u32) -> Option<u32> {
        let mut value = 0_u32;
        for index in 0..count {
            let byte = *self.data.get(self.at)?;
            value |= u32::from((byte >> self.bit) & 1) << index;
            self.bit += 1;
            if self.bit == 8 {
                self.bit = 0;
                self.at += 1;
            }
        }
        Some(value)
    }

    fn align(&mut self) {
        if self.bit != 0 {
            self.bit = 0;
            self.at += 1;
        }
    }
}

/// A canonical Huffman code: how many symbols carry each length, and the symbols in code order.
struct Huffman {
    counts: [u16; 16],
    symbols: Vec<u16>,
}

impl Huffman {
    fn build(lengths: &[u8]) -> Option<Self> {
        // Both guards make `build` total on an arbitrary length vector rather than total only
        // under its callers' invariants: a length of sixteen or more would index past `counts`,
        // and more than `u16::MAX` symbols would leave the symbol wire.
        if lengths.len() > u16::MAX as usize || lengths.iter().any(|length| *length >= 16) {
            return None;
        }
        let mut counts = [0_u16; 16];
        for length in lengths {
            counts[*length as usize] += 1;
        }
        counts[0] = 0;
        // An over-subscribed code is malformed; an incomplete one is admitted only when it is
        // empty or a single symbol, which RFC 1951 permits for the distance code.
        let mut left = 1_i32;
        for count in counts.iter().skip(1) {
            left <<= 1;
            left -= i32::from(*count);
            if left < 0 {
                return None;
            }
        }
        let mut offsets = [0_u16; 16];
        for length in 1..15 {
            offsets[length + 1] = offsets[length] + counts[length];
        }
        let mut symbols = vec![0_u16; lengths.len()];
        for (symbol, length) in lengths.iter().enumerate() {
            if *length != 0 {
                symbols[offsets[*length as usize] as usize] = symbol as u16;
                offsets[*length as usize] += 1;
            }
        }
        Some(Self { counts, symbols })
    }

    /// The RFC 1951 §3.2.6 fixed literal/length and distance codes, written out directly.
    ///
    /// [definition] These are constants of the format, not a decode of anything, so they are
    /// stated as the canonical tables rather than derived through the fallible [`Self::build`].
    /// The literal code carries 24 symbols of length 7 (`256..=279`), 152 of length 8
    /// (`0..=143` then `280..=287`) and 112 of length 9 (`144..=255`), in that canonical order;
    /// the distance code carries all 30 symbols at length 5. `fixed_agrees_with_build` checks the
    /// equality with [`Self::build`] so this is a rewriting and not a second definition.
    fn fixed() -> (Self, Self) {
        let mut literal_counts = [0_u16; 16];
        literal_counts[7] = 24;
        literal_counts[8] = 152;
        literal_counts[9] = 112;
        let mut literal_symbols = Vec::with_capacity(288);
        literal_symbols.extend(256_u16..=279);
        literal_symbols.extend(0_u16..=143);
        literal_symbols.extend(280_u16..=287);
        literal_symbols.extend(144_u16..=255);
        let mut distance_counts = [0_u16; 16];
        distance_counts[5] = 30;
        (
            Self {
                counts: literal_counts,
                symbols: literal_symbols,
            },
            Self {
                counts: distance_counts,
                symbols: (0_u16..30).collect(),
            },
        )
    }

    fn decode(&self, reader: &mut BitReader<'_>) -> Option<u16> {
        let mut code = 0_i32;
        let mut first = 0_i32;
        let mut index = 0_i32;
        for length in 1..16 {
            code |= reader.take(1)? as i32;
            let count = i32::from(self.counts[length]);
            if code - first < count {
                return self.symbols.get((index + code - first) as usize).copied();
            }
            index += count;
            first = (first + count) << 1;
            code <<= 1;
        }
        None
    }
}

const LENGTH_BASE: [u16; 29] = [
    3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131,
    163, 195, 227, 258,
];
const LENGTH_EXTRA: [u8; 29] = [
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0,
];
const DISTANCE_BASE: [u16; 30] = [
    1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537,
    2049, 3073, 4097, 6145, 8193, 12_289, 16_385, 24_577,
];
const DISTANCE_EXTRA: [u8; 30] = [
    0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13,
    13,
];
const CODE_LENGTH_ORDER: [usize; 19] = [
    16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15,
];

/// Inflate one RFC 1951 stream. `expected` is the **declared** output extent: it bounds the
/// output, and it is itself bounded by [`declared_extent_bound`] before it is allowed to bound
/// anything, because nothing has authenticated it at this point.
///
/// A declaration outside that bound is [`IntakeRefusal::DeclaredExtentUnbounded`], naming the
/// member, the declared extent, the payload it was declared over and the bound. The output is
/// reserved at [`OUTPUT_RESERVE`] and grows incrementally from there, so even an admitted
/// declaration never sizes an allocation.
pub fn inflate(
    member_lineage: &str,
    input: &[u8],
    expected: usize,
) -> Result<Vec<u8>, IntakeRefusal> {
    let refusal = |detail: &str| IntakeRefusal::MalformedArchive {
        archive: member_lineage.to_owned(),
        detail: detail.to_owned(),
    };
    let bound = declared_extent_bound(input.len());
    if expected > bound {
        return Err(IntakeRefusal::DeclaredExtentUnbounded {
            member: member_lineage.to_owned(),
            declared: expected,
            compressed: input.len(),
            bound,
            detail: format!(
                "the bound is the smaller of the {MAXIMUM_DECLARED_EXTENT} octet ceiling and the \
                 {MAXIMUM_DEFLATE_EXPANSION}:1 maximum RFC 1951 expansion of the payload present"
            ),
        });
    }
    let mut reader = BitReader::new(input);
    let mut out = Vec::with_capacity(expected.min(OUTPUT_RESERVE));
    loop {
        let final_block = reader.take(1).ok_or_else(|| refusal("the stream ends inside a block header"))?;
        let kind = reader.take(2).ok_or_else(|| refusal("the stream ends inside a block header"))?;
        match kind {
            0 => {
                reader.align();
                if reader.at + 4 > reader.data.len() {
                    return Err(refusal("a stored block header leaves the stream"));
                }
                let length =
                    u16::from_le_bytes([reader.data[reader.at], reader.data[reader.at + 1]]) as usize;
                let complement =
                    u16::from_le_bytes([reader.data[reader.at + 2], reader.data[reader.at + 3]]);
                if complement != !(length as u16) {
                    return Err(refusal("a stored block's length complement disagrees"));
                }
                reader.at += 4;
                if reader.at + length > reader.data.len() {
                    return Err(refusal("a stored block leaves the stream"));
                }
                if out.len().saturating_add(length) > expected {
                    return Err(refusal(
                        "the stream produced more octets than the directory declares",
                    ));
                }
                out.extend_from_slice(&reader.data[reader.at..reader.at + length]);
                reader.at += length;
            }
            1 => {
                let (literal, distance) = Huffman::fixed();
                inflate_block(&mut reader, &literal, &distance, &mut out, expected, &refusal)?;
            }
            2 => {
                let (literal, distance) = dynamic_codes(&mut reader, &refusal)?;
                inflate_block(&mut reader, &literal, &distance, &mut out, expected, &refusal)?;
            }
            _ => return Err(refusal("block type 3 is reserved")),
        }
        if out.len() > expected {
            return Err(refusal("the stream produced more octets than the directory declares"));
        }
        if final_block == 1 {
            break;
        }
    }
    Ok(out)
}

/// The RFC 1951 §3.2.6 fixed code lengths: 8 bits for `0..=143`, 9 for `144..=255`, 7 for
/// `256..=279` and 8 for `280..=287`, with every distance symbol at 5. The decoder reads
/// [`Huffman::fixed`] directly; these lengths exist so the equality between the two is checkable.
#[cfg(test)]
fn fixed_code_lengths() -> ([u8; 288], [u8; 30]) {
    let mut literal_lengths = [0_u8; 288];
    for (symbol, length) in literal_lengths.iter_mut().enumerate() {
        *length = match symbol {
            0..=143 => 8,
            144..=255 => 9,
            256..=279 => 7,
            _ => 8,
        };
    }
    (literal_lengths, [5_u8; 30])
}

/// Whether the directly written fixed tables agree with the canonical construction from the RFC
/// 1951 §3.2.6 code lengths.
///
/// This is what [`Huffman::fixed`] replaces two `expect` calls with: the equality is checked by
/// `physical_intake/tests.rs` instead of asserted at runtime on a path that must not panic.
#[cfg(test)]
pub fn fixed_agrees_with_build() -> bool {
    let (literal_lengths, distance_lengths) = fixed_code_lengths();
    let (literal, distance) = Huffman::fixed();
    let agrees = |direct: &Huffman, lengths: &[u8]| match Huffman::build(lengths) {
        Some(built) => built.counts == direct.counts && built.symbols == direct.symbols,
        None => false,
    };
    agrees(&literal, &literal_lengths) && agrees(&distance, &distance_lengths)
}

fn dynamic_codes(
    reader: &mut BitReader<'_>,
    refusal: &impl Fn(&str) -> IntakeRefusal,
) -> Result<(Huffman, Huffman), IntakeRefusal> {
    let literal_count =
        reader.take(5).ok_or_else(|| refusal("a dynamic header ends early"))? as usize + 257;
    let distance_count =
        reader.take(5).ok_or_else(|| refusal("a dynamic header ends early"))? as usize + 1;
    let code_count =
        reader.take(4).ok_or_else(|| refusal("a dynamic header ends early"))? as usize + 4;
    if literal_count > 286 || distance_count > 30 {
        return Err(refusal("a dynamic header declares too many codes"));
    }
    let mut code_lengths = [0_u8; 19];
    for position in CODE_LENGTH_ORDER.iter().take(code_count) {
        code_lengths[*position] =
            reader.take(3).ok_or_else(|| refusal("a code-length header ends early"))? as u8;
    }
    let code_length_code =
        Huffman::build(&code_lengths).ok_or_else(|| refusal("the code-length code is malformed"))?;

    let total = literal_count + distance_count;
    let mut lengths = vec![0_u8; total];
    let mut at = 0usize;
    while at < total {
        let symbol = code_length_code
            .decode(reader)
            .ok_or_else(|| refusal("a code-length symbol ends the stream"))?;
        match symbol {
            0..=15 => {
                lengths[at] = symbol as u8;
                at += 1;
            }
            16 => {
                if at == 0 {
                    return Err(refusal("a repeat code precedes any length"));
                }
                let previous = lengths[at - 1];
                let repeat =
                    reader.take(2).ok_or_else(|| refusal("a repeat count ends the stream"))? as usize
                        + 3;
                if at + repeat > total {
                    return Err(refusal("a repeat count overruns the code-length table"));
                }
                for slot in &mut lengths[at..at + repeat] {
                    *slot = previous;
                }
                at += repeat;
            }
            17 => {
                let repeat =
                    reader.take(3).ok_or_else(|| refusal("a zero run ends the stream"))? as usize + 3;
                if at + repeat > total {
                    return Err(refusal("a zero run overruns the code-length table"));
                }
                at += repeat;
            }
            18 => {
                let repeat =
                    reader.take(7).ok_or_else(|| refusal("a zero run ends the stream"))? as usize
                        + 11;
                if at + repeat > total {
                    return Err(refusal("a zero run overruns the code-length table"));
                }
                at += repeat;
            }
            _ => return Err(refusal("a code-length symbol is out of range")),
        }
    }
    let literal = Huffman::build(&lengths[..literal_count])
        .ok_or_else(|| refusal("the literal/length code is malformed"))?;
    let distance = Huffman::build(&lengths[literal_count..])
        .ok_or_else(|| refusal("the distance code is malformed"))?;
    Ok((literal, distance))
}

fn inflate_block(
    reader: &mut BitReader<'_>,
    literal: &Huffman,
    distance: &Huffman,
    out: &mut Vec<u8>,
    expected: usize,
    refusal: &impl Fn(&str) -> IntakeRefusal,
) -> Result<(), IntakeRefusal> {
    loop {
        let symbol = literal
            .decode(reader)
            .ok_or_else(|| refusal("a literal/length symbol ends the stream"))?;
        match symbol {
            0..=255 => out.push(symbol as u8),
            256 => return Ok(()),
            257..=285 => {
                let index = symbol as usize - 257;
                let extra = u32::from(LENGTH_EXTRA[index]);
                let length = LENGTH_BASE[index] as usize
                    + reader.take(extra).ok_or_else(|| refusal("a length ends the stream"))?
                        as usize;
                let distance_symbol = distance
                    .decode(reader)
                    .ok_or_else(|| refusal("a distance symbol ends the stream"))?
                    as usize;
                if distance_symbol >= DISTANCE_BASE.len() {
                    return Err(refusal("a distance symbol is out of range"));
                }
                let distance_extra = u32::from(DISTANCE_EXTRA[distance_symbol]);
                let back = DISTANCE_BASE[distance_symbol] as usize
                    + reader
                        .take(distance_extra)
                        .ok_or_else(|| refusal("a distance ends the stream"))?
                        as usize;
                if back > out.len() {
                    return Err(refusal("a back reference precedes the output"));
                }
                if out.len() + length > expected {
                    return Err(refusal(
                        "the stream produced more octets than the directory declares",
                    ));
                }
                let start = out.len() - back;
                for offset in 0..length {
                    let byte = out[start + offset];
                    out.push(byte);
                }
            }
            _ => return Err(refusal("a literal/length symbol is out of range")),
        }
        if out.len() > expected {
            return Err(refusal("the stream produced more octets than the directory declares"));
        }
    }
}

/// The ISO 3309 / RFC 1952 CRC-32 of a byte population, computed bitwise so no table is stored.
pub fn crc32_of(data: &[u8]) -> u32 {
    let mut crc = 0xffff_ffff_u32;
    for byte in data {
        crc ^= u32::from(*byte);
        for _ in 0..8 {
            let mask = (crc & 1).wrapping_neg();
            crc = (crc >> 1) ^ (0xedb8_8320 & mask);
        }
    }
    !crc
}
