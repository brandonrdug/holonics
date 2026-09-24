//! The laws of the library intake, and the measured M5 table it reproduces through the library
//! path.
//!
//! The synthetic tests state what the Lean owner
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/ExteriorIntake.lean` proves, and they
//! run everywhere with no fixture and no environment variable. The three fixture tests reproduce
//! the authenticated release and **fail** when it is absent: a test that cannot run says so by
//! failing, because cargo discards the output of a passing test.

use std::collections::BTreeMap;
use std::path::PathBuf;

use num_bigint::BigInt;
use num_bigint::BigUint;
use relational_geometry::Rat;

use super::deflate::{
    MAXIMUM_DECLARED_EXTENT, MAXIMUM_DEFLATE_EXPANSION, crc32_of, declared_extent_bound, inflate,
    read_zip_members,
};
use super::mmcif::{DecimalToken, StructurePresentation};
use super::numpy::{ExactWord, NpyArray, NumpySource, UncertaintyWordFormat};
use super::*;
use holonics::exact_value::ieee754::{FloatReading, decode_binary16_bits, decode_binary32_bits};
use crate::physical_constraint_complex::ContactClass;

// ---------------------------------------------------------------------------------------------
// Fixture addresses. Both follow the pattern `grain_tower/tests.rs` established.
// ---------------------------------------------------------------------------------------------

const STRUCTURE_ROOT_ENV: &str = "HOLONICS_M5_STRUCTURE_ROOT";
const DEFAULT_STRUCTURE_ROOT: &str = "/home/b/Downloads/holonics-m5-rbx1-rank05";
const BOLTZ_ROOT_ENV: &str = "HOLONICS_BOLTZ_PREDICTION_ROOT";
/// Relative to the repository root, which is two directories above this crate's manifest. Cargo
/// runs a test with the crate directory as its working directory, so the default is resolved
/// rather than assumed.
const DEFAULT_BOLTZ_ROOT: &str = ".local/boltz-smoke/out/boltz_results_test/predictions/test";

/// The resident decimal grain the M5 family is carried on, the same one
/// `crates/holonic-life/examples/m5/fold.rs::derive_resident_places` derives and
/// `grain_tower/tests.rs` reproduces.
const RESIDENT_DECIMAL_PLACES: u32 = 7;
/// The declared contact radius, in whole angstroms.
const CONTACT_RADIUS: i128 = 8;
/// The alpha-carbon representative the M5 deed selects.
const REPRESENTATIVE: &str = "CA";
const SELECTION_LINEAGE: &str =
    "label_atom_id == CA, the receiver crates/holonic-life/examples/m5/cif.rs::REPRESENTATIVE enacts";

fn structure_root() -> PathBuf {
    std::env::var_os(STRUCTURE_ROOT_ENV)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(DEFAULT_STRUCTURE_ROOT))
}

fn boltz_root() -> PathBuf {
    std::env::var_os(BOLTZ_ROOT_ENV)
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("../..")
                .join(DEFAULT_BOLTZ_ROOT)
        })
}

// ---------------------------------------------------------------------------------------------
// Exterior container codec
// ---------------------------------------------------------------------------------------------

fn hex_octets(text: &str) -> Vec<u8> {
    let digits = text.as_bytes();
    assert!(digits.len().is_multiple_of(2), "a hex vector has even length");
    digits
        .chunks_exact(2)
        .map(|pair| {
            let value = |digit: u8| match digit {
                b'0'..=b'9' => digit - b'0',
                b'a'..=b'f' => digit - b'a' + 10,
                _ => panic!("the hex vector carries a non-hex digit"),
            };
            value(pair[0]) * 16 + value(pair[1])
        })
        .collect()
}

/// The payload of the dynamic-Huffman vector below: a linear congruential walk over an alphabet,
/// then a repeated block so the stream carries back references as well as literals.
fn deflate_vector_payload() -> Vec<u8> {
    let alphabet = b"abcdefghijklmnopqrstuvwxyz ";
    let mut state: u64 = 1;
    let mut payload = Vec::with_capacity(996);
    for _ in 0..900 {
        state = (state * 1_103_515_245 + 12_345) % (1_u64 << 31);
        payload.push(alphabet[((state >> 16) % 27) as usize]);
    }
    for _ in 0..8 {
        payload.extend_from_slice(b"repeat-block");
    }
    payload
}

/// A raw RFC 1951 **dynamic Huffman** stream of [`deflate_vector_payload`], produced once by
/// `zlib.compress(payload, 9)` with the zlib wrapper stripped. Retained as a vector so the codec is
/// checked without any fixture and without a compressor in the workspace.
const DYNAMIC_DEFLATE_VECTOR: &str = concat!(
    "b592d98d45210c435ba1815714610d4b80b053fddc26e62f91222bb60ffb3a20b995c33eb997e9aabc33aa2bf53ad196",
    "c92dd9d8649d2564b032cde5d4e64bdd2378224777e1d964668df7c59d5983a636c8cda9b46e5b74e57bfff4d3293862",
    "9e3eb7b69ffcb6cc9f4885c1c6ba63bd2b06520613049cac3aa93834033b4d662b2ac675cf718b7dd00ae7989fe59ce3",
    "dea08fb424dd90d4974eb11b7562d979b377efa91c34373bd2586a5f9de727d8c965ba62a6717c5407dfe557caf79caf",
    "4eb328a289535682bdec5cfdf4363785d6dba953bd3269298f16c635f10c1d6e4d33da2bbd9a8eb7ea38451ccbe4e008",
    "269858d55ebea898a59b19cb961e854eb51925fa6b16ac1a0bab59d5b9567343c9a7a5f8d9083e8dee77d944d1dad244",
    "aa70bfef2a2f6d5189a2cee18bb9ba925d647c7ebea15d2eaf197d8741a4f81e3a837d9b2595eb464e273d73e21a81c4",
    "fd626e523738fac5a1da04e9e8a17f73f1de171ae7ebdf2a6e2dd2287b11346c57ef5db8c921061a1b6b5d460d5bc842",
    "30efe384cb144bef1052d0dec350ae7457ddd76d2df812e900815478e5cd7444faec35ae9d5563a6e4f70ad380bd2dca",
    "0f01a4603e7339fad4fd31dad7bcbfce4ab99960ece6b30f826de9d87df5fe0b6899db37be41b86315da72c584fd9e69",
    "bb1bdd953bc04b33bc72b86c3e746ede8506901b5f0a327e87306744e1473c72178c8765688524e3bde1b22303e0eba1",
    "d2ca3adb9e0b1985d961049f199398fc187247cf3680a23086083bc2c752f280a7d5c5a87a90244cbb014ab66caa91e3",
    "07e9a3e43fe63f",
);

#[test]
fn the_exterior_container_codec_inflates_a_dynamic_huffman_stream_and_checks_its_crc() {
    let payload = deflate_vector_payload();
    assert_eq!(payload.len(), 996, "the vector's payload is 996 octets");
    let stream = hex_octets(DYNAMIC_DEFLATE_VECTOR);
    // Block header: the low bit is `final`, the next two bits are the block type. Type 2 is the
    // dynamic-Huffman path, which is the part of RFC 1951 with a code-length code of its own.
    assert_eq!(stream[0] & 1, 1, "the vector is one final block");
    assert_eq!((stream[0] >> 1) & 3, 2, "the vector exercises dynamic Huffman");
    let recovered = inflate("the dynamic deflate vector", &stream, payload.len())
        .expect("the vector inflates");
    assert_eq!(recovered, payload, "inflation is exact");
    assert_eq!(
        crc32_of(&recovered),
        0x485e_bd0c,
        "the CRC-32 of the recovered payload"
    );
}

#[test]
fn a_truncated_deflate_stream_is_a_typed_refusal_and_never_a_panic() {
    let payload = deflate_vector_payload();
    let stream = hex_octets(DYNAMIC_DEFLATE_VECTOR);
    for cut in [1_usize, 7, 40, stream.len() - 1] {
        let refusal = inflate("truncated", &stream[..cut], payload.len())
            .expect_err("a truncated stream cannot inflate");
        assert!(
            matches!(refusal, IntakeRefusal::MalformedArchive { .. }),
            "a truncated stream is a typed refusal, not a panic: {refusal}"
        );
    }
    let refusal = inflate("bounded", &stream, 4).expect_err("an under-declared extent refuses");
    assert!(matches!(refusal, IntakeRefusal::MalformedArchive { .. }));
}

// ---------------------------------------------------------------------------------------------
// Synthetic NumPy sources
// ---------------------------------------------------------------------------------------------

fn npy_bytes(descr: &str, shape: &[usize], payload: &[u8]) -> Vec<u8> {
    let shape_text = match shape {
        [] => String::new(),
        [only] => format!("{only},"),
        many => many
            .iter()
            .map(usize::to_string)
            .collect::<Vec<_>>()
            .join(", "),
    };
    let mut header =
        format!("{{'descr': '{descr}', 'fortran_order': False, 'shape': ({shape_text}), }}");
    while !(10 + header.len() + 1).is_multiple_of(64) {
        header.push(' ');
    }
    header.push('\n');
    let mut out = Vec::new();
    out.extend_from_slice(b"\x93NUMPY\x01\x00");
    out.extend_from_slice(&(header.len() as u16).to_le_bytes());
    out.extend_from_slice(header.as_bytes());
    out.extend_from_slice(payload);
    out
}

fn unicode_scalar_npy(value: &str) -> Vec<u8> {
    let codes = value.chars().collect::<Vec<_>>();
    let width = codes.len().max(1);
    let mut payload = Vec::with_capacity(width * 4);
    for at in 0..width {
        let code = codes.get(at).copied().map_or(0_u32, u32::from);
        payload.extend_from_slice(&code.to_le_bytes());
    }
    npy_bytes(&format!("<U{width}"), &[], &payload)
}

fn unicode_vector_npy(values: &[&str]) -> Vec<u8> {
    let width = values.iter().map(|value| value.chars().count()).max().unwrap_or(1).max(1);
    let mut payload = Vec::with_capacity(values.len() * width * 4);
    for value in values {
        let codes = value.chars().collect::<Vec<_>>();
        for at in 0..width {
            let code = codes.get(at).copied().map_or(0_u32, u32::from);
            payload.extend_from_slice(&code.to_le_bytes());
        }
    }
    npy_bytes(&format!("<U{width}"), &[values.len()], &payload)
}

fn i32_vector_npy(values: &[i32]) -> Vec<u8> {
    let mut payload = Vec::with_capacity(values.len() * 4);
    for value in values {
        payload.extend_from_slice(&value.to_le_bytes());
    }
    npy_bytes("<i4", &[values.len()], &payload)
}

fn binary16_square_npy(extent: usize, word: impl Fn(usize, usize) -> u16) -> Vec<u8> {
    let mut payload = Vec::with_capacity(extent * extent * 2);
    for row in 0..extent {
        for column in 0..extent {
            payload.extend_from_slice(&word(row, column).to_le_bytes());
        }
    }
    npy_bytes("<f2", &[extent, extent], &payload)
}

fn source_from(members: &[(&str, Vec<u8>)]) -> NumpySource {
    NumpySource {
        lineage: "synthetic".to_owned(),
        members: members
            .iter()
            .map(|(name, bytes)| {
                (
                    (*name).to_owned(),
                    NpyArray::parse(format!("synthetic::{name}"), bytes)
                        .expect("the synthetic member parses"),
                )
            })
            .collect(),
    }
}

/// One member of a synthetic ZIP container, with every field a hostile writer controls left
/// separate from the payload: the compression method, the **declared** CRC-32 and the **declared**
/// uncompressed extent are what the central directory carries, not what the payload measures.
struct SyntheticMember {
    name: String,
    method: u16,
    payload: Vec<u8>,
    crc32: u32,
    uncompressed: u32,
}

impl SyntheticMember {
    /// A stored member whose declarations all agree with its payload.
    fn stored(name: &str, bytes: Vec<u8>) -> Self {
        let crc32 = crc32_of(&bytes);
        let uncompressed = bytes.len() as u32;
        Self {
            name: name.to_owned(),
            method: 0,
            payload: bytes,
            crc32,
            uncompressed,
        }
    }
}

/// A ZIP container over declared members. Both the local header and the central directory carry
/// the member's own declarations, so a test can declare whatever a malformed writer would.
fn zip_container(members: &[SyntheticMember]) -> Vec<u8> {
    let mut out = Vec::new();
    let mut directory = Vec::new();
    for member in members {
        let offset = out.len() as u32;
        let name = member.name.as_bytes();
        let compressed = member.payload.len() as u32;
        out.extend_from_slice(b"PK\x03\x04");
        out.extend_from_slice(&20_u16.to_le_bytes());
        out.extend_from_slice(&0_u16.to_le_bytes());
        out.extend_from_slice(&member.method.to_le_bytes());
        out.extend_from_slice(&0_u32.to_le_bytes());
        out.extend_from_slice(&member.crc32.to_le_bytes());
        out.extend_from_slice(&compressed.to_le_bytes());
        out.extend_from_slice(&member.uncompressed.to_le_bytes());
        out.extend_from_slice(&(name.len() as u16).to_le_bytes());
        out.extend_from_slice(&0_u16.to_le_bytes());
        out.extend_from_slice(name);
        out.extend_from_slice(&member.payload);

        directory.extend_from_slice(b"PK\x01\x02");
        directory.extend_from_slice(&20_u16.to_le_bytes());
        directory.extend_from_slice(&20_u16.to_le_bytes());
        directory.extend_from_slice(&0_u16.to_le_bytes());
        directory.extend_from_slice(&member.method.to_le_bytes());
        directory.extend_from_slice(&0_u32.to_le_bytes());
        directory.extend_from_slice(&member.crc32.to_le_bytes());
        directory.extend_from_slice(&compressed.to_le_bytes());
        directory.extend_from_slice(&member.uncompressed.to_le_bytes());
        directory.extend_from_slice(&(name.len() as u16).to_le_bytes());
        directory.extend_from_slice(&0_u16.to_le_bytes());
        directory.extend_from_slice(&0_u16.to_le_bytes());
        directory.extend_from_slice(&0_u16.to_le_bytes());
        directory.extend_from_slice(&0_u16.to_le_bytes());
        directory.extend_from_slice(&0_u32.to_le_bytes());
        directory.extend_from_slice(&offset.to_le_bytes());
        directory.extend_from_slice(name);
    }
    let directory_offset = out.len() as u32;
    let directory_octets = directory.len() as u32;
    out.extend_from_slice(&directory);
    out.extend_from_slice(b"PK\x05\x06");
    out.extend_from_slice(&0_u16.to_le_bytes());
    out.extend_from_slice(&0_u16.to_le_bytes());
    out.extend_from_slice(&(members.len() as u16).to_le_bytes());
    out.extend_from_slice(&(members.len() as u16).to_le_bytes());
    out.extend_from_slice(&directory_octets.to_le_bytes());
    out.extend_from_slice(&directory_offset.to_le_bytes());
    out.extend_from_slice(&0_u16.to_le_bytes());
    out
}

/// A ZIP container whose members are **stored**, so the container path is checked independently of
/// the deflate path.
fn stored_zip(members: &[(&str, Vec<u8>)]) -> Vec<u8> {
    let members = members
        .iter()
        .map(|(name, bytes)| SyntheticMember::stored(name, bytes.clone()))
        .collect::<Vec<_>>();
    zip_container(&members)
}

/// A bit vector packed exactly as RFC 1951 §3.1.1 packs one, so a test can write a malformed
/// deflate stream by hand: header fields least significant bit first, Huffman codes most
/// significant bit first.
#[derive(Default)]
struct BitVector {
    bytes: Vec<u8>,
    bit: u32,
}

impl BitVector {
    /// `count` bits of `value`, least significant first. This is how a header field is packed.
    fn push(&mut self, value: u32, count: u32) {
        for index in 0..count {
            if self.bit == 0 {
                self.bytes.push(0);
            }
            let at = self.bytes.len() - 1;
            self.bytes[at] |= (((value >> index) & 1) as u8) << self.bit;
            self.bit = (self.bit + 1) % 8;
        }
    }

    /// One Huffman code of `length` bits, most significant first. This is how a code is packed.
    fn push_code(&mut self, code: u32, length: u32) {
        for index in (0..length).rev() {
            self.push((code >> index) & 1, 1);
        }
    }

    fn finish(self) -> Vec<u8> {
        self.bytes
    }
}

#[test]
fn a_stored_zip_container_is_read_through_the_same_member_path_as_a_deflated_one() {
    let bytes = stored_zip(&[
        ("pae.npy", binary16_square_npy(2, |row, column| 0x3000 + (row * 2 + column) as u16)),
        ("seed.npy", unicode_scalar_npy("7")),
    ]);
    let path = std::env::temp_dir().join("holonics-physical-intake-stored.npz");
    std::fs::write(&path, &bytes).expect("the synthetic container writes");
    let source = NumpySource::read_archive(&path).expect("the stored container reads");
    std::fs::remove_file(&path).ok();
    assert_eq!(source.member_names(), vec!["pae.npy", "seed.npy"]);
    assert_eq!(source.member("seed.npy").unwrap().unicode_scalar().unwrap(), "7");
    let (format, words) = source.member("pae.npy").unwrap().float_words().unwrap();
    assert_eq!(format, UncertaintyWordFormat::Binary16);
    assert_eq!(words, vec![0x3000, 0x3001, 0x3002, 0x3003]);
}

// ---------------------------------------------------------------------------------------------
// The hostile container. Every one of these is reachable from ordinary malformed input, and every
// one must return a **typed refusal**: not a panic, and not the process abort that a declared size
// handed to an allocator produces.
// ---------------------------------------------------------------------------------------------

#[test]
fn a_member_whose_declared_crc32_disagrees_with_its_payload_is_a_typed_refusal() {
    let mut member = SyntheticMember::stored(
        "pae.npy",
        binary16_square_npy(2, |row, column| 0x3000 + (row * 2 + column) as u16),
    );
    let declared = member.crc32 ^ 0x0000_0001;
    member.crc32 = declared;
    let refusal = read_zip_members("crc mismatch", &zip_container(&[member]))
        .expect_err("a member whose checksum disagrees is not admitted");
    match refusal {
        IntakeRefusal::MalformedArchive { detail, .. } => assert!(
            detail.contains("CRC-32") && detail.contains(&format!("{declared:#010x}")),
            "the refusal names the disagreement and the declaration: {detail}"
        ),
        other => panic!("returned {other}"),
    }
}

#[test]
fn a_declared_extent_no_payload_can_produce_is_refused_before_it_sizes_anything() {
    // The whole defect in one container: a few hundred octets of payload declaring that they
    // inflate to four gibioctets. Sized as an allocation this is `handle_alloc_error`, which
    // aborts the process and cannot be caught; it must be a refusal taken from the declaration
    // alone, before a single octet is decompressed.
    let payload = deflate_vector_payload();
    let stream = hex_octets(DYNAMIC_DEFLATE_VECTOR);
    let compressed = stream.len();
    let member = SyntheticMember {
        name: "pae.npy".to_owned(),
        method: 8,
        crc32: crc32_of(&payload),
        uncompressed: 0xffff_fffe,
        payload: stream,
    };
    let refusal = read_zip_members("over-declared", &zip_container(&[member]))
        .expect_err("an extent the payload cannot produce is not admitted");
    match refusal {
        IntakeRefusal::DeclaredExtentUnbounded {
            member,
            declared,
            compressed: measured,
            bound,
            ..
        } => {
            assert_eq!(member, "pae.npy", "the refusal names the member");
            assert_eq!(declared, 0xffff_fffe, "the refusal names the declaration");
            assert_eq!(measured, compressed, "and the payload it was declared over");
            assert_eq!(bound, declared_extent_bound(compressed), "and the bound");
            assert!(bound < declared, "the bound is what the declaration exceeded");
        }
        other => panic!("returned {other}"),
    }

    // The same container, honestly declared, still reads: the bound refuses over-declaration, not
    // compression.
    let honest = SyntheticMember {
        name: "pae.npy".to_owned(),
        method: 8,
        crc32: crc32_of(&payload),
        uncompressed: payload.len() as u32,
        payload: hex_octets(DYNAMIC_DEFLATE_VECTOR),
    };
    let members = read_zip_members("honest", &zip_container(&[honest]))
        .expect("an honestly declared deflated member reads");
    assert_eq!(members[0].bytes, payload, "the member inflates exactly");
}

#[test]
fn a_declared_extent_above_the_absolute_ceiling_is_a_typed_refusal() {
    // Inside the expansion ratio and outside the ceiling: a mebioctet of payload could lawfully
    // produce a gibioctet, so the ratio alone admits this declaration and the ceiling refuses it.
    let payload = vec![0_u8; 1_100_000];
    let compressed = payload.len();
    assert!(
        compressed * MAXIMUM_DEFLATE_EXPANSION > MAXIMUM_DECLARED_EXTENT,
        "the payload is large enough that the ratio alone would admit the declaration"
    );
    let member = SyntheticMember {
        name: "pae.npy".to_owned(),
        method: 8,
        crc32: 0,
        uncompressed: (MAXIMUM_DECLARED_EXTENT + 1) as u32,
        payload,
    };
    let refusal = read_zip_members("above the ceiling", &zip_container(&[member]))
        .expect_err("an extent above the absolute ceiling is not admitted");
    match refusal {
        IntakeRefusal::DeclaredExtentUnbounded { declared, bound, .. } => {
            assert_eq!(declared, MAXIMUM_DECLARED_EXTENT + 1);
            assert_eq!(bound, MAXIMUM_DECLARED_EXTENT, "the ceiling is the bound here");
        }
        other => panic!("returned {other}"),
    }
}

#[test]
fn an_over_subscribed_huffman_table_is_a_typed_refusal() {
    // A dynamic block whose *code-length* code is over-subscribed: four symbols sharing a one-bit
    // code is a Kraft sum of two, which no prefix code can carry.
    let mut stream = BitVector::default();
    stream.push(1, 1); // the final block
    stream.push(2, 2); // dynamic Huffman
    stream.push(0, 5); // 257 literal/length codes
    stream.push(0, 5); // one distance code
    stream.push(0, 4); // four code-length codes
    for _ in 0..4 {
        stream.push(1, 3);
    }
    let refusal = inflate("over-subscribed code lengths", &stream.finish(), 64)
        .expect_err("an over-subscribed code-length code is not a code");
    match refusal {
        IntakeRefusal::MalformedArchive { detail, .. } => {
            assert_eq!(detail, "the code-length code is malformed")
        }
        other => panic!("returned {other}"),
    }

    // And a well-formed code-length code that then declares an over-subscribed literal/length
    // code: 257 literals sharing a one-bit code.
    let mut stream = BitVector::default();
    stream.push(1, 1);
    stream.push(2, 2);
    stream.push(0, 5);
    stream.push(0, 5);
    stream.push(15, 4); // all nineteen code-length codes are declared
    // CODE_LENGTH_ORDER positions 2 and 17 are the symbols 18 and 1; giving exactly those two a
    // one-bit length is a complete code, under which the bit `0` decodes to the symbol `1`.
    for position in 0..19 {
        stream.push(u32::from(position == 2 || position == 17), 3);
    }
    for _ in 0..258 {
        stream.push_code(0, 1);
    }
    let refusal = inflate("over-subscribed literals", &stream.finish(), 64)
        .expect_err("an over-subscribed literal/length code is not a code");
    match refusal {
        IntakeRefusal::MalformedArchive { detail, .. } => {
            assert_eq!(detail, "the literal/length code is malformed")
        }
        other => panic!("returned {other}"),
    }
}

#[test]
fn a_back_reference_beyond_the_produced_output_is_a_typed_refusal() {
    // One literal, then a match whose distance reaches four octets back into an output that is one
    // octet long. Indexed rather than checked this reads before the start of the buffer.
    let mut stream = BitVector::default();
    stream.push(1, 1); // the final block
    stream.push(1, 2); // fixed Huffman
    stream.push_code(0x30 + 97, 8); // the literal `a`
    stream.push_code(1, 7); // length symbol 257: three octets, no extra bits
    stream.push_code(3, 5); // distance symbol 3: four octets back, no extra bits
    let refusal = inflate("back reference", &stream.finish(), 64)
        .expect_err("a distance beyond the produced output is not a reference");
    match refusal {
        IntakeRefusal::MalformedArchive { detail, .. } => {
            assert_eq!(detail, "a back reference precedes the output")
        }
        other => panic!("returned {other}"),
    }
}

#[test]
fn the_fixed_deflate_tables_are_written_out_rather_than_asserted_at_runtime() {
    // `Huffman::fixed` replaces two `expect` calls on a path whose whole claim is that it cannot
    // panic. The equality those `expect`s asserted at runtime is checked here instead.
    assert!(
        super::deflate::fixed_agrees_with_build(),
        "the directly written RFC 1951 fixed tables are the canonical construction"
    );
}

// ---------------------------------------------------------------------------------------------
// The exterior codeword
// ---------------------------------------------------------------------------------------------

#[test]
fn every_admitted_word_format_decodes_to_its_exact_dyadic() {
    // `1.5` in each format. The decoded value is the codeword's own value, not a rounding of it.
    let three_halves = Rat::new(BigInt::from(3), BigInt::from(2));
    for (format, bits) in [
        (UncertaintyWordFormat::Binary16, 0x3e00_u64),
        (UncertaintyWordFormat::Binary32, 0x3fc0_0000_u64),
        (UncertaintyWordFormat::Binary64, 0x3ff8_0000_0000_0000_u64),
    ] {
        let word = ExactWord::decode(format, 0, bits).expect("a finite word decodes");
        assert_eq!(word.value, three_halves, "{} decodes 1.5 exactly", format.descr());
        assert_eq!(word.bits, bits, "the exterior codeword is retained whole");
        assert!(word.as_point().is_point(), "the value is retained as a point");
    }

    // The ulp strictly narrows with the format, which is the whole content of "binary32 is finer".
    let ulp = |format: UncertaintyWordFormat, bits: u64| {
        ExactWord::decode(format, 0, bits).unwrap().unit_in_last_place
    };
    let narrow = ulp(UncertaintyWordFormat::Binary16, 0x3e00);
    let wide = ulp(UncertaintyWordFormat::Binary32, 0x3fc0_0000);
    let widest = ulp(UncertaintyWordFormat::Binary64, 0x3ff8_0000_0000_0000);
    assert!(wide < narrow, "binary32's last place is narrower than binary16's");
    assert!(widest < wide, "binary64's last place is narrower than binary32's");
    assert_eq!(
        UncertaintyWordFormat::Binary16.stored_significand_bits() + 13,
        UncertaintyWordFormat::Binary32.stored_significand_bits(),
        "thirteen additional significand bits"
    );
    for (format, species) in [
        (UncertaintyWordFormat::Binary16, "binary16"),
        (UncertaintyWordFormat::Binary32, "binary32"),
        (UncertaintyWordFormat::Binary64, "binary64"),
    ] {
        assert_eq!(
            format.species().name(),
            species,
            "each admitted wire names its species in the exact owner"
        );
    }

    // A value binary16 cannot carry, carried exactly by binary32. `1 + 2^-23`.
    let fine = ExactWord::decode(UncertaintyWordFormat::Binary32, 0, 0x3f80_0001)
        .expect("the word is finite");
    assert_eq!(
        fine.value,
        &Rat::from_integer(BigInt::from(1))
            + &Rat::new(BigInt::from(1), BigInt::from(1_i64 << 23)),
        "binary32 carries 1 + 2^-23 exactly"
    );
    let coarsest = decode_binary16_bits(0x3c01).expect("the neighbouring binary16 word is finite");
    assert_eq!(
        coarsest.enclosure(FloatReading::ExactBitPattern).lower,
        &Rat::from_integer(BigInt::from(1)) + &Rat::new(BigInt::from(1), BigInt::from(1_024)),
        "the nearest binary16 value above one is 1 + 2^-10, thirteen octaves coarser"
    );
    assert_eq!(
        decode_binary32_bits(0x3f80_0001).unwrap().ulp_bits(),
        23,
        "the exact owner agrees on the format's last place"
    );
}

#[test]
fn a_non_finite_word_is_refused_by_name() {
    for (format, bits, what) in [
        (UncertaintyWordFormat::Binary16, 0x7c00_u64, "binary16 +infinity"),
        (UncertaintyWordFormat::Binary16, 0xfc00_u64, "binary16 -infinity"),
        (UncertaintyWordFormat::Binary16, 0x7e00_u64, "binary16 NaN"),
        (UncertaintyWordFormat::Binary32, 0x7f80_0000_u64, "binary32 +infinity"),
        (UncertaintyWordFormat::Binary32, 0x7fc0_0000_u64, "binary32 NaN"),
        (UncertaintyWordFormat::Binary64, 0x7ff0_0000_0000_0000_u64, "binary64 +infinity"),
    ] {
        let refusal = ExactWord::decode(format, 17, bits).expect_err("a non-finite word refuses");
        match refusal {
            IntakeRefusal::NonFiniteUncertaintyWord {
                format: named,
                index,
                bits: returned,
                ..
            } => {
                assert_eq!(named, format.descr(), "{what}: the format is named");
                assert_eq!(index, 17, "{what}: the index is named");
                assert_eq!(returned, bits, "{what}: the codeword is named");
            }
            other => panic!("{what} returned {other}"),
        }
    }

    // And the whole array refuses at founding, so a consumer never holds a non-finite cell.
    let words = vec![0x3c00_u64, 0x7c00, 0x3c00, 0x3c00];
    let refusal = UncertaintyArray::found(
        "synthetic",
        UncertaintyWordFormat::Binary16,
        &[2, 2],
        words,
    )
    .expect_err("an array carrying an infinity refuses");
    assert!(matches!(
        refusal,
        IntakeRefusal::NonFiniteUncertaintyWord { index: 1, .. }
    ));
}

#[test]
fn an_unadmitted_word_format_is_refused_with_what_is_admitted() {
    let member = NpyArray::parse("synthetic", &npy_bytes("<i8", &[2, 2], &[0_u8; 32]))
        .expect("the member parses");
    let refusal = member.float_words().expect_err("<i8 is not a float wire");
    match refusal {
        IntakeRefusal::UnadmittedWordFormat { descr, admitted, .. } => {
            assert_eq!(descr, "<i8");
            assert_eq!(admitted, "<f2, <f4, <f8");
        }
        other => panic!("returned {other}"),
    }
}

// ---------------------------------------------------------------------------------------------
// The hostile header. A `.npy` header is attacker-declared text; its `shape` and its `descr` are
// checked against the payload that is present before either may size anything.
// ---------------------------------------------------------------------------------------------

#[test]
fn a_zero_width_unicode_array_may_not_size_a_collection_from_its_declared_count() {
    // `<U0` carries no payload at all, so `data.len()` constrains nothing about the declared
    // element count. Pre-sizing from that count is a multi-terabyte allocation chosen by a header
    // of a few dozen octets — and it is on the advertised path, because `token_chain_ids.npy`,
    // `token_entity.npy` and every scalar of the environment index are read as `<U*`.
    let member = NpyArray::parse(
        "synthetic::token_chain_ids.npy",
        &npy_bytes("<U0", &[999_999_999_999], &[]),
    )
    .expect("the header itself is well formed");
    let refusal = member
        .unicode_words()
        .expect_err("a zero-width array with a declared element count is refused");
    match refusal {
        IntakeRefusal::MalformedNumpyMember { detail, .. } => assert!(
            detail.contains("999999999999") && detail.contains("zero width"),
            "the refusal names the declared count and why it is not honoured: {detail}"
        ),
        other => panic!("returned {other}"),
    }

    // A zero-width **scalar** is the same refusal rather than a fabricated empty string.
    let scalar = NpyArray::parse("synthetic::target_form.npy", &npy_bytes("<U0", &[], &[]))
        .expect("the header itself is well formed");
    assert!(matches!(
        scalar.unicode_scalar(),
        Err(IntakeRefusal::MalformedNumpyMember { .. })
    ));

    // And the same member reached through `EnvironmentIndex::from_numpy_source`, which is the
    // ordinary advertised entry point.
    let members = synthetic_environment_members(6)
        .into_iter()
        .map(|(name, bytes)| {
            if name == "token_chain_ids.npy" {
                (name, npy_bytes("<U0", &[999_999_999_999], &[]))
            } else {
                (name, bytes)
            }
        })
        .collect::<Vec<_>>();
    let refusal = EnvironmentIndex::from_numpy_source(&source_from(&members))
        .expect_err("the environment index refuses the zero-width declaration");
    assert!(matches!(
        refusal,
        IntakeRefusal::MalformedNumpyMember { .. }
    ));
}

#[test]
fn a_declared_shape_that_leaves_the_extent_wire_is_a_typed_refusal() {
    // A plain `shape.iter().product()` panics here under `overflow-checks`, which is Cargo's
    // default for the dev and test profiles, and wraps silently in release — where the wrapped
    // extent can make the length-consistency guard pass and a truncated payload be read as whole.
    let overflowing = NpyArray::parse(
        "synthetic::pae.npy",
        &npy_bytes("<f2", &[usize::MAX, 2], &[0_u8; 8]),
    )
    .expect("the header itself is well formed");
    assert!(
        matches!(
            overflowing.elements(),
            Err(IntakeRefusal::DeclaredExtentOverflows { .. })
        ),
        "the declared element count is refused rather than wrapped"
    );
    assert!(matches!(
        overflowing.float_words(),
        Err(IntakeRefusal::DeclaredExtentOverflows { .. })
    ));

    // The element count fits and the payload extent does not: `elements · octets` is the second
    // unchecked multiplication, and it is checked in every reader.
    for (descr, octets) in [("<f2", 2_usize), ("<f4", 4), ("<f8", 8)] {
        let member = NpyArray::parse(
            "synthetic::pae.npy",
            &npy_bytes(descr, &[usize::MAX], &[0_u8; 8]),
        )
        .expect("the header itself is well formed");
        assert_eq!(member.elements().unwrap(), usize::MAX);
        assert!(
            matches!(
                member.float_words(),
                Err(IntakeRefusal::DeclaredExtentOverflows { .. })
            ),
            "{descr} at {octets} octets per element leaves the extent wire"
        );
    }
    let integers = NpyArray::parse(
        "synthetic::token_res_ids.npy",
        &npy_bytes("<i4", &[usize::MAX], &[0_u8; 8]),
    )
    .expect("the header itself is well formed");
    assert!(matches!(
        integers.i32_words(),
        Err(IntakeRefusal::DeclaredExtentOverflows { .. })
    ));
    let words = NpyArray::parse(
        "synthetic::token_chain_ids.npy",
        &npy_bytes("<U8", &[usize::MAX], &[0_u8; 8]),
    )
    .expect("the header itself is well formed");
    assert!(matches!(
        words.unicode_words(),
        Err(IntakeRefusal::DeclaredExtentOverflows { .. })
    ));

    // A `<U*` width whose octets-per-element overflows is the same refusal.
    let wide = NpyArray::parse(
        "synthetic::token_chain_ids.npy",
        &npy_bytes(&format!("<U{}", usize::MAX), &[1], &[0_u8; 8]),
    )
    .expect("the header itself is well formed");
    assert!(matches!(
        wide.unicode_words(),
        Err(IntakeRefusal::DeclaredExtentOverflows { .. })
    ));

    // And the square uncertainty extent, whose `extent²` is the same class of declaration.
    let refusal = UncertaintyArray::found(
        "synthetic",
        UncertaintyWordFormat::Binary16,
        &[usize::MAX, usize::MAX],
        Vec::new(),
    )
    .expect_err("a square extent that leaves the wire is refused");
    assert!(matches!(
        refusal,
        IntakeRefusal::DeclaredExtentOverflows { .. }
    ));
}

// ---------------------------------------------------------------------------------------------
// The coordinate discipline
// ---------------------------------------------------------------------------------------------

#[test]
fn a_coordinate_token_is_retained_at_its_own_last_place() {
    let token = DecimalToken::parse("4.697824").expect("a plain decimal parses");
    assert_eq!(token.significand, 4_697_824);
    assert_eq!(token.decimal_places, 6);
    assert_eq!(
        token.exact_centre().unwrap(),
        Rat::new(BigInt::from(4_697_824), BigInt::from(1_000_000))
    );
    let enclosure = token.source_enclosure().unwrap();
    assert_eq!(
        enclosure.lower,
        Rat::new(BigInt::from(4_697_823), BigInt::from(1_000_000))
    );
    assert_eq!(
        enclosure.upper,
        Rat::new(BigInt::from(4_697_825), BigInt::from(1_000_000))
    );

    // A token written with more zeros is different testimony and keeps a narrower enclosure. This
    // is exactly what a family-wide decimal count destroys at parse time.
    let coarse = DecimalToken::parse("12.3").unwrap();
    let fine = DecimalToken::parse("12.300").unwrap();
    assert_eq!(coarse.exact_centre().unwrap(), fine.exact_centre().unwrap());
    assert!(
        fine.source_enclosure().unwrap().lower > coarse.source_enclosure().unwrap().lower,
        "three declared places enclose more tightly than one"
    );
}

#[test]
fn the_resident_projection_is_outward_and_therefore_contains_the_source() {
    for raw in ["0.0", "1.5", "-1.5", "19.046", "4.697824", "-58.90272", "123.45678901"] {
        let token = DecimalToken::parse(raw).expect("a plain decimal parses");
        let source = token.source_enclosure().unwrap();
        for places in 0..=11_u32 {
            let projected = token.projected_enclosure(places).unwrap();
            assert!(
                projected.lower <= source.lower && source.upper <= projected.upper,
                "{raw} at 10^-{places}: the projection contains the source enclosure"
            );
            assert!(
                projected.lower <= projected.upper,
                "{raw} at 10^-{places}: the projection is ordered"
            );
        }
        // Projection onto at least the token's own precision is exact multiplication: no widening.
        let exact = token.projected_enclosure(token.decimal_places).unwrap();
        assert_eq!(exact, source, "{raw}: the token's own grid is the source grid");
    }
}

#[test]
fn a_malformed_coordinate_is_a_typed_refusal_and_never_a_panic() {
    for raw in ["", ".", "1.2.3", "1e5", "abc", "-", "1 2", "0x10", "１２３"] {
        let refusal = DecimalToken::parse(raw).expect_err("{raw} is not a plain decimal");
        assert!(
            matches!(refusal, IntakeRefusal::CoordinateNotAPlainDecimal { .. }),
            "{raw:?} returned {refusal}"
        );
    }
    let overflow = DecimalToken::parse("1.00000000000000000000000000")
        .expect_err("a twenty-six place token leaves the exact i64 wire");
    assert!(matches!(
        overflow,
        IntakeRefusal::CoordinateLeavesTheExactWire { .. }
    ));

    // A doubly signed token is refused rather than read with the sign of its first character.
    // Trimming the whole run of signs admitted `"+-4.5"` as `+4.5` and `"--4.5"` as `-4.5`, both
    // of which are coordinates the source never wrote.
    for raw in ["+-4.5", "--4.5", "-+4.5", "++4.5", "-.5-", "+"] {
        let refusal = DecimalToken::parse(raw).expect_err("a malformed sign sequence is refused");
        assert!(
            matches!(refusal, IntakeRefusal::CoordinateNotAPlainDecimal { .. }),
            "{raw:?} returned {refusal}"
        );
    }
    // One leading sign remains a plain decimal, in both directions.
    assert_eq!(DecimalToken::parse("+4.5").unwrap().significand, 45);
    assert_eq!(DecimalToken::parse("-4.5").unwrap().significand, -45);
}

// ---------------------------------------------------------------------------------------------
// All-atom mmCIF
// ---------------------------------------------------------------------------------------------

/// Two chains of three residues, each residue carrying `N`, `CA`, `C` and a long `SC` atom.
///
/// The `SC` atoms of the two chains sit one angstrom apart while the alpha carbons sit eleven
/// apart, so the atom grain sees contacts the alpha-carbon selection cannot — which is the whole
/// point of all-atom retention, exhibited without any fixture.
fn synthetic_cif() -> String {
    let mut text = String::from(
        "data_synthetic\n#\nloop_\n_atom_site.group_PDB\n_atom_site.id\n_atom_site.type_symbol\n\
         _atom_site.label_atom_id\n_atom_site.label_alt_id\n_atom_site.label_comp_id\n\
         _atom_site.label_asym_id\n_atom_site.label_entity_id\n_atom_site.label_seq_id\n\
         _atom_site.Cartn_x\n_atom_site.Cartn_y\n_atom_site.Cartn_z\n",
    );
    let mut id = 1;
    for (chain, entity) in [("A", "1"), ("B", "2")] {
        for residue in 1..=3_i32 {
            let x = 10.0 * f64_free(residue);
            let y = if chain == "A" {
                0.0
            } else if residue < 3 {
                11.0
            } else {
                6.0
            };
            let side = if chain == "A" { y + 5.0 } else { y - 5.0 };
            for (label, element, ax, ay) in [
                ("N", "N", x - 1.5, y),
                ("CA", "C", x, y),
                ("C", "C", x + 1.5, y),
                ("SC", "C", x, side),
            ] {
                text.push_str(&format!(
                    "ATOM {id} {element} {label} . GLY {chain} {entity} {residue} {} {} 0.000\n",
                    decimal3(ax),
                    decimal3(ay)
                ));
                id += 1;
            }
        }
    }
    text.push_str("#\n");
    text
}

/// A whole-number ordinal as a coordinate multiplier. No coordinate is ever parsed from a float;
/// this only lays out the synthetic fixture's text.
fn f64_free(residue: i32) -> f64 {
    f64::from(residue)
}

fn decimal3(value: f64) -> String {
    format!("{value:.3}")
}

#[test]
fn the_all_atom_intake_retains_every_atom_site_row() {
    let presentation =
        StructurePresentation::parse("synthetic", &synthetic_cif()).expect("the presentation reads");
    assert_eq!(presentation.atom_occurrences, 24, "two chains of three residues of four atoms");
    assert_eq!(
        presentation.atom_occurrences, presentation.presented_rows,
        "every presented row is retained"
    );
    assert_eq!(presentation.maximum_decimal_places, 3);
    assert_eq!(presentation.chains.len(), 2);
    let chain = presentation.chain("A").expect("chain A is present");
    assert_eq!(chain.residues.len(), 3);
    assert_eq!(chain.atom_occurrences, 12);
    assert_eq!(chain.entity.as_deref(), Some("1"));
    assert_eq!(chain.source_ordinals(), vec![1, 2, 3]);
    assert_eq!(
        chain.residues[0]
            .atoms
            .iter()
            .map(|atom| atom.label.as_str())
            .collect::<Vec<_>>(),
        vec!["N", "CA", "C", "SC"],
        "atoms are retained in the presentation's own order"
    );
    assert_eq!(
        chain.residues[0].labelled_atom("CA").unwrap(),
        Some(1),
        "the representative is located, not filtered for"
    );
    assert_eq!(chain.residues[0].labelled_atom("ZZ").unwrap(), None);

    // Each atom's source box is its own tokens' last places, and the resident projection contains
    // it on every declared denominator.
    let atom = &chain.residues[0].atoms[0];
    let source = atom.source_box().unwrap();
    for places in [0_u32, 3, 7, 11] {
        let projected = atom.projected_box(places).unwrap();
        for (projected_axis, source_axis) in [
            (&projected.x, &source.x),
            (&projected.y, &source.y),
            (&projected.z, &source.z),
        ] {
            assert!(
                projected_axis.lower <= source_axis.lower
                    && source_axis.upper <= projected_axis.upper,
                "the resident projection at 10^-{places} contains the atom's source box"
            );
        }
    }
    assert_eq!(atom.decimal_places(), 3);
    assert_eq!(atom.element.as_deref(), Some("N"));

    // Addressing a chain by residue count is refused unless it is unique.
    assert!(presentation.chain_with_residue_count(3).is_err());
    assert!(matches!(
        presentation.chain("Z"),
        Err(IntakeRefusal::ChainAbsent { .. })
    ));
}

#[test]
fn a_malformed_structure_is_a_typed_refusal_and_never_a_panic() {
    let cases: [(&str, &str); 4] = [
        ("data_x\n#\n", "no atom_site loop"),
        (
            "data_x\nloop_\n_atom_site.label_atom_id\n_atom_site.Cartn_x\nCA\n#\n",
            "a row with too few fields",
        ),
        (
            "data_x\nloop_\n_atom_site.label_atom_id\n_atom_site.label_comp_id\n\
             _atom_site.label_asym_id\n_atom_site.label_seq_id\n_atom_site.Cartn_x\n\
             _atom_site.Cartn_y\nCA GLY A 1 1.0 2.0\n#\n",
            "no Cartn_z column",
        ),
        (
            "data_x\nloop_\n_atom_site.label_atom_id\n_atom_site.label_comp_id\n\
             _atom_site.label_asym_id\n_atom_site.label_seq_id\n_atom_site.Cartn_x\n\
             _atom_site.Cartn_y\n_atom_site.Cartn_z\nCA GLY A one 1.0 2.0 3.0\n#\n",
            "a non-integer label_seq_id",
        ),
    ];
    for (text, what) in cases {
        let refusal = StructurePresentation::parse("synthetic", text)
            .expect_err("a malformed structure refuses");
        assert!(
            matches!(
                refusal,
                IntakeRefusal::MalformedStructure { .. } | IntakeRefusal::StructureColumnAbsent { .. }
            ),
            "{what} returned {refusal}"
        );
    }
}

// ---------------------------------------------------------------------------------------------
// The environment index
// ---------------------------------------------------------------------------------------------

fn synthetic_environment_members(extent: usize) -> Vec<(&'static str, Vec<u8>)> {
    let chains = (0..extent)
        .map(|at| if at < extent / 2 { "A" } else { "B" })
        .collect::<Vec<_>>();
    let residues = (0..extent)
        .map(|at| (at % (extent / 2)) as i32 + 1)
        .collect::<Vec<_>>();
    vec![
        (
            "pae.npy",
            binary16_square_npy(extent, |row, column| 0x3000 + (row * extent + column) as u16),
        ),
        ("token_chain_ids.npy", unicode_vector_npy(&chains)),
        ("token_res_ids.npy", i32_vector_npy(&residues)),
        (
            "token_entity.npy",
            unicode_vector_npy(&vec!["protein"; extent]),
        ),
        ("design_uuid.npy", unicode_scalar_npy("synthetic-uuid")),
        ("design_name.npy", unicode_scalar_npy("synthetic-design")),
        ("target.npy", unicode_scalar_npy("TGT")),
        ("cofolding_model.npy", unicode_scalar_npy("synth")),
        ("stoichiometry.npy", unicode_scalar_npy("1to1")),
        ("target_form.npy", unicode_scalar_npy("free")),
        ("seed.npy", unicode_scalar_npy("11")),
    ]
}

#[test]
fn an_occurrence_cannot_be_founded_without_its_environment() {
    // A predictor that emits only the uncertainty array. This is the Boltz-2 shape.
    let bare = source_from(&[(
        "pae.npy",
        binary16_square_npy(6, |row, column| 0x3000 + (row * 6 + column) as u16),
    )]);
    let refusal = EnvironmentIndex::from_numpy_source(&bare)
        .expect_err("an array with no environment founds no index");
    match refusal {
        IntakeRefusal::EnvironmentArraysAbsent { absent, present, .. } => {
            assert_eq!(absent.len(), 10, "every environment array is named at once");
            assert!(absent.contains(&"token_chain_ids.npy".to_owned()));
            assert!(absent.contains(&"design_uuid.npy".to_owned()));
            assert!(absent.contains(&"target_form.npy".to_owned()));
            assert!(!absent.contains(&"pae.npy".to_owned()), "the array itself is present");
            assert_eq!(present, vec!["pae.npy".to_owned()]);
        }
        other => panic!("returned {other}"),
    }

    // A declared index admits the same array, and the declaration travels with it.
    let array = UncertaintyArray::from_numpy_source(&bare).expect("the array reads");
    let declared = EnvironmentIndex::declared(
        "declared by the intake test for a predictor that emits only pae",
        TargetEcology {
            target: "TGT".to_owned(),
            target_form: "free".to_owned(),
            stoichiometry: "1to1".to_owned(),
            cofolding_model: "synth".to_owned(),
        },
        DesignLineage {
            design_uuid: "synthetic-uuid".to_owned(),
            design_name: "synthetic-design".to_owned(),
            seed: "0".to_owned(),
        },
        (0..6)
            .map(|at| TokenAddress {
                chain: if at < 3 { "A" } else { "B" }.to_owned(),
                residue: at % 3 + 1,
                entity: None,
            })
            .collect(),
    )
    .expect("a declaration with a stated ground is admitted");
    let occurrence =
        AddressedUncertainty::found(declared, array.clone()).expect("the occurrence founds");
    assert!(matches!(
        occurrence.environment().provenance,
        EnvironmentProvenance::DeclaredByCaller { .. }
    ));

    // A declaration with no stated ground is not a declaration.
    assert!(matches!(
        EnvironmentIndex::declared(
            "   ",
            TargetEcology {
                target: String::new(),
                target_form: String::new(),
                stoichiometry: String::new(),
                cofolding_model: String::new(),
            },
            DesignLineage {
                design_uuid: String::new(),
                design_name: String::new(),
                seed: String::new(),
            },
            vec![TokenAddress { chain: "A".to_owned(), residue: 1, entity: None }],
        ),
        Err(IntakeRefusal::EnvironmentDeclarationEmpty)
    ));

    // A token population that does not address the array is refused, not padded.
    let short = EnvironmentIndex::declared(
        "a short declaration",
        TargetEcology {
            target: "TGT".to_owned(),
            target_form: "free".to_owned(),
            stoichiometry: "1to1".to_owned(),
            cofolding_model: "synth".to_owned(),
        },
        DesignLineage {
            design_uuid: "u".to_owned(),
            design_name: "n".to_owned(),
            seed: "0".to_owned(),
        },
        vec![TokenAddress { chain: "A".to_owned(), residue: 1, entity: None }],
    )
    .unwrap();
    assert!(matches!(
        AddressedUncertainty::found(short, array.clone()),
        Err(IntakeRefusal::TokenPopulationDisagrees { extent: 6, tokens: 1, .. })
    ));

    // A repeated address makes the addressing ambiguous and is refused.
    let repeated = EnvironmentIndex::declared(
        "a repeated declaration",
        TargetEcology {
            target: "TGT".to_owned(),
            target_form: "free".to_owned(),
            stoichiometry: "1to1".to_owned(),
            cofolding_model: "synth".to_owned(),
        },
        DesignLineage {
            design_uuid: "u".to_owned(),
            design_name: "n".to_owned(),
            seed: "0".to_owned(),
        },
        vec![TokenAddress { chain: "A".to_owned(), residue: 1, entity: None }; 6],
    )
    .unwrap();
    assert!(matches!(
        AddressedUncertainty::found(repeated, array),
        Err(IntakeRefusal::TokenAddressRepeated { .. })
    ));
}

#[test]
fn a_self_indexed_source_founds_its_own_environment_and_its_addressed_pair_population() {
    let source = source_from(&synthetic_environment_members(6));
    let environment = EnvironmentIndex::from_numpy_source(&source).expect("the index reads");
    assert_eq!(environment.ecology.target, "TGT");
    assert_eq!(environment.ecology.target_form, "free");
    assert_eq!(environment.lineage.seed, "11");
    assert_eq!(environment.tokens.len(), 6);
    assert!(environment.addresses_are_distinct());
    assert!(matches!(
        environment.provenance,
        EnvironmentProvenance::CarriedByArrays { .. }
    ));
    assert!(environment.ecology.blank_coordinates().is_empty());

    let array = UncertaintyArray::from_numpy_source(&source).expect("the array reads");
    assert_eq!(array.extent, 6);
    assert_eq!(array.finite_words, 36);
    let occurrence = AddressedUncertainty::found(environment, array).expect("the occurrence founds");

    // The addressed pair population is exactly `|left| * |right|`, and a reading is directional.
    let uncertainty = occurrence
        .pair_uncertainty("A", &[1, 2, 3], "B", &[1, 2, 3])
        .expect("every addressed pair has a reading");
    assert_eq!(uncertainty.len(), 9, "the addressed pair population");
    let (row, column) = occurrence
        .directional_words("A", 1, "B", 1)
        .expect("both directions are carried");
    assert_ne!(
        row.value, column.value,
        "the row and column readings are separate and are never symmetrized"
    );
    assert_eq!(row.bits, 0x3003, "token A:1 is row 0, token B:1 is column 3");
    assert_eq!(column.bits, 0x3012, "and the reverse cell is row 3, column 0");

    // An unaddressed token is a refusal naming it.
    assert!(matches!(
        occurrence.directional_words("A", 9, "B", 1),
        Err(IntakeRefusal::TokenAbsent { residue: 9, .. })
    ));
}

// ---------------------------------------------------------------------------------------------
// Reaching the existing owners
// ---------------------------------------------------------------------------------------------

#[test]
fn the_intake_reaches_the_constraint_complex_and_its_graded_family() {
    let structure =
        StructurePresentation::parse("synthetic", &synthetic_cif()).expect("the presentation reads");
    let source = source_from(&synthetic_environment_members(6));
    let occurrence = AddressedOccurrence::found(
        structure,
        AddressedUncertainty::found(
            EnvironmentIndex::from_numpy_source(&source).unwrap(),
            UncertaintyArray::from_numpy_source(&source).unwrap(),
        )
        .unwrap(),
    );

    let left = occurrence.structure.chain("A").unwrap().clone();
    let right = occurrence.structure.chain("B").unwrap().clone();
    let aperture = DistanceAperture {
        lineage: "declared contact receiver: exact distance not greater than 8 angstroms".to_owned(),
        squared: Rat::from_integer(BigInt::from(64)),
    };
    let complex = occurrence
        .constraint_complex(
            "synthetic all-atom intake",
            EventId(1),
            &left,
            &right,
            &ContactPresentation {
                grain: ComponentGrain::Representative {
                    atom_label: REPRESENTATIVE.to_owned(),
                },
                resident_decimal_places: RESIDENT_DECIMAL_PLACES,
                aperture: aperture.clone(),
            },
        )
        .expect("the constraint complex founds through the library intake");
    let family = complex
        .contact_family(ConstraintComponentId(1), ConstraintComponentId(2))
        .expect("the family is present");
    assert_eq!(family.readings.len(), 9, "three residues against three");
    assert!(
        family.readings.iter().all(|reading| reading.uncertainty.is_some()),
        "every addressed pair carries its directional uncertainty"
    );
    assert_eq!(
        family
            .readings
            .iter()
            .filter(|reading| reading.class == ContactClass::Inside)
            .count(),
        1,
        "the alpha-carbon selection admits exactly the third residue pair"
    );

    // The same intake at the atom grain sees contacts the selection cannot.
    let atom_complex = occurrence
        .constraint_complex(
            "synthetic all-atom intake",
            EventId(2),
            &left,
            &right,
            &ContactPresentation {
                grain: ComponentGrain::Atom,
                resident_decimal_places: RESIDENT_DECIMAL_PLACES,
                aperture,
            },
        )
        .expect("the atom-grain complex founds");
    let atom_family = atom_complex
        .contact_family(ConstraintComponentId(1), ConstraintComponentId(2))
        .expect("the atom family is present");
    assert_eq!(atom_family.readings.len(), 144, "twelve atoms against twelve");
    let atom_inside = atom_family
        .readings
        .iter()
        .filter(|reading| reading.class == ContactClass::Inside)
        .count();
    assert!(
        atom_inside > 1,
        "the atom grain admits more than the alpha-carbon selection: {atom_inside}"
    );

    // And the open class reaches the graded family with no further adapter.
    let graded = graded_family(&atom_complex).expect("the apertured graded family founds");
    assert_eq!(
        graded.cardinality(),
        BigUint::from(1_u8) << graded.open_contacts.len(),
        "the family has 2^n members"
    );
    assert!(
        graded.refusing.complex.validate().is_ok() && graded.admitting.complex.validate().is_ok(),
        "both bounding members satisfy the boundary law"
    );
    assert_eq!(
        graded.refusing.f_vector().get(&0).copied(),
        Some(24),
        "every retained atom is a zero-cell"
    );
}

#[test]
fn the_grain_census_identities_hold_on_a_synthetic_all_atom_intake() {
    let structure =
        StructurePresentation::parse("synthetic", &synthetic_cif()).expect("the presentation reads");
    let aperture = contact_aperture(CONTACT_RADIUS, RESIDENT_DECIMAL_PLACES).unwrap();
    let left = scaled_component_wire(
        structure.chain("A").unwrap(),
        "synthetic chain A",
        1,
        RESIDENT_DECIMAL_PLACES,
        REPRESENTATIVE,
    )
    .expect("chain A scales");
    let right = scaled_component_wire(
        structure.chain("B").unwrap(),
        "synthetic chain B",
        2,
        RESIDENT_DECIMAL_PLACES,
        REPRESENTATIVE,
    )
    .expect("chain B scales");
    assert_eq!(left.atoms.len(), 12, "every atom reaches the grain wire");
    assert_eq!(left.representatives.len(), 3);

    let returned = enact_grain_family("synthetic A x B", &left, &right, &aperture, SELECTION_LINEAGE)
        .expect("the family enacts");
    let census = &returned.census;
    assert_eq!(
        [
            census.pairs,
            census.fine_inside,
            census.fine_open,
            census.coarse_inside,
            census.coarse_open,
            census.fine_only_inside,
            census.coarse_only_inside,
            census.open_shared,
        ],
        [9, 3, 0, 1, 0, 2, 0, 0],
        "pairs / fine inside / fine open / coarse inside / coarse open / fine-only / coarse-only \
         / open-shared"
    );
    assert_eq!(census.coarse_only_inside, 0, "coarse implies fine, checked not assumed");
    assert_eq!(
        census.fine_inside - census.coarse_inside,
        census.fine_only_inside,
        "with no coarse-only pair the fine-only count is forced"
    );
    assert_eq!(returned.reopen.source_reopened, 1, "reopen_apply");
    assert!(
        returned.inflation.certified_bound_squared >= returned.inflation.coarse_aperture_squared,
        "the grain-radius certificate bounds the measured requirement"
    );
    returned
        .inflation
        .check_declared(&Rat::from_integer(BigInt::from(64)))
        .expect_err("the equal 8 angstrom coarse aperture does not carry the fine contacts");
    assert_eq!(
        returned.tower.relation().name(),
        "inflated-coarse",
        "the measured inflation travels with the tower"
    );
    assert_eq!(returned.tower.atom_face().grain(), Grain::Atom);

    let totals = GrainCensusTotals::over(std::slice::from_ref(&returned)).unwrap();
    assert_eq!(totals.pairs, 9);
    assert_eq!(totals.fine_only_inside, 2);
    assert!(matches!(
        GrainCensusTotals::over(&[]),
        Err(IntakeRefusal::EmptyFamilyPopulation)
    ));
}

// ---------------------------------------------------------------------------------------------
// The measured M5 fixture
// ---------------------------------------------------------------------------------------------

#[test]
fn the_m5_pair_table_reproduces_through_the_library_intake() {
    let root = structure_root();
    assert!(
        root.is_dir(),
        "the authenticated M5 structure root {} is absent, so the measured pair table cannot be \
         checked through the library intake, and this test refuses to report success without \
         checking it. Place the authenticated release at that path, or set \
         {STRUCTURE_ROOT_ENV} to the directory carrying designed-free-rbx1.cif, \
         ptxv2-free-rbx1-seed2.cif and ptxv2-cul1-rbx1-seed0.cif. The intake laws and the \
         pair-table identities themselves are checked without any fixture by \
         the_grain_census_identities_hold_on_a_synthetic_all_atom_intake.",
        root.display()
    );

    let read = |name: &str| {
        StructurePresentation::read(&root.join(name))
            .unwrap_or_else(|error| panic!("{name}: {error}"))
    };
    let designed = read("designed-free-rbx1.cif");
    let free = read("ptxv2-free-rbx1-seed2.cif");
    let complex = read("ptxv2-cul1-rbx1-seed0.cif");
    assert_eq!(designed.atom_occurrences, 1_333, "every designed atom is retained");
    assert_eq!(free.atom_occurrences, 1_667, "every free-prediction atom is retained");
    assert_eq!(complex.atom_occurrences, 4_648, "every complex atom is retained");

    let aperture = contact_aperture(CONTACT_RADIUS, RESIDENT_DECIMAL_PLACES).unwrap();
    // Components are bound by residue count exactly as the M5 deed binds them by ordered sequence:
    // the binder carries 96 residues, RBX1 carries 108 and CUL1 carries 366. The single-residue
    // chains are the zinc occurrences, which carry no alpha carbon and are not protein components.
    let wire = |presentation: &StructurePresentation, residues: usize, component: u32| {
        let chain = presentation
            .chain_with_residue_count(residues)
            .unwrap_or_else(|error| panic!("{error}"));
        scaled_component_wire(
            chain,
            format!("{} / chain {}", presentation.source_lineage, chain.label_asym_id),
            component,
            RESIDENT_DECIMAL_PLACES,
            REPRESENTATIVE,
        )
        .unwrap_or_else(|error| panic!("{error}"))
    };

    let families: [(&str, ScaledComponentWire, ScaledComponentWire, [usize; 8]); 4] = [
        (
            "designed free RBX1 / binder x RBX1",
            wire(&designed, 96, 1),
            wire(&designed, 108, 2),
            [10_368, 303, 1, 64, 1, 239, 0, 0],
        ),
        (
            "Protenix free seed 2 / binder x RBX1",
            wire(&free, 96, 1),
            wire(&free, 108, 2),
            [10_368, 366, 0, 59, 0, 307, 0, 0],
        ),
        (
            "Protenix CUL1-RBX1 seed 0 / binder x RBX1",
            wire(&complex, 96, 1),
            wire(&complex, 108, 2),
            [10_368, 260, 0, 45, 0, 215, 0, 0],
        ),
        (
            "Protenix CUL1-RBX1 seed 0 / CUL1 x RBX1",
            wire(&complex, 366, 1),
            wire(&complex, 108, 2),
            [39_528, 468, 0, 133, 0, 335, 0, 0],
        ),
    ];

    let mut returns = Vec::new();
    for (lineage, left, right, expected) in &families {
        let returned = enact_grain_family(*lineage, left, right, &aperture, SELECTION_LINEAGE)
            .unwrap_or_else(|error| panic!("{lineage}: {error}"));
        let census = &returned.census;
        let measured = [
            census.pairs,
            census.fine_inside,
            census.fine_open,
            census.coarse_inside,
            census.coarse_open,
            census.fine_only_inside,
            census.coarse_only_inside,
            census.open_shared,
        ];
        assert_eq!(
            measured, *expected,
            "{lineage}: pairs / fine inside / fine open / coarse inside / coarse open / fine-only \
             / coarse-only / open-shared"
        );
        assert_eq!(
            census.coarse_only_inside, 0,
            "{lineage}: coarse implies fine is a theorem, checked not assumed"
        );
        assert_eq!(
            census.fine_inside - census.coarse_inside,
            census.fine_only_inside,
            "{lineage}: with no coarse-only pair the fine-only count is forced"
        );
        assert_eq!(returned.reopen.source_reopened, 1, "{lineage}: reopen_apply");
        assert!(
            returned.inflation.certified_bound_squared >= returned.inflation.coarse_aperture_squared,
            "{lineage}: the grain-radius certificate bounds the measured requirement"
        );
        returned
            .inflation
            .check_declared(&Rat::from_integer(BigInt::from(64)))
            .expect_err(&format!(
                "{lineage}: the equal 8 angstrom coarse aperture does not carry the fine contacts"
            ));
        eprintln!(
            "physical_intake fixture | {lineage} | pairs {} | fine inside {} | coarse inside {} | \
             fine-only {} | coarse-only {} | open fine/coarse/shared {}/{}/{}",
            census.pairs,
            census.fine_inside,
            census.coarse_inside,
            census.fine_only_inside,
            census.coarse_only_inside,
            census.fine_open,
            census.coarse_open,
            census.open_shared,
        );
        returns.push(returned);
    }

    let totals = GrainCensusTotals::over(&returns).expect("four families are a population");
    assert_eq!(
        [
            totals.pairs,
            totals.fine_inside,
            totals.fine_open,
            totals.coarse_inside,
            totals.coarse_open,
            totals.fine_only_inside,
            totals.coarse_only_inside,
            totals.open_shared,
        ],
        [70_632, 1_397, 1, 301, 1, 1_096, 0, 0],
        "the complete M5 pair table, reproduced through the library intake"
    );
    // 116656202097359145 / 10^14 exactly: CUL1 residue 366 against RBX1 residue 60, forced by a
    // carbonyl oxygen 27.6 angstroms from its own alpha carbon.
    assert_eq!(
        totals.required_coarse_aperture_squared,
        Rat::new(
            BigInt::from(116_656_202_097_359_145_i128),
            BigInt::from(100_000_000_000_000_i128)
        ),
        "the least coarse aperture squared that carries every fine contact, attained at {}",
        totals.required_lineage
    );
    let root_bound = rational_root_upper_bound(
        &totals.required_coarse_aperture_squared,
        &BigUint::from(10_000_u32),
    )
    .expect("the required aperture has a rational root bound");
    assert_eq!(
        root_bound,
        Rat::new(BigInt::from(341_550_i64), BigInt::from(10_000_i64)),
        "34.1550 angstroms, 4.2694 times the 8 angstrom fine aperture"
    );
}

#[test]
fn the_m5_uncertainty_occurrence_founds_its_environment_and_reaches_the_constraint_complex() {
    let root = structure_root();
    assert!(
        root.is_dir(),
        "the authenticated M5 structure root {} is absent, so the environment-indexed intake \
         cannot be checked, and this test refuses to report success without checking it. Set \
         {STRUCTURE_ROOT_ENV} to the directory carrying ptxv2-free-rbx1-seed2.cif, \
         ptxv2-free-rbx1-seed2-pae.npz, ptxv2-cul1-rbx1-seed0.cif and \
         ptxv2-cul1-rbx1-seed0-pae.npz. The environment law itself is checked without any fixture \
         by an_occurrence_cannot_be_founded_without_its_environment.",
        root.display()
    );

    let free = AddressedUncertainty::read_self_indexed(&root.join("ptxv2-free-rbx1-seed2-pae.npz"))
        .expect("the free npz carries its own environment");
    assert_eq!(free.array().extent, 207);
    assert_eq!(free.array().format, UncertaintyWordFormat::Binary16);
    assert_eq!(free.array().finite_words, 207 * 207);
    assert_eq!(free.environment().tokens.len(), 207);
    assert_eq!(free.environment().ecology.target, "RBX1");
    assert_eq!(free.environment().ecology.cofolding_model, "ptxv2");
    assert_eq!(free.environment().ecology.stoichiometry, "1to1");
    assert_eq!(free.environment().lineage.seed, "2");
    assert_eq!(
        free.environment().lineage.design_uuid,
        "c29097fd-ea46-5842-8b8f-b38ad7e732ae"
    );
    // The released free-form wire leaves `target_form` blank. A blank is presented testimony and is
    // retained as such; it is named rather than defaulted.
    assert_eq!(
        free.environment().ecology.blank_coordinates(),
        vec!["target_form"],
        "a blank declared coordinate is named, never filled in"
    );

    let complex_pae =
        AddressedUncertainty::read_self_indexed(&root.join("ptxv2-cul1-rbx1-seed0-pae.npz"))
            .expect("the complex npz carries its own environment");
    assert_eq!(complex_pae.array().extent, 573);
    assert_eq!(complex_pae.environment().ecology.stoichiometry, "1to2");
    assert_eq!(complex_pae.environment().ecology.target_form, "rbx1_cul1_zn");
    assert_eq!(complex_pae.environment().lineage.seed, "0");
    assert!(complex_pae.environment().addresses_are_distinct());

    // The whole occurrence: structure, environment and uncertainty, reaching the exact complex.
    let structure = StructurePresentation::read(&root.join("ptxv2-free-rbx1-seed2.cif"))
        .expect("the free structure reads");
    let occurrence = AddressedOccurrence::found(structure, free);
    let binder = occurrence.structure.chain("B").unwrap().clone();
    let target = occurrence.structure.chain("A").unwrap().clone();
    assert_eq!(binder.residues.len(), 96);
    assert_eq!(target.residues.len(), 108);

    let complex = occurrence
        .constraint_complex(
            "Protenix free seed 2 / binder x RBX1, through the library intake",
            EventId(1),
            &binder,
            &target,
            &ContactPresentation {
                grain: ComponentGrain::Representative {
                    atom_label: REPRESENTATIVE.to_owned(),
                },
                resident_decimal_places: RESIDENT_DECIMAL_PLACES,
                aperture: DistanceAperture {
                    lineage:
                        "declared contact receiver: exact distance not greater than 8 angstroms"
                            .to_owned(),
                    squared: Rat::from_integer(BigInt::from(64)),
                },
            },
        )
        .expect("the constraint complex founds from the environment-indexed occurrence");
    let family = complex
        .contact_family(ConstraintComponentId(1), ConstraintComponentId(2))
        .expect("the family is present");
    assert_eq!(family.readings.len(), 10_368, "96 residues against 108");
    assert!(
        family.readings.iter().all(|reading| reading.uncertainty.is_some()),
        "every addressed pair carries its directional uncertainty"
    );
    let inside = family
        .readings
        .iter()
        .filter(|reading| reading.class == ContactClass::Inside)
        .count();
    assert_eq!(
        inside, 59,
        "the alpha-carbon selection's contact count, which the grain census also measures"
    );
    // And the whole reading population reaches the apertured graded family.
    let graded = graded_family(&complex).expect("the graded family founds");
    assert_eq!(
        graded.cardinality(),
        BigUint::from(1_u8) << graded.open_contacts.len()
    );
    assert!(graded.refusing.complex.validate().is_ok());

    // A directional reading is retained in both directions.
    let (row, column) = occurrence
        .uncertainty
        .directional_words("B", 1, "A", 1)
        .expect("both directions are carried");
    assert!(row.value >= Rat::from_integer(BigInt::from(0)));
    assert!(column.value >= Rat::from_integer(BigInt::from(0)));
    assert_eq!(row.format, UncertaintyWordFormat::Binary16);
}

#[test]
fn the_boltz_npz_is_refused_without_an_environment_and_admitted_with_one() {
    let root = boltz_root();
    assert!(
        root.is_dir(),
        "the Boltz-2 prediction root {} is absent, so the external-predictor intake path cannot \
         be checked, and this test refuses to report success without checking it. Set \
         {BOLTZ_ROOT_ENV} to the directory carrying pae_test_model_0.npz and test_model_0.cif. \
         The environment law itself is checked without any fixture by \
         an_occurrence_cannot_be_founded_without_its_environment.",
        root.display()
    );

    let source = NumpySource::read(&root.join("pae_test_model_0.npz"))
        .expect("the Boltz npz container reads");
    assert_eq!(
        source.member_names(),
        vec!["pae.npy".to_owned()],
        "an external predictor emits only the uncertainty array"
    );
    let array = UncertaintyArray::from_numpy_source(&source).expect("the array reads");
    assert_eq!(array.format, UncertaintyWordFormat::Binary32, "Boltz-2 writes <f4");
    assert_eq!(array.extent, 330);
    assert_eq!(array.finite_words, 330 * 330);

    // Without an environment index there is no index to found, and the refusal names what is
    // missing rather than defaulting anything.
    let refusal = EnvironmentIndex::from_numpy_source(&source)
        .expect_err("the Boltz npz founds no environment index");
    match refusal {
        IntakeRefusal::EnvironmentArraysAbsent { absent, .. } => {
            assert_eq!(absent.len(), 10);
            assert!(absent.contains(&"token_chain_ids.npy".to_owned()));
            assert!(absent.contains(&"cofolding_model.npy".to_owned()));
        }
        other => panic!("returned {other}"),
    }

    // With one declared, the same array is admitted. The token population comes from the
    // prediction's own structure, which is what makes the declaration checkable.
    let structure = StructurePresentation::read(&root.join("test_model_0.cif"))
        .expect("the Boltz structure reads");
    assert_eq!(structure.chains.len(), 1);
    let chain = structure.chain_with_residue_count(330).expect("one chain of 330 residues");
    let tokens = chain
        .residues
        .iter()
        .map(|residue| TokenAddress {
            chain: chain.label_asym_id.clone(),
            residue: residue.source_ordinal,
            entity: chain.entity.clone(),
        })
        .collect::<Vec<_>>();
    let environment = EnvironmentIndex::declared(
        "declared for a Boltz-2 run that emits only pae: the token population is the prediction's \
         own mmCIF chain, and the ecology is the caller's declaration about the run",
        TargetEcology {
            target: "boltz-smoke".to_owned(),
            target_form: "free".to_owned(),
            stoichiometry: "1to0".to_owned(),
            cofolding_model: "boltz2".to_owned(),
        },
        DesignLineage {
            design_uuid: "boltz-smoke-test".to_owned(),
            design_name: "test_model_0".to_owned(),
            seed: "0".to_owned(),
        },
        tokens,
    )
    .expect("a declaration with a stated ground is admitted");
    let occurrence = AddressedUncertainty::found(environment, array)
        .expect("the Boltz occurrence founds once an environment is supplied");
    assert!(matches!(
        occurrence.environment().provenance,
        EnvironmentProvenance::DeclaredByCaller { .. }
    ));
    let (row, column) = occurrence
        .directional_words(&chain.label_asym_id, 1, &chain.label_asym_id, 2)
        .expect("both directions are carried");
    assert_eq!(row.format, UncertaintyWordFormat::Binary32);
    for word in [&row, &column] {
        assert!(
            word.value >= Rat::from_integer(BigInt::from(0)),
            "a predicted alignment error is non-negative"
        );
        assert!(word.unit_in_last_place > Rat::from_integer(BigInt::from(0)));
        let quotient = &word.value / &word.unit_in_last_place;
        assert!(
            quotient.is_integer(),
            "the exact value is an integer multiple of the format's own last place, which is what \
             makes the decoding exact rather than a rounding"
        );
    }

    // The same structure reaches the grain tower, all atoms retained.
    let scaled = scaled_component_wire(
        chain,
        "Boltz-2 smoke / chain A",
        1,
        RESIDENT_DECIMAL_PLACES,
        REPRESENTATIVE,
    )
    .expect("the Boltz chain scales");
    assert_eq!(scaled.atoms.len(), structure.atom_occurrences);
    assert_eq!(scaled.representatives.len(), 330);
}

/// A guard on the whole file: the intake's own modules contain no floating-point type, so no float
/// can parse, store or decide a coordinate on this path. The one lawful float appearance is an
/// exterior IEEE codeword, which is an **integer** here until `exact_value::ieee754` turns it into
/// an exact dyadic.
#[test]
fn no_float_participates_in_the_intake() {
    for (name, source) in [
        ("physical_intake.rs", include_str!("../physical_intake.rs")),
        ("physical_intake/mmcif.rs", include_str!("mmcif.rs")),
        ("physical_intake/numpy.rs", include_str!("numpy.rs")),
        ("physical_intake/deflate.rs", include_str!("deflate.rs")),
    ] {
        for forbidden in ["f32", "f64", "to_bits", "from_bits"] {
            let body = source
                .lines()
                .filter(|line| !line.trim_start().starts_with("//"))
                .collect::<Vec<_>>()
                .join("\n");
            assert!(
                !body.contains(forbidden),
                "{name} mentions {forbidden} outside its documentation"
            );
        }
    }
}

/// A map from each Lean declaration of `Foundation/ExteriorIntake.lean` to the Rust owner that
/// enacts it, checked to be the map the module header publishes. This is the bidirectional
/// citation, kept from drifting by a test rather than by a promise.
#[test]
fn the_module_header_publishes_the_bidirectional_correspondence() {
    let header = include_str!("../physical_intake.rs");
    let expected: BTreeMap<&str, &str> = BTreeMap::from([
        ("FloatFormat", "UncertaintyWordFormat"),
        ("decode_total_on_finite", "ExactWord::decode"),
        ("decode_exact_on_finite", "ExactWord::value"),
        ("decode_refuses_nonfinite", "NonFiniteUncertaintyWord"),
        ("wider_format_carries_every_value", "<f4"),
        ("projectOutward", "projected_wire"),
        ("widening_never_flips_a_decision", "mmcif"),
        ("EnvironmentIndex", "EnvironmentIndex"),
        ("found_none_of_environment_absent", "AddressedUncertainty::found"),
        ("addressed_pair_population", "pair_uncertainty"),
        ("reading_is_directional", "column_given_row"),
    ]);
    // The Lean owner itself, so a cited declaration name is checked to exist rather than trusted.
    let owner = include_str!(
        "../../../../formal/elementary-holonics/ElementaryHolonics/Foundation/ExteriorIntake.lean"
    );
    for (lean, rust) in expected {
        assert!(
            owner.contains(lean),
            "Foundation/ExteriorIntake.lean declares no {lean}, so the header cites a name that              does not exist"
        );
        let row = header
            .lines()
            .find(|line| line.starts_with("//! |") && line.contains(lean))
            .unwrap_or_else(|| panic!("the header names no Lean declaration {lean}"));
        assert!(
            row.contains(rust),
            "the header row for {lean} does not name its Rust owner {rust}: {row}"
        );
    }
    // Every other Lean name the header's correspondence table cites also exists in that owner.
    for row in header.lines().filter(|line| line.starts_with("//! | `")) {
        let lean_cell = row.split('|').nth(1).unwrap_or_default();
        for name in lean_cell.split('`').skip(1).step_by(2) {
            let name = name.trim();
            let leaf = name.rsplit('.').next().unwrap_or(name);
            if leaf.is_empty() || !leaf.chars().next().is_some_and(|c| c.is_ascii_alphabetic()) {
                continue;
            }
            if leaf.contains(' ') || leaf.contains('≤') {
                continue;
            }
            assert!(
                owner.contains(leaf),
                "the header cites Lean declaration {name}, which Foundation/ExteriorIntake.lean                  does not declare"
            );
        }
    }
}

/// **The optional numeric columns of a row are retained, and the format's absent cell is no
/// value.** Intake retained every row and dropped `occupancy` and `B_iso_or_equiv`; a row now
/// carries both where the presentation does, `.` and `?` read as absent, and a malformed cell is
/// refused rather than read as absent.
#[test]
fn occupancy_and_temperature_factor_are_retained_and_an_absent_cell_is_no_value() {
    let head = "data_columns\nloop_\n_atom_site.group_PDB\n_atom_site.label_atom_id\n\
                _atom_site.label_comp_id\n_atom_site.label_asym_id\n_atom_site.label_seq_id\n\
                _atom_site.Cartn_x\n_atom_site.Cartn_y\n_atom_site.Cartn_z\n\
                _atom_site.occupancy\n_atom_site.B_iso_or_equiv\n";
    let text = format!(
        "{head}ATOM N GLY A 1 1.0 2.0 3.0 1.00 35.25\nATOM CA GLY A 1 2.0 2.0 3.0 . ?\n#\n"
    );
    let presentation = StructurePresentation::parse("columns", &text).expect("reads");
    let atoms = &presentation.chains[0].residues[0].atoms;
    assert_eq!(
        atoms[0].occupancy,
        Some(DecimalToken::parse("1.00").expect("token"))
    );
    assert_eq!(
        atoms[0].temperature_factor,
        Some(DecimalToken::parse("35.25").expect("token"))
    );
    assert_eq!((&atoms[1].occupancy, &atoms[1].temperature_factor), (&None, &None));

    let malformed = format!("{head}ATOM N GLY A 1 1.0 2.0 3.0 full 35.25\n#\n");
    assert!(StructurePresentation::parse("columns", &malformed).is_err());
}
