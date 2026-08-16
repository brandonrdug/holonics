//! THE RESERVATION DECIDES WHETHER THE CARD MOUNTS — the orbit of one authored level.
//!
//! `soma/life/src/text_material_cuda.rs:20` carries
//!
//! ```text
//!   const RESIDENT_LOGICAL_WORD_RESERVATION: usize = u32::MAX as usize;
//! ```
//!
//! and `resident_buffer` is called **five times** by the resident mount — `section_rows`,
//! `section_features`, `section_tokens`, `feature_heads`, `feature_nodes`. Each call reserves
//! `u32::MAX` **elements** of `u32`, so each is `4,294,967,295 × 4 = 17,179,869,180` octets of
//! device virtual address space, and the mount asks for five of them: **≈85.9 GB**.
//!
//! Nothing derives that number from the material. The atlas this driver family mounts is 335
//! occurrences and 628 sections — six research records — and the reservation is identical whether
//! the atlas holds six records or six million.
//!
//! `eros_agentic_research_conversation` refuses at `cuMemAddressReserve` with
//! `CUDA_ERROR_OUT_OF_MEMORY`. That refusal is a *claim about a level*, and a claim about a level
//! is a measurement, so this driver takes it: it reserves at a ladder of extents against the same
//! device and the same `VirtualDeviceBuffer::reserve` the resident mount calls, one buffer at a
//! time and then five at once, which is what the mount does.
//!
//! ## MEASURED 2026-08-09, and the first reading was WRONG
//!
//! The reading this file was written to confirm — *"the level is too large for this 16 GB card"* —
//! is **false**. On an RTX 4080 SUPER, with no `ulimit -v`, **all five** `u32::MAX`-word
//! reservations are admitted. A CUDA VMM reservation is device *address space*, not device memory,
//! and 86 GB of it fits on a 16 GB card without complaint.
//!
//! What the refusal actually was, measured across three frames of one process limit:
//!
//! ```text
//!   ulimit -v          largest single reserve      five-buffer mount
//!   (none)             4,294,967,295 words = 16 GiB    5 of 5   ADMITTED
//!   67,108,864 KiB     4,294,967,295 words = 16 GiB    3 of 5   REFUSED at buffer 3
//!   12,582,912 KiB     1,073,741,824 words =  4 GiB    would refuse at buffer 0
//! ```
//!
//! **Under unified virtual addressing a `CUdeviceptr` is a process virtual address**, so
//! `cuMemAddressReserve` is charged against the *cpu* `RLIMIT_AS`. The level and the process
//! limit are one constraint, not two: `RESIDENT_LOGICAL_WORD_RESERVATION` makes the resident text
//! mount demand ≈86 GB of process VA, and therefore makes the organ unmountable under any
//! `ulimit -v` below roughly 90 GB — a bound no caller can discover from the API, and one nothing
//! in the material asks for.
//!
//! The level is still authored: it is invariant in the material, identical for six records and for
//! six million. What is now measured is its **orbit** — it does not decide whether the card can
//! hold the atlas, it decides what process limit the caller must not set.
//!
//! Run:
//! ```text
//!   cargo run -p life --example the_reservation_decides_whether_the_card_mounts
//! ```

use mount::cuda::{Context, Device, VirtualDeviceBuffer};

/// The level under test, verbatim from `text_material_cuda.rs:20`.
const RESIDENT_LOGICAL_WORD_RESERVATION: usize = u32::MAX as usize;

/// How many buffers the resident mount reserves before it can serve one query.
const RESIDENT_BUFFERS: usize = 5;

fn main() {
    if let Err(error) = mount::cuda::init() {
        println!("cuInit refused: {error:?}");
        return;
    }
    let device_ordinal = 0;
    let device = match Device::get(device_ordinal) {
        Ok(device) => device,
        Err(error) => {
            println!("no device {device_ordinal}: {error:?}");
            return;
        }
    };
    let context = match Context::create(&device) {
        Ok(context) => context,
        Err(error) => {
            println!("no context: {error:?}");
            return;
        }
    };
    let _ = context.make_current();

    println!("STATION 1 — THE LEVEL UNDER TEST");
    println!(
        "  RESIDENT_LOGICAL_WORD_RESERVATION  {RESIDENT_LOGICAL_WORD_RESERVATION} words = {} octets",
        RESIDENT_LOGICAL_WORD_RESERVATION * 4
    );
    println!(
        "  the mount reserves                 {RESIDENT_BUFFERS} of these = {} octets",
        RESIDENT_LOGICAL_WORD_RESERVATION * 4 * RESIDENT_BUFFERS
    );

    println!("\nSTATION 2 — ONE BUFFER, AT A LADDER OF EXTENTS");
    println!("  {:>18}  {:>16}  {}", "words", "octets", "reserve");
    let mut single_ceiling = 0usize;
    for exponent in 20..=32u32 {
        let words = 1usize << exponent;
        let words = words.min(RESIDENT_LOGICAL_WORD_RESERVATION);
        match VirtualDeviceBuffer::<u32>::reserve(device_ordinal, words, 1) {
            Ok(buffer) => {
                println!("  {words:>18}  {:>16}  OK", words * 4);
                single_ceiling = words;
                drop(buffer);
            }
            Err(error) => {
                println!("  {words:>18}  {:>16}  REFUSED {error:?}", words * 4);
                break;
            }
        }
    }
    println!("  highest single reservation that held: {single_ceiling} words");

    println!("\nSTATION 3 — THE LEVEL ITSELF, ONE BUFFER");
    match VirtualDeviceBuffer::<u32>::reserve(device_ordinal, RESIDENT_LOGICAL_WORD_RESERVATION, 1)
    {
        Ok(buffer) => {
            println!("  u32::MAX words, one buffer          OK");
            drop(buffer);
        }
        Err(error) => println!("  u32::MAX words, one buffer          REFUSED {error:?}"),
    }

    println!("\nSTATION 4 — THE LEVEL ITSELF, FIVE BUFFERS — WHAT THE MOUNT ACTUALLY DOES");
    let mut held = Vec::new();
    let mut admitted = 0usize;
    for at in 0..RESIDENT_BUFFERS {
        match VirtualDeviceBuffer::<u32>::reserve(
            device_ordinal,
            RESIDENT_LOGICAL_WORD_RESERVATION,
            1,
        ) {
            Ok(buffer) => {
                admitted += 1;
                held.push(buffer);
                println!("  buffer {at}                            OK");
            }
            Err(error) => {
                println!("  buffer {at}                            REFUSED {error:?}");
                break;
            }
        }
    }
    println!(
        "\n  admitted {admitted} of {RESIDENT_BUFFERS}. The resident mount needs all {RESIDENT_BUFFERS}."
    );
    drop(held);

    println!("\nSTATION 5 — WHAT THE MATERIAL WOULD HAVE ASKED FOR");
    println!(
        "  The atlas `eros_agentic_research_conversation` mounts is 628 sections. Its five resident"
    );
    println!(
        "  arrays are bounded by the section, feature and token populations, all far below 2^20."
    );
    println!(
        "  The reservation is invariant in the material: it is the same number for six records and"
    );
    println!("  for six million. That is the definition of an authored level, not an aperture.");
    println!();
    println!(
        "  But it does NOT bound the card. Run this with and without `ulimit -v` and read STATION 4:"
    );
    println!(
        "  the reservation is charged to the CPU process address space through unified addressing,"
    );
    println!(
        "  so the level's real orbit is the process limit a caller may set, not the device it fits."
    );
}
