//! The exterior Athena's commands share (C6 of #603): a pinned read of an input by its SHA-256 and extent, a write that never
//! overwrites, the argument counts, and the printed readings of a held read and a lap's step. Moved from the store line's harness
//! (`examples/solenoidal_alpha.rs` and `complete_language.rs`), each item's text as it stood but for its visibility; the harness
//! imports them from here while it stands.

use holonics_engine::codec::count;
use holonics_engine::units::Units;
use std::io::{Read, Write};
use std::path::Path;
use std::process::{Command, Stdio};

pub type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

/// [agent-inferred, November 1] **The held-out read on `2^(−20)` bits to six decimals**
/// (millionths): `[opening, context, foil]`, each a code over its sites ([`held_out`]), and the question's
/// effect, the foil's rate less the context's (signed), beside the context's. Why six decimals
/// (reading 9): the held answer coded 5.629 bits a byte beside its own question and 5.629 beside a
/// foil's, equal at the printed thousandth, so a question effect below a thousandth of a bit could
/// not be seen; the effect is the difference of the two rates and is printed as such, not left to
/// the reader's subtraction of two rounded numbers. One formatter for every `FIELD_HELD` line.
pub fn held_text(held: &[(i64, usize); 3]) -> String {
    let rate = |k: usize| micro_bits(held[k].0 as i128, held[k].1 as i128);
    let effect = match (held[2], held[1]) {
        ((_, 0), _) | (_, (_, 0)) => "-".to_string(),
        ((a, na), (b, nb)) => micro_bits(a as i128 * nb as i128 - b as i128 * na as i128, na as i128 * nb as i128),
    };
    format!("answer={} classes={} context={} context_classes={} foil={} question={effect}", rate(0), held[0].1, rate(1), held[1].1, rate(2))
}

pub fn micro_bits(num: i128, sites: i128) -> String {
    if sites == 0 {
        return "-".into();
    }
    let den = sites << 20;
    let scaled = num * 1_000_000;
    let millionths = if scaled >= 0 { (scaled + den / 2) / den } else { -((-scaled + den / 2) / den) };
    format!("{}{}.{:06}", if millionths < 0 { "-" } else { "" }, millionths.abs() / 1_000_000, millionths.abs() % 1_000_000)
}

/// [agent-inferred, November 4, §16.41] **The octave a lap's transfers read**: `+1` (the step doubles), `−1` (it halves) or
/// `0`. Each step's transfer `t` is the first-order change of the next section's code were the step taken once more, so along
/// the lap's steps the joint code is `F(μ) = cμ + b′μ²` with `F′(1) = Σ t`; `b′` is read from the own curvatures `Σ b` of the
/// steps priced (a section's own parabola, the receipt's `change − predicted`), so the joint parabola's least is
/// `μ* = 1 − Σt / 2Σb`. The step halves where `μ* < 1/√2` and doubles where `μ* > √2`, the octave nearest `μ*` on the rate's
/// own carrier, compared exactly (`u = 2Σb − Σt = 2Σb μ*`: halve where `u < 0` or `u² < 2(Σb)²`, double where `u² > 8(Σb)²`).
/// Where no curvature is read (`Σ b ≤ 0`) the transfer's sign alone moves it. [the unified-theory reading of November 6, 08:54]
/// Since the step fluxes (no reread, so no `change`), the trainer reads it as the lap's line search, `step_transfer(2Σt,
/// Σ(t − p_ext))`: `μ* = −Σp_ext / Σ(t − p_ext)`, the curvature `t − p_ext` read from the pass alone ([`Receipt::external`]).
/// Why the next sections and not the step's own:
/// a step's own parabola read its least near five times the step at rate `2^(−11)` and its law drove the step to `2^(−7)`,
/// where the joint code rose from 1.127 to 1.59 nats a place (`_receipts/law50/`): a step's own fall is mostly the fit to its
/// own section, and only the next sections price what it generalizes.
pub fn step_transfer(transfers: i128, curvatures: i128) -> i32 {
    if curvatures <= 0 {
        return -(transfers.signum() as i32);
    }
    let u = 2 * curvatures - transfers;
    let b2 = curvatures * curvatures;
    if u < 0 || u.saturating_mul(u) < 2 * b2 {
        -1
    } else if u.saturating_mul(u) > 8 * b2 {
        1
    } else {
        0
    }
}

/// A units file (`founded-units-v1 0`, a founding of no merges, is the bytes).
pub fn units_of(path: &str, sha: &str) -> Result<Units> {
    Units::from_text(std::str::from_utf8(&pinned_read(path, sha, READ_BUDGET as usize)?)?).map_err(|e| e.to_string().into())
}

/// A learner's state read ceiling, `2^30` bytes.
pub const STATE_BUDGET: usize = 1 << 30;

/// A count a text is divided by (a number of streams, a stride): at least one.
pub fn positive(s: &str) -> Result<usize> {
    match count(s)? {
        0 => Err("a stream or stride count must be at least one".into()),
        n => Ok(n),
    }
}

pub const READ_BUDGET: u64 = 64 * 1024 * 1024;

pub fn write_new(path: &Path, bytes: &[u8]) -> Result<()> {
    let mut file = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)?;
    file.write_all(bytes)?;
    file.sync_all()?;
    Ok(())
}

pub fn pinned_read(path: &str, expected: &str, maximum: usize) -> Result<Vec<u8>> {
    let file = std::fs::File::open(path)?;
    if file.metadata()?.len() > maximum as u64 {
        return Err("declared input extent exceeded".into());
    }
    let mut bytes = Vec::new();
    file.take(maximum as u64 + 1).read_to_end(&mut bytes)?;
    if bytes.len() > maximum || sha256(&bytes)? != expected {
        return Err("input SHA256 or extent mismatch".into());
    }
    Ok(bytes)
}

pub fn sha256(bytes: &[u8]) -> Result<String> {
    // SHA belongs to exterior artifact provenance. No checksum enters a native relation.
    let mut process = Command::new("sha256sum")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()?;
    let mut input = process.stdin.take().ok_or("sha256sum stdin unavailable")?;
    std::thread::scope(|scope| -> Result<String> {
        let writer = scope.spawn(move || input.write_all(bytes));
        let output = process.wait_with_output()?;
        writer.join().map_err(|_| "sha256 writer failed")??;
        if !output.status.success() {
            return Err("sha256sum failed".into());
        }
        let digest = std::str::from_utf8(&output.stdout)?
            .split_whitespace()
            .next()
            .ok_or("missing SHA256")?;
        if digest.len() != 64 || !digest.bytes().all(|c| c.is_ascii_hexdigit()) {
            return Err("invalid SHA256 output".into());
        }
        Ok(digest.to_owned())
    })
}
