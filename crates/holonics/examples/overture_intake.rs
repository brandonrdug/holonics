//! `overture_intake FILE`: the overture's intake (#146; record
//! `2026-10-29_INHERITED_WEIGHTS_ARE_AN_OVERTURE…` §5) read over one released `safetensors` file.
//! Every tensor is decoded exactly at the boundary (`holonics::hnn::overture`) and listed with its
//! name, format, shape and count, its zero count, and the places of its values' leading bits (the
//! exponent of the highest set bit, lowest and highest). The totals close the listing. It reads the
//! file whole; it founds nothing and runs no model.
use holonics::hnn::overture::Safetensors;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = std::env::args().collect();
    let [_, path] = &args[..] else { return Err("overture_intake FILE".into()) };
    let started = std::time::Instant::now();
    // The exterior boundary reads the file; nothing inside the machinery does (guard 7).
    #[allow(clippy::disallowed_methods)]
    let bytes = std::fs::read(path)?;
    let file = Safetensors::read(&bytes)?;
    let (mut values, mut zeros, mut lowest, mut highest) = (0usize, 0usize, i32::MAX, i32::MIN);
    for entry in &file.entries {
        let decoded = file.decoded(entry)?;
        let tops = decoded.iter().filter(|d| d.numerator != 0).map(|d| 63 - d.numerator.unsigned_abs().leading_zeros() as i32 + d.exponent);
        let (low, high) = tops.fold((i32::MAX, i32::MIN), |(l, h), t| (l.min(t), h.max(t)));
        let zero = decoded.iter().filter(|d| d.numerator == 0).count();
        println!("OVERTURE_TENSOR name={} format={}/{} shape={:?} count={} zeros={zero} leading_place={low}..={high}", entry.name, entry.format.significand_bits, entry.format.exponent_bits, entry.shape, decoded.len());
        (values, zeros, lowest, highest) = (values + decoded.len(), zeros + zero, lowest.min(low), highest.max(high));
    }
    println!("OVERTURE_INTAKE tensors={} values={values} zeros={zeros} leading_place={lowest}..={highest} bytes={} elapsed_ms={}", file.entries.len(), bytes.len(), started.elapsed().as_millis());
    Ok(())
}
