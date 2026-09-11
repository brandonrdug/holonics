//! Exterior Hephaestus comparison: common analytic receiver, changed head/tail generators.
use holonic_engine::surprisal::SymbolicSurprisal;
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use relational_geometry::{
    ComplexInterval, ComplexReceiverBox, Rat, RatInterval, eta_chain_decomposition,
    eta_partial_current, pi_interval, read_atlas, verify_artifact,
};
use serde_json::{Value, json};
use std::{collections::BTreeMap, path::Path, time::Instant};
#[path = "support/phase_signature.rs"]
mod phase_receiver;
use phase_receiver::phase_signature;
type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;
fn q(n: i64, d: i64) -> Rat {
    Rat::new(n.into(), d.into())
}
fn interval(v: &RatInterval) -> Value {
    json!([v.lower.to_string(), v.upper.to_string()])
}
fn complex(v: &ComplexInterval) -> Value {
    json!({"re":interval(&v.re),"im":interval(&v.im)})
}
fn information(v: &SymbolicSurprisal) -> Result<Value> {
    let b = v.enclosure_at(32, 96)?;
    Ok(
        json!({"exact_bits":v.named(),"display":interval(&RatInterval::new(b.lower,b.upper).round_out(8))}),
    )
}
// Closed seam charts overlap at integer turns. Each piece keeps its integer lift;
// the union reconstructs the input interval exactly, including negative windings.
fn lifted_turn(turn: &RatInterval, period: &RatInterval) -> Result<Value> {
    let cycles = turn.divide(period)?;
    let first = cycles.lower.floor().to_integer();
    let last = cycles.upper.floor().to_integer();
    let mut winding = first;
    let mut pieces = Vec::new();
    while winding <= last {
        let k = Rat::from_integer(winding.clone());
        let lo = cycles.lower.clone().max(k.clone());
        let hi = cycles.upper.clone().min(&k + Rat::one());
        let residue = RatInterval::new(lo, hi).subtract(&RatInterval::point(k));
        pieces.push(json!({"winding":winding.to_string(),"residue":interval(&residue)}));
        winding += 1;
    }
    Ok(
        json!({"radians":interval(turn),"period":interval(period),"cycle_enclosure":interval(&cycles),
        "lifted_pieces":pieces,"seam_convention":"closed charts; seam overlap retained"}),
    )
}
// A canonical prefix code for one explicit exterior reference population.
// It is not a native tokenizer. Lengths are found with integer comparisons, never float logs.
fn shannon_code(population: &BTreeMap<u64, u64>) -> Result<BTreeMap<u64, String>> {
    let total: u64 = population.values().sum();
    let mut lengths = Vec::new();
    for (&label, &count) in population {
        assert!(count > 0);
        let mut scaled = BigUint::from(count);
        let mut length = 0usize;
        while scaled < BigUint::from(total) {
            scaled <<= 1;
            length += 1;
        }
        // This caller has multiple symbols; empty singleton words require an external count.
        assert!(length > 0);
        lengths.push((length, label));
    }
    lengths.sort();
    let mut code = BigUint::zero();
    let mut previous = 0;
    let mut result = BTreeMap::new();
    for (length, label) in lengths {
        code <<= length - previous;
        assert!(code < (BigUint::one() << length));
        result.insert(
            label,
            format!("{:0>width$}", code.to_str_radix(2), width = length),
        );
        code += BigUint::one();
        previous = length;
    }
    Ok(result)
}
fn decode(code: &BTreeMap<u64, String>, bits: &str) -> Result<(Vec<u64>, String)> {
    let mut pending = String::new();
    let mut output = Vec::new();
    for bit in bits.chars() {
        pending.push(bit);
        if let Some((&label, _)) = code.iter().find(|(_, word)| **word == pending) {
            output.push(label);
            pending.clear();
        } else if !code.values().any(|word| word.starts_with(&pending)) {
            return Err("bit prefix has no continuation in this code".into());
        }
    }
    Ok((output, pending))
}
fn main() -> Result<()> {
    let args: Vec<_> = std::env::args().collect();
    let source = args.get(1).ok_or("supply exact atlas path")?;
    let frame_width: usize = args
        .get(3)
        .ok_or("supply an exterior packet frame width")?
        .parse()?;
    if frame_width == 0 {
        return Err("packet frame width must be positive".into());
    }
    let verification = verify_artifact(Path::new(source))?;
    let atlas = read_atlas(Path::new(source))?;
    let mut returns = Vec::new();
    let mut phase_stream = Vec::new();
    for lineage in &atlas.zero_lineages {
        let receiver = ComplexReceiverBox::point(q(1, 2), lineage.final_receiver.tau.midpoint());
        let mut config = lineage.config.clone();
        let started = Instant::now();
        let chain = eta_chain_decomposition(&receiver, &config)?;
        let time_a = started.elapsed().as_micros();
        let start = config.euler_maclaurin_start;
        config.euler_maclaurin_start = start.checked_mul(2).ok_or("head extent overflow")?;
        let started = Instant::now();
        let expanded = eta_chain_decomposition(&receiver, &config)?;
        let time_b = started.elapsed().as_micros();
        config.euler_maclaurin_start = start;
        let started = Instant::now();
        let direct = eta_partial_current(q(1, 2), receiver.tau.lower.clone(), start, &config)?;
        let time_direct = started.elapsed().as_micros();
        let direct_value = direct
            .terms
            .last()
            .unwrap()
            .partial_sum
            .add_disc(&direct.tail_radius);
        let difference = chain.eta.subtract(&expanded.eta);
        let direct_difference = chain.eta.subtract(&direct_value);
        assert!(difference.contains_origin() && direct_difference.contains_origin());
        let period = pi_interval(config.dyadic_bits).scale(&q(2, 1));
        let mut constituents = Vec::new();
        for term in &chain.head {
            let signature = phase_signature(&term.value);
            phase_stream.push(signature);
            constituents.push(json!({"base":term.base,"prime_address":term.address,
                "amplitude":interval(&term.amplitude),"value":complex(&term.value),
                "phase_signature":signature,"turn":lifted_turn(&term.turn,&period)?}));
        }
        let mut rebuilt = ComplexInterval::zero();
        for term in &chain.head {
            rebuilt = rebuilt.add(&term.value).round_out(config.dyadic_bits);
        }
        rebuilt = rebuilt
            .add(&chain.integral_term)
            .add(&chain.boundary_half)
            .round_out(config.dyadic_bits);
        for crossing in &chain.crossings {
            rebuilt = rebuilt.add(&crossing.value).round_out(config.dyadic_bits);
        }
        rebuilt = rebuilt
            .add_disc(&chain.remainder_radius)
            .multiply(&chain.alternating_factor);
        assert!(rebuilt.subtract(&chain.eta).contains_origin());
        // remainder_radius in EtaChainDecomposition belongs to zeta, before the eta factor.
        let factor_bound =
            &chain.alternating_factor.re.abs_upper() + &chain.alternating_factor.im.abs_upper();
        returns.push(json!({"lineage":lineage.ordinal,"receiver_tau":receiver.tau.lower.to_string(),
            "receiver_sigma":"1/2","representative_is_not_asserted_zero":true,
            "config":config,"source_zero_box":interval(&lineage.final_receiver.tau),
            "euler_maclaurin":{"start":start,"value":complex(&chain.eta),"phase_signature":phase_signature(&chain.eta),
                "source_zeta_remainder":chain.remainder_radius.to_string(),
                "transported_eta_remainder_bound":(&chain.remainder_radius*factor_bound).to_string(),
                "head":constituents,"integral_term":complex(&chain.integral_term),
                "boundary_half":complex(&chain.boundary_half),"alternating_factor":complex(&chain.alternating_factor),
                "crossings":chain.crossings,"reconstructed_eta":complex(&rebuilt),"elapsed_microseconds":time_a},
            "expanded_euler_maclaurin":{"start":config.euler_maclaurin_start*2,"value":complex(&expanded.eta),
                "source_zeta_remainder":expanded.remainder_radius.to_string(),"phase_signature":phase_signature(&expanded.eta),
                "elapsed_microseconds":time_b},
            "direct_alternating":{"terms":direct.terms,"tail_radius":direct.tail_radius.to_string(),
                "value":complex(&direct_value),"phase_signature":phase_signature(&direct_value),"elapsed_microseconds":time_direct},
            "differences":{"em_minus_expanded":complex(&difference),"em_minus_direct":complex(&direct_difference)},
            "work_scope":"source extents and exterior elapsed time; chain owner also re-evaluates its sum; full arithmetic work not counted"}));
    }
    let mut population = BTreeMap::new();
    for &label in &phase_stream {
        *population.entry(label).or_insert(0u64) += 1;
    }
    let code = shannon_code(&population)?;
    let total = phase_stream.len();
    let packet = phase_stream
        .iter()
        .map(|s| code[s].as_str())
        .collect::<String>();
    assert_eq!(
        decode(&code, &packet)?,
        (phase_stream.clone(), String::new())
    );
    // Test actual handoffs at every bit cut: the suffix starts with the retained partial word.
    for cut in 0..=packet.len() {
        let (mut prefix, remainder) = decode(&code, &packet[..cut])?;
        let (suffix, tail) = decode(&code, &(remainder + &packet[cut..]))?;
        prefix.extend(suffix);
        assert!(tail.is_empty());
        assert_eq!(prefix, phase_stream);
    }
    let mut kraft = Rat::zero();
    let mut entropy = SymbolicSurprisal::zero();
    let mut words = Vec::new();
    for (&label, &count) in &population {
        let probability = Rat::new(count.into(), total.into());
        let surprise = SymbolicSurprisal::of_probability(&probability)?;
        entropy = entropy.plus(&surprise.scaled(&probability));
        let length = code[&label].len();
        kraft += Rat::new(BigInt::one(), BigInt::one() << length);
        words.push(
            json!({"signature":label,"count":count,"probability":probability.to_string(),
            "surprise":information(&surprise)?,"codeword":code[&label],"length_bits":length}),
        );
    }
    assert!(kraft <= Rat::one());
    let actual = Rat::new(packet.len().into(), total.into());
    let overhead = SymbolicSurprisal::term(2, actual.clone())?.minus(&entropy);
    let parent_count = atlas.zero_lineages.len();
    let mut offset = 0;
    let mut parent_packets = Vec::new();
    for parent in &returns {
        let head_count = parent["euler_maclaurin"]["head"].as_array().unwrap().len();
        let words = &phase_stream[offset..offset + head_count];
        let bits = words.iter().map(|s| code[s].len()).sum::<usize>();
        parent_packets
            .push(json!({"lineage":parent["lineage"],"term_count":head_count,"payload_bits":bits}));
        offset += head_count;
    }
    let framed_prefix = packet.len() / frame_width * frame_width;
    let result = json!({"schema":"holonics.hephaestus.eta-generator-comparison.v1","source":source,
        "verification_scope":"stored atlas consistency, not independent analytic recertification",
        "verification":verification,"receivers":returns,
        "code":{"scope":"exterior canonical Shannon code over head-term enclosure signatures; counting measure per term, not the earlier contour-length measure",
            "words":words,"packet":packet,"source_signatures":phase_stream,"kraft_sum":kraft.to_string(),
            "ideal_bits_per_term":information(&entropy)?,"actual_bits_per_term":actual.to_string(),
            "integer_code_overhead_per_term":information(&overhead)?,"all_bit_cut_handoffs_verified":true,
            "verified_bit_cuts":packet.len()+1,"parent_packets":parent_packets,
            "mean_terms_per_receiver":Rat::new(total.into(),parent_count.into()).to_string(),
            "mean_payload_bits_per_receiver":Rat::new(packet.len().into(),parent_count.into()).to_string(),
            "packet_frame":{"declared_width_bits":frame_width,"complete_frames":packet.len()/frame_width,
                "residue_bits":&packet[framed_prefix..],"residue_length":packet.len()%frame_width,
                "scope":"exterior bit framing; no identification of bits with nucleotides"},
            "retained_decoder_required":true,"codebook_and_framing_bits_not_in_payload_length":true},
        "native_model_changed":false});
    let text = serde_json::to_string_pretty(&result)?;
    if let Some(path) = args.get(2) {
        std::fs::write(path, format!("{text}\n"))?;
    }
    println!("{text}");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn a_negative_phase_seam_retains_both_winding_lifts() {
        let lifted = lifted_turn(
            &RatInterval::new(q(-5, 4), q(-3, 4)),
            &RatInterval::point(q(1, 1)),
        )
        .unwrap();
        assert_eq!(
            lifted["lifted_pieces"],
            json!([
                {"winding":"-2","residue":["3/4","1"]},
                {"winding":"-1","residue":["0","1/4"]}
            ])
        );
    }
    #[test]
    fn a_partial_codeword_survives_the_next_packet() {
        let code = shannon_code(&BTreeMap::from([(1, 4), (2, 2), (3, 1), (4, 1)])).unwrap();
        let (decoded, remainder) = decode(&code, "011").unwrap();
        assert_eq!(decoded, vec![1]);
        assert_eq!(remainder, "11");
        assert_eq!(
            decode(&code, &(remainder + "0")).unwrap(),
            (vec![3], String::new())
        );
    }
    #[test]
    fn an_unused_prefix_is_not_repaired_into_a_symbol() {
        let code = shannon_code(&BTreeMap::from([(1, 1), (2, 1), (3, 1)])).unwrap();
        assert!(decode(&code, "11").is_err());
    }
}
