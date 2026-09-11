//! Hephaestus receiver over an existing exact eta/zero atlas.
//! Reads complete intervals and boundary images, never treats an ordinate midpoint as a zero.
use std::{collections::BTreeMap, path::Path};

use holonic_engine::surprisal::{CrossEntropyFiber, SymbolicSurprisal, cross_entropy_fiber};
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use relational_geometry::{
    ComplexInterval, ComplexReceiverBox, Rat, RatInterval, WindingReceipt, ZeroLineage,
    derive_ordinate_relations, eta_evaluate, read_atlas, verify_artifact,
};
use serde_json::{Value, json};

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
fn form(v: &SymbolicSurprisal) -> Result<Value> {
    let enclosure = v.enclosure_at(32, 96)?;
    let displayed = RatInterval::new(enclosure.lower, enclosure.upper).round_out(8);
    Ok(
        json!({"exact_bits":v.named(),"display_enclosure":interval(&displayed),
        "enclosure_terms":32,"enclosure_bits":96,"display_bits":8}),
    )
}
fn counts(weights: &BTreeMap<u64, Rat>) -> BTreeMap<u64, BigUint> {
    let common: BigInt = weights.values().map(|v| v.denom().clone()).product();
    weights
        .iter()
        .map(|(k, v)| {
            assert!(!v.is_negative());
            (
                *k,
                (v.numer() * (&common / v.denom())).to_biguint().unwrap(),
            )
        })
        .collect()
}
fn weights_json(weights: &BTreeMap<u64, Rat>) -> Value {
    json!(
        weights
            .iter()
            .map(|(k, v)| (k.to_string(), v.to_string()))
            .collect::<BTreeMap<_, _>>()
    )
}
fn entropy(weights: &BTreeMap<u64, Rat>) -> Result<SymbolicSurprisal> {
    let population = counts(weights);
    match cross_entropy_fiber(&population, &population)? {
        CrossEntropyFiber::Supported(value) => Ok(value),
        _ => Err("a nonempty positive measured population must support its own code".into()),
    }
}
fn reading(reading: &CrossEntropyFiber) -> Result<Value> {
    Ok(match reading {
        CrossEntropyFiber::Supported(v) => json!({"disposition":"full","form":form(v)?}),
        CrossEntropyFiber::Partial {
            form_over_supported,
            supported_mass,
            unsupported,
            unsupported_mass,
        } => json!({"disposition":"partial","form_over_supported":form(form_over_supported)?,
                "supported_mass":supported_mass.to_string(),"code_missing_labels":unsupported,
                "code_missing_mass":unsupported_mass.to_string()}),
        CrossEntropyFiber::Unsupported { unsupported } => {
            let disposition = if unsupported.is_empty() {
                "no_population"
            } else {
                "reference_code_has_no_mass"
            };
            json!({"disposition":disposition,"labels":unsupported})
        }
    })
}
fn final_winding(lineage: &ZeroLineage) -> &WindingReceipt {
    match lineage.refinements.last() {
        None => &lineage.root,
        Some(step) if step.selected == "left" => &step.left,
        Some(step) if step.selected == "right" => &step.right,
        _ => unreachable!("verified refinement selection"),
    }
}

// Closed quadrant signatures. Axis uncertainty is retained as a set of possible quadrants.
fn phase_signature(z: &ComplexInterval) -> u64 {
    let mut mask = 0;
    for re_negative in 0..2 {
        for im_negative in 0..2 {
            let re = if re_negative == 1 {
                z.re.lower <= Rat::zero()
            } else {
                z.re.upper >= Rat::zero()
            };
            let im = if im_negative == 1 {
                z.im.lower <= Rat::zero()
            } else {
                z.im.upper >= Rat::zero()
            };
            if re && im {
                mask |= 1 << (2 * re_negative + im_negative);
            }
        }
    }
    mask
}
fn conjugate_signature(mask: u64) -> u64 {
    let mut result = 0;
    for i in 0..4 {
        if mask & (1 << i) != 0 {
            result |= 1 << (i ^ 1);
        }
    }
    result
}
fn phase_population(boundary: &WindingReceipt, conjugated: bool) -> BTreeMap<u64, Rat> {
    let mut result = BTreeMap::new();
    let mut total = Rat::zero();
    for segment in &boundary.segments {
        assert!(!segment.image.contains_origin());
        let weight = (&segment.end.re - &segment.start.re).abs()
            + (&segment.end.im - &segment.start.im).abs();
        total += &weight;
        let image = if conjugated {
            segment.image.conjugate()
        } else {
            segment.image.clone()
        };
        let mask = phase_signature(&image);
        assert!(mask != 0 && mask != 15);
        *result.entry(mask).or_insert_with(Rat::zero) += weight;
    }
    assert!(total.is_positive());
    // One zero-localization occurrence has measure one; source contour length distributes it.
    for value in result.values_mut() {
        *value /= &total;
    }
    result
}

fn main() -> Result<()> {
    let args: Vec<_> = std::env::args().collect();
    let source = args.get(1).ok_or("supply an exact eta-atlas RON path")?;
    let verification = verify_artifact(Path::new(source))?;
    let atlas = read_atlas(Path::new(source))?;
    if atlas.zero_lineages.len() < 4 {
        return Err("four distinct zero marks are needed for the Swing receiver".into());
    }
    let n = q(atlas.zero_lineages.len().try_into()?, 1);
    let mut total_resolution = SymbolicSurprisal::zero();
    let mut conditional_phase = SymbolicSurprisal::zero();
    let mut pooled = BTreeMap::new();
    let mut later = BTreeMap::new();
    let mut first = None;
    let mut zero_returns = Vec::new();
    let mut total_segments = 0;
    for (index, lineage) in atlas.zero_lineages.iter().enumerate() {
        let parent_width = lineage.root.receiver.tau.width();
        let refined_width = lineage.final_receiver.tau.width();
        let gain = SymbolicSurprisal::of_probability(&(&refined_width / &parent_width))?;
        total_resolution = total_resolution.plus(&gain);
        let boundary = final_winding(lineage);
        total_segments += boundary.segments.len();
        let phases = phase_population(boundary, false);
        let swung_phases = phase_population(boundary, true);
        let transported: BTreeMap<_, _> = phases
            .iter()
            .map(|(k, v)| (conjugate_signature(*k), v.clone()))
            .collect();
        assert_eq!(transported, swung_phases);
        let h = entropy(&phases)?;
        assert_eq!(h, entropy(&swung_phases)?);
        conditional_phase = conditional_phase.plus(&h);
        if index == 0 {
            first = Some(phases.clone());
        }
        for (label, mass) in &phases {
            *pooled.entry(*label).or_insert_with(Rat::zero) += mass;
            if index > 0 {
                *later.entry(*label).or_insert_with(Rat::zero) += mass;
            }
        }
        // A declared rational representative is compared with zero, never installed as the zero.
        let point = ComplexReceiverBox::point(q(1, 2), lineage.final_receiver.tau.midpoint());
        let value = eta_evaluate(&point, &lineage.config)?;
        let reflected = eta_evaluate(
            &ComplexReceiverBox::point(q(1, 2), -point.tau.lower.clone()),
            &lineage.config,
        )?;
        assert_eq!(reflected.value, value.value.conjugate());
        zero_returns.push(json!({"source_lineage":lineage.ordinal,
            "tau":interval(&lineage.final_receiver.tau),"sigma":"1/2 by unique-zero reflection",
            "winding":boundary.winding,"boundary_segments":boundary.segments.len(),
            "resolution_information":form(&gain)?,"phase_signature_mass":weights_json(&phases),
            "phase_entropy":form(&h)?,"conjugate_phase_covariance":true,
            "representative_tau":point.tau.lower.to_string(),"eta_residual":complex(&value.value),
            "eta_residual_norm_squared":interval(&value.value.re.square().add(&value.value.im.square())),
            "eta_remainder_radius":value.remainder_radius.to_string(),
            "representative_is_not_asserted_to_be_zero":true}));
    }
    let ordinates: Vec<_> = atlas
        .zero_lineages
        .iter()
        .map(|z| z.final_receiver.tau.clone())
        .collect();
    let swung: Vec<_> = ordinates.iter().map(RatInterval::neg).collect();
    let (relations, _) = derive_ordinate_relations(&ordinates)?;
    let (swung_relations, _) = derive_ordinate_relations(&swung)?;
    let mut swings = Vec::new();
    let gaps: Vec<_> = relations
        .iter()
        .filter(|r| r.kind == "successive_gap")
        .collect();
    for (left, right) in relations.iter().zip(&swung_relations) {
        if left.kind == "ordered_projective_cross_ratio" {
            assert_eq!(left.value, right.value);
            swings.push(json!({"ordered_marks":left.members,"pair":interval(&left.value),
                "swung_pair":interval(&right.value),"scope":"interval cross-ratio in the transported chart"}));
        }
    }
    let mut trends = BTreeMap::new();
    let mut trend_events = Vec::new();
    let mut unresolved = 0;
    for (i, pair) in gaps.windows(2).enumerate() {
        let delta = pair[1].value.subtract(&pair[0].value);
        let label = if delta.lower > Rat::zero() {
            Some(1)
        } else if delta.upper < Rat::zero() {
            Some(0)
        } else {
            None
        };
        if let Some(label) = label {
            *trends.entry(label).or_insert_with(Rat::zero) += Rat::one();
        } else {
            unresolved += 1;
        }
        trend_events
            .push(json!({"source_marks":[i,i+1,i+2],"difference":interval(&delta),"label":label}));
    }
    let trend_h = if trends.is_empty() {
        None
    } else {
        Some(entropy(&trends)?)
    };
    let trend_code = BTreeMap::from([(0, BigUint::one()), (1, BigUint::one())]);
    let trend_ce = cross_entropy_fiber(&counts(&trends), &trend_code)?;
    let trend_entropy = trend_h.as_ref().map(form).transpose()?;
    let trend_excess = trend_ce
        .form()
        .zip(trend_h.as_ref())
        .map(|(ce, h)| form(&ce.minus(h)))
        .transpose()?;
    let phase_h = entropy(&pooled)?;
    let phase_avg = conditional_phase.scaled(&n.recip());
    let phase_mutual = phase_h.minus(&phase_avg);
    // Possible nonempty quadrant signatures of an origin-excluding rectangle: 4 singletons,
    // and 4 adjacent pairs. The code is a declared geometric reference, not a native prior.
    let phase_code = BTreeMap::from_iter([1, 2, 3, 4, 5, 8, 10, 12].map(|k| (k, BigUint::one())));
    let result = json!({"schema":"holonics.hephaestus.zeta-information.v1",
        "source_atlas":source,"artifact_verification":verification,
        "source_scope":{"sigma":interval(&atlas.scan.sigma),"tau":interval(&atlas.scan.tau),
            "zero_localization_occurrences":atlas.zero_lineages.len(),"integer_bands":atlas.bands.len(),
            "source_apparatus":atlas.apparatus,"atlas_elapsed_milliseconds":atlas.elapsed_milliseconds,
            "global_RH_or_complete_strip_claim":false},
        "zero_returns":zero_returns,"ordered_relations":relations.iter().map(|r|
            json!({"kind":r.kind,"members":r.members,"enclosure":interval(&r.value)})).collect::<Vec<_>>(),
        "swing":swings,
        "localization_rate":{"total_information":form(&total_resolution)?,"measure":n.to_string(),
            "bits_per_zero_localization_holon":form(&total_resolution.scaled(&n.recip()))?,
            "reference":"uniform height measure inside each root band; resolution gain, not a probability of RH"},
        "phase_measurement":{"total_mass":n.to_string(),"per_parent_normalized_contour_L1_measure":true,
            "phase_signature_mass":weights_json(&pooled),"total_conditional_bits":form(&conditional_phase)?,
            "bits_per_zero_localization_holon":form(&phase_avg)?,"pooled_signature_entropy":form(&phase_h)?,
            "parent_signature_mutual_information":form(&phase_mutual)?,
            "reference_code_loss":reading(&cross_entropy_fiber(&counts(&pooled),&phase_code)?)?,
            "later_spectral_windows_under_first_window_code":reading(&cross_entropy_fiber(&counts(&later),&counts(&first.unwrap()))?)?,
            "scope":"entropy of certified enclosure signatures; ambiguous phase sectors remain set-valued"},
        "gap_comparison":{"events":trend_events,"counts":weights_json(&trends),"unresolved":unresolved,
            "entropy_bits_per_resolved_comparison":trend_entropy,"reference_code_loss":reading(&trend_ce)?,
            "excess_bits":trend_excess,
            "scope":"overlapping spectral triples; not an independent-process entropy rate or an HNN prediction"},
        "work":{"distinct_boundary_segments_measured":total_segments,"additional_point_eta_evaluations":2*atlas.zero_lineages.len(),
            "full_internal_arithmetic_work":"not counted by this existing analytic owner",
            "no_fabricated_ExactWork":true},
        "representation_cost":{"source_ron_bytes":std::fs::metadata(source)?.len(),
            "scope":"serialized exterior witness size, not entropy or native compression"},
        "native_model_changed":false});
    let text = serde_json::to_string_pretty(&result)?;
    if let Some(path) = args.get(2) {
        std::fs::write(path, format!("{text}\n"))?;
    }
    println!("{text}");
    Ok(())
}
