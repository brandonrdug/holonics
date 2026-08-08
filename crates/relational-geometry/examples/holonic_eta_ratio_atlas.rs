//! Generate a bounded eta-zero atlas from exact rational receiver currents.
//!
//! No known zero ordinate is accepted as input.  Integer height bands are
//! scanned independently, zero-bearing bands are refined through exact
//! boundary winding, and all reported coordinates remain rational intervals.

use std::env;
use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, mpsc};
use std::thread;
use std::time::Instant;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use relational_geometry::{
    ComplexInterval, ComplexReceiverBox, EtaCurrentReceipt, ExactSeriesConfig, RatComplex,
    RatInterval, WindingReceipt, eta_boundary_winding, eta_partial_current,
    interval_common_continued_fraction,
};
use serde::{Deserialize, Serialize};

type Rat = BigRational;

fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn rat(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn receiver(tau: RatInterval) -> ComplexReceiverBox {
    ComplexReceiverBox::new(RatInterval::new(rat(2, 5), rat(3, 5)), tau)
}

fn exact_config() -> ExactSeriesConfig {
    ExactSeriesConfig {
        dyadic_bits: 96,
        euler_maclaurin_start: 12,
        euler_maclaurin_order: 10,
        log_terms: 28,
        exponential_terms: 18,
        trigonometric_terms: 16,
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct BandReceipt {
    ordinal: usize,
    winding: WindingReceipt,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct RefinementStep {
    grain: u32,
    split: Rat,
    left: WindingReceipt,
    right: WindingReceipt,
    selected: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct ZeroLineage {
    ordinal: usize,
    root: WindingReceipt,
    refinements: Vec<RefinementStep>,
    final_receiver: ComplexReceiverBox,
    midpoint_current: EtaCurrentReceipt,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct IntervalRelation {
    kind: String,
    members: Vec<usize>,
    value: RatInterval,
    common_continued_fraction: Vec<BigInt>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct ReciprocalMoment {
    order: u32,
    value: RatInterval,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct EtaRatioAtlas {
    schema: String,
    arithmetic: String,
    source_function: String,
    receiver_law: String,
    symmetry_read: String,
    scan: ComplexReceiverBox,
    config: ExactSeriesConfig,
    physical_workers: usize,
    elapsed_milliseconds: u64,
    bands: Vec<BandReceipt>,
    zero_lineages: Vec<ZeroLineage>,
    interval_relations: Vec<IntervalRelation>,
    reciprocal_moments: Vec<ReciprocalMoment>,
}

fn scan_integer_bands(
    lower: i64,
    upper: i64,
    workers: usize,
    config: &ExactSeriesConfig,
) -> Result<Vec<BandReceipt>, String> {
    let bands = Arc::new((lower..upper).collect::<Vec<_>>());
    let next = Arc::new(AtomicUsize::new(0));
    let config = Arc::new(config.clone());
    let (sender, receiver_channel) = mpsc::channel();

    thread::scope(|scope| {
        for _ in 0..workers {
            let bands = Arc::clone(&bands);
            let next = Arc::clone(&next);
            let config = Arc::clone(&config);
            let sender = sender.clone();
            scope.spawn(move || {
                loop {
                    let index = next.fetch_add(1, Ordering::Relaxed);
                    let Some(&tau_lower) = bands.get(index) else {
                        break;
                    };
                    let band_receiver =
                        receiver(RatInterval::new(integer(tau_lower), integer(tau_lower + 1)));
                    let result = eta_boundary_winding(&band_receiver, &config, 14)
                        .map(|winding| BandReceipt {
                            ordinal: index,
                            winding,
                        })
                        .map_err(|error| {
                            format!("band [{tau_lower},{}] failed: {error}", tau_lower + 1)
                        });
                    sender.send(result).expect("scan receiver remains live");
                }
            });
        }
    });
    drop(sender);

    let mut receipts = Vec::with_capacity((upper - lower) as usize);
    for result in receiver_channel {
        receipts.push(result?);
    }
    receipts.sort_by_key(|receipt| receipt.ordinal);
    Ok(receipts)
}

fn refine_one(
    ordinal: usize,
    root: WindingReceipt,
    grains: u32,
    config: &ExactSeriesConfig,
) -> Result<ZeroLineage, String> {
    if root.winding != 1 {
        return Err(format!(
            "lineage {ordinal} cannot refine winding {} as one closure",
            root.winding
        ));
    }
    let mut current = root.clone();
    let mut refinements = Vec::new();
    let candidate_splits = [rat(1, 2), rat(2, 5), rat(3, 5)];

    for grain in 1..=grains {
        let lower = current.receiver.tau.lower.clone();
        let upper = current.receiver.tau.upper.clone();
        let extent = &upper - &lower;
        let mut accepted = None;

        for fraction in &candidate_splits {
            let split = &lower + &extent * fraction;
            let left_receiver = receiver(RatInterval::new(lower.clone(), split.clone()));
            let right_receiver = receiver(RatInterval::new(split.clone(), upper.clone()));
            let Ok(left) = eta_boundary_winding(&left_receiver, config, 14) else {
                continue;
            };
            let Ok(right) = eta_boundary_winding(&right_receiver, config, 14) else {
                continue;
            };
            if left.winding + right.winding != current.winding {
                continue;
            }
            if !matches!((left.winding, right.winding), (1, 0) | (0, 1)) {
                continue;
            }
            let selected = if left.winding == 1 { "left" } else { "right" };
            accepted = Some((split, left, right, selected.to_owned()));
            break;
        }

        let Some((split, left, right, selected)) = accepted else {
            return Err(format!(
                "lineage {ordinal} could not certify a lawful split at grain {grain}"
            ));
        };
        current = if selected == "left" {
            left.clone()
        } else {
            right.clone()
        };
        refinements.push(RefinementStep {
            grain,
            split,
            left,
            right,
            selected,
        });
    }

    let final_receiver = current.receiver.clone();
    let midpoint_current =
        eta_partial_current(rat(1, 2), final_receiver.tau.midpoint(), 96, config)
            .map_err(|error| format!("lineage {ordinal} current failed: {error}"))?;
    Ok(ZeroLineage {
        ordinal,
        root,
        refinements,
        final_receiver,
        midpoint_current,
    })
}

fn refine_lineages(
    roots: Vec<(usize, WindingReceipt)>,
    grains: u32,
    config: &ExactSeriesConfig,
) -> Result<Vec<ZeroLineage>, String> {
    let (sender, receiver_channel) = mpsc::channel();
    thread::scope(|scope| {
        for (ordinal, root) in roots {
            let sender = sender.clone();
            let config = config.clone();
            scope.spawn(move || {
                sender
                    .send(refine_one(ordinal, root, grains, &config))
                    .expect("lineage receiver remains live");
            });
        }
    });
    drop(sender);
    let mut lineages = Vec::new();
    for result in receiver_channel {
        lineages.push(result?);
    }
    lineages.sort_by(|left, right| {
        left.final_receiver
            .tau
            .lower
            .cmp(&right.final_receiver.tau.lower)
    });
    for (ordinal, lineage) in lineages.iter_mut().enumerate() {
        lineage.ordinal = ordinal;
    }
    Ok(lineages)
}

fn positive_ratio(
    numerator: &RatInterval,
    denominator: &RatInterval,
) -> Result<RatInterval, String> {
    numerator
        .divide(denominator)
        .map_err(|error| error.to_string())
}

fn interval_power(value: &RatInterval, exponent: u32) -> RatInterval {
    let mut result = RatInterval::point(Rat::one());
    for _ in 0..exponent {
        result = result.multiply(value);
    }
    result
}

fn relation(kind: &str, members: Vec<usize>, value: RatInterval) -> IntervalRelation {
    IntervalRelation {
        kind: kind.to_owned(),
        members,
        common_continued_fraction: if value.lower.is_positive() {
            interval_common_continued_fraction(&value, 16)
        } else {
            Vec::new()
        },
        value,
    }
}

fn derive_relations(
    lineages: &[ZeroLineage],
) -> Result<(Vec<IntervalRelation>, Vec<ReciprocalMoment>), String> {
    let ordinates = lineages
        .iter()
        .map(|lineage| lineage.final_receiver.tau.clone())
        .collect::<Vec<_>>();
    let mut relations = Vec::new();

    for index in 0..ordinates.len().saturating_sub(1) {
        let gap = ordinates[index + 1].subtract(&ordinates[index]);
        relations.push(relation("successive_gap", vec![index, index + 1], gap));
        relations.push(relation(
            "successive_ordinate_ratio",
            vec![index, index + 1],
            positive_ratio(&ordinates[index + 1], &ordinates[index])?,
        ));
    }
    for index in 0..ordinates.len().saturating_sub(2) {
        let first = ordinates[index + 1].subtract(&ordinates[index]);
        let second = ordinates[index + 2].subtract(&ordinates[index + 1]);
        relations.push(relation(
            "successive_gap_ratio",
            vec![index, index + 1, index + 2],
            positive_ratio(&second, &first)?,
        ));
    }
    for index in 0..ordinates.len().saturating_sub(3) {
        let a_minus_c = ordinates[index].subtract(&ordinates[index + 2]);
        let b_minus_d = ordinates[index + 1].subtract(&ordinates[index + 3]);
        let a_minus_d = ordinates[index].subtract(&ordinates[index + 3]);
        let b_minus_c = ordinates[index + 1].subtract(&ordinates[index + 2]);
        let cross_ratio = a_minus_c
            .multiply(&b_minus_d)
            .divide(&a_minus_d.multiply(&b_minus_c))
            .map_err(|error| error.to_string())?;
        relations.push(relation(
            "ordered_projective_cross_ratio",
            vec![index, index + 1, index + 2, index + 3],
            cross_ratio,
        ));
    }

    let mut moments = Vec::new();
    for order in 1..=4u32 {
        let mut sum = RatInterval::point(Rat::zero());
        for ordinate in &ordinates {
            let powered = interval_power(ordinate, 2 * order);
            sum = sum.add(
                &RatInterval::point(Rat::one())
                    .divide(&powered)
                    .map_err(|error| error.to_string())?,
            );
        }
        moments.push(ReciprocalMoment { order, value: sum });
    }
    Ok((relations, moments))
}

fn require(condition: bool, message: impl Into<String>) -> Result<(), String> {
    if condition {
        Ok(())
    } else {
        Err(message.into())
    }
}

fn interval_contains(container: &RatInterval, contained: &RatInterval) -> bool {
    container.lower <= contained.lower && container.upper >= contained.upper
}

fn complex_interval_contains(container: &ComplexInterval, contained: &ComplexInterval) -> bool {
    interval_contains(&container.re, &contained.re)
        && interval_contains(&container.im, &contained.im)
}

fn transformed_ray_point_for_verification(point: &RatComplex, parameter: i64) -> RatComplex {
    let k = integer(parameter);
    RatComplex::new(&point.re + &k * &point.im, &point.im - k * &point.re)
}

fn stored_polygon_winding(receipt: &WindingReceipt) -> Result<i32, String> {
    let transformed = receipt
        .polygon
        .iter()
        .map(|point| transformed_ray_point_for_verification(point, receipt.ray_parameter))
        .collect::<Vec<_>>();
    require(
        !transformed.iter().any(|point| point.im.is_zero()),
        "stored winding ray intersects a polygon vertex",
    )?;
    let mut winding = 0i32;
    for index in 0..transformed.len() {
        let start = &transformed[index];
        let end = &transformed[(index + 1) % transformed.len()];
        let cross = start.cross(end);
        if start.im.is_negative() && end.im.is_positive() && cross.is_positive() {
            winding += 1;
        } else if start.im.is_positive() && end.im.is_negative() && cross.is_negative() {
            winding -= 1;
        }
    }
    Ok(winding)
}

fn verify_winding(receipt: &WindingReceipt, label: &str) -> Result<(), String> {
    require(
        !receipt.segments.is_empty(),
        format!("{label}: empty boundary receipt"),
    )?;
    // The net and the two arms are two readings of one crossing population and must agree.
    require(
        receipt.crossings.winding() == receipt.winding,
        format!("{label}: the net winding disagrees with the crossing arms"),
    )?;
    // Every crossing carries a segment address and every address resolves.
    for index in receipt
        .crossings
        .with_the_turn
        .iter()
        .chain(receipt.crossings.against_the_turn.iter())
    {
        require(
            *index < receipt.polygon.len(),
            format!("{label}: crossing address {index} is outside the boundary"),
        )?;
    }
    require(
        receipt.segments.len() == receipt.polygon.len(),
        format!("{label}: segment/polygon extent differs"),
    )?;
    for index in 0..receipt.segments.len() {
        let segment = &receipt.segments[index];
        let next = &receipt.segments[(index + 1) % receipt.segments.len()];
        require(
            !segment.image.contains_origin(),
            format!("{label}: segment {index} image contains the origin"),
        )?;
        require(
            segment.end == next.start,
            format!("{label}: segment {index} does not meet its successor"),
        )?;
        require(
            segment.end_value == next.start_value,
            format!("{label}: segment {index} endpoint image is discontinuous"),
        )?;
        require(
            complex_interval_contains(&segment.image, &segment.start_value)
                && complex_interval_contains(&segment.image, &segment.end_value),
            format!("{label}: segment {index} image omits an endpoint"),
        )?;
        require(
            receipt.polygon[index] == segment.start_value.midpoint(),
            format!("{label}: polygon vertex {index} is not the stored midpoint"),
        )?;
    }
    require(
        stored_polygon_winding(receipt)? == receipt.winding,
        format!("{label}: stored winding does not re-derive"),
    )
}

fn verify_current(
    current: &EtaCurrentReceipt,
    final_receiver: &ComplexReceiverBox,
    config: &ExactSeriesConfig,
    label: &str,
) -> Result<(), String> {
    require(
        current.receiver.sigma == RatInterval::point(rat(1, 2)),
        format!("{label}: current is not received on sigma=1/2"),
    )?;
    require(
        current.receiver.tau == RatInterval::point(final_receiver.tau.midpoint()),
        format!("{label}: current does not use the final receiver midpoint"),
    )?;
    require(
        current.terms.len() == 96,
        format!("{label}: partial-current extent is not 96"),
    )?;
    let mut partial = ComplexInterval::zero();
    for (index, term) in current.terms.iter().enumerate() {
        let ordinal = (index + 1) as u32;
        require(
            term.ordinal == ordinal,
            format!("{label}: term {ordinal} has the wrong ordinal"),
        )?;
        require(
            term.hand == if ordinal % 2 == 1 { 1 } else { -1 },
            format!("{label}: term {ordinal} has the wrong causal hand"),
        )?;
        let reconstructed = term.valuations.iter().fold(1u32, |product, valuation| {
            product * valuation.prime.pow(valuation.exponent)
        });
        require(
            reconstructed == ordinal,
            format!("{label}: term {ordinal} prime valuations do not reconstruct it"),
        )?;
        partial = partial
            .add(&term.contribution)
            .round_out(config.dyadic_bits);
        require(
            partial == term.partial_sum,
            format!("{label}: term {ordinal} breaks the partial-current recurrence"),
        )?;
    }
    require(
        current.tail_radius.is_positive(),
        format!("{label}: tail radius is not positive"),
    )
}

fn classify_crossing(cross: &RatInterval) -> char {
    if cross.lower.is_positive() {
        '+'
    } else if cross.upper.is_negative() {
        '-'
    } else {
        '0'
    }
}

fn current_turn_word(current: &EtaCurrentReceipt) -> String {
    let mut word = String::with_capacity(current.terms.len().saturating_sub(1));
    for pair in current.terms.windows(2) {
        let left = &pair[0].contribution;
        let right = &pair[1].contribution;
        let cross = left
            .re
            .multiply(&right.im)
            .subtract(&left.im.multiply(&right.re));
        word.push(classify_crossing(&cross));
    }
    word
}

fn turn_positions(current: &EtaCurrentReceipt, requested: char) -> Vec<u32> {
    let mut positions = Vec::new();
    for pair in current.terms.windows(2) {
        let left = &pair[0].contribution;
        let right = &pair[1].contribution;
        let cross = left
            .re
            .multiply(&right.im)
            .subtract(&left.im.multiply(&right.re));
        if classify_crossing(&cross) == requested {
            positions.push(pair[0].ordinal);
        }
    }
    positions
}

fn certified_axis_crossings(current: &EtaCurrentReceipt) -> (usize, usize) {
    let mut real_axis = 0usize;
    let mut imaginary_axis = 0usize;
    for pair in current.terms.windows(2) {
        let left = &pair[0].partial_sum;
        let right = &pair[1].partial_sum;
        let crosses_real = (left.im.upper.is_negative() && right.im.lower.is_positive())
            || (left.im.lower.is_positive() && right.im.upper.is_negative());
        let crosses_imaginary = (left.re.upper.is_negative() && right.re.lower.is_positive())
            || (left.re.lower.is_positive() && right.re.upper.is_negative());
        if crosses_real {
            real_axis += 1;
        }
        if crosses_imaginary {
            imaginary_axis += 1;
        }
    }
    (real_axis, imaginary_axis)
}

fn nearest_partial_returns(current: &EtaCurrentReceipt, count: usize) -> Vec<u32> {
    let mut ranked = current
        .terms
        .iter()
        .map(|term| (term.partial_sum.l1_upper(), term.ordinal))
        .collect::<Vec<_>>();
    ranked.sort_by(|left, right| left.0.cmp(&right.0).then(left.1.cmp(&right.1)));
    ranked
        .into_iter()
        .take(count)
        .map(|(_, ordinal)| ordinal)
        .collect()
}

fn verify_artifact(path: &PathBuf) -> Result<(), String> {
    let encoded = fs::read_to_string(path).map_err(|error| error.to_string())?;
    let atlas: EtaRatioAtlas = ron::from_str(&encoded).map_err(|error| error.to_string())?;
    require(
        atlas.schema == "laboratory.holonic-eta-ratio-atlas.v1",
        "unexpected atlas schema",
    )?;
    require(!atlas.bands.is_empty(), "atlas contains no integer bands")?;
    require(
        atlas.physical_workers > 0,
        "atlas records no physical worker",
    )?;

    for (index, band) in atlas.bands.iter().enumerate() {
        require(
            band.ordinal == index,
            format!("band {index}: ordinal discontinuity"),
        )?;
        require(
            band.winding.receiver.sigma == atlas.scan.sigma,
            format!("band {index}: sigma receiver differs from the scan"),
        )?;
        let expected_lower = &atlas.scan.tau.lower + integer(index as i64);
        require(
            band.winding.receiver.tau
                == RatInterval::new(expected_lower.clone(), expected_lower + integer(1)),
            format!("band {index}: tau receiver is not the contiguous integer band"),
        )?;
        verify_winding(&band.winding, &format!("band {index}"))?;
    }
    let expected_upper = &atlas.scan.tau.lower + integer(atlas.bands.len() as i64);
    require(
        expected_upper == atlas.scan.tau.upper,
        "integer bands do not cover the declared scan",
    )?;

    for (index, lineage) in atlas.zero_lineages.iter().enumerate() {
        let label = format!("lineage {index}");
        require(
            lineage.ordinal == index,
            format!("{label}: ordinal discontinuity"),
        )?;
        require(
            lineage.root.winding == 1,
            format!("{label}: root is not one positively oriented closure"),
        )?;
        require(
            atlas.bands.iter().any(|band| band.winding == lineage.root),
            format!("{label}: root is absent from the band population"),
        )?;
        verify_winding(&lineage.root, &format!("{label} root"))?;
        let mut current = lineage.root.clone();
        for (step_index, step) in lineage.refinements.iter().enumerate() {
            require(
                step.grain == (step_index + 1) as u32,
                format!("{label}: refinement grain discontinuity"),
            )?;
            require(
                step.left.receiver.sigma == current.receiver.sigma
                    && step.right.receiver.sigma == current.receiver.sigma,
                format!("{label}: refinement changed the sigma receiver"),
            )?;
            require(
                step.left.receiver.tau.lower == current.receiver.tau.lower
                    && step.left.receiver.tau.upper == step.split
                    && step.right.receiver.tau.lower == step.split
                    && step.right.receiver.tau.upper == current.receiver.tau.upper,
                format!("{label}: refinement children do not partition their parent"),
            )?;
            require(
                step.left.winding + step.right.winding == current.winding,
                format!("{label}: refinement winding is not additive"),
            )?;
            require(
                matches!((step.left.winding, step.right.winding), (1, 0) | (0, 1)),
                format!("{label}: refinement does not select one closure"),
            )?;
            verify_winding(&step.left, &format!("{label} grain {} left", step.grain))?;
            verify_winding(&step.right, &format!("{label} grain {} right", step.grain))?;
            current = match step.selected.as_str() {
                "left" if step.left.winding == 1 => step.left.clone(),
                "right" if step.right.winding == 1 => step.right.clone(),
                _ => {
                    return Err(format!(
                        "{label}: refinement selection contradicts its winding"
                    ));
                }
            };
        }
        require(
            lineage.final_receiver == current.receiver,
            format!("{label}: final receiver is not the carried child"),
        )?;
        require(
            &lineage.final_receiver.sigma.lower + &lineage.final_receiver.sigma.upper == Rat::one(),
            format!("{label}: receiver is not reflection-symmetric"),
        )?;
        verify_current(
            &lineage.midpoint_current,
            &lineage.final_receiver,
            &atlas.config,
            &label,
        )?;
    }

    let nonzero_bands = atlas
        .bands
        .iter()
        .filter(|band| band.winding.winding != 0)
        .count();
    require(
        nonzero_bands == atlas.zero_lineages.len(),
        "nonzero band population and lineage population differ",
    )?;
    let (relations, moments) = derive_relations(&atlas.zero_lineages)?;
    require(
        relations == atlas.interval_relations,
        "stored interval relations do not re-derive",
    )?;
    require(
        moments == atlas.reciprocal_moments,
        "stored reciprocal moments do not re-derive",
    )?;

    println!(
        "VERIFIED schema={} bands={} winding_sum={} closures={} refinements={} workers={}",
        atlas.schema,
        atlas.bands.len(),
        atlas
            .bands
            .iter()
            .map(|band| band.winding.winding)
            .sum::<i32>(),
        atlas.zero_lineages.len(),
        atlas
            .zero_lineages
            .iter()
            .map(|lineage| lineage.refinements.len())
            .sum::<usize>(),
        atlas.physical_workers,
    );
    for lineage in &atlas.zero_lineages {
        let (real_crossings, imaginary_crossings) =
            certified_axis_crossings(&lineage.midpoint_current);
        let turn_word = current_turn_word(&lineage.midpoint_current);
        let positive_turns = turn_word.chars().filter(|turn| *turn == '+').count();
        let negative_turns = turn_word.chars().filter(|turn| *turn == '-').count();
        let unresolved_turns = turn_word.chars().filter(|turn| *turn == '0').count();
        println!(
            "PATH zero={} tau={} turns=+{}/-{}/open{} negative_turn_edges={:?} axis_crossings=real:{}/imaginary:{} nearest_partial_returns={:?}",
            lineage.ordinal,
            lineage.final_receiver.tau,
            positive_turns,
            negative_turns,
            unresolved_turns,
            turn_positions(&lineage.midpoint_current, '-'),
            real_crossings,
            imaginary_crossings,
            nearest_partial_returns(&lineage.midpoint_current, 8),
        );
    }
    for relation in &atlas.interval_relations {
        println!(
            "RELATION {} {:?}={} cf={:?}",
            relation.kind, relation.members, relation.value, relation.common_continued_fraction,
        );
    }
    for moment in &atlas.reciprocal_moments {
        let rebased = moment.value.round_out(24);
        println!(
            "MOMENT order={} dyadic_outer={} cf={:?}",
            moment.order,
            rebased,
            interval_common_continued_fraction(&moment.value, 16),
        );
    }
    println!("artifact={}", path.display());
    Ok(())
}

fn main() -> Result<(), String> {
    let arguments = env::args().skip(1).collect::<Vec<_>>();
    if arguments.first().map(String::as_str) == Some("verify") {
        let path = arguments
            .get(1)
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from("holonic-eta-ratio-atlas.ron"));
        return verify_artifact(&path);
    }
    let lower = arguments
        .first()
        .map(|value| value.parse::<i64>().map_err(|error| error.to_string()))
        .transpose()?
        .unwrap_or(12);
    let upper = arguments
        .get(1)
        .map(|value| value.parse::<i64>().map_err(|error| error.to_string()))
        .transpose()?
        .unwrap_or(36);
    let output = arguments
        .get(2)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("holonic-eta-ratio-atlas.ron"));
    let available = thread::available_parallelism()
        .map(|count| count.get())
        .unwrap_or(1);
    let workers = arguments
        .get(3)
        .map(|value| value.parse::<usize>().map_err(|error| error.to_string()))
        .transpose()?
        .unwrap_or(available.div_ceil(2))
        .max(1)
        .min((upper - lower).max(1) as usize);
    let refinement_grains = arguments
        .get(4)
        .map(|value| value.parse::<u32>().map_err(|error| error.to_string()))
        .transpose()?
        .unwrap_or(6);
    if lower >= upper {
        return Err("the scan height must have positive extent".to_owned());
    }

    let config = exact_config();
    let started = Instant::now();
    let bands = scan_integer_bands(lower, upper, workers, &config)?;
    let roots = bands
        .iter()
        .filter(|band| band.winding.winding != 0)
        .map(|band| (band.ordinal, band.winding.clone()))
        .collect::<Vec<_>>();
    let zero_lineages = refine_lineages(roots, refinement_grains, &config)?;
    let (interval_relations, reciprocal_moments) = derive_relations(&zero_lineages)?;

    let atlas = EtaRatioAtlas {
        schema: "laboratory.holonic-eta-ratio-atlas.v1".to_owned(),
        arithmetic: "BigInt/BigRational only; every transcendental is a rational series enclosure; every grain projection rounds outwards".to_owned(),
        source_function: "eta(s)=sum_(n>=1)(-1)^(n-1)n^(-s)=(1-2^(1-s))zeta(s)".to_owned(),
        receiver_law: "each rational sigma/tau box is mapped through Euler--Maclaurin with exact Bernoulli corrections and a rational remainder; its boundary winding is invariant under the certified nonzero segment homotopies".to_owned(),
        symmetry_read: "a reflection-symmetric receiver containing exactly one nontrivial zeta zero fixes that zero under rho -> 1-conjugate(rho), hence sigma=1/2".to_owned(),
        scan: receiver(RatInterval::new(integer(lower), integer(upper))),
        config,
        physical_workers: workers,
        elapsed_milliseconds: started
            .elapsed()
            .as_millis()
            .min(u128::from(u64::MAX)) as u64,
        bands,
        zero_lineages,
        interval_relations,
        reciprocal_moments,
    };

    if let Some(parent) = output.parent().filter(|path| !path.as_os_str().is_empty()) {
        fs::create_dir_all(parent).map_err(|error| error.to_string())?;
    }
    let pretty = ron::ser::PrettyConfig::new()
        .depth_limit(128)
        .separate_tuple_members(true)
        .enumerate_arrays(true);
    let encoded = ron::ser::to_string_pretty(&atlas, pretty).map_err(|error| error.to_string())?;
    fs::write(&output, encoded).map_err(|error| error.to_string())?;

    println!(
        "exact eta atlas: bands={} closures={} workers={} elapsed_ms={}",
        atlas.bands.len(),
        atlas.zero_lineages.len(),
        atlas.physical_workers,
        atlas.elapsed_milliseconds
    );
    for lineage in &atlas.zero_lineages {
        // What the bisection discarded, and whether the discarded half was doing work.
        //
        // A half is dropped on `winding == 0`, which is correct by the argument principle. It is
        // not the same as *the image never approached the ray*: a half whose crossings cancel met
        // the ray and came back. Until the two crossing arms were retained this atlas could not
        // tell the two apart, and a net winding still cannot. `CLAUDE.md` §2b.
        let (mut discarded, mut cancelling, mut crossings_dropped) = (0usize, 0usize, 0usize);
        for step in &lineage.refinements {
            let dropped = if step.selected == "left" {
                &step.right
            } else {
                &step.left
            };
            discarded += 1;
            crossings_dropped += dropped.crossings.total();
            if dropped.crossings.cancels() {
                cancelling += 1;
            }
        }
        println!(
            "zero {} tau={} root_winding={} refinement_grains={} discarded={} of_which_cancelling={} crossings_in_discarded={}",
            lineage.ordinal,
            lineage.final_receiver.tau,
            lineage.root.winding,
            lineage.refinements.len(),
            discarded,
            cancelling,
            crossings_dropped
        );
    }
    for relation in &atlas.interval_relations {
        println!(
            "{} {:?}={} cf={:?}",
            relation.kind, relation.members, relation.value, relation.common_continued_fraction
        );
    }
    println!("artifact={}", output.display());
    Ok(())
}
