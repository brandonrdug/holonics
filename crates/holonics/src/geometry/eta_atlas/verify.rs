use super::*;

// --- verification ----------------------------------------------------------------------------

pub(super) fn require(condition: bool, message: impl Into<String>) -> Result<(), String> {
    if condition {
        Ok(())
    } else {
        Err(message.into())
    }
}

pub(super) fn interval_contains(container: &RatInterval, contained: &RatInterval) -> bool {
    container.lower <= contained.lower && container.upper >= contained.upper
}

pub(super) fn complex_interval_contains(
    container: &ComplexInterval,
    contained: &ComplexInterval,
) -> bool {
    interval_contains(&container.re, &contained.re)
        && interval_contains(&container.im, &contained.im)
}

pub(super) fn transformed_ray_point_for_verification(
    point: &RatComplex,
    parameter: i64,
) -> RatComplex {
    let k = integer(parameter);
    RatComplex::new(&point.re + &k * &point.im, &point.im - k * &point.re)
}

pub(super) fn stored_polygon_winding(receipt: &WindingReceipt) -> Result<i32, String> {
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

pub fn verify_winding(receipt: &WindingReceipt, label: &str) -> Result<(), String> {
    require(
        !receipt.segments.is_empty(),
        format!("{label}: empty boundary receipt"),
    )?;
    require(
        receipt.crossings.winding() == receipt.winding,
        format!("{label}: the net winding disagrees with the crossing arms"),
    )?;
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
    let receiver = &receipt.receiver;
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
        let on_boundary = |point: &RatComplex| {
            (point.re == receiver.sigma.lower || point.re == receiver.sigma.upper)
                && receiver.tau.lower <= point.im
                && point.im <= receiver.tau.upper
                || (point.im == receiver.tau.lower || point.im == receiver.tau.upper)
                    && receiver.sigma.lower <= point.re
                    && point.re <= receiver.sigma.upper
        };
        require(
            on_boundary(&segment.start) && on_boundary(&segment.end),
            format!("{label}: segment {index} leaves the receiver's boundary"),
        )?;
    }
    require(
        stored_polygon_winding(receipt)? == receipt.winding,
        format!("{label}: stored winding does not re-derive"),
    )
}

pub(super) fn verify_current(
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

pub(super) fn classify_crossing(cross: &RatInterval) -> char {
    if cross.lower.is_positive() {
        '+'
    } else if cross.upper.is_negative() {
        '-'
    } else {
        '0'
    }
}

pub(super) fn current_turn_word(current: &EtaCurrentReceipt) -> String {
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

pub(super) fn turn_positions(current: &EtaCurrentReceipt, requested: char) -> Vec<u32> {
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

pub(super) fn certified_axis_crossings(current: &EtaCurrentReceipt) -> (usize, usize) {
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

pub(super) fn nearest_partial_returns(current: &EtaCurrentReceipt, count: usize) -> Vec<u32> {
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

/// Verify a stored atlas under the law above, without any apparatus: derived starts re-derive,
/// every stored winding re-derives from its own polygon, refinements partition their parents and
/// select one closure, relations and moments re-derive. Returns the report.
pub fn verify_artifact(path: &Path) -> Result<String, String> {
    let encoded = fs::read_to_string(path).map_err(|error| error.to_string())?;
    let atlas: EtaRatioAtlas = ron::from_str(&encoded).map_err(|error| error.to_string())?;
    require(atlas.schema == ATLAS_SCHEMA, "unexpected atlas schema")?;
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
        let derived =
            derive_euler_maclaurin_start(&band.winding.receiver, &atlas.config, atlas.grain_bits)
                .map_err(|error| format!("band {index}: start derivation failed: {error}"))?;
        require(
            derived == band.config,
            format!(
                "band {index}: stored start {} is not the derived start {}",
                band.config.euler_maclaurin_start, derived.euler_maclaurin_start
            ),
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
            lineage.root.winding >= 1,
            format!("{label}: root does not wind positively"),
        )?;
        let root_band = atlas
            .bands
            .iter()
            .find(|band| band.winding == lineage.root)
            .ok_or_else(|| format!("{label}: root is absent from the band population"))?;
        require(
            root_band.config == lineage.config,
            format!("{label}: lineage config differs from its root band's derived config"),
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
                step.left.winding >= 0
                    && step.right.winding >= 0
                    && step.left.winding + step.right.winding == current.winding,
                format!("{label}: refinement winding is not additive"),
            )?;
            verify_winding(&step.left, &format!("{label} grain {} left", step.grain))?;
            verify_winding(&step.right, &format!("{label} grain {} right", step.grain))?;
            current = match step.selected.as_str() {
                "left" if step.left.winding >= 1 => step.left.clone(),
                "right" if step.right.winding >= 1 => step.right.clone(),
                _ => {
                    return Err(format!(
                        "{label}: refinement selection contradicts its winding"
                    ));
                }
            };
        }
        require(
            current.winding == 1,
            format!("{label}: lineage does not end at one closure"),
        )?;
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
            &lineage.config,
            &label,
        )?;
    }
    let winding_sum: i32 = atlas.bands.iter().map(|band| band.winding.winding).sum();
    require(
        winding_sum >= 0 && winding_sum as usize == atlas.zero_lineages.len(),
        "band winding sum and lineage population differ",
    )?;
    for (index, band) in atlas.bands.iter().enumerate() {
        let lineages = atlas
            .zero_lineages
            .iter()
            .filter(|lineage| lineage.root == band.winding)
            .count();
        require(
            band.winding.winding >= 0 && lineages == band.winding.winding as usize,
            format!(
                "band {index}: winding {} but {lineages} lineages",
                band.winding.winding
            ),
        )?;
    }
    let (relations, moments) = derive_relations(&atlas.zero_lineages)?;
    require(
        relations == atlas.interval_relations,
        "stored interval relations do not re-derive",
    )?;
    require(
        moments == atlas.reciprocal_moments,
        "stored reciprocal moments do not re-derive",
    )?;

    let mut report = format!(
        "VERIFIED schema={} apparatus={} bands={} winding_sum={} closures={} refinements={} workers={}\n",
        atlas.schema,
        atlas.apparatus,
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
        report.push_str(&format!(
            "PATH zero={} tau={} turns=+{}/-{}/open{} negative_turn_edges={:?} axis_crossings=real:{}/imaginary:{} nearest_partial_returns={:?}\n",
            lineage.ordinal,
            lineage.final_receiver.tau,
            positive_turns,
            negative_turns,
            unresolved_turns,
            turn_positions(&lineage.midpoint_current, '-'),
            real_crossings,
            imaginary_crossings,
            nearest_partial_returns(&lineage.midpoint_current, 8),
        ));
    }
    for relation in &atlas.interval_relations {
        report.push_str(&format!(
            "RELATION {} {:?}={} cf={:?}\n",
            relation.kind, relation.members, relation.value, relation.common_continued_fraction,
        ));
    }
    for moment in &atlas.reciprocal_moments {
        report.push_str(&format!(
            "MOMENT order={} dyadic_outer={} cf={:?}\n",
            moment.order,
            moment.value.round_out(24),
            interval_common_continued_fraction(&moment.value, 16),
        ));
    }
    Ok(report)
}
