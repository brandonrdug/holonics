//! Exact boundary transport and winding receivers.

use super::*;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BoundarySegmentReceipt {
    pub start: RatComplex,
    pub end: RatComplex,
    pub start_value: ComplexInterval,
    pub end_value: ComplexInterval,
    pub image: ComplexInterval,
    pub depth: u32,
}

/// The ray crossings of one closed boundary, held as two arms and never netted.
///
/// A winding number is what survives after the two hands are subtracted, and the subtraction is
/// exactly the deletion `CLAUDE.md` §2b names: it keeps the magnitude and discards which passages
/// produced it. Both arms are kept here, **by segment index**, so a receiver can ask not only *how
/// many times did the image enclose the origin* but *where on this boundary is the image doing
/// work*. Those are different questions and only the second can say which half to subdivide.
///
/// `winding()` is the group completion and is what the argument principle counts; it is a reading
/// of the arms and never replaces them. A boundary whose image crosses the ray four times and
/// encloses nothing is not the same object as one that never approaches it, and `winding == 0`
/// cannot tell them apart.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct RayCrossings {
    /// Indices of the polygon segments crossing the ray upward, in boundary order.
    pub with_the_turn: Vec<usize>,
    /// Indices of the polygon segments crossing the ray downward, in boundary order.
    pub against_the_turn: Vec<usize>,
}

impl RayCrossings {
    /// The argument-principle winding: the two arms, group-completed.
    pub fn winding(&self) -> i32 {
        self.with_the_turn.len() as i32 - self.against_the_turn.len() as i32
    }

    /// Every crossing, both hands. Zero exactly when the image never meets the ray.
    pub fn total(&self) -> usize {
        self.with_the_turn.len() + self.against_the_turn.len()
    }

    /// The image crosses the ray and still encloses nothing.
    ///
    /// This is the case a net winding cannot report, and it is the one that says a half is worth
    /// subdividing rather than discarding.
    pub fn cancels(&self) -> bool {
        self.total() > 0 && self.winding() == 0
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WindingReceipt {
    pub receiver: ComplexReceiverBox,
    /// `crossings.winding()`, carried for readers that want the group completion directly.
    pub winding: i32,
    pub crossings: RayCrossings,
    pub ray_parameter: i64,
    pub segments: Vec<BoundarySegmentReceipt>,
    pub polygon: Vec<RatComplex>,
}

pub(super) fn receiver_segment(start: &RatComplex, end: &RatComplex) -> ComplexReceiverBox {
    ComplexReceiverBox::new(
        RatInterval::new(
            min(start.re.clone(), end.re.clone()),
            max(start.re.clone(), end.re.clone()),
        ),
        RatInterval::new(
            min(start.im.clone(), end.im.clone()),
            max(start.im.clone(), end.im.clone()),
        ),
    )
}

pub(super) fn certify_boundary_segment(
    start: RatComplex,
    start_image: ComplexInterval,
    end: RatComplex,
    end_image: ComplexInterval,
    depth: u32,
    max_depth: u32,
    config: &ExactSeriesConfig,
    second_derivative_bound: &Rat,
    output: &mut Vec<BoundarySegmentReceipt>,
) -> Result<(), ExactAnalysisError> {
    let receiver = receiver_segment(&start, &end);
    let midpoint = RatComplex::new(
        (&start.re + &end.re) / integer(2),
        (&start.im + &end.im) / integer(2),
    );
    let midpoint_jet = eta_evaluate_jet(
        &ComplexReceiverBox::point(midpoint.re.clone(), midpoint.im.clone()),
        config,
    )?;
    let midpoint_image = midpoint_jet.value;
    let derivative_bound = midpoint_jet.derivative.l1_upper();
    let parameter_radius = (receiver.sigma.width() + receiver.tau.width()) / integer(2);
    let transport_radius = &parameter_radius * derivative_bound
        + &parameter_radius * &parameter_radius * second_derivative_bound / integer(2);
    let mut image = midpoint_image.add_disc(&transport_radius);
    image = image.hull(&start_image).hull(&end_image);

    if !image.contains_origin() {
        output.push(BoundarySegmentReceipt {
            start,
            end,
            start_value: start_image,
            end_value: end_image,
            image,
            depth,
        });
        return Ok(());
    }
    if depth >= max_depth {
        return Err(ExactAnalysisError::UnresolvedBoundary(depth));
    }
    certify_boundary_segment(
        start.clone(),
        start_image,
        midpoint.clone(),
        midpoint_image.clone(),
        depth + 1,
        max_depth,
        config,
        second_derivative_bound,
        output,
    )?;
    certify_boundary_segment(
        midpoint,
        midpoint_image,
        end,
        end_image,
        depth + 1,
        max_depth,
        config,
        second_derivative_bound,
        output,
    )
}

pub(super) fn transformed_ray_point(point: &RatComplex, parameter: i64) -> RatComplex {
    let k = integer(parameter);
    RatComplex::new(&point.re + &k * &point.im, &point.im - k * &point.re)
}

pub fn polygon_winding(polygon: &[RatComplex]) -> Result<(RayCrossings, i64), ExactAnalysisError> {
    for parameter in 0..=32i64 {
        let transformed = polygon
            .iter()
            .map(|point| transformed_ray_point(point, parameter))
            .collect::<Vec<_>>();
        if transformed.iter().any(|point| point.im.is_zero()) {
            continue;
        }
        let mut crossings = RayCrossings::default();
        for index in 0..transformed.len() {
            let start = &transformed[index];
            let end = &transformed[(index + 1) % transformed.len()];
            let cross = start.cross(end);
            if start.im.is_negative() && end.im.is_positive() && cross.is_positive() {
                crossings.with_the_turn.push(index);
            } else if start.im.is_positive() && end.im.is_negative() && cross.is_negative() {
                crossings.against_the_turn.push(index);
            }
        }
        return Ok((crossings, parameter));
    }
    Err(ExactAnalysisError::NoAdmissibleWindingRay)
}

pub fn eta_boundary_winding(
    receiver: &ComplexReceiverBox,
    config: &ExactSeriesConfig,
    max_depth: u32,
) -> Result<WindingReceipt, ExactAnalysisError> {
    let lower_left = RatComplex::new(receiver.sigma.lower.clone(), receiver.tau.lower.clone());
    let lower_right = RatComplex::new(receiver.sigma.upper.clone(), receiver.tau.lower.clone());
    let upper_right = RatComplex::new(receiver.sigma.upper.clone(), receiver.tau.upper.clone());
    let upper_left = RatComplex::new(receiver.sigma.lower.clone(), receiver.tau.upper.clone());

    let mut segments = Vec::new();
    let second_derivative_bound = eta_second_derivative_bound(receiver, config, 64)?;
    let lower_left_image = eta_evaluate(
        &ComplexReceiverBox::point(lower_left.re.clone(), lower_left.im.clone()),
        config,
    )?
    .value;
    let lower_right_image = eta_evaluate(
        &ComplexReceiverBox::point(lower_right.re.clone(), lower_right.im.clone()),
        config,
    )?
    .value;
    let upper_right_image = eta_evaluate(
        &ComplexReceiverBox::point(upper_right.re.clone(), upper_right.im.clone()),
        config,
    )?
    .value;
    let upper_left_image = eta_evaluate(
        &ComplexReceiverBox::point(upper_left.re.clone(), upper_left.im.clone()),
        config,
    )?
    .value;
    for (start, start_image, end, end_image) in [
        (
            lower_left.clone(),
            lower_left_image.clone(),
            lower_right.clone(),
            lower_right_image.clone(),
        ),
        (
            lower_right,
            lower_right_image,
            upper_right.clone(),
            upper_right_image.clone(),
        ),
        (
            upper_right,
            upper_right_image,
            upper_left.clone(),
            upper_left_image.clone(),
        ),
        (upper_left, upper_left_image, lower_left, lower_left_image),
    ] {
        certify_boundary_segment(
            start,
            start_image,
            end,
            end_image,
            0,
            max_depth,
            config,
            &second_derivative_bound,
            &mut segments,
        )?;
    }

    let mut polygon = Vec::with_capacity(segments.len());
    for segment in &segments {
        polygon.push(segment.start_value.midpoint());
    }
    let (crossings, ray_parameter) = polygon_winding(&polygon)?;
    Ok(WindingReceipt {
        receiver: receiver.clone(),
        winding: crossings.winding(),
        crossings,
        ray_parameter,
        segments,
        polygon,
    })
}
