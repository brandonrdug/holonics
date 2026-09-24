use super::*;

/// Where the `O(N)` heads come from. The law that consumes them — tail, remainder, factor,
/// certification, winding — is below and is the same for every source.
pub trait HeadSource {
    /// `Some` heads, one per receiver, or `None` to have the serial owner sum them.
    fn heads(
        &mut self,
        receivers: &[ComplexReceiverBox],
        config: &ExactSeriesConfig,
    ) -> Result<Option<Vec<HeadJet>>, String>;

    fn apparatus(&self) -> String;
}

/// The serial apparatus: no heads supplied, everything summed by `exact_analysis`.
pub struct SerialJets;

impl HeadSource for SerialJets {
    fn heads(
        &mut self,
        _receivers: &[ComplexReceiverBox],
        _config: &ExactSeriesConfig,
    ) -> Result<Option<Vec<HeadJet>>, String> {
        Ok(None)
    }

    fn apparatus(&self) -> String {
        "serial BigRational (exact_analysis)".to_owned()
    }
}

/// Which function's boundary is being certified.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Field {
    /// `eta`, transported by its first derivative with a uniform second-derivative bound: the
    /// zeros are its windings.
    Eta,
    /// The derivative of `zeta`, transported by the second derivative with a uniform
    /// third-derivative bound: the saddles between the zeros' basins are its windings
    /// (Speiser: RH iff none lie left of the mirror).
    ZetaPrime,
}

/// A value and the derivative that transports it, for one field.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldJet {
    pub value: ComplexInterval,
    pub derivative: ComplexInterval,
}

/// The field jets at many receivers: heads from the source, the rest from the serial law.
pub fn field_jets<J: HeadSource + ?Sized>(
    source: &mut J,
    field: Field,
    receivers: &[ComplexReceiverBox],
    config: &ExactSeriesConfig,
) -> Result<Vec<FieldJet>, String> {
    let heads = source.heads(receivers, config)?;
    receivers
        .iter()
        .enumerate()
        .map(|(index, receiver)| {
            let head = heads.as_ref().map(|heads| &heads[index]);
            match field {
                Field::Eta => eta_evaluate_jet_with_head(receiver, config, head)
                    .map(|jet| FieldJet {
                        value: jet.value,
                        derivative: jet.derivative,
                    })
                    .map_err(|error| error.to_string()),
                Field::ZetaPrime => zeta_evaluate_jet2_with_head(receiver, config, head)
                    .map(|jet| FieldJet {
                        value: jet.jet.first,
                        derivative: jet.jet.second,
                    })
                    .map_err(|error| error.to_string()),
            }
        })
        .collect()
}

/// Corner values. With no supplied head the `eta` corners come from `eta_evaluate`, so the
/// serial receipts reproduce the depth-first owner's bit for bit.
pub fn field_values<J: HeadSource + ?Sized>(
    source: &mut J,
    field: Field,
    receivers: &[ComplexReceiverBox],
    config: &ExactSeriesConfig,
) -> Result<Vec<ComplexInterval>, String> {
    let heads = source.heads(receivers, config)?;
    if heads.is_none() && field == Field::Eta {
        return receivers
            .iter()
            .map(|receiver| {
                eta_evaluate(receiver, config)
                    .map(|evaluation| evaluation.value)
                    .map_err(|error| error.to_string())
            })
            .collect();
    }
    receivers
        .iter()
        .enumerate()
        .map(|(index, receiver)| {
            let head = heads.as_ref().map(|heads| &heads[index]);
            match field {
                Field::Eta => eta_evaluate_jet_with_head(receiver, config, head)
                    .map(|jet| jet.value)
                    .map_err(|error| error.to_string()),
                Field::ZetaPrime => zeta_evaluate_jet2_with_head(receiver, config, head)
                    .map(|jet| jet.jet.first)
                    .map_err(|error| error.to_string()),
            }
        })
        .collect()
}

/// The uniform bound on the second derivative of the field over the box: the alternating-series
/// law for `eta`, the Euler--Maclaurin law (third derivative of `zeta`) for its derivative.
pub(super) fn field_second_derivative_bound(
    field: Field,
    receiver: &ComplexReceiverBox,
    config: &ExactSeriesConfig,
) -> Result<Rat, String> {
    match field {
        Field::Eta => {
            eta_second_derivative_bound(receiver, config, 64).map_err(|error| error.to_string())
        }
        Field::ZetaPrime => {
            zeta_derivative_bound_uniform(receiver, config, 3).map_err(|error| error.to_string())
        }
    }
}

/// One boundary edge with its endpoint images, to be certified.
#[derive(Clone, Debug)]
pub struct Edge {
    pub start: RatComplex,
    pub start_value: ComplexInterval,
    pub end: RatComplex,
    pub end_value: ComplexInterval,
}

pub(super) fn point_box(point: &RatComplex) -> ComplexReceiverBox {
    ComplexReceiverBox::point(point.re.clone(), point.im.clone())
}

/// Certify edges breadth-first: every pending midpoint of one depth is one batch to the source.
/// Returns, per edge, its certified segments in boundary order.
pub fn certify_edges<J: HeadSource + ?Sized>(
    source: &mut J,
    field: Field,
    config: &ExactSeriesConfig,
    max_depth: u32,
    second_derivative_bound: &Rat,
    edges: &[Edge],
) -> Result<Vec<Vec<BoundarySegmentReceipt>>, String> {
    enum Slot {
        Pending(Edge, u32),
        Accepted(BoundarySegmentReceipt),
        Split(usize, usize),
    }
    let two = integer(2);
    let mut slots: Vec<Slot> = edges
        .iter()
        .map(|edge| Slot::Pending(edge.clone(), 0))
        .collect();
    loop {
        let pending: Vec<usize> = slots
            .iter()
            .enumerate()
            .filter(|(_, slot)| matches!(slot, Slot::Pending(..)))
            .map(|(index, _)| index)
            .collect();
        if pending.is_empty() {
            break;
        }
        let midpoints: Vec<RatComplex> = pending
            .iter()
            .map(|&index| match &slots[index] {
                Slot::Pending(edge, _) => RatComplex::new(
                    (&edge.start.re + &edge.end.re) / &two,
                    (&edge.start.im + &edge.end.im) / &two,
                ),
                _ => unreachable!(),
            })
            .collect();
        let boxes: Vec<ComplexReceiverBox> = midpoints.iter().map(point_box).collect();
        let jets = field_jets(source, field, &boxes, config)?;
        for ((&index, midpoint), jet) in pending.iter().zip(midpoints).zip(jets) {
            let Slot::Pending(edge, depth) =
                std::mem::replace(&mut slots[index], Slot::Split(0, 0))
            else {
                unreachable!()
            };
            let parameter_radius = ((&edge.start.re - &edge.end.re).abs()
                + (&edge.start.im - &edge.end.im).abs())
                / &two;
            let transport_radius = &parameter_radius * jet.derivative.l1_upper()
                + &parameter_radius * &parameter_radius * second_derivative_bound / &two;
            let image = jet
                .value
                .add_disc(&transport_radius)
                .hull(&edge.start_value)
                .hull(&edge.end_value);
            if !image.contains_origin() {
                slots[index] = Slot::Accepted(BoundarySegmentReceipt {
                    start: edge.start,
                    end: edge.end,
                    start_value: edge.start_value,
                    end_value: edge.end_value,
                    image,
                    depth,
                });
                continue;
            }
            if depth >= max_depth {
                return Err(format!(
                    "a boundary segment remained unresolved at depth {depth}"
                ));
            }
            let left = slots.len();
            slots.push(Slot::Pending(
                Edge {
                    start: edge.start,
                    start_value: edge.start_value,
                    end: midpoint.clone(),
                    end_value: jet.value.clone(),
                },
                depth + 1,
            ));
            let right = slots.len();
            slots.push(Slot::Pending(
                Edge {
                    start: midpoint,
                    start_value: jet.value,
                    end: edge.end,
                    end_value: edge.end_value,
                },
                depth + 1,
            ));
            slots[index] = Slot::Split(left, right);
        }
    }
    fn flatten(slots: &[Slot], index: usize, out: &mut Vec<BoundarySegmentReceipt>) {
        match &slots[index] {
            Slot::Accepted(receipt) => out.push(receipt.clone()),
            Slot::Split(left, right) => {
                flatten(slots, *left, out);
                flatten(slots, *right, out);
            }
            Slot::Pending(..) => unreachable!("every slot resolved before flattening"),
        }
    }
    Ok((0..edges.len())
        .map(|root| {
            let mut out = Vec::new();
            flatten(&slots, root, &mut out);
            out
        })
        .collect())
}

pub(super) fn receipt_from_segments(
    receiver: &ComplexReceiverBox,
    segments: Vec<BoundarySegmentReceipt>,
) -> Result<WindingReceipt, String> {
    let polygon: Vec<RatComplex> = segments
        .iter()
        .map(|segment| segment.start_value.midpoint())
        .collect();
    let (crossings, ray_parameter) =
        polygon_winding(&polygon).map_err(|error| error.to_string())?;
    Ok(WindingReceipt {
        receiver: receiver.clone(),
        winding: crossings.winding(),
        crossings,
        ray_parameter,
        segments,
        polygon,
    })
}

/// The boundary winding of one receiver box: corners, four edges, one polygon.
pub fn boundary_winding<J: HeadSource + ?Sized>(
    source: &mut J,
    field: Field,
    receiver: &ComplexReceiverBox,
    config: &ExactSeriesConfig,
    max_depth: u32,
) -> Result<WindingReceipt, String> {
    let corners = [
        RatComplex::new(receiver.sigma.lower.clone(), receiver.tau.lower.clone()),
        RatComplex::new(receiver.sigma.upper.clone(), receiver.tau.lower.clone()),
        RatComplex::new(receiver.sigma.upper.clone(), receiver.tau.upper.clone()),
        RatComplex::new(receiver.sigma.lower.clone(), receiver.tau.upper.clone()),
    ];
    let boxes: Vec<ComplexReceiverBox> = corners.iter().map(point_box).collect();
    let values = field_values(source, field, &boxes, config)?;
    let second_derivative_bound = field_second_derivative_bound(field, receiver, config)?;
    let edges: Vec<Edge> = (0..4)
        .map(|index| Edge {
            start: corners[index].clone(),
            start_value: values[index].clone(),
            end: corners[(index + 1) % 4].clone(),
            end_value: values[(index + 1) % 4].clone(),
        })
        .collect();
    let certified = certify_edges(
        source,
        field,
        config,
        max_depth,
        &second_derivative_bound,
        &edges,
    )?;
    receipt_from_segments(receiver, certified.into_iter().flatten().collect())
}

pub(super) fn reversed(segments: &[BoundarySegmentReceipt]) -> Vec<BoundarySegmentReceipt> {
    segments
        .iter()
        .rev()
        .map(|segment| BoundarySegmentReceipt {
            start: segment.end.clone(),
            end: segment.start.clone(),
            start_value: segment.end_value.clone(),
            end_value: segment.start_value.clone(),
            image: segment.image.clone(),
            depth: segment.depth,
        })
        .collect()
}

/// Split a certified box at height `split`, reusing every certified segment that survives and
/// certifying only the cut and the at most two side segments the cut passes through.
pub fn split_winding<J: HeadSource + ?Sized>(
    source: &mut J,
    field: Field,
    parent: &WindingReceipt,
    split: &Rat,
    config: &ExactSeriesConfig,
    max_depth: u32,
) -> Result<(WindingReceipt, WindingReceipt), String> {
    let receiver = &parent.receiver;
    let (sigma_lower, sigma_upper) = (&receiver.sigma.lower, &receiver.sigma.upper);
    let (tau_lower, tau_upper) = (&receiver.tau.lower, &receiver.tau.upper);
    if !(tau_lower < split && split < tau_upper) {
        return Err("the split must lie strictly inside the receiver's height".to_owned());
    }
    // the parent's four edges, by geometry
    let on = |segment: &BoundarySegmentReceipt, edge: usize| -> bool {
        match edge {
            0 => segment.start.im == *tau_lower && segment.end.im == *tau_lower,
            1 => segment.start.re == *sigma_upper && segment.end.re == *sigma_upper,
            2 => segment.start.im == *tau_upper && segment.end.im == *tau_upper,
            _ => segment.start.re == *sigma_lower && segment.end.re == *sigma_lower,
        }
    };
    let edge_segments = |edge: usize| -> Vec<&BoundarySegmentReceipt> {
        parent
            .segments
            .iter()
            .filter(|segment| on(segment, edge))
            .collect()
    };
    let (bottom, right_side, top, left_side) = (
        edge_segments(0),
        edge_segments(1),
        edge_segments(2),
        edge_segments(3),
    );
    if bottom.len() + right_side.len() + top.len() + left_side.len() != parent.segments.len() {
        return Err("the parent's segments do not partition into its four edges".to_owned());
    }
    let cut_right = RatComplex::new(sigma_upper.clone(), split.clone());
    let cut_left = RatComplex::new(sigma_lower.clone(), split.clone());
    // A cut that lands on an existing segment endpoint must carry that endpoint's stored image:
    // an apparatus may enclose the same point differently through two paths (the serial source
    // reads corners through `eta_evaluate` and midpoints through the jet), and a boundary whose
    // consecutive segments disagree on a shared point is not a boundary.
    let stored_right = right_side
        .iter()
        .find(|segment| segment.end == cut_right)
        .map(|segment| segment.end_value.clone());
    let stored_left = left_side
        .iter()
        .find(|segment| segment.end == cut_left)
        .map(|segment| segment.end_value.clone());
    let (cut_right_value, cut_left_value) = match (stored_right, stored_left) {
        (Some(right), Some(left)) => (right, left),
        (right, left) => {
            let mut wanted = Vec::new();
            if right.is_none() {
                wanted.push(point_box(&cut_right));
            }
            if left.is_none() {
                wanted.push(point_box(&cut_left));
            }
            let mut fresh = field_values(source, field, &wanted, config)?.into_iter();
            let right = right.unwrap_or_else(|| fresh.next().expect("a right cut value"));
            let left = left.unwrap_or_else(|| fresh.next().expect("a left cut value"));
            (right, left)
        }
    };
    let second_derivative_bound = field_second_derivative_bound(field, receiver, config)?;

    // edges to certify: the cut (right to left, the left child's top), then any straddled sides
    let mut edges = vec![Edge {
        start: cut_right.clone(),
        start_value: cut_right_value.clone(),
        end: cut_left.clone(),
        end_value: cut_left_value.clone(),
    }];
    // right side runs upward: split into below/above; a straddler has start.im < split < end.im
    let mut right_below: Vec<BoundarySegmentReceipt> = Vec::new();
    let mut right_above: Vec<BoundarySegmentReceipt> = Vec::new();
    let mut right_straddle: Option<usize> = None;
    for segment in right_side.iter() {
        if segment.end.im <= *split {
            right_below.push((*segment).clone());
        } else if segment.start.im >= *split {
            right_above.push((*segment).clone());
        } else {
            right_straddle = Some(edges.len());
            edges.push(Edge {
                start: segment.start.clone(),
                start_value: segment.start_value.clone(),
                end: cut_right.clone(),
                end_value: cut_right_value.clone(),
            });
            edges.push(Edge {
                start: cut_right.clone(),
                start_value: cut_right_value.clone(),
                end: segment.end.clone(),
                end_value: segment.end_value.clone(),
            });
        }
    }
    // left side runs downward: a straddler has start.im > split > end.im
    let mut left_above: Vec<BoundarySegmentReceipt> = Vec::new();
    let mut left_below: Vec<BoundarySegmentReceipt> = Vec::new();
    let mut left_straddle: Option<usize> = None;
    for segment in left_side.iter() {
        if segment.end.im >= *split {
            left_above.push((*segment).clone());
        } else if segment.start.im <= *split {
            left_below.push((*segment).clone());
        } else {
            left_straddle = Some(edges.len());
            edges.push(Edge {
                start: segment.start.clone(),
                start_value: segment.start_value.clone(),
                end: cut_left.clone(),
                end_value: cut_left_value.clone(),
            });
            edges.push(Edge {
                start: cut_left.clone(),
                start_value: cut_left_value.clone(),
                end: segment.end.clone(),
                end_value: segment.end_value.clone(),
            });
        }
    }
    let certified = certify_edges(
        source,
        field,
        config,
        max_depth,
        &second_derivative_bound,
        &edges,
    )?;
    let cut = certified[0].clone();
    if let Some(index) = right_straddle {
        right_below.extend(certified[index].iter().cloned());
        let mut above = certified[index + 1].clone();
        above.extend(right_above);
        right_above = above;
    }
    if let Some(index) = left_straddle {
        left_above.extend(certified[index].iter().cloned());
        let mut below = certified[index + 1].clone();
        below.extend(left_below);
        left_below = below;
    }
    let mut left_child_segments: Vec<BoundarySegmentReceipt> = Vec::new();
    left_child_segments.extend(bottom.iter().map(|s| (*s).clone()));
    left_child_segments.extend(right_below);
    left_child_segments.extend(cut.iter().cloned());
    left_child_segments.extend(left_below);
    let mut right_child_segments: Vec<BoundarySegmentReceipt> = reversed(&cut);
    right_child_segments.extend(right_above);
    right_child_segments.extend(top.iter().map(|s| (*s).clone()));
    right_child_segments.extend(left_above);
    let left_receiver = ComplexReceiverBox::new(
        receiver.sigma.clone(),
        RatInterval::new(tau_lower.clone(), split.clone()),
    );
    let right_receiver = ComplexReceiverBox::new(
        receiver.sigma.clone(),
        RatInterval::new(split.clone(), tau_upper.clone()),
    );
    Ok((
        receipt_from_segments(&left_receiver, left_child_segments)?,
        receipt_from_segments(&right_receiver, right_child_segments)?,
    ))
}
