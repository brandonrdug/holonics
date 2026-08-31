use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::cuda_refine::CudaRefineExecutor;

use super::{
    digest_json, form_digest, holon_address, DeviceOpticalHolonReceipt, EquationGlyphFibre,
    ExactOpticalIncidenceReceipt, ExactOpticalScale, HierarchicalOpticalPassage,
    NativeEquationConstraintSection, NativeHierarchicalOpticalConsequence, OpticalAlternativeCover,
    OpticalFormMember, OpticalHolon, OpticalHolonGrain, OpticalHolonIncidence,
    OpticalHolonIncidenceKind, OpticalHolonIntervention, OpticalLocalRelation, OpticalObjectClass,
    OpticalObjectClassFace, RepeatedOpticalFormFibre, OPTICAL_HOLON_SCHEMA,
};
use crate::mathematical_source::{OpticalBounds, OpticalPassage, SourceLayoutError};

struct Atom {
    holon: usize,
    bounds: OpticalBounds,
    glyph_ordinal: Option<u32>,
}

#[derive(Clone, Copy)]
struct InternalRelation {
    from: usize,
    to: usize,
    kind: OpticalHolonIncidenceKind,
    class: u8,
}

/// Grow every admitted optical grain from one borrowed N1 passage. The passage remains owned by
/// its caller. The only resident semantic front is the complete atom-pair incidence return.
pub fn grow_optical_holons(
    card: &mut CudaRefineExecutor,
    predecessor: &OpticalPassage,
    intervention: OpticalHolonIntervention,
) -> Result<(HierarchicalOpticalPassage, DeviceOpticalHolonReceipt), SourceLayoutError> {
    let intervention_sha = digest_json(&intervention)?;
    let occurrence = format!(
        "e1/optical-holons/{}/{intervention_sha}",
        predecessor.source_sha256
    );
    let (width, height) = intervened_extent(predecessor, &intervention)?;
    let mut holons = Vec::<OpticalHolon>::new();
    let mut incidences = Vec::<OpticalHolonIncidence>::new();
    let mut component_holons = BTreeMap::<u32, usize>::new();

    for (ordinal, component) in predecessor.components.iter().enumerate() {
        let ordinal = u32::try_from(ordinal).map_err(|_| SourceLayoutError::Extent)?;
        if !admitted(component.bounds, &intervention) {
            continue;
        }
        let bounds = transformed(component.bounds, &intervention)?;
        let shape = digest_json(&(
            "component-shape-v1",
            bounds.right - bounds.left,
            bounds.bottom - bounds.top,
            component.payload_octets,
            component.four_connected_fibre.len(),
        ))?;
        let form_members = vec![OpticalFormMember {
            child_form_sha256: shape,
            relative_bounds: relative(bounds, bounds),
            inherited_face: None,
        }];
        let at = push_holon(
            &occurrence,
            OpticalHolonGrain::Component,
            bounds,
            Vec::new(),
            Vec::new(),
            vec![ordinal],
            None,
            form_members,
            &mut holons,
            &mut incidences,
        )?;
        component_holons.insert(ordinal, at);
    }

    let mut components_claimed_by_glyph = BTreeSet::<u32>::new();
    let mut atoms = Vec::<Atom>::new();
    if let Some(testimony) = predecessor.glyph_testimony.as_ref() {
        let bindings = testimony
            .bindings
            .iter()
            .map(|binding| (binding.glyph_ordinal, binding))
            .collect::<BTreeMap<_, _>>();
        for glyph in &testimony.glyphs {
            if matches!(
                intervention,
                OpticalHolonIntervention::WithoutInheritedGlyph { glyph_ordinal }
                    if glyph_ordinal == glyph.ordinal
            ) || !admitted(glyph.bounds, &intervention)
            {
                continue;
            }
            let bounds = transformed(glyph.bounds, &intervention)?;
            let binding = bindings.get(&glyph.ordinal).ok_or_else(|| {
                SourceLayoutError::OpticalHolon(format!("glyph {} has no binding", glyph.ordinal))
            })?;
            let children = binding
                .component_candidates
                .iter()
                .filter_map(|component| component_holons.get(component).copied())
                .collect::<Vec<_>>();
            components_claimed_by_glyph.extend(
                binding
                    .component_candidates
                    .iter()
                    .filter(|component| component_holons.contains_key(component))
                    .copied(),
            );
            let component_ordinals = children
                .iter()
                .flat_map(|child| holons[*child].component_ordinals.iter().copied())
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>();
            let form_members = children
                .iter()
                .map(|child| OpticalFormMember {
                    child_form_sha256: holons[*child].form_sha256.clone(),
                    relative_bounds: relative(bounds, holons[*child].bounds),
                    inherited_face: None,
                })
                .collect::<Vec<_>>();
            let at = push_holon(
                &occurrence,
                OpticalHolonGrain::GlyphOrSubfigure,
                bounds,
                children,
                vec![glyph.ordinal],
                component_ordinals,
                Some(glyph.utf8_face.clone()),
                form_members,
                &mut holons,
                &mut incidences,
            )?;
            atoms.push(Atom {
                holon: at,
                bounds,
                glyph_ordinal: Some(glyph.ordinal),
            });
        }
    }
    for (component, child) in &component_holons {
        if components_claimed_by_glyph.contains(component) {
            continue;
        }
        let bounds = holons[*child].bounds;
        let form_members = vec![OpticalFormMember {
            child_form_sha256: holons[*child].form_sha256.clone(),
            relative_bounds: relative(bounds, bounds),
            inherited_face: None,
        }];
        let at = push_holon(
            &occurrence,
            OpticalHolonGrain::GlyphOrSubfigure,
            bounds,
            vec![*child],
            Vec::new(),
            vec![*component],
            None,
            form_members,
            &mut holons,
            &mut incidences,
        )?;
        atoms.push(Atom {
            holon: at,
            bounds,
            glyph_ordinal: None,
        });
    }
    atoms.sort_by_key(|atom| {
        (
            atom.bounds.top,
            atom.bounds.left,
            atom.bounds.bottom,
            atom.bounds.right,
            atom.glyph_ordinal,
        )
    });
    if atoms.is_empty() {
        return Err(SourceLayoutError::OpticalHolon(
            "the intervention retained no optical atoms".into(),
        ));
    }

    let scale = scale_of(&atoms)?;
    let pair_count = atoms
        .len()
        .checked_mul(atoms.len().saturating_sub(1))
        .and_then(|pairs| pairs.checked_div(2))
        .ok_or(SourceLayoutError::Extent)?;
    let mut lower = Vec::with_capacity(atoms.len() * 3);
    let mut upper = Vec::with_capacity(atoms.len() * 3);
    for atom in &atoms {
        lower.extend_from_slice(&[atom.bounds.left, atom.bounds.top, 0]);
        upper.extend_from_slice(&[atom.bounds.right, atom.bounds.bottom, 0]);
    }
    let mut task_left = Vec::with_capacity(pair_count);
    let mut task_right = Vec::with_capacity(pair_count);
    for left in 0..atoms.len() {
        for right in left + 1..atoms.len() {
            task_left.push(u32::try_from(left).map_err(|_| SourceLayoutError::Extent)?);
            task_right.push(u32::try_from(right).map_err(|_| SourceLayoutError::Extent)?);
        }
    }
    let aperture_squared = scale
        .line_gap
        .checked_mul(scale.line_gap)
        .ok_or(SourceLayoutError::Extent)?;
    let device = card
        .optical_incidence_on_device(
            &lower,
            &upper,
            &task_left,
            &task_right,
            aperture_squared,
            scale.term_gap,
            scale.line_gap,
        )
        .map_err(|error| SourceLayoutError::Device(error.to_string()))?;
    if device.incidence_words.len() != pair_count || device.contact_classes.len() != pair_count {
        return Err(SourceLayoutError::OpticalDeviceShape);
    }

    let mut internal = Vec::<InternalRelation>::new();
    let mut local_relations = Vec::<OpticalLocalRelation>::new();
    for at in 0..pair_count {
        let left = task_left[at] as usize;
        let right = task_right[at] as usize;
        for (from, to, mask) in [
            (left, right, device.incidence_words[at] as u16),
            (right, left, (device.incidence_words[at] >> 16) as u16),
        ] {
            for kind in relation_kinds() {
                if kind.bit().is_some_and(|bit| mask & bit != 0) {
                    internal.push(InternalRelation {
                        from,
                        to,
                        kind,
                        class: device.contact_classes[at],
                    });
                    local_relations.push(OpticalLocalRelation {
                        from_atom_address: holons[atoms[from].holon].address_sha256.clone(),
                        to_atom_address: holons[atoms[to].holon].address_sha256.clone(),
                        kind,
                        device_contact_class: device.contact_classes[at],
                    });
                }
            }
        }
    }

    let decorated = grow_decorated(&occurrence, &atoms, &internal, &mut holons, &mut incidences)?;
    let term_edges = edge_population(&internal, OpticalHolonIncidenceKind::TermContact);
    let term_groups = connected_groups(atoms.len(), &term_edges);
    let (terms, atom_to_term) = grow_groups(
        &occurrence,
        OpticalHolonGrain::Term,
        &term_groups,
        &atoms,
        &[],
        &mut holons,
        &mut incidences,
    )?;
    let assemblies = grow_assemblies(
        &occurrence,
        &atoms,
        &internal,
        &atom_to_term,
        &decorated,
        &mut holons,
        &mut incidences,
    )?;
    let line_edges = internal
        .iter()
        .filter(|relation| {
            matches!(
                relation.kind,
                OpticalHolonIncidenceKind::LineContact
                    | OpticalHolonIncidenceKind::SuperscriptAttachment
                    | OpticalHolonIncidenceKind::SubscriptAttachment
                    | OpticalHolonIncidenceKind::FractionNumerator
                    | OpticalHolonIncidenceKind::FractionDenominator
                    | OpticalHolonIncidenceKind::RadicalEnclosure
                    | OpticalHolonIncidenceKind::DelimiterAttachment
            )
        })
        .map(|relation| (relation.from, relation.to))
        .collect::<Vec<_>>();
    let line_groups = connected_groups(atoms.len(), &line_edges);
    let line_extras = terms
        .iter()
        .chain(&assemblies)
        .chain(&decorated)
        .copied()
        .collect::<Vec<_>>();
    let (lines, _) = grow_groups(
        &occurrence,
        OpticalHolonGrain::RelationOrEquation,
        &line_groups,
        &atoms,
        &line_extras,
        &mut holons,
        &mut incidences,
    )?;
    let blocks = grow_blocks(&occurrence, &lines, &mut holons, &mut incidences)?;
    let page_children = if blocks.is_empty() {
        lines.clone()
    } else {
        blocks.clone()
    };
    let page_bounds = OpticalBounds {
        left: 0,
        top: 0,
        right: i64::from(width),
        bottom: i64::from(height),
    };
    let page_glyphs = page_children
        .iter()
        .flat_map(|child| holons[*child].glyph_ordinals.iter().copied())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let page_components = page_children
        .iter()
        .flat_map(|child| holons[*child].component_ordinals.iter().copied())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let page_face = inherited_face(&page_children, &holons);
    let page_form = form_members(page_bounds, &page_children, &holons);
    push_holon(
        &occurrence,
        OpticalHolonGrain::Page,
        page_bounds,
        page_children,
        page_glyphs,
        page_components,
        page_face,
        page_form,
        &mut holons,
        &mut incidences,
    )?;

    let classifications = classify(&holons, &internal, &atoms);
    let alternative_covers = alternative_covers(&holons, &incidences, &internal, &atoms);
    let repeated_forms = repeated_forms(&holons, &incidences);
    let native_consequence =
        native_consequence(&holons, &classifications, &terms, &assemblies, &blocks);
    let relation_words_sha256 = digest_json(&(
        "resident-optical-relation-words-v1",
        &device.contact_classes,
        &device.incidence_words,
    ))?;
    let passage = HierarchicalOpticalPassage {
        schema: OPTICAL_HOLON_SCHEMA.to_owned(),
        truth_status: "implemented-exact".to_owned(),
        predecessor_occurrence: predecessor.occurrence.clone(),
        predecessor_source_sha256: predecessor.source_sha256.clone(),
        occurrence,
        width,
        height,
        intervention,
        scale,
        holons,
        incidences,
        local_relations,
        alternative_covers,
        classifications,
        repeated_forms,
        native_consequence,
        relation_receipt: ExactOpticalIncidenceReceipt {
            atom_population: atoms.len() as u64,
            complete_pair_population: pair_count as u64,
            complete_relation_words_sha256: relation_words_sha256,
        },
        productive_transcript_present: false,
        productive_text_layer_present: false,
        productive_anchor_labels_present: false,
    };
    passage.validate()?;
    Ok((
        passage,
        DeviceOpticalHolonReceipt {
            device_name: card.device_name().to_owned(),
            launches: device.launches,
            synchronizations: device.synchronizations,
            host_ingress_octets: device.host_ingress_octets,
            host_egress_octets: device.host_egress_octets,
            resident_octets: device.resident_octets,
            cpu_semantic_fallback: false,
        },
    ))
}

fn push_holon(
    occurrence: &str,
    grain: OpticalHolonGrain,
    bounds: OpticalBounds,
    mut children: Vec<usize>,
    mut glyph_ordinals: Vec<u32>,
    mut component_ordinals: Vec<u32>,
    inherited_face: Option<String>,
    form_members: Vec<OpticalFormMember>,
    holons: &mut Vec<OpticalHolon>,
    incidences: &mut Vec<OpticalHolonIncidence>,
) -> Result<usize, SourceLayoutError> {
    children.sort_unstable();
    children.dedup();
    glyph_ordinals.sort_unstable();
    glyph_ordinals.dedup();
    component_ordinals.sort_unstable();
    component_ordinals.dedup();
    let constituents = children
        .iter()
        .map(|child| holons[*child].address_sha256.clone())
        .collect::<Vec<_>>();
    let form_sha256 = form_digest(grain, &form_members, inherited_face.as_deref())?;
    let address_sha256 = holon_address(occurrence, grain, bounds, &constituents, &form_sha256)?;
    if let Some((at, standing)) = holons
        .iter()
        .enumerate()
        .find(|(_, holon)| holon.address_sha256 == address_sha256)
    {
        if standing.form_sha256 != form_sha256
            || standing.grain != grain
            || standing.bounds != bounds
            || standing.constituents != constituents
            || standing.glyph_ordinals != glyph_ordinals
            || standing.component_ordinals != component_ordinals
            || standing.inherited_face != inherited_face
            || standing.form_members != form_members
        {
            return Err(SourceLayoutError::OpticalHolon(format!(
                "optical occurrence {address_sha256} was addressed twice with different lineage"
            )));
        }
        return Ok(at);
    }
    let at = holons.len();
    holons.push(OpticalHolon {
        address_sha256: address_sha256.clone(),
        form_sha256,
        grain,
        bounds,
        constituents,
        glyph_ordinals,
        component_ordinals,
        inherited_face,
        form_members,
    });
    for child in children {
        incidences.push(OpticalHolonIncidence {
            from_address: holons[child].address_sha256.clone(),
            to_address: address_sha256.clone(),
            kind: OpticalHolonIncidenceKind::Contains,
            device_contact_class: None,
        });
    }
    Ok(at)
}

fn grow_decorated(
    occurrence: &str,
    atoms: &[Atom],
    relations: &[InternalRelation],
    holons: &mut Vec<OpticalHolon>,
    incidences: &mut Vec<OpticalHolonIncidence>,
) -> Result<Vec<usize>, SourceLayoutError> {
    let mut by_base = BTreeMap::<usize, Vec<InternalRelation>>::new();
    for relation in relations.iter().copied().filter(|relation| {
        matches!(
            relation.kind,
            OpticalHolonIncidenceKind::SuperscriptAttachment
                | OpticalHolonIncidenceKind::SubscriptAttachment
        )
    }) {
        by_base.entry(relation.from).or_default().push(relation);
    }
    let mut returned = Vec::new();
    for (base, attachments) in by_base {
        let mut atom_members = vec![base];
        atom_members.extend(attachments.iter().map(|relation| relation.to));
        atom_members.sort_unstable();
        atom_members.dedup();
        let children = atom_members
            .iter()
            .map(|atom| atoms[*atom].holon)
            .collect::<Vec<_>>();
        let bounds = hull(&children, holons)?;
        let glyphs = glyphs(&children, holons);
        let components = components(&children, holons);
        let face = inherited_face(&children, holons);
        let form = form_members(bounds, &children, holons);
        let parent = push_holon(
            occurrence,
            OpticalHolonGrain::DecoratedSymbol,
            bounds,
            children,
            glyphs,
            components,
            face,
            form,
            holons,
            incidences,
        )?;
        for relation in attachments {
            incidences.push(OpticalHolonIncidence {
                from_address: holons[atoms[relation.to].holon].address_sha256.clone(),
                to_address: holons[parent].address_sha256.clone(),
                kind: relation.kind,
                device_contact_class: Some(relation.class),
            });
        }
        returned.push(parent);
    }
    returned.sort_unstable();
    returned.dedup();
    Ok(returned)
}

fn grow_groups(
    occurrence: &str,
    grain: OpticalHolonGrain,
    groups: &[Vec<usize>],
    atoms: &[Atom],
    extras: &[usize],
    holons: &mut Vec<OpticalHolon>,
    incidences: &mut Vec<OpticalHolonIncidence>,
) -> Result<(Vec<usize>, Vec<usize>), SourceLayoutError> {
    let mut atom_to_group = vec![0usize; atoms.len()];
    let mut returned = Vec::new();
    for group in groups {
        let atom_set = group.iter().copied().collect::<BTreeSet<_>>();
        let mut children = group
            .iter()
            .map(|atom| atoms[*atom].holon)
            .collect::<Vec<_>>();
        children.extend(extras.iter().copied().filter(|extra| {
            let glyphs = &holons[*extra].glyph_ordinals;
            !glyphs.is_empty()
                && glyphs.iter().all(|glyph| {
                    atoms.iter().enumerate().any(|(at, atom)| {
                        atom_set.contains(&at) && atom.glyph_ordinal == Some(*glyph)
                    })
                })
        }));
        children.sort_unstable();
        children.dedup();
        let bounds = hull(&children, holons)?;
        let glyph_ordinals = glyphs(&children, holons);
        let component_ordinals = components(&children, holons);
        let inherited_face = inherited_face(&children, holons);
        let form_members = form_members(bounds, &children, holons);
        let parent = push_holon(
            occurrence,
            grain,
            bounds,
            children,
            glyph_ordinals,
            component_ordinals,
            inherited_face,
            form_members,
            holons,
            incidences,
        )?;
        for atom in group {
            atom_to_group[*atom] = parent;
        }
        returned.push(parent);
    }
    Ok((returned, atom_to_group))
}

fn grow_assemblies(
    occurrence: &str,
    atoms: &[Atom],
    relations: &[InternalRelation],
    atom_to_term: &[usize],
    decorated: &[usize],
    holons: &mut Vec<OpticalHolon>,
    incidences: &mut Vec<OpticalHolonIncidence>,
) -> Result<Vec<usize>, SourceLayoutError> {
    let structural = [
        OpticalHolonIncidenceKind::FractionNumerator,
        OpticalHolonIncidenceKind::FractionDenominator,
        OpticalHolonIncidenceKind::RadicalEnclosure,
        OpticalHolonIncidenceKind::DelimiterAttachment,
        OpticalHolonIncidenceKind::DiagramIncidence,
    ];
    let mut by_frame = BTreeMap::<usize, Vec<InternalRelation>>::new();
    for relation in relations
        .iter()
        .copied()
        .filter(|relation| structural.contains(&relation.kind))
    {
        by_frame.entry(relation.from).or_default().push(relation);
    }
    let mut returned = Vec::new();
    for (frame, frame_relations) in by_frame {
        let kinds = frame_relations
            .iter()
            .map(|relation| relation.kind)
            .collect::<BTreeSet<_>>();
        let fraction = kinds.contains(&OpticalHolonIncidenceKind::FractionNumerator)
            && kinds.contains(&OpticalHolonIncidenceKind::FractionDenominator);
        let enclosure = kinds.contains(&OpticalHolonIncidenceKind::RadicalEnclosure)
            || kinds.contains(&OpticalHolonIncidenceKind::DelimiterAttachment);
        let diagram = kinds.contains(&OpticalHolonIncidenceKind::DiagramIncidence);
        if !fraction && !enclosure && !diagram {
            continue;
        }
        let atom_members = std::iter::once(frame)
            .chain(frame_relations.iter().map(|relation| relation.to))
            .collect::<BTreeSet<_>>();
        let member_glyphs = atom_members
            .iter()
            .filter_map(|atom| atoms[*atom].glyph_ordinal)
            .collect::<BTreeSet<_>>();
        let mut children = atom_members
            .iter()
            .map(|atom| atom_to_term[*atom])
            .collect::<BTreeSet<_>>();
        children.extend(decorated.iter().copied().filter(|child| {
            !holons[*child].glyph_ordinals.is_empty()
                && holons[*child]
                    .glyph_ordinals
                    .iter()
                    .all(|glyph| member_glyphs.contains(glyph))
        }));
        let children = children.into_iter().collect::<Vec<_>>();
        let bounds = hull(&children, holons)?;
        let glyph_ordinals = glyphs(&children, holons);
        let component_ordinals = components(&children, holons);
        let inherited_face = inherited_face(&children, holons);
        let form_members = form_members(bounds, &children, holons);
        let parent = push_holon(
            occurrence,
            OpticalHolonGrain::Assembly,
            bounds,
            children,
            glyph_ordinals,
            component_ordinals,
            inherited_face,
            form_members,
            holons,
            incidences,
        )?;
        for relation in frame_relations {
            incidences.push(OpticalHolonIncidence {
                from_address: holons[atoms[relation.to].holon].address_sha256.clone(),
                to_address: holons[parent].address_sha256.clone(),
                kind: relation.kind,
                device_contact_class: Some(relation.class),
            });
        }
        returned.push(parent);
    }
    returned.sort_unstable();
    returned.dedup();
    Ok(returned)
}

fn grow_blocks(
    occurrence: &str,
    lines: &[usize],
    holons: &mut Vec<OpticalHolon>,
    incidences: &mut Vec<OpticalHolonIncidence>,
) -> Result<Vec<usize>, SourceLayoutError> {
    if lines.is_empty() {
        return Ok(Vec::new());
    }
    let mut nearest = Vec::new();
    for (at, line) in lines.iter().enumerate() {
        if let Some(gap) = lines
            .iter()
            .enumerate()
            .filter(|(other, candidate)| {
                *other != at && horizontal_overlap(holons[*line].bounds, holons[**candidate].bounds)
            })
            .map(|(_, candidate)| vertical_gap(holons[*line].bounds, holons[*candidate].bounds))
            .filter(|gap| *gap > 0)
            .min()
        {
            nearest.push(gap);
        }
    }
    if nearest.is_empty() {
        nearest.push(
            lines
                .iter()
                .map(|line| holons[*line].bounds.bottom - holons[*line].bounds.top)
                .max()
                .unwrap_or(1)
                .unsigned_abs(),
        );
    }
    let (_, block_gap) = median_interval(&mut nearest)?;
    let mut edges = Vec::new();
    for left in 0..lines.len() {
        for right in left + 1..lines.len() {
            if horizontal_overlap(holons[lines[left]].bounds, holons[lines[right]].bounds)
                && vertical_gap(holons[lines[left]].bounds, holons[lines[right]].bounds)
                    <= block_gap
            {
                edges.push((left, right));
            }
        }
    }
    let groups = connected_groups(lines.len(), &edges);
    let mut returned = Vec::new();
    for group in groups {
        let children = group.iter().map(|line| lines[*line]).collect::<Vec<_>>();
        let bounds = hull(&children, holons)?;
        let glyph_ordinals = glyphs(&children, holons);
        let component_ordinals = components(&children, holons);
        let inherited_face = inherited_face(&children, holons);
        let form_members = form_members(bounds, &children, holons);
        returned.push(push_holon(
            occurrence,
            OpticalHolonGrain::LabelledOrDiagramBlock,
            bounds,
            children,
            glyph_ordinals,
            component_ordinals,
            inherited_face,
            form_members,
            holons,
            incidences,
        )?);
    }
    Ok(returned)
}

fn classify(
    holons: &[OpticalHolon],
    relations: &[InternalRelation],
    atoms: &[Atom],
) -> Vec<OpticalObjectClassFace> {
    holons
        .iter()
        .map(|holon| {
            let mut classes = match holon.grain {
                OpticalHolonGrain::Component => vec![OpticalObjectClass::RawComponent],
                OpticalHolonGrain::GlyphOrSubfigure => vec![if holon.inherited_face.is_some() {
                    OpticalObjectClass::Glyph
                } else {
                    OpticalObjectClass::UnresolvedSubfigure
                }],
                OpticalHolonGrain::DecoratedSymbol => vec![OpticalObjectClass::DecoratedSymbol],
                OpticalHolonGrain::Term => {
                    vec![if is_mathematical(holon.inherited_face.as_deref()) {
                        OpticalObjectClass::MathematicalTerm
                    } else {
                        OpticalObjectClass::ProseTerm
                    }]
                }
                OpticalHolonGrain::Assembly => assembly_classes(holon, relations, atoms),
                OpticalHolonGrain::RelationOrEquation => vec![if is_equation(holon, holons) {
                    OpticalObjectClass::Equation
                } else {
                    OpticalObjectClass::TextLine
                }],
                OpticalHolonGrain::LabelledOrDiagramBlock => {
                    let equation = holon.constituents.iter().any(|child| {
                        holons.iter().any(|candidate| {
                            candidate.address_sha256 == *child && is_equation(candidate, holons)
                        })
                    });
                    let label = holon.inherited_face.as_deref().is_some_and(|face| {
                        ["Proposition", "Lemma", "Theorem", "Proof"]
                            .iter()
                            .any(|label| face.contains(label))
                    });
                    vec![if equation || label {
                        OpticalObjectClass::LabelledMathematicalBlock
                    } else {
                        OpticalObjectClass::ProseBlock
                    }]
                }
                OpticalHolonGrain::Page => vec![OpticalObjectClass::Page],
            };
            classes.sort();
            classes.dedup();
            OpticalObjectClassFace {
                holon_address: holon.address_sha256.clone(),
                classes,
                inherited_face: holon.inherited_face.clone(),
                classification_routes_geometry: false,
            }
        })
        .collect()
}

fn assembly_classes(
    holon: &OpticalHolon,
    relations: &[InternalRelation],
    atoms: &[Atom],
) -> Vec<OpticalObjectClass> {
    let glyphs = holon
        .glyph_ordinals
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    let mut kinds = BTreeSet::new();
    for relation in relations {
        let from = atoms[relation.from].glyph_ordinal;
        let to = atoms[relation.to].glyph_ordinal;
        if from.is_some_and(|glyph| glyphs.contains(&glyph))
            && to.is_some_and(|glyph| glyphs.contains(&glyph))
        {
            kinds.insert(relation.kind);
        }
    }
    let mut classes = Vec::new();
    if kinds.contains(&OpticalHolonIncidenceKind::FractionNumerator)
        && kinds.contains(&OpticalHolonIncidenceKind::FractionDenominator)
    {
        classes.push(OpticalObjectClass::FractionAssembly);
    }
    if kinds.contains(&OpticalHolonIncidenceKind::RadicalEnclosure)
        || kinds.contains(&OpticalHolonIncidenceKind::DelimiterAttachment)
    {
        classes.push(OpticalObjectClass::RadicalOrDelimiterAssembly);
    }
    if kinds.contains(&OpticalHolonIncidenceKind::DiagramIncidence) {
        classes.push(OpticalObjectClass::DiagramAssembly);
    }
    if classes.is_empty() {
        classes.push(OpticalObjectClass::MathematicalTerm);
    }
    classes
}

fn alternative_covers(
    holons: &[OpticalHolon],
    incidences: &[OpticalHolonIncidence],
    relations: &[InternalRelation],
    atoms: &[Atom],
) -> Vec<OpticalAlternativeCover> {
    let grain = holons
        .iter()
        .map(|holon| (holon.address_sha256.as_str(), holon.grain))
        .collect::<BTreeMap<_, _>>();
    let mut parents = BTreeMap::<String, BTreeMap<OpticalHolonGrain, BTreeSet<String>>>::new();
    for incidence in incidences
        .iter()
        .filter(|incidence| incidence.kind == OpticalHolonIncidenceKind::Contains)
    {
        if let Some(parent_grain) = grain.get(incidence.to_address.as_str()) {
            parents
                .entry(incidence.from_address.clone())
                .or_default()
                .entry(*parent_grain)
                .or_default()
                .insert(incidence.to_address.clone());
        }
    }
    parents
        .into_iter()
        .flat_map(|(subject, by_grain)| {
            by_grain
                .into_values()
                .filter(|set| set.len() > 1)
                .map(move |set| {
                    let atom_at = atoms
                        .iter()
                        .position(|atom| holons[atom.holon].address_sha256 == subject);
                    let separating_relation_kinds = atom_at
                        .map(|at| {
                            relations
                                .iter()
                                .filter(|relation| relation.from == at || relation.to == at)
                                .map(|relation| relation.kind)
                                .collect::<BTreeSet<_>>()
                                .into_iter()
                                .collect()
                        })
                        .unwrap_or_default();
                    OpticalAlternativeCover {
                        subject_address: subject.clone(),
                        alternative_parent_addresses: set.into_iter().collect(),
                        separating_relation_kinds,
                        complete_within_resident_relation_word: true,
                        richer_receiver_reopens: true,
                    }
                })
        })
        .collect()
}

fn repeated_forms(
    holons: &[OpticalHolon],
    incidences: &[OpticalHolonIncidence],
) -> Vec<RepeatedOpticalFormFibre> {
    let mut forms = BTreeMap::<String, Vec<String>>::new();
    for holon in holons.iter().filter(|holon| {
        matches!(
            holon.grain,
            OpticalHolonGrain::GlyphOrSubfigure
                | OpticalHolonGrain::DecoratedSymbol
                | OpticalHolonGrain::Term
                | OpticalHolonGrain::Assembly
        )
    }) {
        forms
            .entry(holon.form_sha256.clone())
            .or_default()
            .push(holon.address_sha256.clone());
    }
    forms
        .into_iter()
        .filter(|(_, occurrences)| occurrences.len() > 1)
        .filter_map(|(form_sha256, occurrence_addresses)| {
            let parent_context_addresses = occurrence_addresses
                .iter()
                .map(|occurrence| {
                    incidences
                        .iter()
                        .filter(|incidence| {
                            incidence.kind == OpticalHolonIncidenceKind::Contains
                                && incidence.from_address == *occurrence
                        })
                        .map(|incidence| incidence.to_address.clone())
                        .collect::<BTreeSet<_>>()
                        .into_iter()
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            let distinct = parent_context_addresses
                .iter()
                .collect::<BTreeSet<_>>()
                .len()
                > 1;
            distinct.then_some(RepeatedOpticalFormFibre {
                form_sha256,
                occurrence_addresses,
                parent_context_addresses,
                occurrences_remain_distinct: true,
                context_covers_distinct: true,
            })
        })
        .collect()
}

fn native_consequence(
    holons: &[OpticalHolon],
    classes: &[OpticalObjectClassFace],
    terms: &[usize],
    assemblies: &[usize],
    blocks: &[usize],
) -> NativeHierarchicalOpticalConsequence {
    let equation_addresses = classes
        .iter()
        .filter(|face| face.classes.contains(&OpticalObjectClass::Equation))
        .map(|face| face.holon_address.clone())
        .collect::<Vec<_>>();
    let equation_glyph_fibres = equation_addresses
        .iter()
        .filter_map(|address| holons.iter().find(|holon| holon.address_sha256 == *address))
        .map(|equation| EquationGlyphFibre {
            equation_address: equation.address_sha256.clone(),
            glyph_holon_addresses: holons
                .iter()
                .filter(|holon| {
                    holon.grain == OpticalHolonGrain::GlyphOrSubfigure
                        && holon
                            .glyph_ordinals
                            .iter()
                            .any(|glyph| equation.glyph_ordinals.contains(glyph))
                })
                .map(|holon| holon.address_sha256.clone())
                .collect(),
            glyph_ordinals: equation.glyph_ordinals.clone(),
            complete_constituent_reconstruction: true,
        })
        .collect::<Vec<_>>();
    let equation_constraint_sections =
        equation_constraint_sections(holons, &equation_addresses, &equation_glyph_fibres);
    NativeHierarchicalOpticalConsequence {
        term_addresses: terms
            .iter()
            .map(|at| holons[*at].address_sha256.clone())
            .collect(),
        assembly_addresses: assemblies
            .iter()
            .map(|at| holons[*at].address_sha256.clone())
            .collect(),
        equation_addresses,
        block_addresses: blocks
            .iter()
            .map(|at| holons[*at].address_sha256.clone())
            .collect(),
        higher_equation_objects_change_native_consequence: !equation_constraint_sections.is_empty(),
        equation_glyph_fibres,
        equation_constraint_sections,
        glyph_fibres_retained: true,
        open_exterior: vec![
            "semantic identity beyond the inherited glyph and exact-geometry receiver remains open"
                .to_owned(),
            "alternative covers remain complete rather than silently selected".to_owned(),
            "future mathematical receivers may split every current object-class quotient"
                .to_owned(),
        ],
    }
}

fn equation_constraint_sections(
    holons: &[OpticalHolon],
    equation_addresses: &[String],
    equation_glyph_fibres: &[EquationGlyphFibre],
) -> Vec<NativeEquationConstraintSection> {
    let mut returned = Vec::new();
    for equation_address in equation_addresses {
        let Some(equation) = holons
            .iter()
            .find(|holon| holon.address_sha256 == *equation_address)
        else {
            continue;
        };
        let complete_glyph_holon_addresses = equation_glyph_fibres
            .iter()
            .find(|fibre| fibre.equation_address == *equation_address)
            .map(|fibre| fibre.glyph_holon_addresses.clone())
            .unwrap_or_default();
        let relation_glyphs = holons.iter().filter(|holon| {
            holon.grain == OpticalHolonGrain::GlyphOrSubfigure
                && holon
                    .glyph_ordinals
                    .iter()
                    .any(|ordinal| equation.glyph_ordinals.contains(ordinal))
                && holon.inherited_face.as_deref().is_some_and(|face| {
                    face.chars()
                        .any(|character| matches!(character, '=' | '<' | '>' | '≤' | '≥' | '≠'))
                })
        });
        for relation in relation_glyphs {
            let relation_center_twice = relation.bounds.left + relation.bounds.right;
            let mut before = Vec::new();
            let mut after = Vec::new();
            let mut crossing = Vec::new();
            for member in holons.iter().filter(|candidate| {
                candidate.address_sha256 != relation.address_sha256
                    && !candidate.glyph_ordinals.is_empty()
                    && candidate
                        .glyph_ordinals
                        .iter()
                        .all(|ordinal| equation.glyph_ordinals.contains(ordinal))
                    && matches!(
                        candidate.grain,
                        OpticalHolonGrain::GlyphOrSubfigure
                            | OpticalHolonGrain::DecoratedSymbol
                            | OpticalHolonGrain::Term
                            | OpticalHolonGrain::Assembly
                    )
            }) {
                if member.bounds.right.saturating_mul(2) <= relation_center_twice {
                    before.push(member.address_sha256.clone());
                } else if member.bounds.left.saturating_mul(2) >= relation_center_twice {
                    after.push(member.address_sha256.clone());
                } else {
                    crossing.push(member.address_sha256.clone());
                }
            }
            before.sort();
            before.dedup();
            after.sort();
            after.dedup();
            crossing.sort();
            crossing.dedup();
            if before.is_empty() || after.is_empty() {
                continue;
            }
            let relation_face = relation.inherited_face.clone().unwrap_or_default();
            let form = digest_json(&(
                "native-equation-constraint-section-v1",
                &equation.form_sha256,
                &relation.form_sha256,
                &relation_face,
                before
                    .iter()
                    .filter_map(|address| {
                        holons
                            .iter()
                            .find(|holon| holon.address_sha256 == *address)
                            .map(|holon| holon.form_sha256.as_str())
                    })
                    .collect::<Vec<_>>(),
                after
                    .iter()
                    .filter_map(|address| {
                        holons
                            .iter()
                            .find(|holon| holon.address_sha256 == *address)
                            .map(|holon| holon.form_sha256.as_str())
                    })
                    .collect::<Vec<_>>(),
                crossing
                    .iter()
                    .filter_map(|address| {
                        holons
                            .iter()
                            .find(|holon| holon.address_sha256 == *address)
                            .map(|holon| holon.form_sha256.as_str())
                    })
                    .collect::<Vec<_>>(),
            ))
            .unwrap_or_default();
            returned.push(NativeEquationConstraintSection {
                equation_address: equation.address_sha256.clone(),
                relation_glyph_address: relation.address_sha256.clone(),
                relation_glyph_ordinals: relation.glyph_ordinals.clone(),
                inherited_relation_face: relation_face,
                before_member_addresses: before,
                after_member_addresses: after,
                crossing_member_addresses: crossing,
                complete_glyph_holon_addresses: complete_glyph_holon_addresses.clone(),
                constraint_form_sha256: form,
                exact_ordered_constraint_geometry: true,
            });
        }
    }
    returned.sort_by(|left, right| {
        (&left.equation_address, &left.relation_glyph_address)
            .cmp(&(&right.equation_address, &right.relation_glyph_address))
    });
    returned
}

fn relation_kinds() -> [OpticalHolonIncidenceKind; 14] {
    [
        OpticalHolonIncidenceKind::BaselineAlignment,
        OpticalHolonIncidenceKind::ReadingTransport,
        OpticalHolonIncidenceKind::SuperscriptAttachment,
        OpticalHolonIncidenceKind::SubscriptAttachment,
        OpticalHolonIncidenceKind::FractionNumerator,
        OpticalHolonIncidenceKind::FractionDenominator,
        OpticalHolonIncidenceKind::RadicalEnclosure,
        OpticalHolonIncidenceKind::DelimiterAttachment,
        OpticalHolonIncidenceKind::MatrixRow,
        OpticalHolonIncidenceKind::MatrixColumn,
        OpticalHolonIncidenceKind::AlignmentRegion,
        OpticalHolonIncidenceKind::DiagramIncidence,
        OpticalHolonIncidenceKind::TermContact,
        OpticalHolonIncidenceKind::LineContact,
    ]
}

fn scale_of(atoms: &[Atom]) -> Result<ExactOpticalScale, SourceLayoutError> {
    let mut heights = atoms
        .iter()
        .map(|atom| {
            u64::try_from(atom.bounds.bottom - atom.bounds.top)
                .map_err(|_| SourceLayoutError::Extent)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut widths = atoms
        .iter()
        .map(|atom| {
            u64::try_from(atom.bounds.right - atom.bounds.left)
                .map_err(|_| SourceLayoutError::Extent)
        })
        .collect::<Result<Vec<_>, _>>()?;
    heights.retain(|extent| *extent > 0);
    widths.retain(|extent| *extent > 0);
    let (lower_median_height, upper_median_height) = median_interval(&mut heights)?;
    let (lower_median_width, upper_median_width) = median_interval(&mut widths)?;
    let mut nearest = Vec::new();
    for (at, atom) in atoms.iter().enumerate() {
        if let Some(gap) = atoms
            .iter()
            .enumerate()
            .filter(|(other, candidate)| {
                *other != at && vertical_overlap(atom.bounds, candidate.bounds)
            })
            .map(|(_, candidate)| horizontal_gap(atom.bounds, candidate.bounds))
            .filter(|gap| *gap > 0)
            .min()
        {
            nearest.push(gap);
        }
    }
    if nearest.is_empty() {
        nearest.push(lower_median_width);
        nearest.push(upper_median_width);
    }
    let (lower_median_nearest_gap, upper_median_nearest_gap) = median_interval(&mut nearest)?;
    let term_gap = upper_median_nearest_gap;
    let line_gap = upper_median_height.max(upper_median_width).max(term_gap);
    Ok(ExactOpticalScale {
        lower_median_height,
        upper_median_height,
        lower_median_width,
        upper_median_width,
        lower_median_nearest_gap,
        upper_median_nearest_gap,
        term_gap,
        line_gap,
        authored_capacity_constant: false,
    })
}

fn median_interval(values: &mut [u64]) -> Result<(u64, u64), SourceLayoutError> {
    if values.is_empty() {
        return Err(SourceLayoutError::OpticalHolon(
            "an optical scale population is empty".into(),
        ));
    }
    values.sort_unstable();
    Ok((values[(values.len() - 1) / 2], values[values.len() / 2]))
}

fn edge_population(
    relations: &[InternalRelation],
    kind: OpticalHolonIncidenceKind,
) -> Vec<(usize, usize)> {
    relations
        .iter()
        .filter(|relation| relation.kind == kind)
        .map(|relation| (relation.from, relation.to))
        .collect()
}

fn connected_groups(population: usize, edges: &[(usize, usize)]) -> Vec<Vec<usize>> {
    let mut parent = (0..population).collect::<Vec<_>>();
    fn root(parent: &mut [usize], mut at: usize) -> usize {
        while parent[at] != at {
            parent[at] = parent[parent[at]];
            at = parent[at];
        }
        at
    }
    for (left, right) in edges {
        let a = root(&mut parent, *left);
        let b = root(&mut parent, *right);
        if a != b {
            let lower = a.min(b);
            parent[a] = lower;
            parent[b] = lower;
        }
    }
    let mut groups = BTreeMap::<usize, Vec<usize>>::new();
    for at in 0..population {
        let label = root(&mut parent, at);
        groups.entry(label).or_default().push(at);
    }
    groups.into_values().collect()
}

fn form_members(
    bounds: OpticalBounds,
    children: &[usize],
    holons: &[OpticalHolon],
) -> Vec<OpticalFormMember> {
    children
        .iter()
        .map(|child| OpticalFormMember {
            child_form_sha256: holons[*child].form_sha256.clone(),
            relative_bounds: relative(bounds, holons[*child].bounds),
            inherited_face: holons[*child].inherited_face.clone(),
        })
        .collect()
}

fn inherited_face(children: &[usize], holons: &[OpticalHolon]) -> Option<String> {
    let face = children
        .iter()
        .filter_map(|child| holons[*child].inherited_face.as_deref())
        .collect::<Vec<_>>()
        .join("");
    (!face.is_empty()).then_some(face)
}

fn glyphs(children: &[usize], holons: &[OpticalHolon]) -> Vec<u32> {
    children
        .iter()
        .flat_map(|child| holons[*child].glyph_ordinals.iter().copied())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn components(children: &[usize], holons: &[OpticalHolon]) -> Vec<u32> {
    children
        .iter()
        .flat_map(|child| holons[*child].component_ordinals.iter().copied())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn hull(children: &[usize], holons: &[OpticalHolon]) -> Result<OpticalBounds, SourceLayoutError> {
    let first = children
        .first()
        .map(|child| holons[*child].bounds)
        .ok_or_else(|| {
            SourceLayoutError::OpticalHolon("a higher optical holon has no child".into())
        })?;
    Ok(children.iter().skip(1).fold(first, |bounds, child| {
        let next = holons[*child].bounds;
        OpticalBounds {
            left: bounds.left.min(next.left),
            top: bounds.top.min(next.top),
            right: bounds.right.max(next.right),
            bottom: bounds.bottom.max(next.bottom),
        }
    }))
}

fn relative(parent: OpticalBounds, child: OpticalBounds) -> OpticalBounds {
    OpticalBounds {
        left: child.left - parent.left,
        top: child.top - parent.top,
        right: child.right - parent.left,
        bottom: child.bottom - parent.top,
    }
}

fn is_mathematical(face: Option<&str>) -> bool {
    face.is_some_and(|face| {
        face.chars()
            .any(|character| !character.is_alphabetic() && !character.is_whitespace())
    })
}

fn is_equation(holon: &OpticalHolon, holons: &[OpticalHolon]) -> bool {
    holons
        .iter()
        .filter(|candidate| {
            candidate.grain == OpticalHolonGrain::GlyphOrSubfigure
                && candidate
                    .glyph_ordinals
                    .iter()
                    .any(|ordinal| holon.glyph_ordinals.contains(ordinal))
                && candidate.inherited_face.as_deref().is_some_and(|face| {
                    face.chars()
                        .any(|character| matches!(character, '=' | '<' | '>' | '≤' | '≥' | '≠'))
                })
        })
        .any(|relation| {
            let center_twice = relation.bounds.left + relation.bounds.right;
            let members = holons.iter().filter(|candidate| {
                candidate.address_sha256 != relation.address_sha256
                    && !candidate.glyph_ordinals.is_empty()
                    && candidate
                        .glyph_ordinals
                        .iter()
                        .all(|ordinal| holon.glyph_ordinals.contains(ordinal))
                    && matches!(
                        candidate.grain,
                        OpticalHolonGrain::GlyphOrSubfigure
                            | OpticalHolonGrain::DecoratedSymbol
                            | OpticalHolonGrain::Term
                            | OpticalHolonGrain::Assembly
                    )
            });
            let mut before = false;
            let mut after = false;
            for member in members {
                before |= member.bounds.right.saturating_mul(2) <= center_twice;
                after |= member.bounds.left.saturating_mul(2) >= center_twice;
            }
            before && after
        })
}

fn admitted(bounds: OpticalBounds, intervention: &OpticalHolonIntervention) -> bool {
    match intervention {
        OpticalHolonIntervention::Crop { bounds: crop } => boxes_overlap(bounds, *crop),
        _ => true,
    }
}

fn transformed(
    bounds: OpticalBounds,
    intervention: &OpticalHolonIntervention,
) -> Result<OpticalBounds, SourceLayoutError> {
    match intervention {
        OpticalHolonIntervention::Translate {
            horizontal,
            vertical,
        } => Ok(OpticalBounds {
            left: bounds
                .left
                .checked_add(*horizontal)
                .ok_or(SourceLayoutError::Extent)?,
            top: bounds
                .top
                .checked_add(*vertical)
                .ok_or(SourceLayoutError::Extent)?,
            right: bounds
                .right
                .checked_add(*horizontal)
                .ok_or(SourceLayoutError::Extent)?,
            bottom: bounds
                .bottom
                .checked_add(*vertical)
                .ok_or(SourceLayoutError::Extent)?,
        }),
        OpticalHolonIntervention::Crop { bounds: crop } => Ok(OpticalBounds {
            left: bounds.left - crop.left,
            top: bounds.top - crop.top,
            right: bounds.right - crop.left,
            bottom: bounds.bottom - crop.top,
        }),
        _ => Ok(bounds),
    }
}

fn intervened_extent(
    passage: &OpticalPassage,
    intervention: &OpticalHolonIntervention,
) -> Result<(u32, u32), SourceLayoutError> {
    match intervention {
        OpticalHolonIntervention::Crop { bounds } => Ok((
            u32::try_from(bounds.right - bounds.left).map_err(|_| SourceLayoutError::Extent)?,
            u32::try_from(bounds.bottom - bounds.top).map_err(|_| SourceLayoutError::Extent)?,
        )),
        OpticalHolonIntervention::Translate {
            horizontal,
            vertical,
        } => Ok((
            u32::try_from(
                i64::from(passage.width)
                    .checked_add(*horizontal)
                    .ok_or(SourceLayoutError::Extent)?,
            )
            .map_err(|_| SourceLayoutError::Extent)?,
            u32::try_from(
                i64::from(passage.height)
                    .checked_add(*vertical)
                    .ok_or(SourceLayoutError::Extent)?,
            )
            .map_err(|_| SourceLayoutError::Extent)?,
        )),
        _ => Ok((passage.width, passage.height)),
    }
}

fn boxes_overlap(left: OpticalBounds, right: OpticalBounds) -> bool {
    left.left < right.right
        && right.left < left.right
        && left.top < right.bottom
        && right.top < left.bottom
}

fn vertical_overlap(left: OpticalBounds, right: OpticalBounds) -> bool {
    left.top < right.bottom && right.top < left.bottom
}

fn horizontal_overlap(left: OpticalBounds, right: OpticalBounds) -> bool {
    left.left < right.right && right.left < left.right
}

fn horizontal_gap(left: OpticalBounds, right: OpticalBounds) -> u64 {
    if left.right < right.left {
        (right.left - left.right) as u64
    } else if right.right < left.left {
        (left.left - right.right) as u64
    } else {
        0
    }
}

fn vertical_gap(left: OpticalBounds, right: OpticalBounds) -> u64 {
    if left.bottom < right.top {
        (right.top - left.bottom) as u64
    } else if right.bottom < left.top {
        (left.top - right.bottom) as u64
    } else {
        0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn connected_groups_reconstruct_transitive_optical_contact() {
        assert_eq!(
            connected_groups(6, &[(0, 1), (1, 2), (4, 5)]),
            vec![vec![0, 1, 2], vec![3], vec![4, 5]]
        );
    }

    #[test]
    fn translation_does_not_move_relative_form_bounds() {
        let child = OpticalBounds {
            left: 3,
            top: 5,
            right: 8,
            bottom: 11,
        };
        let parent = OpticalBounds {
            left: 1,
            top: 2,
            right: 10,
            bottom: 12,
        };
        let moved_child = OpticalBounds {
            left: 103,
            top: 205,
            right: 108,
            bottom: 211,
        };
        let moved_parent = OpticalBounds {
            left: 101,
            top: 202,
            right: 110,
            bottom: 212,
        };
        assert_eq!(relative(parent, child), relative(moved_parent, moved_child));
    }

    #[test]
    fn overlap_and_gap_are_distinct_receiver_faces() {
        let a = OpticalBounds {
            left: 0,
            top: 0,
            right: 4,
            bottom: 4,
        };
        let b = OpticalBounds {
            left: 7,
            top: 1,
            right: 9,
            bottom: 3,
        };
        assert!(vertical_overlap(a, b));
        assert!(!horizontal_overlap(a, b));
        assert_eq!(horizontal_gap(a, b), 3);
        assert_eq!(vertical_gap(a, b), 0);
    }
}
