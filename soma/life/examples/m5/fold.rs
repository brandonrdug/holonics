//! One lineaged physical-fold family composed through the exact complex and resident carrier.

use std::collections::BTreeSet;
use std::ops::Range;

use holonic_engine::EventId;
use holonic_engine::cuda_refine::CudaRefineExecutor;
use holonic_engine::physical_constraint_complex::{
    ConstraintComponentId, ContactClass, CrossPresentationFibre, DistanceAperture,
    PhysicalConstraintComplex, cross_presentation_fibre,
};
use num_bigint::BigInt;
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};

use super::cif::{CifComponent, CifPresentation};
use super::input::{InputMount, SourceMember};
use super::npy::PaeAtlas;

const CONTACT_RADIUS_ANGSTROMS: u64 = 8;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeviceContactReceipt {
    pub schema: String,
    pub device: String,
    pub warp_size: u32,
    pub derived_block_threads: u32,
    pub coordinate_vertices: usize,
    pub contact_population: usize,
    pub paired_population: usize,
    pub launches: u64,
    pub terminal_synchronizations: u64,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
    pub source_maximum_decimal_places: u32,
    pub resident_decimal_places: u32,
    pub common_decimal_denominator: u64,
    pub aperture_squared_wire: u64,
    pub semantic_testimony: String,
    pub telemetry_boundary: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DesignedContactFace {
    pub schema: String,
    pub source_lineage: String,
    pub complete_pair_population: usize,
    pub inside_pairs: Vec<(u32, u32)>,
    pub outside_pairs: usize,
    pub open_pairs: Vec<(u32, u32)>,
    pub target_residue_ordinals_at_inside_contacts: BTreeSet<i32>,
    pub admission_boundary: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct HigherFaceInvariant {
    pub schema: String,
    pub shared_faces: Vec<(u32, u32, u32)>,
    pub free_only_faces: Vec<(u32, u32, u32)>,
    pub complex_only_faces: Vec<(u32, u32, u32)>,
    pub law: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct EnvironmentReturn {
    pub schema: String,
    pub free_form_response: String,
    pub cul1_rbx1_form_response: String,
    pub response_changed: bool,
    pub designed_target_residues: BTreeSet<i32>,
    pub designed_coordinate_contact_target_residues: BTreeSet<i32>,
    pub cul1_contact_target_residues: BTreeSet<i32>,
    pub designed_cul1_overlap: BTreeSet<i32>,
    pub binder_contact_fibre_reopened: bool,
    pub refusal: String,
}

#[derive(Debug, Serialize)]
pub struct PhysicalFoldReturn {
    pub schema: String,
    pub source_mount: InputMount,
    pub coordinate_presentations: Vec<CifPresentation>,
    pub uncertainty_presentations: Vec<PaeAtlas>,
    pub device_receipt: DeviceContactReceipt,
    pub designed_contact_face: DesignedContactFace,
    pub free_complex: PhysicalConstraintComplex,
    pub cul1_rbx1_complex: PhysicalConstraintComplex,
    pub cross_presentation_fibre: CrossPresentationFibre,
    pub higher_face_invariant: HigherFaceInvariant,
    pub environment_return: EnvironmentReturn,
    pub cultivation_founded: bool,
    pub cultivation_consequence: String,
}

pub fn enact() -> Result<PhysicalFoldReturn, String> {
    let mount = super::input::mount()?;
    let designed_source = member(&mount, "designed-free-rbx1.cif")?.clone();
    let free_source = member(&mount, "ptxv2-free-rbx1-seed2.cif")?.clone();
    let complex_source = member(&mount, "ptxv2-cul1-rbx1-seed0.cif")?.clone();
    let free_pae_source = member(&mount, "ptxv2-free-rbx1-seed2-pae.npz")?.clone();
    let complex_pae_source = member(&mount, "ptxv2-cul1-rbx1-seed0-pae.npz")?.clone();

    let designed = super::cif::read(designed_source.local_path.as_ref(), &designed_source.sha256)?;
    let free = super::cif::read(free_source.local_path.as_ref(), &free_source.sha256)?;
    let complex = super::cif::read(complex_source.local_path.as_ref(), &complex_source.sha256)?;
    let free_pae = super::npy::read(
        &mount.structure_root_path.join("free-pae-npy"),
        &free_pae_source.release_path,
        &free_pae_source.sha256,
    )?;
    let complex_pae = super::npy::read(
        &mount.structure_root_path.join("cul1-pae-npy"),
        &complex_pae_source.release_path,
        &complex_pae_source.sha256,
    )?;
    admit_pae(&mount, &free_pae, "1to1", "", "2")?;
    admit_pae(&mount, &complex_pae, "1to2", "rbx1_cul1_zn", "0")?;

    // Components are bound by complete ordered residue sequence. Source chain names remain
    // addresses used to join coordinate and PAE occurrences; they never select the biological role.
    let designed_binder = designed.component_with_sequence(&mount.family.binder_sequence)?;
    let designed_target = unique_other(&designed, &[designed_binder])?;
    let target_sequence = designed.components[designed_target].one_letter_sequence.clone();
    let free_binder = free.component_with_sequence(&mount.family.binder_sequence)?;
    let free_target = free.component_with_sequence(&target_sequence)?;
    let complex_binder = complex.component_with_sequence(&mount.family.binder_sequence)?;
    let complex_target = complex.component_with_sequence(&target_sequence)?;
    let cul1 = unique_other(&complex, &[complex_binder, complex_target])?;

    let source_maximum_decimal_places = designed
        .maximum_decimal_places
        .max(free.maximum_decimal_places)
        .max(complex.maximum_decimal_places);
    let resident_decimal_places = derive_resident_places(
        &[&designed, &free, &complex],
        source_maximum_decimal_places,
    )?;
    let denominator = 10_u64
        .checked_pow(resident_decimal_places)
        .ok_or_else(|| "the coordinate denominator exceeds the resident u64 wire".to_owned())?;
    let aperture_squared_wire = CONTACT_RADIUS_ANGSTROMS
        .checked_mul(CONTACT_RADIUS_ANGSTROMS)
        .and_then(|square| square.checked_mul(denominator))
        .and_then(|scaled| scaled.checked_mul(denominator))
        .ok_or_else(|| "the exact contact aperture exceeds the resident u64 wire".to_owned())?;

    let mut wire = ContactWire::default();
    let designed_binder_wire = wire.append(&designed.components[designed_binder], resident_decimal_places)?;
    let designed_target_wire = wire.append(&designed.components[designed_target], resident_decimal_places)?;
    let free_binder_wire = wire.append(&free.components[free_binder], resident_decimal_places)?;
    let free_target_wire = wire.append(&free.components[free_target], resident_decimal_places)?;
    let complex_binder_wire = wire.append(&complex.components[complex_binder], resident_decimal_places)?;
    let complex_target_wire = wire.append(&complex.components[complex_target], resident_decimal_places)?;
    let cul1_wire = wire.append(&complex.components[cul1], resident_decimal_places)?;

    let designed_range = wire.cross(&designed_binder_wire, &designed_target_wire)?;
    let free_range = wire.cross(&free_binder_wire, &free_target_wire)?;
    let complex_range = wire.cross(&complex_binder_wire, &complex_target_wire)?;
    let cul1_range = wire.cross(&cul1_wire, &complex_target_wire)?;
    if free_range.len() != complex_range.len() {
        return Err("the two sequence-bound binder/target populations do not correspond".to_owned());
    }
    let comparison_left = (free_range.start..free_range.end)
        .map(as_u32)
        .collect::<Result<Vec<_>, _>>()?;
    let comparison_right = (complex_range.start..complex_range.end)
        .map(as_u32)
        .collect::<Result<Vec<_>, _>>()?;

    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let device = card.device_name().to_owned();
    let warp_size = card.warp_size();
    let derived_block_threads = card.block_threads();
    let passage = card
        .contact_passage_on_device(
            &wire.lower_xyz,
            &wire.upper_xyz,
            &wire.task_left,
            &wire.task_right,
            &comparison_left,
            &comparison_right,
            aperture_squared_wire,
        )
        .map_err(|error| error.to_string())?;
    let classes = passage
        .contact_classes
        .iter()
        .map(|value| ContactClass::from_wire(*value).map_err(|error| error.to_string()))
        .collect::<Result<Vec<_>, _>>()?;
    for ((left, right), paired) in free_range
        .clone()
        .zip(complex_range.clone())
        .zip(&passage.paired_classes)
    {
        let expected = 3 * passage.contact_classes[left] + passage.contact_classes[right];
        if *paired != expected {
            return Err("the resident ordered cross-presentation pair disagrees with its returned classes".to_owned());
        }
    }

    let aperture = || DistanceAperture {
        lineage: format!(
            "declared C-alpha contact receiver: exact distance not greater than {CONTACT_RADIUS_ANGSTROMS} angstroms"
        ),
        squared: Rat::from_integer(BigInt::from(
            CONTACT_RADIUS_ANGSTROMS * CONTACT_RADIUS_ANGSTROMS,
        )),
    };
    let mut free_complex = PhysicalConstraintComplex::found(
        format!("{} / predicted free RBX1", free_source.release_path),
        event_from_sha256(&free_source.sha256)?,
        vec![
            free.components[free_binder]
                .material_at_places("predicted free / binder", resident_decimal_places)?,
            free.components[free_target]
                .material_at_places("predicted free / target", resident_decimal_places)?,
        ],
    )
    .map_err(|error| error.to_string())?;
    let free_uncertainty = free_pae.pair_uncertainty(
        &free.components[free_binder].source_chain,
        &residue_ordinals(&free.components[free_binder]),
        &free.components[free_target].source_chain,
        &residue_ordinals(&free.components[free_target]),
    )?;
    free_complex
        .found_contact_family(
            ConstraintComponentId(1),
            ConstraintComponentId(2),
            aperture(),
            &classes[free_range.clone()],
            &free_uncertainty,
        )
        .map_err(|error| error.to_string())?;

    let mut cul1_rbx1_complex = PhysicalConstraintComplex::found(
        format!("{} / predicted CUL1-RBX1 form", complex_source.release_path),
        event_from_sha256(&complex_source.sha256)?,
        vec![
            complex.components[complex_binder]
                .material_at_places("predicted complex / binder", resident_decimal_places)?,
            complex.components[complex_target]
                .material_at_places("predicted complex / target", resident_decimal_places)?,
            complex.components[cul1]
                .material_at_places(
                    "predicted complex / accompanying component",
                    resident_decimal_places,
                )?,
        ],
    )
    .map_err(|error| error.to_string())?;
    let complex_uncertainty = complex_pae.pair_uncertainty(
        &complex.components[complex_binder].source_chain,
        &residue_ordinals(&complex.components[complex_binder]),
        &complex.components[complex_target].source_chain,
        &residue_ordinals(&complex.components[complex_target]),
    )?;
    cul1_rbx1_complex
        .found_contact_family(
            ConstraintComponentId(1),
            ConstraintComponentId(2),
            aperture(),
            &classes[complex_range.clone()],
            &complex_uncertainty,
        )
        .map_err(|error| error.to_string())?;
    let cul1_uncertainty = complex_pae.pair_uncertainty(
        &complex.components[cul1].source_chain,
        &residue_ordinals(&complex.components[cul1]),
        &complex.components[complex_target].source_chain,
        &residue_ordinals(&complex.components[complex_target]),
    )?;
    cul1_rbx1_complex
        .found_contact_family(
            ConstraintComponentId(3),
            ConstraintComponentId(2),
            aperture(),
            &classes[cul1_range.clone()],
            &cul1_uncertainty,
        )
        .map_err(|error| error.to_string())?;

    let cross_presentation_fibre = cross_presentation_fibre(
        &free_complex,
        &cul1_rbx1_complex,
        (ConstraintComponentId(1), ConstraintComponentId(2)),
        (ConstraintComponentId(1), ConstraintComponentId(2)),
    )
    .map_err(|error| error.to_string())?;
    if cross_presentation_fibre.shared_inside.is_empty()
        || cross_presentation_fibre.shortest_separator.is_none()
    {
        return Err("the admitted family did not return both a shared invariant and a separator".to_owned());
    }
    let higher_face_invariant = higher_face_invariant(
        free_complex
            .contact_family(ConstraintComponentId(1), ConstraintComponentId(2))
            .map_err(|error| error.to_string())?,
        cul1_rbx1_complex
            .contact_family(ConstraintComponentId(1), ConstraintComponentId(2))
            .map_err(|error| error.to_string())?,
    )?;
    if higher_face_invariant.shared_faces.is_empty() {
        return Err("the two presentations returned no shared higher incidence".to_owned());
    }

    let designed_contact_face = designed_contact_face(
        &designed,
        designed_binder,
        designed_target,
        &classes[designed_range],
        aperture(),
        &designed_source,
        resident_decimal_places,
    )?;
    let cul1_contact_target_residues = inside_target_residues(
        cul1_rbx1_complex
            .contact_family(ConstraintComponentId(3), ConstraintComponentId(2))
            .map_err(|error| error.to_string())?,
        &complex.components[complex_target],
    );
    let designed_target_residues = parse_designed_target_ordinals(&mount.family.designed_epitope)?;
    let designed_cul1_overlap = designed_target_residues
        .intersection(&cul1_contact_target_residues)
        .copied()
        .collect::<BTreeSet<_>>();
    let environment_return = EnvironmentReturn {
        schema: "holonics.m5.environment-and-assay-return.v1".to_owned(),
        free_form_response: mount.family.assays[0].response.clone(),
        cul1_rbx1_form_response: mount.family.assays[1].response.clone(),
        response_changed: mount.family.assays[0].response != mount.family.assays[1].response,
        designed_target_residues,
        designed_coordinate_contact_target_residues: designed_contact_face
            .target_residue_ordinals_at_inside_contacts
            .clone(),
        cul1_contact_target_residues,
        designed_cul1_overlap,
        binder_contact_fibre_reopened: !cross_presentation_fibre.left_only_inside.is_empty()
            || !cross_presentation_fibre.right_only_inside.is_empty()
            || !cross_presentation_fibre.unresolved.is_empty(),
        refusal: "[EXACT:conditional] The authenticated source proves a target-form change, an assay-response change, exact coordinate-incidence change and a nonempty CUL1/RBX1 contact population. These co-occurrences do not identify molecular causation, binding energetics, or assay comparability; no such law or calibrated receiver was supplied.".to_owned(),
    };
    if !environment_return.response_changed || !environment_return.binder_contact_fibre_reopened {
        return Err("the physical family did not return its declared environment/response separation".to_owned());
    }

    let device_receipt = DeviceContactReceipt {
        schema: "holonics.m5.single-card-exact-contact-passage.v1".to_owned(),
        device,
        warp_size,
        derived_block_threads,
        coordinate_vertices: wire.lower_xyz.len() / 3,
        contact_population: passage.contact_classes.len(),
        paired_population: passage.paired_classes.len(),
        launches: passage.launches,
        terminal_synchronizations: passage.synchronizations,
        host_ingress_octets: passage.host_ingress_octets,
        host_egress_octets: passage.host_egress_octets,
        resident_octets: passage.resident_octets,
        source_maximum_decimal_places,
        resident_decimal_places,
        common_decimal_denominator: denominator,
        aperture_squared_wire,
        semantic_testimony: "the card classified the complete designed, free, complex and accompanying-component contact populations; free/complex classes remained resident for the ordered-pair comparison; the CPU then audited every enacted class through the same exact outward resident intervals before topology was founded; the resident decimal grain is derived as the finest source-bounded denominator whose complete coordinate span and aperture fit the u64 squared-distance carrier".to_owned(),
        telemetry_boundary: "launch, synchronization, transfer and resident-octet counts are apparatus testimony separate from exact contact semantics; no energy claim is made".to_owned(),
    };

    Ok(PhysicalFoldReturn {
        schema: "holonics.m5.physical-fold-return.v1".to_owned(),
        source_mount: mount,
        coordinate_presentations: vec![designed, free, complex],
        uncertainty_presentations: vec![free_pae, complex_pae],
        device_receipt,
        designed_contact_face,
        free_complex,
        cul1_rbx1_complex,
        cross_presentation_fibre,
        higher_face_invariant,
        environment_return,
        cultivation_founded: false,
        cultivation_consequence: "No returned passage changed reusable morphology in this phase; source-detached remount and ablation are therefore not owed and are not simulated.".to_owned(),
    })
}

fn member<'a>(mount: &'a InputMount, suffix: &str) -> Result<&'a SourceMember, String> {
    mount
        .structure_members
        .iter()
        .find(|member| member.local_path.ends_with(suffix))
        .ok_or_else(|| format!("the admitted structure family has no local {suffix}"))
}

fn admit_pae(
    mount: &InputMount,
    atlas: &PaeAtlas,
    stoichiometry: &str,
    target_form: &str,
    seed: &str,
) -> Result<(), String> {
    if atlas.design_uuid != mount.family.uuid
        || atlas.design_name != mount.family.full_name
        || atlas.target != mount.family.target
        || atlas.cofolding_model != "ptxv2"
        || atlas.stoichiometry != stoichiometry
        || atlas.target_form != target_form
        || atlas.seed != seed
    {
        return Err(format!(
            "PAE metadata does not bind the declared occurrence/form: {} / {} / {}",
            atlas.design_uuid, atlas.target_form, atlas.seed
        ));
    }
    Ok(())
}

fn unique_other(presentation: &CifPresentation, excluded: &[usize]) -> Result<usize, String> {
    let candidates = (0..presentation.components.len())
        .filter(|at| !excluded.contains(at))
        .collect::<Vec<_>>();
    match candidates.as_slice() {
        [at] => Ok(*at),
        _ => Err(format!(
            "{} leaves {} components after sequence binding, not one",
            presentation.source_path,
            candidates.len()
        )),
    }
}

fn residue_ordinals(component: &CifComponent) -> Vec<i32> {
    component
        .residues
        .iter()
        .map(|residue| residue.source_ordinal)
        .collect()
}

fn event_from_sha256(hash: &str) -> Result<EventId, String> {
    let prefix = hash
        .get(..16)
        .ok_or_else(|| "a source digest cannot address an event occurrence".to_owned())?;
    Ok(EventId(
        u64::from_str_radix(prefix, 16).map_err(|error| error.to_string())?,
    ))
}

fn as_u32(value: usize) -> Result<u32, String> {
    u32::try_from(value).map_err(|_| "the resident contact population exceeds u32".to_owned())
}

#[derive(Default)]
struct ContactWire {
    lower_xyz: Vec<i64>,
    upper_xyz: Vec<i64>,
    task_left: Vec<u32>,
    task_right: Vec<u32>,
}

impl ContactWire {
    fn append(&mut self, component: &CifComponent, places: u32) -> Result<Vec<u32>, String> {
        component
            .residues
            .iter()
            .map(|residue| {
                let index = as_u32(self.lower_xyz.len() / 3)?;
                let (lower, upper) = residue.ca.wire(places)?;
                self.lower_xyz.extend(lower);
                self.upper_xyz.extend(upper);
                Ok(index)
            })
            .collect()
    }

    fn cross(&mut self, left: &[u32], right: &[u32]) -> Result<Range<usize>, String> {
        let start = self.task_left.len();
        let addition = left
            .len()
            .checked_mul(right.len())
            .ok_or_else(|| "contact population overflow".to_owned())?;
        self.task_left.reserve(addition);
        self.task_right.reserve(addition);
        for a in left {
            for b in right {
                self.task_left.push(*a);
                self.task_right.push(*b);
            }
        }
        Ok(start..self.task_left.len())
    }
}

fn designed_contact_face(
    presentation: &CifPresentation,
    binder: usize,
    target: usize,
    classes: &[ContactClass],
    aperture: DistanceAperture,
    source: &SourceMember,
    resident_decimal_places: u32,
) -> Result<DesignedContactFace, String> {
    let left = &presentation.components[binder];
    let right = &presentation.components[target];
    if classes.len() != left.residues.len() * right.residues.len() {
        return Err("designed contact class population disagrees with its components".to_owned());
    }
    let mut inside_pairs = Vec::new();
    let mut outside_pairs = 0usize;
    let mut open_pairs = Vec::new();
    let mut target_residues = BTreeSet::new();
    for (left_at, left_residue) in left.residues.iter().enumerate() {
        for (right_at, right_residue) in right.residues.iter().enumerate() {
            let at = left_at * right.residues.len() + right_at;
            let exact = aperture.classify(
                &left_residue
                    .ca
                    .box3_at_places(resident_decimal_places)?
                    .squared_distance(
                        &right_residue
                            .ca
                            .box3_at_places(resident_decimal_places)?,
                    ),
            );
            if classes[at] != exact {
                return Err(format!(
                    "designed contact carrier disagrees at {}:{}",
                    left_at + 1,
                    right_at + 1
                ));
            }
            let pair = (left_at as u32 + 1, right_at as u32 + 1);
            match exact {
                ContactClass::Inside => {
                    inside_pairs.push(pair);
                    target_residues.insert(right_residue.source_ordinal);
                }
                ContactClass::Outside => outside_pairs += 1,
                ContactClass::Open => open_pairs.push(pair),
            }
        }
    }
    Ok(DesignedContactFace {
        schema: "holonics.m5.designed-coordinate-contact-face.v1".to_owned(),
        source_lineage: source.release_path.clone(),
        complete_pair_population: classes.len(),
        inside_pairs,
        outside_pairs,
        open_pairs,
        target_residue_ordinals_at_inside_contacts: target_residues,
        admission_boundary: "The designed source has no matched PAE occurrence in the admitted family, so this is retained as a complete exact coordinate-contact face and is not promoted into the two predictor-backed physical constraint complexes.".to_owned(),
    })
}

fn derive_resident_places(
    presentations: &[&CifPresentation],
    source_maximum: u32,
) -> Result<u32, String> {
    for places in (0..=source_maximum).rev() {
        let Some(denominator) = 10_u64.checked_pow(places) else {
            continue;
        };
        if CONTACT_RADIUS_ANGSTROMS
            .checked_mul(CONTACT_RADIUS_ANGSTROMS)
            .and_then(|square| square.checked_mul(denominator))
            .and_then(|scaled| scaled.checked_mul(denominator))
            .is_none()
        {
            continue;
        }
        let mut minimum = [i64::MAX; 3];
        let mut maximum = [i64::MIN; 3];
        let mut valid = true;
        for residue in presentations
            .iter()
            .flat_map(|presentation| &presentation.components)
            .flat_map(|component| &component.residues)
        {
            let Ok((lower, upper)) = residue.ca.wire(places) else {
                valid = false;
                break;
            };
            for axis in 0..3 {
                minimum[axis] = minimum[axis].min(lower[axis]);
                maximum[axis] = maximum[axis].max(upper[axis]);
            }
        }
        if !valid {
            continue;
        }
        let complete_span_square = (0..3).try_fold(0_u128, |sum, axis| {
            let difference = i128::from(maximum[axis]) - i128::from(minimum[axis]);
            let magnitude = difference.unsigned_abs();
            magnitude
                .checked_mul(magnitude)
                .and_then(|square| sum.checked_add(square))
        });
        if complete_span_square.is_some_and(|square| square <= u128::from(u64::MAX)) {
            return Ok(places);
        }
    }
    Err("no outward decimal projection fits the exact resident distance carrier".to_owned())
}

fn higher_face_invariant(
    free: &holonic_engine::physical_constraint_complex::ContactFamily,
    complex: &holonic_engine::physical_constraint_complex::ContactFamily,
) -> Result<HigherFaceInvariant, String> {
    if free.readings.len() != complex.readings.len() {
        return Err("higher-face populations cannot be compared".to_owned());
    }
    let right_extent = free
        .readings
        .iter()
        .map(|reading| reading.right_ordinal)
        .max()
        .ok_or_else(|| "the contact family is empty".to_owned())? as usize;
    let left_extent = free.readings.len() / right_extent;
    let faces = |family: &holonic_engine::physical_constraint_complex::ContactFamily| {
        let inside = family
            .readings
            .iter()
            .map(|reading| reading.class == ContactClass::Inside)
            .collect::<Vec<_>>();
        let mut result = BTreeSet::new();
        for left in 0..left_extent.saturating_sub(1) {
            for right in 0..right_extent {
                if inside[left * right_extent + right]
                    && inside[(left + 1) * right_extent + right]
                {
                    result.insert((left as u32 + 1, left as u32 + 2, right as u32 + 1));
                }
            }
        }
        result
    };
    let a = faces(free);
    let b = faces(complex);
    Ok(HigherFaceInvariant {
        schema: "holonics.m5.cross-presentation-higher-face-invariant.v1".to_owned(),
        shared_faces: a.intersection(&b).copied().collect(),
        free_only_faces: a.difference(&b).copied().collect(),
        complex_only_faces: b.difference(&a).copied().collect(),
        law: "a local two-cell is the shared-junction incidence [binder_i,binder_(i+1),target_j] founded only when the polygonal edge and both contact edges exist; the intersection is invariant across these two distinct occurrences, while each difference remains in the reconstruction fibre".to_owned(),
    })
}

fn inside_target_residues(
    family: &holonic_engine::physical_constraint_complex::ContactFamily,
    target: &CifComponent,
) -> BTreeSet<i32> {
    family
        .readings
        .iter()
        .filter(|reading| reading.class == ContactClass::Inside)
        .map(|reading| target.residues[reading.right_ordinal as usize - 1].source_ordinal)
        .collect()
}

fn parse_designed_target_ordinals(values: &[String]) -> Result<BTreeSet<i32>, String> {
    values
        .iter()
        .map(|value| {
            let body = value
                .split_once(':')
                .map(|(_, body)| body)
                .unwrap_or(value);
            let digits = body
                .trim_start_matches(|character: char| character.is_ascii_alphabetic())
                .trim();
            digits.parse::<i32>().map_err(|error| {
                format!("designed epitope address {value:?} has no residue ordinal: {error}")
            })
        })
        .collect()
}
