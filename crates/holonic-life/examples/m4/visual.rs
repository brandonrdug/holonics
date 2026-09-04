//! Exact analytic, vector, raster and oriented-mesh faces of the held-out reflection return.

use std::collections::BTreeMap;

use holonic_engine::causal::EventId;
use holonic_engine::certified_face::{certify_face, mark_census, ReceiverWindow};
use holonic_engine::exact_value::IntegerPolynomial;
use holonic_engine::image::ExactRaster;
use holonic_engine::presentation_gauge::{
    rasterize, render, structural_residue, CanvasChart, DisplayGauge,
};
use holonic_engine::simplicial::{Edge, SimplicialComplex, VertexId};
use num_bigint::BigInt;
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};

use super::quadric::CultivationProduct;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MeshVertex {
    pub vertex: VertexId,
    pub chronology: Rat,
    pub bend: Rat,
    pub source_trace_ordinal: usize,
    pub extremum: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MeshReceipt {
    pub schema: String,
    pub underlying_body: String,
    pub complex: SimplicialComplex,
    pub coordinates: Vec<MeshVertex>,
    pub vertex_count: usize,
    pub edge_count: usize,
    pub face_count: usize,
    pub boundary_edge_count: usize,
    pub interior_edge_count: usize,
    pub euler_characteristic: i64,
    pub manifold_boundary: bool,
    pub seams: Vec<String>,
    pub chart_transitions: Vec<String>,
    pub approximation_residual: Rat,
    pub retriangulation_preserved_boundary: bool,
    pub retriangulation_preserved_euler_characteristic: bool,
    pub receiver_family: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RoundTripReceipt {
    pub analytic_face_round_trip: bool,
    pub vector_marks: usize,
    pub vector_gauge_changed_no_structure: bool,
    pub raster_samples: usize,
    pub raster_gauge_changed_no_geometry: bool,
    pub raster_round_trip: bool,
    pub mesh_round_trip: bool,
    pub certified_roots: Vec<[Rat; 2]>,
    pub radius_chart_exclusion: Rat,
}

pub struct VisualProduct {
    pub face: holonic_engine::certified_face::CertifiedFace,
    pub vector_svg: String,
    pub raster: ExactRaster,
    pub raster_ppm: Vec<u8>,
    pub mesh: MeshReceipt,
    pub round_trip: RoundTripReceipt,
}

pub fn produce(product: &CultivationProduct) -> Result<VisualProduct, String> {
    // Holding bends (2,2,3,3) fixed gives Q(x) = -2x² + 20x + 22, whose two roots are the
    // exchanged outer bends -1 and 11.
    let polynomial = IntegerPolynomial::new(vec![22.into(), 20.into(), (-2).into()])
        .map_err(|error| error.to_string())?;
    let lower = integer(-2);
    let upper = integer(12);
    let initial_cells = u32::try_from(14).expect("the exact window width fits u32");
    let subdivision_bound =
        u32::try_from(polynomial.degree()).map_err(|error| error.to_string())?;
    let window = ReceiverWindow::new(lower, upper, initial_cells, subdivision_bound)
        .map_err(|error| error.to_string())?;
    let face = certify_face(&polynomial, &window).map_err(|error| error.to_string())?;
    if !face.population_reconciles() || !face.is_complete() || face.certified_feature_count != 2 {
        return Err("the analytic reflection face did not return both exchanged roots".to_owned());
    }
    let certified_roots = face
        .features
        .iter()
        .map(|feature| {
            [
                feature.interval.lower.clone(),
                feature.interval.upper.clone(),
            ]
        })
        .collect::<Vec<_>>();
    if certified_roots != vec![[integer(-1), integer(-1)], [integer(11), integer(11)]] {
        return Err("the certified face isolated the wrong root population".to_owned());
    }
    let station_extent = u32::try_from(face.stations.len()).map_err(|error| error.to_string())?;
    let chart = CanvasChart::new(station_extent * 24, station_extent * 16, station_extent);
    let declared = DisplayGauge::declared();
    let permuted = DisplayGauge::permuted();
    let vector_svg = render(&face, &chart, &declared);
    let vector_control = render(&face, &chart, &permuted);
    let vector_gauge_changed_no_structure = structural_residue(&vector_svg, &declared)
        == structural_residue(&vector_control, &permuted);
    if !vector_gauge_changed_no_structure {
        return Err("the vector gauge moved analytic structure".to_owned());
    }
    let raster = rasterize(&face, &chart, &declared).map_err(|error| error.to_string())?;
    let raster_control = rasterize(&face, &chart, &permuted).map_err(|error| error.to_string())?;
    let raster_gauge_changed_no_geometry = raster_mask(&raster) == raster_mask(&raster_control);
    if !raster_gauge_changed_no_geometry {
        return Err("the raster gauge moved analytic geometry".to_owned());
    }
    let raster_bytes = serde_json::to_vec(&raster).map_err(|error| error.to_string())?;
    let raster_round_trip = serde_json::from_slice::<ExactRaster>(&raster_bytes)
        .map_err(|error| error.to_string())?
        == raster;
    let raster_ppm = raster.ppm_bytes();
    let mesh = mesh(&product.mathematical.held_out_trace)?;
    let mesh_bytes = serde_json::to_vec(&mesh).map_err(|error| error.to_string())?;
    let mesh_round_trip = serde_json::from_slice::<MeshReceipt>(&mesh_bytes)
        .map_err(|error| error.to_string())?
        == mesh;
    let face_bytes = serde_json::to_vec(&face).map_err(|error| error.to_string())?;
    let analytic_face_round_trip =
        serde_json::from_slice::<holonic_engine::certified_face::CertifiedFace>(&face_bytes)
            .map_err(|error| error.to_string())?
            == face;
    let vector_marks = mark_census(&face).values().sum();
    let round_trip = RoundTripReceipt {
        analytic_face_round_trip,
        vector_marks,
        vector_gauge_changed_no_structure,
        raster_samples: raster.samples.len(),
        raster_gauge_changed_no_geometry,
        raster_round_trip,
        mesh_round_trip,
        certified_roots,
        radius_chart_exclusion: integer(0),
    };
    Ok(VisualProduct {
        face,
        vector_svg,
        raster,
        raster_ppm,
        mesh,
        round_trip,
    })
}

fn mesh(trace: &[Vec<Rat>]) -> Result<MeshReceipt, String> {
    if trace.len() < 2 || trace.iter().any(|state| state.is_empty()) {
        return Err("the held-out trace cannot found an oriented strip".to_owned());
    }
    let mut complex = SimplicialComplex::default();
    let mut coordinates = Vec::new();
    let mut rails = Vec::new();
    for (at, state) in trace.iter().enumerate() {
        let lower_bend = state.iter().min().cloned().expect("nonempty state");
        let upper_bend = state.iter().max().cloned().expect("nonempty state");
        let event = EventId(at as u64 + 1);
        let lower = complex.found_vertex(format!("trace-{at}-lower"), event);
        let upper = complex.found_vertex(format!("trace-{at}-upper"), event);
        coordinates.push(MeshVertex {
            vertex: lower,
            chronology: integer(at as i64),
            bend: lower_bend,
            source_trace_ordinal: at,
            extremum: "lower".to_owned(),
        });
        coordinates.push(MeshVertex {
            vertex: upper,
            chronology: integer(at as i64),
            bend: upper_bend,
            source_trace_ordinal: at,
            extremum: "upper".to_owned(),
        });
        rails.push((lower, upper));
    }
    let mut diagonals = Vec::new();
    for at in 0..rails.len() - 1 {
        let (lower, upper) = rails[at];
        let (next_lower, next_upper) = rails[at + 1];
        let event = EventId((trace.len() + at + 1) as u64);
        complex
            .found_face(
                format!("strip-{at}-lower"),
                event,
                [lower, next_lower, next_upper],
            )
            .map_err(|error| error.to_string())?;
        complex
            .found_face(
                format!("strip-{at}-upper"),
                event,
                [lower, next_upper, upper],
            )
            .map_err(|error| error.to_string())?;
        let diagonal = Edge::new(lower, next_upper).map_err(|error| error.to_string())?;
        let hinge = complex
            .found_hinge(format!("strip-{at}-diagonal"), event, diagonal)
            .map_err(|error| error.to_string())?;
        diagonals.push((
            hinge,
            Edge::new(upper, next_lower).map_err(|error| error.to_string())?,
        ));
    }
    let before = topology(&complex);
    let mut retriangulated = complex.clone();
    for (at, (hinge, proposed)) in diagonals.iter().enumerate() {
        retriangulated
            .flip_hinge(
                EventId((2 * trace.len() + at + 1) as u64),
                *hinge,
                *proposed,
            )
            .map_err(|error| error.to_string())?;
    }
    let after = topology(&retriangulated);
    let retriangulation_preserved_boundary = before.3 == after.3;
    let retriangulation_preserved_euler_characteristic = before.5 == after.5;
    if !retriangulation_preserved_boundary || !retriangulation_preserved_euler_characteristic {
        return Err("the oriented retriangulation moved the admitted strip body".to_owned());
    }
    Ok(MeshReceipt {
        schema: "holonics.m4.exact-reflection-orbit-mesh.v1".to_owned(),
        underlying_body: "the min/max bend envelope over the exact ordered reflection trace"
            .to_owned(),
        complex,
        coordinates,
        vertex_count: before.0,
        edge_count: before.1,
        face_count: before.2,
        boundary_edge_count: before.3,
        interior_edge_count: before.4,
        euler_characteristic: before.5,
        manifold_boundary: before.3 > 0 && before.3 + before.4 == before.1,
        seams: Vec::new(),
        chart_transitions: vec![
            "bend chart b_i".to_owned(),
            "reciprocal-radius chart r_i=b_i^{-1}, with b_i=0 excluded".to_owned(),
        ],
        approximation_residual: integer(0),
        retriangulation_preserved_boundary,
        retriangulation_preserved_euler_characteristic,
        receiver_family: vec![
            "ordered chronology".to_owned(),
            "bend extrema".to_owned(),
            "oriented boundary".to_owned(),
            "Euler characteristic".to_owned(),
        ],
    })
}

fn topology(complex: &SimplicialComplex) -> (usize, usize, usize, usize, usize, i64) {
    let mut edges = BTreeMap::<Edge, usize>::new();
    for face in complex.faces.values() {
        for (edge, _) in face.boundary() {
            *edges.entry(edge).or_default() += 1;
        }
    }
    let boundary = edges.values().filter(|count| **count == 1).count();
    let interior = edges.values().filter(|count| **count == 2).count();
    let vertices = complex.vertices.len();
    let faces = complex.faces.len();
    let euler = vertices as i64 - edges.len() as i64 + faces as i64;
    (vertices, edges.len(), faces, boundary, interior, euler)
}

fn raster_mask(raster: &ExactRaster) -> Vec<bool> {
    let ground = raster.samples[0];
    raster
        .samples
        .iter()
        .map(|sample| *sample != ground)
        .collect()
}

fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}
