//! Exterior exact constitutive experiment, using the standing exact linear owner.
//!
//! This is a rational current chart, not an HNN cultivation path or a physical
//! power measurement. The full reference solves the independently assembled
//! branch equation; six continuing coordinates use its derived two-face return.
use holonic_engine::exact_linear::ExactRatMatrix as Matrix;
use num_traits::{One, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use std::{collections::BTreeMap, error::Error, fs, path::Path, time::Instant};

type Result<T> = std::result::Result<T, Box<dyn Error>>;

fn rat(n: i64, d: i64) -> Rat {
    Rat::new(n.into(), d.into())
}

fn add(a: &[Rat], b: &[Rat]) -> Vec<Rat> {
    assert_eq!(a.len(), b.len());
    a.iter().zip(b).map(|(a, b)| a + b).collect()
}

fn sub(a: &[Rat], b: &[Rat]) -> Vec<Rat> {
    assert_eq!(a.len(), b.len());
    a.iter().zip(b).map(|(a, b)| a - b).collect()
}

fn zeros(a: &[Rat]) -> bool {
    a.iter().all(Zero::is_zero)
}

struct Geometry {
    side: usize,
    vertices: usize,
    edges: usize,
    cut: Matrix,
    axis: Matrix,
    face: Matrix,
    face_t: Matrix,
    boundary: Matrix,
    gram: Matrix,
    coupling: Matrix,
}

impl Geometry {
    fn new(side: usize) -> Result<Self> {
        if side < 2 {
            return Err("the two distinct square faces require side >= 2".into());
        }
        let vertices = side.checked_pow(4).ok_or("vertex extent overflow")?;
        let edges = vertices.checked_mul(4).ok_or("edge extent overflow")?;
        let mut cuts = vec![vec![Rat::zero(); edges]; 4];
        let mut axes = vec![vec![Rat::zero(); 4]; edges];
        let mut boundary = vec![vec![Rat::zero(); edges]; vertices];
        for direction in 0..4 {
            let stride = side.pow(direction as u32);
            for base in 0..vertices {
                let edge = direction * vertices + base;
                let coordinate = (base / stride) % side;
                let target = if coordinate + 1 == side {
                    base - (side - 1) * stride
                } else {
                    base + stride
                };
                boundary[target][edge] += Rat::one();
                boundary[base][edge] -= Rat::one();
                if coordinate == 0 {
                    cuts[direction][edge] = Rat::one();
                }
                if base == coordinate * stride {
                    axes[edge][direction] = Rat::one();
                }
            }
        }
        let square = |a: usize, b: usize| {
            let mut column = vec![Rat::zero(); edges];
            column[a * vertices] += Rat::one();
            column[b * vertices + side.pow(a as u32)] += Rat::one();
            column[a * vertices + side.pow(b as u32)] -= Rat::one();
            column[b * vertices] -= Rat::one();
            column
        };
        let c0 = square(0, 1);
        let c1 = square(0, 2);
        let face = Matrix::new(
            (0..edges)
                .map(|e| vec![c0[e].clone(), c1[e].clone()])
                .collect(),
        )?;
        let face_t = face.transpose()?;
        let axis = Matrix::new(axes)?;
        let cut = Matrix::new(cuts)?;
        let boundary = Matrix::new(boundary)?;
        let gram = face_t.multiply(&face)?;
        let coupling = face_t.multiply(&axis)?;
        assert_eq!(cut.multiply(&axis)?, Matrix::identity(4)?);
        assert_eq!(cut.multiply(&face)?, Matrix::zero(4, 2)?);
        assert_eq!(boundary.multiply(&axis)?, Matrix::zero(vertices, 4)?);
        assert_eq!(boundary.multiply(&face)?, Matrix::zero(vertices, 2)?);
        assert_eq!(
            gram,
            Matrix::new(vec![vec![rat(4, 1), rat(1, 1)], vec![rat(1, 1), rat(4, 1)]])?
        );
        assert_eq!(
            coupling,
            Matrix::new(vec![
                vec![rat(1, 1), rat(-1, 1), rat(0, 1), rat(0, 1)],
                vec![rat(1, 1), rat(0, 1), rat(-1, 1), rat(0, 1)]
            ])?
        );
        let decoder = Matrix::new(
            (0..edges)
                .map(|e| [axis.row(e).unwrap(), face.row(e).unwrap()].concat())
                .collect(),
        )?;
        assert_eq!(decoder.rank()?, 6);
        Ok(Self {
            side,
            vertices,
            edges,
            cut,
            axis,
            face,
            face_t,
            boundary,
            gram,
            coupling,
        })
    }

    fn decode(&self, state: &State) -> Result<Vec<Rat>> {
        if state.side != self.side || state.cuts.len() != 4 || state.faces.len() != 2 {
            return Err("checkpoint current chart does not match decoder".into());
        }
        let mut current = add(
            &self.axis.apply(&state.cuts)?,
            &self.face.apply(&state.faces)?,
        );
        let mut last = None;
        for (edge, value) in &state.blind_residual {
            if *edge >= self.edges
                || value.is_zero()
                || last.is_some_and(|previous| previous >= *edge)
            {
                return Err(
                    "cold residual must have unique increasing in-range nonzero entries".into(),
                );
            }
            current[*edge] += value;
            last = Some(*edge);
        }
        Ok(current)
    }

    fn extract(&self, current: &[Rat], step: usize, clock: Rat) -> Result<State> {
        let cuts = self.cut.apply(current)?;
        let faces = self.gram.inverse()?.apply(&sub(
            &self.face_t.apply(current)?,
            &self.coupling.apply(&cuts)?,
        ))?;
        let remainder = sub(
            current,
            &add(&self.axis.apply(&cuts)?, &self.face.apply(&faces)?),
        );
        assert!(zeros(&self.cut.apply(&remainder)?));
        assert!(zeros(&self.face_t.apply(&remainder)?));
        let state = State {
            format: "holonics-four-torus-two-face-v1".into(),
            side: self.side,
            step,
            clock,
            cuts,
            faces,
            blind_residual: remainder
                .into_iter()
                .enumerate()
                .filter(|(_, v)| !v.is_zero())
                .collect(),
        };
        assert_eq!(self.decode(&state)?, current);
        Ok(state)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct State {
    format: String,
    side: usize,
    step: usize,
    clock: Rat,
    cuts: Vec<Rat>,
    faces: Vec<Rat>,
    // This is immutable across admitted events, not discarded or called six-number storage.
    blind_residual: Vec<(usize, Rat)>,
}

#[derive(Clone, Serialize)]
struct Event {
    ordinal: usize,
    tau: Rat,
    mu: Rat,
    nu: Rat,
    winding_source: Vec<Rat>,
    face_source: Vec<Rat>,
}

// A declared world-input sequence, independent of current readings and reference answers.
// Three material/clock classes repeat; the full inverse standing is reused per class.
fn event(ordinal: usize) -> Event {
    let (tau, mu, nu) = match ordinal % 3 {
        0 => (rat(1, 2), rat(2, 1), rat(1, 2)),
        1 => (rat(1, 3), rat(3, 2), rat(-1, 2)),
        _ => (rat(2, 5), rat(1, 1), rat(1, 1)),
    };
    let s = if ordinal % 2 == 0 { 1 } else { -1 };
    Event {
        ordinal,
        tau,
        mu,
        nu,
        winding_source: vec![rat(s, 3), rat(1, 5), rat(-s, 7), rat(1, 11)],
        face_source: vec![rat(s, 2), rat(1, 3)],
    }
}

fn material(input: &Event) -> Result<Matrix> {
    if input.tau < Rat::zero()
        || &input.mu + &input.nu < Rat::zero()
        || &input.mu - &input.nu < Rat::zero()
    {
        return Err("material and clock outside admitted positive-semidefinite domain".into());
    }
    Ok(Matrix::new(vec![
        vec![input.mu.clone(), input.nu.clone()],
        vec![input.nu.clone(), input.mu.clone()],
    ])?)
}

fn advance(geometry: &Geometry, state: &mut State, input: &Event) -> Result<()> {
    if input.ordinal != state.step {
        return Err("event chronology mismatch".into());
    }
    material(input)?;
    let q = add(&state.cuts, &input.winding_source);
    let h = geometry.coupling.apply(&q)?;
    // The 5 and 3 modes come from the actual face Gram matrix checked above.
    let g_plus = geometry.gram.get(0, 0)? + geometry.gram.get(0, 1)?;
    let g_minus = geometry.gram.get(0, 0)? - geometry.gram.get(0, 1)?;
    let m_plus = &input.mu + &input.nu;
    let m_minus = &input.mu - &input.nu;
    let p = (&state.faces[0] + &state.faces[1] + &input.face_source[0] + &input.face_source[1]
        - &input.tau * &m_plus * (&h[0] + &h[1]))
        / (Rat::one() + g_plus * &input.tau * m_plus);
    let m = (&state.faces[0] - &state.faces[1] + &input.face_source[0]
        - &input.face_source[1]
        - &input.tau * &m_minus * (&h[0] - &h[1]))
        / (Rat::one() + g_minus * &input.tau * m_minus);
    state.faces = vec![(&p + &m) / rat(2, 1), (p - m) / rat(2, 1)];
    state.cuts = q;
    state.clock += &input.tau;
    state.step += 1;
    Ok(())
}

#[derive(Serialize)]
struct StepReceipt {
    input: Event,
    clock_before: String,
    clock_after: String,
    cuts: Vec<String>,
    face_readings: Vec<String>,
    active_material_energy: String,
    full_law_exact: bool,
    full_decoder_exact: bool,
    operator_assembly_ns: u128,
    source_assembly_ns: u128,
    fine_solve_ns: u128,
    compact_advance_ns: u128,
    decoder_ns: u128,
}

fn strings(values: &[Rat]) -> Vec<String> {
    values.iter().map(ToString::to_string).collect()
}

fn initial(geometry: &Geometry, blind: bool) -> Result<State> {
    let state = State {
        format: "holonics-four-torus-two-face-v1".into(),
        side: geometry.side,
        step: 0,
        clock: Rat::zero(),
        cuts: vec![rat(1, 1), rat(-2, 1), rat(1, 2), rat(3, 1)],
        faces: vec![rat(2, 3), rat(-1, 4)],
        blind_residual: vec![],
    };
    let mut current = geometry.decode(&state)?;
    if blind {
        // F12 + F01/3 - F02/3 is a closed, nonzero joint-blind remainder.
        let n = geometry.vertices;
        current[n] += Rat::one();
        current[2 * n + geometry.side] += Rat::one();
        current[n + geometry.side.pow(2)] -= Rat::one();
        current[2 * n] -= Rat::one();
        let correction = geometry.face.apply(&[rat(1, 3), rat(-1, 3)])?;
        current = add(&current, &correction);
    }
    let extracted = geometry.extract(&current, 0, Rat::zero())?;
    assert_eq!(extracted.cuts, state.cuts);
    assert_eq!(extracted.faces, state.faces);
    assert_eq!(extracted.blind_residual.is_empty(), !blind);
    assert!(zeros(&geometry.boundary.apply(&current)?));
    Ok(extracted)
}

fn run(
    geometry: Geometry,
    mut state: State,
    steps: usize,
    output: &Path,
    setup_ns: u128,
) -> Result<()> {
    let run_timer = Instant::now();
    if state.format != "holonics-four-torus-two-face-v1" {
        return Err("unsupported checkpoint".into());
    }
    let mut full = geometry.decode(&state)?;
    assert_eq!(
        geometry.extract(&full, state.step, state.clock.clone())?,
        state
    );
    let initial_residual = state.blind_residual.clone();
    let start_step = state.step;
    let start_clock = state.clock.clone();
    let mut inverses = BTreeMap::new();
    let mut receipts = Vec::new();
    let mut inverse_setup_ns = 0;
    for _ in 0..steps {
        let input = event(state.step);
        let assembly_timer = Instant::now();
        let m = material(&input)?;
        let a = Matrix::identity(geometry.edges)?.add(
            &geometry
                .face
                .multiply(&m)?
                .multiply(&geometry.face_t)?
                .scaled(&input.tau),
        )?;
        let operator_assembly_ns = assembly_timer.elapsed().as_nanos();
        let key = (input.tau.clone(), input.mu.clone(), input.nu.clone());
        if !inverses.contains_key(&key) {
            eprintln!(
                "side {} event {}: certifying full {}-branch inverse",
                geometry.side, state.step, geometry.edges
            );
            let timer = Instant::now();
            inverses.insert(key.clone(), a.inverse()?);
            inverse_setup_ns += timer.elapsed().as_nanos();
        }
        let source_timer = Instant::now();
        let rhs = add(
            &add(&full, &geometry.axis.apply(&input.winding_source)?),
            &geometry.face.apply(&input.face_source)?,
        );
        let source_assembly_ns = source_timer.elapsed().as_nanos();
        let timer = Instant::now();
        let reference = inverses[&key].apply(&rhs)?;
        let fine_solve_ns = timer.elapsed().as_nanos();
        assert_eq!(a.apply(&reference)?, rhs);
        let clock_before = state.clock.to_string();
        let timer = Instant::now();
        advance(&geometry, &mut state, &input)?;
        let compact_advance_ns = timer.elapsed().as_nanos();
        let timer = Instant::now();
        let decoded = geometry.decode(&state)?;
        let decoder_ns = timer.elapsed().as_nanos();
        assert_eq!(reference, decoded);
        assert_eq!(geometry.cut.apply(&reference)?, state.cuts);
        assert!(zeros(&geometry.boundary.apply(&reference)?));
        assert_eq!(state.blind_residual, initial_residual);
        let face_readings = geometry.face_t.apply(&reference)?;
        let material_readings = m.apply(&face_readings)?;
        let energy: Rat = face_readings
            .iter()
            .zip(&material_readings)
            .map(|(a, b)| a * b)
            .sum::<Rat>()
            / rat(2, 1);
        receipts.push(StepReceipt {
            input,
            clock_before,
            clock_after: state.clock.to_string(),
            cuts: strings(&state.cuts),
            face_readings: strings(&face_readings),
            active_material_energy: energy.to_string(),
            full_law_exact: true,
            full_decoder_exact: true,
            operator_assembly_ns,
            source_assembly_ns,
            fine_solve_ns,
            compact_advance_ns,
            decoder_ns,
        });
        full = reference;
        eprintln!(
            "side {} event {}: exact law and decoder returned",
            geometry.side, state.step
        );
    }
    // A four-cut-only decoder erases contractible current. Keep a separating probe.
    let lost = sub(&full, &geometry.axis.apply(&state.cuts)?);
    let separator = lost
        .iter()
        .enumerate()
        .find(|(_, v)| !v.is_zero())
        .map(|(e, v)| (e, v.to_string()));
    assert!(separator.is_some());
    let state_bytes = serde_json::to_vec(&state)?;
    let full_bytes = serde_json::to_vec(&full)?;
    let standing_bytes = serde_json::to_vec(&(
        &geometry.cut,
        &geometry.axis,
        &geometry.face,
        &geometry.gram,
        &geometry.coupling,
    ))?
    .len();
    let inverse_bytes = inverses
        .values()
        .map(serde_json::to_vec)
        .collect::<std::result::Result<Vec<_>, _>>()?
        .iter()
        .map(Vec::len)
        .sum::<usize>();
    fs::create_dir_all(output)?;
    fs::write(output.join("state.json"), &state_bytes)?;
    fs::write(output.join("full-current.json"), &full_bytes)?;
    let receipt = serde_json::json!({
        "grade": "established-bounded", "evidence": ["implemented-exact", "computational-witness", "measured"],
        "scope": "exterior rational two-face constitutive law; dimensionless chart; no HNN or hardware power claim",
        "source_owner": "crates/holonic-engine/examples/four_torus_current.rs",
        "side": geometry.side, "grain": geometry.side - 1, "vertices": geometry.vertices, "branches": geometry.edges,
        "active_dimension": 6, "start_step": start_step, "end_step": state.step,
        "start_clock": start_clock.to_string(), "end_clock": state.clock.to_string(),
        "gram": [[4,1],[1,4]], "cut_face_coupling": [[1,-1,0,0],[1,0,-1,0]],
        "blind_residual_entries": state.blind_residual.len(),
        "checkpoint_json_bytes": state_bytes.len(), "full_current_json_bytes": full_bytes.len(),
        "dense_decoder_standing_json_bytes": standing_bytes,
        "reference_inverse_standing_json_bytes": inverse_bytes,
        "geometry_certificate_setup_ns": setup_ns, "reference_inverse_certificate_setup_ns": inverse_setup_ns,
        "run_through_state_and_current_write_ns": run_timer.elapsed().as_nanos(),
        "four_cut_only_current_separator": separator,
        "steps": receipts,
    });
    fs::write(
        output.join("receipt.json"),
        serde_json::to_vec_pretty(&receipt)?,
    )?;
    println!(
        "side={} events={}..{} branches={} continuing=6 residual={} checkpoint={}B full={}B",
        geometry.side,
        start_step,
        state.step,
        geometry.edges,
        state.blind_residual.len(),
        state_bytes.len(),
        full_bytes.len()
    );
    Ok(())
}

fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().collect();
    let timer = Instant::now();
    match args.get(1).map(String::as_str) {
        Some("run") if args.len() == 5 || args.len() == 6 => {
            let geometry = Geometry::new(args[2].parse()?)?;
            let blind = match args.get(5).map(String::as_str) {
                None => false,
                Some("blind") => true,
                _ => return Err("expected optional 'blind'".into()),
            };
            let state = initial(&geometry, blind)?;
            run(
                geometry,
                state,
                args[3].parse()?,
                Path::new(&args[4]),
                timer.elapsed().as_nanos(),
            )
        }
        Some("resume") if args.len() == 5 => {
            let state: State = serde_json::from_slice(&fs::read(&args[2])?)?;
            let geometry = Geometry::new(state.side)?;
            run(
                geometry,
                state,
                args[3].parse()?,
                Path::new(&args[4]),
                timer.elapsed().as_nanos(),
            )
        }
        _ => Err(
            "usage: four_torus_current run SIDE STEPS OUTPUT [blind] | resume STATE STEPS OUTPUT"
                .into(),
        ),
    }
}
