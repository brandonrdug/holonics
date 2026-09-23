//! Diagnostic (tests only): the deposition-work term of the Holon balance. For each observe,
//! the pre-observe checkpoint `A` and post-observe checkpoint `B` are split into hybrids that
//! take exactly one of the observe's body material updates from `B`: reaction material `M`
//! (the normal-law `W` on `Φ(s,c)=s⊕c⊕(c⊗s)`) or the field (pair amplitude `ρ` and the declared
//! contact material). Encoder `E` and receiver `R`/stop do not enter a silent word. Each is
//! probed by silent commits (zero encoder table: no moment, no condition), whose per-commit
//! energy ratio `‖q_(k+1)‖²/‖q_k‖²` says whether the word is passive (≤ 1) or active (> 1).
//! Nothing here changes a learning law; the hybrids are read-only recombinations of two rests.
use super::*;
use holonic_engine::native_ecology::constitutive_fibre::ResidentNormalEnclosureSection;
use std::path::{Path, PathBuf};

#[path = "../../../../examples/support/generator_machine.rs"]
mod generator_machine;

fn take_blob(bytes: &[u8], at: &mut usize) -> Vec<u8> {
    let n = u64::from_le_bytes(bytes[*at..*at + 8].try_into().unwrap()) as usize;
    let blob = bytes[*at + 8..*at + 8 + n].to_vec();
    *at += 8 + n;
    blob
}

fn put_blob(out: &mut Vec<u8>, blob: &[u8]) {
    out.extend_from_slice(&(blob.len() as u64).to_le_bytes());
    out.extend_from_slice(blob);
}

/// A generator session checkpoint split into its parts: session header, incident header,
/// field rest, reaction materials and pending blobs.
struct Split {
    magic: Vec<u8>,
    session_header: Vec<u8>,
    incident_magic: Vec<u8>,
    incident_header: Vec<u8>,
    field: Vec<u8>,
    materials: Vec<Vec<u8>>,
    pending: Vec<Vec<u8>>,
}

fn split(path: &Path) -> Split {
    let bytes = std::fs::read(path).unwrap();
    let magic = bytes[..GENERATOR_MAGIC.len()].to_vec();
    assert_eq!(magic, GENERATOR_MAGIC);
    let mut at = magic.len();
    let session_header = take_blob(&bytes, &mut at);
    let body = take_blob(&bytes, &mut at);
    assert_eq!(body[0], 3, "incident body");
    let incident_magic = body[1..20].to_vec();
    let mut at = 20;
    let incident_header = take_blob(&body, &mut at);
    let field = take_blob(&body, &mut at);
    let header: Value = serde_json::from_slice(&incident_header).unwrap();
    let pending_blobs: usize = header["pending"]
        .as_array()
        .map(|p| p.len() * 2)
        .unwrap_or(0);
    let mut rest = Vec::new();
    while at < body.len() {
        rest.push(take_blob(&body, &mut at));
    }
    let materials = rest[..rest.len() - pending_blobs].to_vec();
    let pending = rest[rest.len() - pending_blobs..].to_vec();
    Split {
        magic,
        session_header,
        incident_magic,
        incident_header,
        field,
        materials,
        pending,
    }
}

/// `A` with `B`'s reaction materials and/or `B`'s field rest.
fn hybrid(a: &Split, b: &Split, material: bool, field: bool, path: &Path) {
    let mut body = vec![3u8];
    body.extend_from_slice(&a.incident_magic);
    put_blob(&mut body, &a.incident_header);
    put_blob(&mut body, if field { &b.field } else { &a.field });
    for m in if material { &b.materials } else { &a.materials } {
        put_blob(&mut body, m);
    }
    for p in &a.pending {
        put_blob(&mut body, p);
    }
    let mut out = a.magic.clone();
    put_blob(&mut out, &a.session_header);
    put_blob(&mut out, &body);
    std::fs::write(path, out).unwrap();
}

fn energy(session: &mut NativeFieldSession<'_>, sites: usize) -> f64 {
    let current = session.body.inspect_current().unwrap();
    super::super::measurement::site_energies(&current["joint"], sites)
        .iter()
        .flatten()
        .sum()
}

/// Silent commits on a reopened checkpoint: the energies `E_0..E_k` of the committed current.
fn silent_probe(path: &Path, commits: usize) -> Result<Vec<f64>> {
    let (energies, refused) = silent_probe_partial(path, commits)?;
    match refused {
        None => Ok(energies),
        Some(error) => Err(invalid(error)),
    }
}

/// The same probe, keeping the energies reached before a refusal and the refusal itself.
fn silent_probe_partial(path: &Path, commits: usize) -> Result<(Vec<f64>, Option<String>)> {
    NativeFieldSavedSession::open(path)?.with_session(|session, _| silent_commits(session, commits))
}

/// The same probe with each silent commit's energy balance.
fn silent_probe_balanced(
    path: &Path,
    commits: usize,
) -> Result<(Vec<f64>, Option<String>, Vec<Value>)> {
    NativeFieldSavedSession::open(path)?
        .with_session(|session, _| silent_commits_with_balance(session, commits))
}

/// Silent commits on an open session.
fn silent_commits(
    session: &mut NativeFieldSession<'_>,
    commits: usize,
) -> Result<(Vec<f64>, Option<String>)> {
    silent_commits_with_balance(session, commits).map(|(e, r, _)| (e, r))
}

/// Silent commits, also returning each committed word's exterior energy balance
/// (`IncidentEnergyBalance`, power-neutral law; `null` under the legacy law).
fn silent_commits_with_balance(
    session: &mut NativeFieldSession<'_>,
    commits: usize,
) -> Result<(Vec<f64>, Option<String>, Vec<Value>)> {
    let mut balances = Vec::new();
    {
        let options = session.presentation.spec.generator.clone().unwrap();
        let sites = options.field.machine.sites().len();
        let alphabet = session.presentation.spec.symbols.len();
        let width = options.source.injection_sites.len() * 6;
        let grain = ResidentGrain(session.presentation.spec.fractional_bits);
        let mut energies = vec![energy(session, sites)];
        for _ in 0..commits {
            let table = Rc::new(
                ResidentNormalEnclosureSection::zeros(session.surface, alphabet, width, grain)
                    .map_err(invalid)?,
            );
            let start = session.generator.as_ref().unwrap().next_event;
            let step = session
                .body
                .prepare_generator_symbol_episode(
                    table,
                    &[0],
                    options.source.clone(),
                    start,
                    Vec::new(),
                )
                .and_then(|generated| session.body.publish_incident_field(generated, true, false));
            if let Err(error) = step {
                return Ok((energies, Some(error.to_string()), balances));
            }
            session.generator.as_mut().unwrap().next_event += 1;
            energies.push(energy(session, sites));
            balances.push(session.body.inspect_current()?["energy_balance"].clone());
        }
        Ok((energies, None, balances))
    }
}

fn ratios(energies: &[f64]) -> Vec<f64> {
    energies.windows(2).map(|w| w[1] / w[0]).collect()
}

/// Complex coefficient matrix of reaction material `member` (targets × features).
fn coefficients(session: &mut NativeFieldSession<'_>, member: usize) -> Vec<Vec<(f64, f64)>> {
    fn find<'v>(value: &'v Value) -> Option<&'v Value> {
        match value {
            Value::Object(map) => map
                .get("coefficients")
                .or_else(|| map.values().find_map(find)),
            Value::Array(items) => items.iter().find_map(find),
            _ => None,
        }
    }
    let value = session.body.inspect_predictive_material(member).unwrap();
    let rat = |v: &Value| -> f64 {
        use num_traits::ToPrimitive;
        serde_json::from_value::<relational_geometry::Rat>(v.clone())
            .ok()
            .and_then(|r| r.to_f64())
            .unwrap_or(f64::NAN)
    };
    find(&value)
        .and_then(Value::as_array)
        .map(|rows| {
            rows.iter()
                .map(|row| {
                    row.as_array()
                        .unwrap()
                        .iter()
                        .map(|z| (rat(&z["real"]), rat(&z["imaginary"])))
                        .collect()
                })
                .collect()
        })
        .unwrap_or_default()
}

/// Structure of `W` on `Φ(s,c)=s⊕c⊕(c⊗s)` with `s` of 6 complex coordinates: Frobenius norms of
/// the `s`, `c` and `c⊗s` column blocks, and the largest singular value of `I + W_s`, the
/// state-independent linear gain of `incoming = s + WΦ` on the current.
fn structure(w: &[Vec<(f64, f64)>], law: crate::native::ReactionLaw) -> Value {
    if w.is_empty() {
        return json!(null);
    }
    let rows = w.len();
    let f = w[0].len();
    // Legacy `6 + 7c` (c ⊗ s); power-neutral `6 + 13c` (one slice per real contrast coordinate).
    let c = match law {
        crate::native::ReactionLaw::Legacy => (f - 6) / 7,
        crate::native::ReactionLaw::PowerNeutral => (f - 6) / 13,
    };
    let block = |from: usize, to: usize| -> f64 {
        w.iter()
            .flat_map(|r| r[from..to].iter())
            .map(|(a, b)| a * a + b * b)
            .sum::<f64>()
            .sqrt()
    };
    // Largest singular value of G = I + W_s by power iteration on G*G.
    let g = |i: usize, j: usize| -> (f64, f64) {
        let (a, b) = w[i][j];
        (a + if i == j { 1.0 } else { 0.0 }, b)
    };
    let n = rows.min(6);
    let mut v = vec![(1.0f64, 0.0f64); n];
    let mut sigma = 0.0;
    for _ in 0..200 {
        let gv: Vec<(f64, f64)> = (0..n)
            .map(|i| {
                (0..n).fold((0.0, 0.0), |acc, j| {
                    let (a, b) = g(i, j);
                    (
                        acc.0 + a * v[j].0 - b * v[j].1,
                        acc.1 + a * v[j].1 + b * v[j].0,
                    )
                })
            })
            .collect();
        let gtgv: Vec<(f64, f64)> = (0..n)
            .map(|j| {
                (0..n).fold((0.0, 0.0), |acc, i| {
                    let (a, b) = g(i, j);
                    // conj(G)ᵀ
                    (
                        acc.0 + a * gv[i].0 + b * gv[i].1,
                        acc.1 + a * gv[i].1 - b * gv[i].0,
                    )
                })
            })
            .collect();
        let norm = gtgv.iter().map(|(a, b)| a * a + b * b).sum::<f64>().sqrt();
        if norm == 0.0 {
            break;
        }
        sigma = norm.sqrt();
        v = gtgv.iter().map(|(a, b)| (a / norm, b / norm)).collect();
    }
    json!({"rows":rows,"features":f,"condition":c,"law":law,
        "s_block":block(0,6),"c_block":block(6,6+c),"cs_block":block(6+c,f),
        "sigma_max_I_plus_Ws":sigma})
}

fn law_of(session: &NativeFieldSession<'_>) -> crate::native::ReactionLaw {
    session
        .presentation
        .spec
        .generator
        .as_ref()
        .map(|g| g.field.reaction_law)
        .unwrap_or_default()
}

/// `DEPOSITION_LAW=legacy|power-neutral` overrides the declared law of the synthetic control.
fn with_law(mut spec: FieldSessionSpec) -> FieldSessionSpec {
    if let Ok(law) = std::env::var("DEPOSITION_LAW") {
        spec.generator.as_mut().unwrap().field.reaction_law =
            serde_json::from_value(json!(law)).expect("DEPOSITION_LAW");
    }
    spec
}

fn probe_pair(a: &Path, b: &Path, dir: &Path, label: &str, commits: usize) -> Value {
    let (sa, sb) = (split(a), split(b));
    let mut out = serde_json::Map::new();
    for (name, material, field) in [
        ("pre", false, false),
        ("reaction_M", true, false),
        ("field_rho_D", false, true),
        ("post", true, true),
    ] {
        let path = dir.join(format!("{label}-{name}.hna"));
        hybrid(&sa, &sb, material, field, &path);
        let result = match silent_probe(&path, commits) {
            Ok(energies) => {
                let r = ratios(&energies);
                json!({"E0":energies[0],"ratios":r,
                    "max_ratio":r.iter().cloned().fold(f64::MIN, f64::max),
                    "active":r.iter().any(|x| *x > 1.0)})
            }
            Err(error) => json!({"refused":error.to_string()}),
        };
        out.insert(name.into(), result);
    }
    Value::Object(out)
}

fn request(text: &str, commit: bool) -> FieldSectionRequest {
    FieldSectionRequest {
        text: text.into(),
        partial: None,
        output_symbols: None,
        context: vec![],
        incident_preparation: None,
        commit,
        retain_comparison: true,
    }
}

/// Synthetic long control: 48 observed cycles over a three-symbol alphabet with pseudo-random
/// passages; per observe the silent-probe split and the structure of `W`.
#[test]
#[ignore = "requires CUDA; deposition split of the silent-probe energy ratio, synthetic control"]
fn deposition_split_synthetic_long_control() {
    // Checkpoints are large; keep them on the project disk, not the tmpfs.
    let directory =
        tempfile::tempdir_in(std::env::var("DEPOSITION_DIR").unwrap_or_else(|_| ".".into()))
            .unwrap();
    let dir = directory.path();
    let spec = with_law(generator_machine::generator_session_spec(2, 8, 2).unwrap());
    let cycles = std::env::var("DEPOSITION_CYCLES")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(48usize);
    let mut pairs = Vec::new();
    super::super::with_field_session(&spec, |session| {
        let symbols = ['a', 'b', 'c'];
        session.admit_generator_source_texts(&["abc".into()])?;
        let mut seed = 0x9e3779b97f4a7c15u64;
        let mut next = || {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (seed >> 33) as usize
        };
        for cycle in 0..cycles {
            let n = 2 + next() % 6;
            let source: String = (0..n).map(|_| symbols[next() % 3]).collect();
            let target: String = (0..2).map(|_| symbols[next() % 3]).collect();
            let id = session.request(&request(&source, true))?["comparison"]
                .as_u64()
                .unwrap();
            let a = dir.join(format!("c{cycle}-A.hna"));
            let b = dir.join(format!("c{cycle}-B.hna"));
            session.checkpoint(&a, &HnaStreamState::default())?;
            let w_before = structure(&coefficients(session, 0), law_of(session));
            let observed = session.observe(id, &target, 8);
            session.checkpoint(&b, &HnaStreamState::default())?;
            let w_after = structure(&coefficients(session, 0), law_of(session));
            let refused = observed.as_ref().err().map(|e| e.to_string());
            pairs.push((cycle, a, b, w_before, w_after, refused.clone()));
            if refused.is_some() {
                break;
            }
        }
        Ok(())
    })
    .unwrap();
    for (cycle, a, b, w_before, w_after, refused) in pairs {
        let split = probe_pair(&a, &b, dir, &format!("c{cycle}"), 12);
        for name in ["pre", "reaction_M", "field_rho_D", "post"] {
            let _ = std::fs::remove_file(dir.join(format!("c{cycle}-{name}.hna")));
        }
        let _ = std::fs::remove_file(&a);
        let _ = std::fs::remove_file(&b);
        eprintln!(
            "DEPOSITION-SYNTH {}",
            json!({"cycle":cycle,"refused":refused,"W_before":w_before,"W_after":w_after,"split":split})
        );
    }
}

/// Exposure checkpoints produced by the driver at `frame − 1` (A) and `frame` (B), supplied as
/// `DEPOSITION_PAIRS=label:A:B,...`.
#[test]
#[ignore = "requires CUDA and driver checkpoints; deposition split on the exposure sample"]
fn deposition_split_exposure_pairs() {
    let Ok(pairs) = std::env::var("DEPOSITION_PAIRS") else {
        return;
    };
    let directory =
        tempfile::tempdir_in(std::env::var("DEPOSITION_DIR").unwrap_or_else(|_| ".".into()))
            .unwrap();
    for pair in pairs.split(',') {
        let parts: Vec<&str> = pair.split(':').collect();
        let (label, a, b) = (parts[0], PathBuf::from(parts[1]), PathBuf::from(parts[2]));
        let w = |path: &Path| {
            NativeFieldSavedSession::open(path)
                .unwrap()
                .with_session(|session, _| {
                    Ok(structure(&coefficients(session, 0), law_of(session)))
                })
                .unwrap()
        };
        let split = probe_pair(&a, &b, directory.path(), label, 12);
        for name in ["pre", "reaction_M", "field_rho_D", "post"] {
            let _ = std::fs::remove_file(directory.path().join(format!("{label}-{name}.hna")));
        }
        eprintln!(
            "DEPOSITION-EXPOSURE {}",
            json!({"label":label,"W_before":w(&a),"W_after":w(&b),"split":split})
        );
    }
}

/// The power-neutral law on the synthetic control: after many learning steps the committed word
/// stays passive. Checkpoints every `DEPOSITION_EVERY` cycles are probed by silent commits; each
/// per-commit energy ratio must be `≤ 1`. The deposit receipt and the reaction structure are
/// printed per checkpoint. `DEPOSITION_LAW=legacy` runs the same control under the old law.
#[test]
#[ignore = "requires CUDA; power-neutral silent-probe energy ratio after many learning steps"]
fn power_neutral_silent_probe_after_learning() {
    let directory =
        tempfile::tempdir_in(std::env::var("DEPOSITION_DIR").unwrap_or_else(|_| ".".into()))
            .unwrap();
    let kept = std::env::var("DEPOSITION_KEEP")
        .ok()
        .map(std::path::PathBuf::from);
    let dir = kept.as_deref().unwrap_or(directory.path());
    let spec = with_law(generator_machine::generator_session_spec(2, 8, 2).unwrap());
    let env = |name: &str, default: usize| {
        std::env::var(name)
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(default)
    };
    let (cycles, every, commits) = (
        env("DEPOSITION_CYCLES", 48),
        env("DEPOSITION_EVERY", 8),
        env("DEPOSITION_COMMITS", 16),
    );
    let mut checkpoints = Vec::new();
    let mut refused = None;
    super::super::with_field_session(&spec, |session| {
        let symbols = ['a', 'b', 'c'];
        session.admit_generator_source_texts(&["abc".into()])?;
        let mut seed = 0x9e3779b97f4a7c15u64;
        let mut next = || {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (seed >> 33) as usize
        };
        for cycle in 0..cycles {
            let n = 2 + next() % 6;
            let source: String = (0..n).map(|_| symbols[next() % 3]).collect();
            let target: String = (0..2).map(|_| symbols[next() % 3]).collect();
            let id = session.request(&request(&source, true))?["comparison"]
                .as_u64()
                .unwrap();
            if let Err(error) = session.observe(id, &target, 8) {
                refused = Some((cycle, error.to_string()));
                break;
            }
            if cycle % every == every - 1 || cycle + 1 == cycles {
                let path = dir.join(format!("pn{cycle}.hna"));
                session.checkpoint(&path, &HnaStreamState::default())?;
                let current = session.body.inspect_current()?;
                checkpoints.push((
                    cycle,
                    path,
                    current["reaction_deposits"].clone(),
                    structure(&coefficients(session, 0), law_of(session)),
                ));
            }
        }
        Ok(())
    })
    .unwrap();
    let mut worst = 0.0f64;
    let mut probe_refusals = 0usize;
    let mut reaction_nonzero = 0usize;
    for (cycle, path, deposits, w) in &checkpoints {
        let (energies, probe_refused, balances) = silent_probe_balanced(path, commits).unwrap();
        let r = ratios(&energies);
        let max = r.iter().cloned().fold(f64::MIN, f64::max);
        worst = worst.max(max);
        probe_refusals += usize::from(probe_refused.is_some());
        // The skew reaction's work is exactly zero in every committed word's balance.
        reaction_nonzero += balances
            .iter()
            .filter(|b| {
                let zero = |v: &Value| {
                    serde_json::from_value::<relational_geometry::Rat>(v.clone())
                        .is_ok_and(|r| num_traits::Zero::is_zero(&r))
                };
                !b.is_null() && !(zero(&b["reaction"]) && zero(&b["residual"]))
            })
            .count();
        eprintln!(
            "POWER-NEUTRAL-SYNTH {}",
            json!({"cycle":cycle,"law":law_of_spec(&spec),"energies":energies,"ratios":r,"max_ratio":max,
                "probe_refused":probe_refused,"W":w,"reaction_deposits":deposits,
                "energy_balance":balances.last()})
        );
        if std::env::var("DEPOSITION_KEEP").is_err() {
            let _ = std::fs::remove_file(path);
        }
    }
    eprintln!(
        "POWER-NEUTRAL-SYNTH-SUMMARY {}",
        json!({"cycles":cycles,"checkpoints":checkpoints.len(),"worst_ratio":worst,"probe_refusals":probe_refusals,
            "refused":refused.as_ref().map(|(c, e)| json!({"cycle":c,"error":e}))})
    );
    assert!(refused.is_none(), "learning refused: {refused:?}");
    if law_of_spec(&spec) == crate::native::ReactionLaw::PowerNeutral {
        assert_eq!(probe_refusals, 0, "a silent probe refused");
        assert_eq!(
            reaction_nonzero, 0,
            "a committed balance with nonzero reaction work or residual"
        );
        assert!(
            worst <= 1.0,
            "an active silent commit under the power-neutral law: {worst}"
        );
    }
}

fn law_of_spec(spec: &FieldSessionSpec) -> crate::native::ReactionLaw {
    spec.generator
        .as_ref()
        .map(|g| g.field.reaction_law)
        .unwrap_or_default()
}

/// Attribute a power-neutral checkpoint's silent activity to reaction blocks: silent commits with
/// each block zeroed in turn (`DEPOSITION_CHECKPOINTS=path,...`).
#[test]
#[ignore = "requires CUDA and a power-neutral checkpoint; block attribution of silent activity"]
fn power_neutral_block_attribution() {
    let Ok(paths) = std::env::var("DEPOSITION_CHECKPOINTS") else {
        return;
    };
    let commits = std::env::var("DEPOSITION_COMMITS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(16usize);
    for path in paths.split(',') {
        let mut out = serde_json::Map::new();
        for (name, linear, coupling, slices) in [
            ("as_learned", false, false, false),
            ("without_linear", true, false, false),
            ("without_coupling", false, true, false),
            ("without_slices", false, false, true),
            ("slices_only", true, true, false),
            ("coupling_only", true, false, true),
            ("without_reaction", true, true, true),
        ] {
            let result = NativeFieldSavedSession::open(Path::new(path))
                .unwrap()
                .with_session(|session, _| {
                    session
                        .body
                        .zero_reaction_blocks(linear, coupling, slices)?;
                    silent_commits(session, commits)
                })
                .unwrap();
            let r = ratios(&result.0);
            out.insert(
                name.into(),
                json!({"energies":result.0,"max_ratio":r.iter().cloned().fold(f64::MIN, f64::max),
                    "refused":result.1.map(|e| e.chars().take(120).collect::<String>())}),
            );
        }
        eprintln!(
            "POWER-NEUTRAL-BLOCKS {}",
            json!({"checkpoint":path,"variants":out})
        );
    }
}
