//! Process-separated persistence control on actual admitted native material. The engine owns
//! every recurrence; this application only transports occurrences, checkpoints and comparison data.
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::holonic_intelligence::{
        mount_operator_surface, NativeConeRestrictedEcology, NativeFullOperatorSession,
        NativeOperatorResidence, NativeReturnAperture,
    },
};
use holonics_hna::{
    publish_new, read_checkpoint, read_session_checkpoint, save_checkpoint_new, HnaBaseDependency,
    HnaModel, HnaOccurrence,
};
use serde_json::json;
use std::{
    collections::BTreeMap,
    io::{self, BufReader, Write},
    path::Path,
};

fn occurrences(
    base: &NativeConeRestrictedEcology,
) -> Result<Vec<Vec<u32>>, Box<dyn std::error::Error>> {
    let family: BTreeMap<_, _> = base
        .classes
        .iter()
        .flat_map(|class| {
            class
                .fibre
                .iter()
                .map(|held| (held.occurrence, held.addresses.clone()))
        })
        .collect();
    let history = base.histories.first().ok_or("empty history")?;
    let mut result = Vec::new();
    for (_, mut addresses) in family.into_iter().take(3) {
        base.admit(&addresses, history)
            .map_err(|e| format!("admission: {e:?}"))?;
        addresses.extend_from_slice(history);
        result.push(addresses);
    }
    if result.len() != 3 {
        return Err("three declared occurrences required".into());
    }
    Ok(result)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = std::env::args().collect();
    let started = std::time::Instant::now();
    match args.get(1).map(String::as_str) {
        Some("compare-stream") if args.len() == 4 => {
            let actual = read_session_checkpoint(&args[2])?;
            let (_, expected) = read_checkpoint(&args[3])?;
            assert!(actual.state == expected, "streamed native successor differs from its complete reference");
            let transport = actual.transport.ok_or("stream checkpoint lacks transport state")?;
            println!("{}", json!({"schema":"holonics.hnp3.stream-state-control.v1",
                "complete_native_rest_equal":true,"generation":expected.header.generation,
                "sequence":transport.sequence,"pending_input_octets":transport.input.len(),
                "pending_output_octets":transport.output.as_ref().map_or(0,Vec::len),
                "output_accepted":transport.output_accepted,"closed":transport.closed}));
        }
        Some("write") if args.len() == 5 => {
            eprintln!("HNP3: pinning and loading base");
            let dependency = HnaBaseDependency::capture(&args[2], None)?;
            let mut source = BufReader::new(dependency.open_verified(None)?);
            let base = NativeConeRestrictedEcology::read_rest_from(&mut source)?;
            let occurrences = occurrences(&base)?;
            let readout = ResidentReadout::new()?;
            let surface = mount_operator_surface(&readout)?;
            let mut intake = base.intake(dependency.class)?;
            let mut residence = NativeOperatorResidence::mount_from_intake(&surface, &base.ecology, &mut intake)?;
            let mut session = NativeFullOperatorSession::found_with_passage_return(&base.ecology,
                &mut residence, NativeReturnAperture { learning_shift: 16, series_terms: 14 })?;
            eprintln!("HNP3: native development at {:?}", started.elapsed());
            for occurrence in &occurrences { session.advance_cycle_retained(occurrence)?; }
            let generation = session.generation();
            let rank = session.morphology_overlay_rank();
            assert!(session.advance_cycle_retained(&[]).is_err());
            assert!(session.interruption().is_none());
            assert_eq!(session.generation(), generation);
            assert_eq!(session.morphology_overlay_rank(), rank);
            eprintln!("HNP3: detaching generation {generation}, factor extent {rank}");
            let state = session.detach_rest()?;
            assert!(state.terminal_carrier.is_some());
            assert!(!state.overlay.is_empty());
            let checkpoint = Path::new(&args[3]);
            if let Some(parent) = checkpoint.parent() { std::fs::create_dir_all(parent)?; }
            let failed_path = checkpoint.with_extension("interrupted-attempt");
            let failed = publish_new(&failed_path, |file| {
                file.write_all(b"partial checkpoint")?;
                Err::<(), _>(io::Error::new(io::ErrorKind::Interrupted, "declared publication control"))
            });
            assert!(failed.is_err() && !failed_path.exists());
            assert_eq!(session.generation(), generation, "writer failure retains the actual live owner");
            let saved = save_checkpoint_new(checkpoint, &dependency, &state)?;
            drop(state);
            eprintln!("HNP3: published {} bytes; computing the later reference", saved.publication.bytes);
            session.advance_cycle_retained(&occurrences[0])?;
            let after = session.detach_rest()?;
            save_checkpoint_new(&args[4], &dependency, &after)?;
            println!("{}", json!({"schema":"holonics.hnp3.checkpoint-control.v1","phase":"write",
                "checkpoint":checkpoint,"expected_after":args[4],"checkpoint_octets":saved.publication.bytes,
                "saved_generation":generation,"saved_rank":rank,"next_generation":session.generation(),
                "next_rank":session.morphology_overlay_rank(),"failed_publication_preserved_owner":true,
                "elapsed_millis":started.elapsed().as_millis()}));
        }
        Some("resume") if args.len() == 4 || args.len() == 5 => {
            eprintln!("HNP3: verifying and decoding checkpoint");
            let (dependency, state) = read_checkpoint(&args[2])?;
            let (_, expected) = read_checkpoint(&args[3])?;
            let override_path = args.get(4).map(Path::new);
            let mut source = BufReader::new(dependency.open_verified(override_path)?);
            let base = NativeConeRestrictedEcology::read_rest_from(&mut source)?;
            let occurrences = occurrences(&base)?;
            let readout = ResidentReadout::new()?;
            let surface = mount_operator_surface(&readout)?;
            let mut intake = base.intake(dependency.class)?;
            let mut residence = NativeOperatorResidence::mount_from_intake(&surface, &base.ecology, &mut intake)?;
            let mut session = NativeFullOperatorSession::remount_rest(&base.ecology, &mut residence, &state)?;
            eprintln!("HNP3: remounted at {:?}; comparing complete held state", started.elapsed());
            assert!(session.detach_rest()? == state, "complete state changed across remount");
            drop(state);
            session.advance_cycle_retained(&occurrences[0])?;
            let returned = session.detach_rest()?;
            assert!(returned == expected, "later complete successor differs after process restart");
            println!("{}", json!({"schema":"holonics.hnp3.checkpoint-control.v1","phase":"resume",
                "checkpoint":args[2],"complete_rest_equal":true,"complete_later_successor_equal":true,
                "generation":session.generation(),"rank":session.morphology_overlay_rank(),
                "elapsed_millis":started.elapsed().as_millis()}));
        }
        Some("api") if args.len() == 4 || args.len() == 5 => {
            let (_, expected) = read_checkpoint(args.get(4).unwrap_or(&args[2]))?;
            let model = HnaModel::from_checkpoint(&args[2], None)?;
            let occurrence = model.declared_occurrences().into_iter().min_by_key(|o| o.ordinal)
                .ok_or("declared occurrence absent")?.occurrence;
            let anatomy = model.with_session(|session| {
                let before = session.anatomy();
                let outside = HnaOccurrence { row_addresses: vec![u32::MAX], history: vec![] };
                assert!(session.advance(&outside).is_err());
                assert_eq!(session.anatomy(), before, "rejected public input preserves the continuing owner");
                if args.len() == 5 { session.advance(&occurrence)?; }
                session.checkpoint(&args[3])?;
                Ok(session.anatomy())
            })?;
            let (_, returned) = read_checkpoint(&args[3])?;
            assert!(returned == expected);
            println!("{}", json!({"schema":"holonics.hnp3.checkpoint-control.v1","phase":"public-api",
                "complete_rest_equal":true,"outside_admission_preserved_owner":true,"anatomy":anatomy}));
        }
        _ => return Err("usage: checkpoint_hnp3 write BASE CHECKPOINT EXPECTED_AFTER | resume CHECKPOINT EXPECTED_AFTER [BASE_OVERRIDE] | api CHECKPOINT REWRITTEN_CHECKPOINT".into()),
    }
    Ok(())
}
