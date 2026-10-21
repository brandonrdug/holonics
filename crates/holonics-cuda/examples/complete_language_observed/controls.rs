//! Twenty fixed synthetic arrivals through the actual shared training exterior; no dataset.
use super::*;

#[test]
fn unknown_backend_refuses_before_input_or_output_access() {
    assert!(
        run(&[
            "complete-language".into(),
            "train-retained-fibre-v1".into(),
            "implicit".into()
        ])
        .is_err()
    );
    assert!(
        run(&[
            "complete-language".into(),
            "sample".into(),
            "cuda-observed-epoch-device0".into()
        ])
        .is_err()
    );
}

fn exercise_fixture(label: &str, bytes: &[u8]) {
    exercise_fixture_command(label,bytes,"train-retained-fibre-v1");
}
fn exercise_fixture_command(label:&str,bytes:&[u8],command:&str){
    let root = std::env::var_os("V92_ADAPTER_FIXTURE_DIR")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| {
            std::env::temp_dir().join(format!("v92-adapter-{}", std::process::id()))
        });
    std::fs::create_dir_all(&root).unwrap();
    let root = root.join(label);
    std::fs::create_dir(&root).unwrap();
    let corpus = root.join("synthetic.bin");
    let cuts = root.join("synthetic-cuts.tsv");
    std::fs::write(&corpus, bytes).unwrap();
    let cells=bytes.len()*4;assert_eq!(cells%10,0);
    std::fs::write(&cuts,if matches!(command,"train-prepared-local-retained-fibre-v1"|"train-prepared-local-retained-held-v1"|"train-source-framing-retained-held-v1"){format!("0\tsynthetic-opening\n13\tthree-pending\n{cells}\tsynthetic-closed\n")}else{format!("0\tsynthetic-opening\n{cells}\tsynthetic-closed\n")}).unwrap();
    fn hash(path: &Path) -> String {
        let out = std::process::Command::new("sha256sum")
            .arg(path)
            .output()
            .unwrap();
        assert!(out.status.success());
        String::from_utf8(out.stdout)
            .unwrap()
            .split_whitespace()
            .next()
            .unwrap()
            .into()
    }
    for backend in ["host-reference", "cuda-observed-epoch-device0"] {
        let args = vec![
            "complete-language".into(),
            command.into(),
            backend.into(),
            corpus.to_str().unwrap().into(),
            hash(&corpus),
            cuts.to_str().unwrap().into(),
            hash(&cuts),
            "16384".into(),
            cells.to_string(),
            (cells/10).to_string(),
            root.join(backend).to_str().unwrap().into(),
        ];
        run(&args).unwrap();
        let complete =
            std::fs::read_to_string(root.join(backend).join("TRAINING_COMPLETE.json")).unwrap();
        assert!(complete.contains("\"cold_exact\":true"));
        assert!(complete.contains(&format!("\"accepted_cells\":{cells}")));
        assert!(complete.contains(&format!("\"actual_epochs\":{}",cells/10)));
        if matches!(command,"train-local-retained-fibre-v1"|"train-prepared-local-retained-fibre-v1"|"train-prepared-local-retained-held-v1"|"train-source-framing-retained-held-v1") {
            let scope=if matches!(command,"train-prepared-local-retained-held-v1"|"train-source-framing-retained-held-v1") { "LocalReceivingReturnWithHeldMap" } else { "LocalReceivingReturn" };
            assert!(complete.contains(&format!("\"deposition_scope\":\"{scope}\"")));
            let execution=std::fs::read_to_string(root.join(backend).join("EXECUTION_CONTRACT.json")).unwrap();
            assert!(execution.contains(&format!("\"command\":\"{command}\"")));
            assert!(execution.contains("\"additional_whole_section_monotone_policy_requested\":false"));
            let fresh=exterior::code_checkpoint_scope_and_source(root.join(backend).join("fresh.state").to_str().unwrap()).unwrap();
            let trained=exterior::code_checkpoint_scope_and_source(root.join(backend).join("trained.state").to_str().unwrap()).unwrap();
            assert_eq!(fresh.0,scope);assert_eq!(trained.0,fresh.0);
            assert_eq!(trained.1,fresh.1,"local command cannot silently update source E normal state");
            assert_ne!(trained.2,fresh.2,"actual local R material must move on this existing varied fixture");
            eprintln!("V93_LOCAL_CLI_OBSERVED {backend} {}",complete.trim());
        }
    }
    let mut checkpoints=vec![
        "fresh.state".to_owned(),
        "trained.state".to_owned(),
        "cut-00000.state".to_owned(),
        format!("cut-{cells:05}.state"),
    ];
    if matches!(command,"train-prepared-local-retained-fibre-v1"|"train-prepared-local-retained-held-v1"|"train-source-framing-retained-held-v1"){checkpoints.push("cut-00013.state".into());}
    for checkpoint in checkpoints {
        let host = exterior::code_checkpoint_native_bytes(
            root.join("host-reference")
                .join(&checkpoint)
                .to_str()
                .unwrap(),
        )
        .unwrap();
        let card = exterior::code_checkpoint_native_bytes(
            root.join("cuda-observed-epoch-device0")
                .join(&checkpoint)
                .to_str()
                .unwrap(),
        )
        .unwrap();
        assert_eq!(
            host, card,
            "complete native checkpoint differs: {checkpoint}"
        );
    }
    let receipt =
        std::fs::read_to_string(root.join("cuda-observed-epoch-device0/CUDA_EXECUTION.json"))
            .unwrap();
    assert!(receipt.contains("\"completed\":true"));
    eprintln!("SHARED_EXTERIOR_CUDA_PARITY {}", receipt.trim());
}

#[test]
#[ignore = "exclusive host CUDA guard; neutral synthetic CODE only"]
fn shared_complete_language_training_host_card_and_cold_parity() {
    exercise_fixture("neutral", &[0; 5]);
}
#[test]
#[ignore = "exclusive host CUDA guard; ORIGINAL varied synthetic CODE only"]
fn original_varied_complete_language_host_card_and_cold_parity() {
    exercise_fixture("original-varied", &[0x1b, 0xe4, 0x1b, 0xe4, 0x00]);
}

#[test]
#[ignore = "exclusive supported HOST CUDA guard; reciprocal CODE continuity only"]
fn reciprocal_host_card_continuity() {
    let host = exterior::code_reciprocal_continuity(&HostObservedEpochExecution).unwrap();
    let card = dispatch::TracedCard::new(ObservedEpochDevice::open(0).unwrap());
    let device = exterior::code_reciprocal_continuity(&card).unwrap();
    assert_eq!(host, device);
    let receipt = card.receipt(true);
    assert!(!receipt.contains("\"successful_card_forwards\":0"));
    eprintln!("V93_RECIPROCAL_HOST_CARD_PARITY {}", receipt.trim());
}

#[test]
#[ignore = "exclusive supported HOST CUDA guard; ordered local R then source CODE only"]
fn ordered_local_receiving_source_host_card() {
    let host = exterior::code_ordered_reciprocal(&HostObservedEpochExecution).unwrap();
    let card = dispatch::TracedCard::new(ObservedEpochDevice::open(0).unwrap());
    let device = exterior::code_ordered_reciprocal(&card).unwrap();
    assert_eq!(host, device);
    card.require_actual_dispatch().unwrap();
    eprintln!("V93_ORDERED_HOST_CARD_PARITY {}", card.receipt(true).trim());
}

#[test]
#[ignore = "exclusive supported HOST CUDA guard; local CLI synthetic40-cell whole-carry CODE only"]
fn local_retained_training_command_host_card_cold_and_scope(){
    exercise_fixture_command("local-retained",&[0x1b,0xe4,0x1b,0xe4,0x00,0x1b,0xe4,0x1b,0xe4,0x00],"train-local-retained-fibre-v1");
}

#[test]
#[ignore = "exclusive supported HOST CUDA guard; prepared forty-class synthetic CODE only"]
fn prepared_local_training_command_host_card_cold_and_scope(){
    exercise_fixture_command("prepared-local-retained",&[0x1b;10],"train-prepared-local-retained-fibre-v1");
}

struct LateAggregate(dispatch::TracedCard);
impl holonics::hnn::reference::observed::ObservedEpochExecution for LateAggregate {
    fn admit_prepared_input(&self)->Result<(),holonics::hnn::HnnError>{self.0.admit_prepared_input()}
    fn forward(&self,f:&holonics::hnn::Field,c:&holonics::hnn::Constitution,r:&holonics::hnn::pending::PendingRatio,ch:&mut holonics::hnn::chart::Charts,o:&holonics::hnn::word::WordOpening)->Result<holonics::hnn::reference::observed::ObservedEpochForwardWord,holonics::hnn::HnnError>{self.0.forward(f,c,r,ch,o)}
    fn forward_scoped(&self,c:&mut holonics::hnn::reference::observed::ObservedEpochForwardContext<'_,'_>,r:&holonics::hnn::pending::PendingRatio,ch:&mut holonics::hnn::chart::Charts,o:&holonics::hnn::word::WordOpening)->Result<holonics::hnn::reference::observed::ObservedEpochForwardWord,holonics::hnn::HnnError>{self.0.forward_scoped(c,r,ch,o)}
    fn pull_back(&self,w:holonics::hnn::Word<'_>,g:&holonics::hnn::RatioCovector,m:&holonics::ratio::linear::ExactRatMatrix,p:&holonics::hnn::ReceivingPhases)->Result<holonics::hnn::port::WordReturn,holonics::hnn::HnnError>{self.0.pull_back(w,g,m,p)}
    fn aggregate_records(&self,l:holonics::hnn::constitution::LinearLocus,r:usize,c:usize,g:u32,n:u64,e:u64,h:u64,records:&[holonics::hnn::constitution::EpochProducerRecordReading])->Result<holonics::hnn::constitution::EpochRecordFlowReading,holonics::hnn::HnnError>{
        let _actual=self.0.aggregate_records(l,r,c,g,n,e,h,records)?;
        Err(holonics::hnn::HnnError::Unadmitted{reason:"synthetic late prepared card aggregate refusal"})
    }
}
#[test]
#[ignore = "exclusive supported HOST CUDA guard; actual ten-cell prepared card rollback"]
fn prepared_late_card_refusal_is_atomic(){
    use holonics::hnn::reference::observed::ObservedEpochExecution;
    let execution=LateAggregate(dispatch::TracedCard::new(ObservedEpochDevice::open(0).unwrap()));
    let refusal=exterior::code_prepared_late_rollback(&execution).unwrap();
    assert!(refusal.contains("synthetic late prepared card aggregate refusal"));
    execution.0.require_actual_dispatch().unwrap();
    eprintln!("V93_PREPARED_LATE_CARD_ROLLBACK {}",execution.0.receipt(true).trim());
}

#[test]
#[ignore = "exclusive supported HOST CUDA; distinct ten-class ArrivalContext CODE declaration"]
fn prepared_arrival_context_lanes_share_packet(){
    let host=exterior::code_prepared_arrival_context(&HostObservedEpochExecution).unwrap();
    let execution=MirroredPrepared(dispatch::TracedCard::new(ObservedEpochDevice::open(0).unwrap()));
    let card=exterior::code_prepared_arrival_context(&execution).unwrap();
    assert_eq!(host,card,"full native/M/cold, work and actual aligned return must match BOTH prepared lanes");
    let root=std::path::PathBuf::from(std::env::var_os("V93_ARRIVAL_FIXTURE_DIR").expect("declared CODE artifact root"));
    std::fs::create_dir(&root).unwrap();
    for (name,body) in [("NATIVE_M.state",&card.0),("ENERGY.txt",&card.1),("ALIGNED_RETURN.txt",&card.2)]{std::fs::write(root.join(name),body).unwrap();}
    std::fs::write(root.join("CUDA_EXECUTION.json"),execution.0.receipt(false)).unwrap();
    eprintln!("V93_PREPARED_ARRIVAL_CONTEXT_PARITY {}",execution.0.receipt(false).trim());
}

struct MirroredPrepared(dispatch::TracedCard);
struct MatchedWord {host:Box<dyn holonics::hnn::reference::observed::ObservedEpochWord>,card:Box<dyn holonics::hnn::reference::observed::ObservedEpochWord>}
impl std::fmt::Debug for MatchedWord{fn fmt(&self,f:&mut std::fmt::Formatter<'_>)->std::fmt::Result{f.write_str("MatchedActualPreparedWords")}}
impl holonics::hnn::reference::observed::ObservedEpochWord for MatchedWord {
    fn charts(&self)->Vec<holonics::hnn::chart::ChartReading>{self.host.charts()}
    fn tube_passages(&self)->Result<Vec<holonics::hnn::ring::TubePassage>,holonics::hnn::HnnError>{self.host.tube_passages()}
    fn return_at(self:Box<Self>,f:&holonics::hnn::Field,e:&dyn holonics::hnn::reference::observed::ObservedEpochExecution,g:&holonics::hnn::RatioCovector,m:&holonics::ratio::linear::ExactRatMatrix,p:&holonics::hnn::ReceivingPhases)->Result<holonics::hnn::port::WordReturn,holonics::hnn::HnnError>{
        let host=self.host.return_at(f,e,g,m,p)?;let card=self.card.return_at(f,e,g,m,p)?;
        assert_eq!(format!("{host:?}"),format!("{card:?}"),"both prepared lanes must return the actual SAME covector exactly");Ok(host)
    }
}
impl holonics::hnn::reference::observed::ObservedEpochExecution for MirroredPrepared {
    fn admit_prepared_input(&self)->Result<(),holonics::hnn::HnnError>{self.0.admit_prepared_input()}
    fn forward(&self,f:&holonics::hnn::Field,c:&holonics::hnn::Constitution,r:&holonics::hnn::pending::PendingRatio,ch:&mut holonics::hnn::chart::Charts,o:&holonics::hnn::word::WordOpening)->Result<holonics::hnn::reference::observed::ObservedEpochForwardWord,holonics::hnn::HnnError>{
        let mut card_charts=ch.clone();let mut host=HostObservedEpochExecution.forward(f,c,r,ch,o)?;let card=self.0.forward(f,c,r,&mut card_charts,o)?;
        assert_eq!(host.faces,card.faces);assert_eq!(host.anchors,card.anchors);assert_eq!(host.reception_end,card.reception_end);assert_eq!(host.source_preparation,card.source_preparation);
        host.word=Box::new(MatchedWord{host:host.word,card:card.word});Ok(host)
    }
    fn pull_back(&self,w:holonics::hnn::Word<'_>,g:&holonics::hnn::RatioCovector,m:&holonics::ratio::linear::ExactRatMatrix,p:&holonics::hnn::ReceivingPhases)->Result<holonics::hnn::port::WordReturn,holonics::hnn::HnnError>{HostObservedEpochExecution.pull_back(w,g,m,p)}
    fn aggregate_records(&self,l:holonics::hnn::constitution::LinearLocus,r:usize,c:usize,g:u32,n:u64,e:u64,h:u64,records:&[holonics::hnn::constitution::EpochProducerRecordReading])->Result<holonics::hnn::constitution::EpochRecordFlowReading,holonics::hnn::HnnError>{self.0.aggregate_records(l,r,c,g,n,e,h,records)}
}

#[test]
#[ignore = "exclusive supported HOST CUDA; held-policy ordinary40-class prepared/cold boundary"]
fn held_prepared_local_training_host_card_and_cold(){
    exercise_fixture_command("held-prepared-local-retained",&[0x1b;10],"train-prepared-local-retained-held-v1");
}
#[test]
#[ignore = "exclusive supported HOST CUDA; explicit held-policy late10class card fault"]
fn held_prepared_late_card_fault_is_atomic(){
    let execution=LateAggregate(dispatch::TracedCard::new(ObservedEpochDevice::open(0).unwrap()));
    let refusal=exterior::code_held_prepared_late_rollback(&execution).unwrap();
    assert!(refusal.contains("synthetic late prepared card aggregate refusal"));
    execution.0.require_actual_dispatch().unwrap();
    eprintln!("HELD_PREPARED_CARD_FAULT {}",execution.0.receipt(false).trim());
}

#[test]
#[ignore = "exclusive supported HOST CUDA; framed40-class command/cold boundary"]
fn source_framing_training_host_card_and_cold(){
    exercise_fixture_command("source-framing-retained",&[0x1b;10],"train-source-framing-retained-held-v1");
}
#[test]
#[ignore = "exclusive supported HOST CUDA; framed late10class rollback"]
fn source_framing_late_card_fault_is_atomic(){
    let execution=LateAggregate(dispatch::TracedCard::new(ObservedEpochDevice::open(0).unwrap()));
    let refusal=exterior::code_framed_prepared_late_rollback(&execution).unwrap();
    assert!(refusal.contains("synthetic late prepared card aggregate refusal"));
    execution.0.require_actual_dispatch().unwrap();
    eprintln!("SOURCE_FRAMING_CARD_FAULT {}",execution.0.receipt(false).trim());
}
