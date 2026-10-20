//! Exact source diagnostic of the original varied fixture; no changed mathematical law.
use super::*;
use holonics::hnn::chart::Charts;
use holonics::hnn::constitution::{Constitution, EpochProducerRecordReading, EpochRecordFlowReading, LinearLocus, Sample, epoch_record_operands};
use holonics::hnn::field::Field;
use holonics::hnn::pending::PendingRatio;
use holonics::hnn::port::WordReturn;
use holonics::hnn::ratio::RatioCovector;
use holonics::hnn::receiving::ReceivingPhases;
use holonics::hnn::reference::observed::{ObservedEpochExecution, ObservedEpochForwardWord};
use holonics::hnn::word::{Word, WordOpening};
use holonics::hnn::HnnError;
use holonics::ratio::{Rat, integer};
use holonics::ratio::linear::ExactRatMatrix;
use num_bigint::BigInt;
use std::sync::Mutex;

struct InspectHost { witnesses: Mutex<Vec<String>> }
impl ObservedEpochExecution for InspectHost {
    fn forward(&self, field: &Field, constitution: &Constitution, ratio: &PendingRatio, charts: &mut Charts, opening: &WordOpening) -> Result<ObservedEpochForwardWord, HnnError> {
        HostObservedEpochExecution.forward(field, constitution, ratio, charts, opening)
    }
    fn pull_back(&self, word: Word<'_>, covector: &RatioCovector, map: &ExactRatMatrix, phases: &ReceivingPhases) -> Result<WordReturn, HnnError> {
        let back = HostObservedEpochExecution.pull_back(word, covector, map, phases)?;
        let descent = covector.descent(0);
        assert_eq!(phases.ring(), 2);
        assert_eq!(back.reads.len(), 1);
        assert_eq!(back.reads[0].1, covector.logits()[0]);
        let feature = &back.reads[0].0;
        let odd = |v: &Rat| v.denom() >> v.denom().trailing_zeros().unwrap() as usize;
        assert!(feature.iter().all(|v| odd(v) == BigInt::from(1)), "feature rows must not confound the covector diagnostic");
        let phase_rows: Vec<_> = (1..descent.len()).step_by(2).collect();
        let sample = Sample { weight: integer(1), feature: feature.clone(), covector: descent.clone(), masses: None };
        if let Err(error) = epoch_record_operands(&[sample], &phase_rows, 3) {
            for (row, value) in descent.iter().enumerate() {
                let divisor = if row % 2 == 0 { 1 } else { 3 };
                let odd_part = odd(value);
                if BigInt::from(divisor) % &odd_part != BigInt::from(0) {
                    self.witnesses.lock().unwrap().push(format!(
                        "{{\"locus\":\"ReceivingMap(2)\",\"row\":{row},\"scope\":\"{}\",\"value\":\"{value}\",\"numerator\":\"{}\",\"denominator\":\"{}\",\"odd_part\":\"{odd_part}\",\"declared_divisor\":{divisor},\"feature_dyadic\":true,\"actual_sample_covector_equals_return_descent\":true,\"typed_refusal\":\"Unadmitted\",\"reason\":\"{error}\"}}",
                        if row % 2 == 0 { "aligned-class-return" } else { "unchanged-phase" }, value.numer(), value.denom()));
                }
            }
        }
        Ok(back)
    }
    fn aggregate_records(&self, locus: LinearLocus, rows: usize, columns: usize, grain: u32, cells: u64, epoch: u64, heard: u64, records: &[EpochProducerRecordReading]) -> Result<EpochRecordFlowReading, HnnError> {
        HostObservedEpochExecution.aggregate_records(locus, rows, columns, grain, cells, epoch, heard, records)
    }
}

#[test]
fn original_varied_refusal_exposes_exact_class_row() {
    let root = std::path::PathBuf::from(std::env::var_os("V92_ADAPTER_REFUSAL_DIR").expect("declared isolated diagnostic path"));
    std::fs::create_dir(&root).unwrap();
    let corpus = root.join("original-varied.bin"); let cuts = root.join("cuts.tsv");
    std::fs::write(&corpus, [0x1b, 0xe4, 0x1b, 0xe4, 0x00]).unwrap();
    std::fs::write(&cuts, b"0\topening\n20\tclosed\n").unwrap();
    let hash = |p: &Path| { let x=std::process::Command::new("sha256sum").arg(p).output().unwrap(); assert!(x.status.success()); String::from_utf8(x.stdout).unwrap().split_whitespace().next().unwrap().to_owned() };
    let execution = InspectHost { witnesses: Mutex::default() };
    let args = vec!["train-retained-fibre-v1".into(), "host-reference".into(), corpus.to_str().unwrap().into(), hash(&corpus), cuts.to_str().unwrap().into(), hash(&cuts), "16384".into(), "20".into(), "2".into(), root.join("training").to_str().unwrap().into()];
    let error = run_complete_language_with_execution(&args, &execution, CompleteLanguageTrainingBackend::HostReference).unwrap_err();
    assert!(error.to_string().contains("an epoch row denominator must divide"));
    let mut witnesses = execution.witnesses.into_inner().unwrap(); witnesses.sort(); witnesses.dedup();
    assert!(!witnesses.is_empty());
    assert!(witnesses.iter().all(|v| v.contains("aligned-class-return")), "a phase row supplied an unqualified denominator");
    std::fs::write(root.join("EXACT_ROW_WITNESSES.json"), format!("{{\"status\":\"REPRODUCED_TYPED_REFUSAL\",\"phase_rows_admitted\":true,\"witnesses\":[{}]}}\n", witnesses.join(","))).unwrap();
    eprintln!("EXACT_CLASS_ROW_WITNESS {}", witnesses[0]);
}
