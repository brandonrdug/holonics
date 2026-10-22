//! Same unchanged host chain, with one genuine matched card contact consumer.
use super::*;
#[test]
#[ignore="scoped exclusive device0 native contact qualification"]
fn actual_native_material_response_and_card_contact(){
    let opened=std::time::Instant::now();
    let execution=ObservedEpochDevice::open(0).expect("actual selected card; no fallback");
    let open_ns=opened.elapsed().as_nanos();let start=std::time::Instant::now();
    let result=exterior::code_native_material_response_device(&execution);
    let reading=execution.realization_reading();
    let evidence=format!("NATIVE_CARD_RESULT device0=true fallback=false context_open_ns={open_ns} connected_ns={} counters={reading:?} result={result:?}\n",start.elapsed().as_nanos());
    println!("{evidence}");
    if let Some(root)=std::env::var_os("V93_CONTROL_ARTIFACT_DIR"){std::fs::create_dir_all(&root).unwrap();std::fs::write(std::path::Path::new(&root).join("CARD_EXECUTION.txt"),evidence).unwrap();}
    result.unwrap();
    assert_eq!(reading.native_full_tick_forwards,1);
    assert_eq!(reading.native_full_tick_returns,1);
    assert_eq!(reading.native_word_forward_launches,2);
    assert_eq!(reading.native_reverse_launches,2);
    assert_eq!(reading.fresh_response_forward_subset,1);
    assert_eq!(reading.fresh_response_reverse_subset,1);
}
