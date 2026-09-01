use holonic_engine::native_ecology::holonic_intelligence::close_direct_source_neutral_cycle;

fn main() {
    match close_direct_source_neutral_cycle() {
        Ok(returned) => {
            println!(
                "{}",
                serde_json::to_string_pretty(&returned.receipt)
                    .expect("the fixed HIF6 receipt serializes")
            );
        }
        Err(error) => {
            eprintln!("HIF6 refused: {error}");
            std::process::exit(1);
        }
    }
}
