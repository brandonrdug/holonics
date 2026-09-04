//! N1 bounded return — raw pixels found optical mathematical incidence without a transcript.

#[path = "n1/artifact.rs"]
mod artifact;
#[path = "n1/product.rs"]
mod product;
#[path = "n1/render.rs"]
mod render;

fn main() {
    let arguments = std::env::args().collect::<Vec<_>>();
    let result = if arguments.get(1).map(String::as_str) == Some("--detached") {
        if arguments.len() != 4 {
            Err("usage: --detached REST RECEIPT".to_owned())
        } else {
            product::detached(arguments[2].as_ref(), arguments[3].as_ref())
        }
    } else {
        let out = arguments
            .get(1)
            .map(String::as_str)
            .unwrap_or(product::DEFAULT_OUT);
        product::construct(&product::root(), out)
    };
    if let Err(error) = result {
        eprintln!("N1 refused: {error}");
        std::process::exit(1);
    }
}
