//! N3 — a separately addressed world return cultivates the native mathematical ecology.

#[path = "n3/artifact.rs"]
mod artifact;
#[path = "n3/cultivation.rs"]
mod cultivation;
#[path = "n3/product.rs"]
mod product;
#[path = "n3/world_return.rs"]
mod world_return;

use std::path::Path;

fn main() {
    let arguments = std::env::args().skip(1).collect::<Vec<_>>();
    let result = match arguments.as_slice() {
        [flag, input, output] if flag == "--optical-return" => {
            world_return::recover(Path::new(input), Path::new(output))
        }
        [flag, rest, sections, output] if flag == "--detached" => {
            product::detached(Path::new(rest), Path::new(sections), Path::new(output))
        }
        [] => product::construct(&product::root(), Path::new(product::DEFAULT_OUT)),
        [output] => product::construct(&product::root(), Path::new(output)),
        _ => Err("usage: [OUTPUT] | --optical-return INPUT OUTPUT | --detached REST SECTIONS OUTPUT".to_owned()),
    };
    if let Err(error) = result {
        eprintln!("N3 refused: {error}");
        std::process::exit(1);
    }
}
