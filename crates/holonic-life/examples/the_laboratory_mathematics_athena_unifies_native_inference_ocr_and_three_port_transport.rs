//! N4 — freeze the bounded laboratory mathematics Athena as one source-detached ecology.

#[path = "n3/artifact.rs"]
mod artifact;
#[allow(dead_code)]
#[path = "n3/cultivation.rs"]
mod cultivation;
#[path = "n4/product.rs"]
mod product;
#[path = "n4/rest.rs"]
mod rest;
#[path = "n3/world_return.rs"]
mod world_return;

use std::path::Path;

fn main() {
    let arguments = std::env::args().skip(1).collect::<Vec<_>>();
    let result = match arguments.as_slice() {
        [flag, input, output] if flag == "--optical-return" => {
            world_return::recover(Path::new(input), Path::new(output))
        }
        [flag, rest, applications, output] if flag == "--detached" => {
            product::detached(Path::new(rest), Path::new(applications), Path::new(output))
        }
        [] => product::construct(&product::root(), Path::new(product::DEFAULT_OUT)),
        [output] => product::construct(&product::root(), Path::new(output)),
        _ => Err(
            "usage: [OUTPUT] | --optical-return INPUT OUTPUT | --detached REST APPLICATIONS OUTPUT"
                .to_owned(),
        ),
    };
    if let Err(error) = result {
        eprintln!("N4 refused: {error}");
        std::process::exit(1);
    }
}
