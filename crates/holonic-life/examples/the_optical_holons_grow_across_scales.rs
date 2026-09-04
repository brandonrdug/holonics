//! E1 — a raw page returns simultaneous optical holons from components through equations/page.

#[path = "e1/artifact.rs"]
mod artifact;
#[path = "e1/product.rs"]
mod product;
#[path = "e1/render.rs"]
mod render;

fn main() {
    let arguments = std::env::args().collect::<Vec<_>>();
    let returned = match arguments.get(1).map(String::as_str) {
        Some("--detached") if arguments.len() == 4 => {
            product::detached(arguments[2].as_ref(), arguments[3].as_ref())
        }
        Some("--detached") => Err("usage: --detached REST RETURN".to_owned()),
        _ => product::construct(
            &product::root(),
            arguments
                .get(1)
                .map(String::as_str)
                .unwrap_or(product::DEFAULT_OUT),
        ),
    };
    if let Err(error) = returned {
        eprintln!("E1 refused: {error}");
        std::process::exit(1);
    }
}
