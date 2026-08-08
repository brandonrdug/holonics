//! sizing probe — temporary

use holonic_engine::grown_cell::{
    found_complex, grow, standard_cells, ComplexAperture, Schedule,
};

fn main() {
    let table = standard_cells();
    for width in [2usize, 4, 8, 16] {
        for (rule, material) in [
            ("brent-kung-adder", vec![width, width, 1]),
            ("ripple-adder", vec![width, width, 1]),
        ] {
            let growth = match grow(&table, rule, &material, Schedule::Instantiation) {
                Ok(growth) => growth,
                Err(refusal) => {
                    println!("{rule} w{width}: refused {refusal:?}");
                    continue;
                }
            };
            let grown = match found_complex(&growth, ComplexAperture::DIVISION) {
                Ok(grown) => grown,
                Err(refusal) => {
                    println!("{rule} w{width}: complex refused {refusal:?}");
                    continue;
                }
            };
            let cells = grown.complex.cells().len();
            let mut per_grade = std::collections::BTreeMap::<u32, usize>::new();
            for cell in grown.complex.cells().values() {
                *per_grade.entry(cell.grade).or_default() += 1;
            }
            println!(
                "{rule} w{width}: nets {} gates {} instances {} depth {} | cells {cells} grades {per_grade:?} arcs {} div-faces {}",
                growth.net_count(),
                growth.gate_count(),
                growth.instance_count(),
                growth.depth(),
                grown.arcs.len(),
                grown.division_faces,
            );
        }
    }
}
