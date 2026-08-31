fn main() {
    let first_population = ["first/a", "first/b"];
    let second_population = ["second/a", "second/b"];
    let joint_population = first_population
        .into_iter()
        .chain(second_population)
        .collect::<Vec<_>>();
    assert_eq!(joint_population.len(), 4);
    println!("{}", joint_population.len());
}
