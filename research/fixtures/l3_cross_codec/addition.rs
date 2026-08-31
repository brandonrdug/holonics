fn main() {
    let left = ["left/0", "left/1"];
    let right = ["right/0", "right/1"];
    let returned = left.into_iter().chain(right).collect::<Vec<_>>();
    assert_eq!(returned.len(), 4);
    println!("{}", returned.len());
}
