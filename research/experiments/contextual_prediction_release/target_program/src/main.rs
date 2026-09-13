mod base; mod changed; mod linear;
use num_rational::BigRational as Q;
fn q(n:i64,d:i64)->Q {Q::new(n.into(),d.into())}
fn show(label:&str,v:Vec<Q>) {println!("{}:{}",label,v.iter().map(ToString::to_string).collect::<Vec<_>>().join(","));}
fn main() {
    let x=[q(2,3),q(-5,4)]; let z=[q(7,5),q(3,2)];
    show("base",base::holonic_apply(&x,&z).unwrap());
    show("changed",changed::holonic_apply(&x,&z).unwrap());
    show("linear",linear::holonic_apply(&x).unwrap());
    assert!(base::holonic_apply(&x[..1],&z).is_err());
    assert!(linear::holonic_apply(&x[..1]).is_err());
}
