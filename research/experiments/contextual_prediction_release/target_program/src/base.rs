// Generated from a retained exact Holonic factor graph.
// domain: left [2], right [2]; output [2]; products [3]
pub fn holonic_apply(left: &[num_rational::BigRational], right: &[num_rational::BigRational]) -> Result<Vec<num_rational::BigRational>, &'static str> {
    if left.len() != 2 { return Err("left input extent mismatch"); }
    if right.len() != 2 { return Err("right input extent mismatch"); }
    let left_0 = (num_rational::BigRational::new(num_bigint::BigInt::parse_bytes(b"1", 10).ok_or("invalid generated numerator")?, num_bigint::BigInt::parse_bytes(b"1", 10).ok_or("invalid generated denominator")?)) * &left[0];
    let right_0 = (num_rational::BigRational::new(num_bigint::BigInt::parse_bytes(b"1", 10).ok_or("invalid generated numerator")?, num_bigint::BigInt::parse_bytes(b"1", 10).ok_or("invalid generated denominator")?)) * &right[0];
    let product_0 = left_0 * right_0;
    let left_1 = (num_rational::BigRational::new(num_bigint::BigInt::parse_bytes(b"1", 10).ok_or("invalid generated numerator")?, num_bigint::BigInt::parse_bytes(b"1", 10).ok_or("invalid generated denominator")?)) * &left[1];
    let right_1 = (num_rational::BigRational::new(num_bigint::BigInt::parse_bytes(b"1", 10).ok_or("invalid generated numerator")?, num_bigint::BigInt::parse_bytes(b"1", 10).ok_or("invalid generated denominator")?)) * &right[1];
    let product_1 = left_1 * right_1;
    let left_2 = (num_rational::BigRational::new(num_bigint::BigInt::parse_bytes(b"1", 10).ok_or("invalid generated numerator")?, num_bigint::BigInt::parse_bytes(b"1", 10).ok_or("invalid generated denominator")?)) * &left[0] + (num_rational::BigRational::new(num_bigint::BigInt::parse_bytes(b"1", 10).ok_or("invalid generated numerator")?, num_bigint::BigInt::parse_bytes(b"1", 10).ok_or("invalid generated denominator")?)) * &left[1];
    let right_2 = (num_rational::BigRational::new(num_bigint::BigInt::parse_bytes(b"1", 10).ok_or("invalid generated numerator")?, num_bigint::BigInt::parse_bytes(b"1", 10).ok_or("invalid generated denominator")?)) * &right[0] + (num_rational::BigRational::new(num_bigint::BigInt::parse_bytes(b"1", 10).ok_or("invalid generated numerator")?, num_bigint::BigInt::parse_bytes(b"1", 10).ok_or("invalid generated denominator")?)) * &right[1];
    let product_2 = left_2 * right_2;
    Ok(vec![
        (num_rational::BigRational::new(num_bigint::BigInt::parse_bytes(b"1", 10).ok_or("invalid generated numerator")?, num_bigint::BigInt::parse_bytes(b"1", 10).ok_or("invalid generated denominator")?)) * &product_0 + (num_rational::BigRational::new(num_bigint::BigInt::parse_bytes(b"-1", 10).ok_or("invalid generated numerator")?, num_bigint::BigInt::parse_bytes(b"1", 10).ok_or("invalid generated denominator")?)) * &product_1,
        (num_rational::BigRational::new(num_bigint::BigInt::parse_bytes(b"-1", 10).ok_or("invalid generated numerator")?, num_bigint::BigInt::parse_bytes(b"1", 10).ok_or("invalid generated denominator")?)) * &product_0 + (num_rational::BigRational::new(num_bigint::BigInt::parse_bytes(b"-1", 10).ok_or("invalid generated numerator")?, num_bigint::BigInt::parse_bytes(b"1", 10).ok_or("invalid generated denominator")?)) * &product_1 + (num_rational::BigRational::new(num_bigint::BigInt::parse_bytes(b"1", 10).ok_or("invalid generated numerator")?, num_bigint::BigInt::parse_bytes(b"1", 10).ok_or("invalid generated denominator")?)) * &product_2,
    ])
}
