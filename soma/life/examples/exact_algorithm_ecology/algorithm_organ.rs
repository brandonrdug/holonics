use std::fmt;

pub const PROGRAM_SCHEMA_TAG: u64 = 2_000;
pub const PROGRAM_DOMAIN_TAG: u64 = 2_001;
pub const PROGRAM_NODE_COUNT_TAG: u64 = 2_002;
pub const PROGRAM_OUTPUT_TAG: u64 = 2_003;
pub const NODE_KIND_TAG: u64 = 2_010;
pub const NODE_LEFT_TAG: u64 = 2_011;
pub const NODE_RIGHT_TAG: u64 = 2_012;
pub const NODE_INPUT_TAG: u64 = 2_013;
pub const NODE_SHIFT_TAG: u64 = 2_014;
pub const NODE_CONST_KIND_TAG: u64 = 2_015;
pub const NODE_CONST_SIGN_TAG: u64 = 2_016;
pub const NODE_CONST_MAGNITUDE_TAG: u64 = 2_017;
pub const NODE_CONST_DENOMINATOR_TAG: u64 = 2_018;
pub const NODE_CONST_UNIT_TAG: u64 = 2_019;

const PROGRAM_SCHEMA: u64 = 1;
const VALUE_RATIONAL: u64 = 2;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AlgorithmWord {
    pub tag: u64,
    pub coordinates: Vec<u64>,
    pub value: u64,
}

impl AlgorithmWord {
    pub fn scalar(tag: u64, value: u64) -> Self {
        Self {
            tag,
            coordinates: Vec::new(),
            value,
        }
    }

    pub fn at(tag: u64, coordinates: impl Into<Vec<u64>>, value: u64) -> Self {
        Self {
            tag,
            coordinates: coordinates.into(),
            value,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Rational {
    pub numerator: i128,
    pub denominator: i128,
}

impl Rational {
    pub fn new(numerator: i128, denominator: i128) -> Result<Self, String> {
        if denominator == 0 {
            return Err("the exact rational denominator is zero".to_owned());
        }
        let mut numerator = numerator;
        let mut denominator = denominator;
        if denominator < 0 {
            numerator = numerator
                .checked_neg()
                .ok_or_else(|| "rational sign normalization overflowed".to_owned())?;
            denominator = denominator
                .checked_neg()
                .ok_or_else(|| "rational sign normalization overflowed".to_owned())?;
        }
        let divisor = gcd(
            numerator
                .checked_abs()
                .ok_or_else(|| "rational magnitude overflowed".to_owned())?,
            denominator,
        );
        Ok(Self {
            numerator: numerator / divisor,
            denominator: denominator / divisor,
        })
    }

    fn checked_add(self, other: Self) -> Result<Self, String> {
        let numerator = self
            .numerator
            .checked_mul(other.denominator)
            .and_then(|left| {
                other
                    .numerator
                    .checked_mul(self.denominator)
                    .and_then(|right| left.checked_add(right))
            })
            .ok_or_else(|| "exact rational addition overflowed".to_owned())?;
        let denominator = self
            .denominator
            .checked_mul(other.denominator)
            .ok_or_else(|| "exact rational addition overflowed".to_owned())?;
        Self::new(numerator, denominator)
    }

    fn checked_sub(self, other: Self) -> Result<Self, String> {
        let numerator = self
            .numerator
            .checked_mul(other.denominator)
            .and_then(|left| {
                other
                    .numerator
                    .checked_mul(self.denominator)
                    .and_then(|right| left.checked_sub(right))
            })
            .ok_or_else(|| "exact rational subtraction overflowed".to_owned())?;
        let denominator = self
            .denominator
            .checked_mul(other.denominator)
            .ok_or_else(|| "exact rational subtraction overflowed".to_owned())?;
        Self::new(numerator, denominator)
    }

    fn checked_mul(self, other: Self) -> Result<Self, String> {
        Self::new(
            self.numerator
                .checked_mul(other.numerator)
                .ok_or_else(|| "exact rational multiplication overflowed".to_owned())?,
            self.denominator
                .checked_mul(other.denominator)
                .ok_or_else(|| "exact rational multiplication overflowed".to_owned())?,
        )
    }

    fn checked_div(self, other: Self) -> Result<Self, String> {
        if other.numerator == 0 {
            return Err("division by the presented zero divisor is OPEN".to_owned());
        }
        Self::new(
            self.numerator
                .checked_mul(other.denominator)
                .ok_or_else(|| "exact rational division overflowed".to_owned())?,
            self.denominator
                .checked_mul(other.numerator)
                .ok_or_else(|| "exact rational division overflowed".to_owned())?,
        )
    }
}

impl fmt::Display for Rational {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.denominator == 1 {
            write!(formatter, "{}", self.numerator)
        } else {
            write!(formatter, "{}/{}", self.numerator, self.denominator)
        }
    }
}

fn gcd(mut left: i128, mut right: i128) -> i128 {
    while right != 0 {
        let remainder = left % right;
        left = right;
        right = remainder;
    }
    left.max(1)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExactValue {
    Word { bits: u8, value: u64 },
    Rational(Rational),
}

impl ExactValue {
    pub fn word(bits: u8, value: u64) -> Result<Self, String> {
        if bits == 0 || bits > 63 {
            return Err(format!("word width {bits} is outside 1..=63"));
        }
        Ok(Self::Word {
            bits,
            value: value & word_mask(bits),
        })
    }

    pub fn rational(numerator: i128, denominator: i128) -> Result<Self, String> {
        Ok(Self::Rational(Rational::new(numerator, denominator)?))
    }

    pub fn display(self) -> String {
        match self {
            Self::Word { bits, value } => format!("{value}:u{bits}"),
            Self::Rational(value) => value.to_string(),
        }
    }
}

fn word_mask(bits: u8) -> u64 {
    (1u64 << bits) - 1
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Unit {
    /// Exact exponents of `(length, time, current, voltage)`.
    pub exponents: [i8; 4],
}

impl Unit {
    pub const DIMENSIONLESS: Self = Self {
        exponents: [0, 0, 0, 0],
    };
    pub const LENGTH: Self = Self {
        exponents: [1, 0, 0, 0],
    };
    pub const TIME: Self = Self {
        exponents: [0, 1, 0, 0],
    };
    pub const CURRENT: Self = Self {
        exponents: [0, 0, 1, 0],
    };
    pub const VOLTAGE: Self = Self {
        exponents: [0, 0, 0, 1],
    };
    pub const RESISTANCE: Self = Self {
        exponents: [0, 0, -1, 1],
    };

    fn checked_mul(self, other: Self) -> Result<Self, String> {
        let mut exponents = [0i8; 4];
        for (at, exponent) in exponents.iter_mut().enumerate() {
            *exponent = self.exponents[at]
                .checked_add(other.exponents[at])
                .ok_or_else(|| "unit multiplication overflowed".to_owned())?;
        }
        Ok(Self { exponents })
    }

    fn checked_div(self, other: Self) -> Result<Self, String> {
        let mut exponents = [0i8; 4];
        for (at, exponent) in exponents.iter_mut().enumerate() {
            *exponent = self.exponents[at]
                .checked_sub(other.exponents[at])
                .ok_or_else(|| "unit division overflowed".to_owned())?;
        }
        Ok(Self { exponents })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Quantity {
    pub value: ExactValue,
    pub unit: Unit,
}

impl Quantity {
    pub fn word(bits: u8, value: u64) -> Result<Self, String> {
        Ok(Self {
            value: ExactValue::word(bits, value)?,
            unit: Unit::DIMENSIONLESS,
        })
    }

    pub fn rational(numerator: i128, denominator: i128, unit: Unit) -> Result<Self, String> {
        Ok(Self {
            value: ExactValue::rational(numerator, denominator)?,
            unit,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Node {
    Input(usize),
    Constant(Quantity),
    Add(usize, usize),
    Subtract(usize, usize),
    Multiply(usize, usize),
    ShiftLeft { source: usize, places: u8 },
    Divide(usize, usize),
    Return(usize),
}

impl Node {
    pub fn operation(&self) -> &'static str {
        match self {
            Self::Input(_) => "INPUT",
            Self::Constant(_) => "CONST",
            Self::Add(_, _) => "ADD",
            Self::Subtract(_, _) => "SUBTRACT",
            Self::Multiply(_, _) => "MULTIPLY",
            Self::ShiftLeft { .. } => "SHIFT_LEFT",
            Self::Divide(_, _) => "DIVIDE",
            Self::Return(_) => "RETURN",
        }
    }

    pub fn antecedents(&self) -> Vec<usize> {
        match *self {
            Self::Input(_) | Self::Constant(_) => Vec::new(),
            Self::Add(left, right)
            | Self::Subtract(left, right)
            | Self::Multiply(left, right)
            | Self::Divide(left, right) => vec![left, right],
            Self::ShiftLeft { source, .. } | Self::Return(source) => vec![source],
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ValueDomain {
    Word(u8),
    Rational,
}

impl ValueDomain {
    fn encode(&self) -> u64 {
        match *self {
            Self::Word(bits) => 100 + u64::from(bits),
            Self::Rational => VALUE_RATIONAL,
        }
    }

    fn decode(value: u64) -> Result<Self, String> {
        if value >= 100 {
            Ok(Self::Word(
                u8::try_from(value - 100).map_err(|error| format!("{error:?}"))?,
            ))
        } else if value == VALUE_RATIONAL {
            Ok(Self::Rational)
        } else {
            Err(format!("unknown exact value domain {value}"))
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Program {
    pub id: u64,
    pub name: String,
    pub domain: ValueDomain,
    pub nodes: Vec<Node>,
    pub output: usize,
}

impl Program {
    pub fn validate(&self) -> Result<(), String> {
        if self.nodes.is_empty() || self.output >= self.nodes.len() {
            return Err(format!("program {} has no lawful output", self.name));
        }
        if matches!(self.domain, ValueDomain::Word(bits) if bits == 0 || bits > 63) {
            return Err(format!("program {} has an invalid word width", self.name));
        }
        for (at, node) in self.nodes.iter().enumerate() {
            for antecedent in node.antecedents() {
                if antecedent >= at {
                    return Err(format!(
                        "program {} node {at} antecedent {antecedent} is not prior",
                        self.name
                    ));
                }
            }
        }
        if !matches!(self.nodes[self.output], Node::Return(_)) {
            return Err(format!("program {} does not end through RETURN", self.name));
        }
        for node in &self.nodes {
            if let Node::Constant(quantity) = node {
                let constant_domain = match quantity.value {
                    ExactValue::Word { bits, .. } => ValueDomain::Word(bits),
                    ExactValue::Rational(_) => ValueDomain::Rational,
                };
                if constant_domain != self.domain {
                    return Err(format!(
                        "program {} constant crosses its exact value domain",
                        self.name
                    ));
                }
            }
        }
        Ok(())
    }

    pub fn shape(&self) -> Vec<StepShape> {
        self.nodes
            .iter()
            .map(|node| StepShape {
                operation: node.operation(),
                antecedents: node.antecedents(),
            })
            .collect()
    }

    /// Exact symbolic face of a one-input fixed-width word program in
    /// `(Z / 2^bits Z)[x]`. This is not a sampled fit: every node is
    /// transported through the ring operations declared by the program.
    pub fn word_polynomial(&self) -> Result<Vec<u64>, String> {
        let bits = match self.domain {
            ValueDomain::Word(bits) => bits,
            ValueDomain::Rational => {
                return Err(format!(
                    "program {} does not inhabit a fixed-width word ring",
                    self.name
                ));
            }
        };
        self.validate()?;
        let mask = word_mask(bits);
        let mut values: Vec<Vec<u64>> = Vec::with_capacity(self.nodes.len());
        for node in &self.nodes {
            let polynomial = match *node {
                Node::Input(0) => vec![0, 1],
                Node::Input(slot) => {
                    return Err(format!(
                        "program {} input slot {slot} is not the one-variable chart",
                        self.name
                    ));
                }
                Node::Constant(Quantity {
                    value:
                        ExactValue::Word {
                            bits: constant_bits,
                            value,
                        },
                    unit: Unit::DIMENSIONLESS,
                }) if constant_bits == bits => vec![value],
                Node::Constant(_) => {
                    return Err(format!(
                        "program {} has a non-word or dimensional constant",
                        self.name
                    ));
                }
                Node::Add(left, right) => {
                    polynomial_add(&values[left], &values[right], mask, false)
                }
                Node::Subtract(left, right) => {
                    polynomial_add(&values[left], &values[right], mask, true)
                }
                Node::Multiply(left, right) => {
                    polynomial_multiply(&values[left], &values[right], mask)
                }
                Node::ShiftLeft { source, places } => values[source]
                    .iter()
                    .map(|coefficient| coefficient.wrapping_shl(u32::from(places)) & mask)
                    .collect(),
                Node::Divide(_, _) => {
                    return Err(format!(
                        "program {} contains division outside the word polynomial ring",
                        self.name
                    ));
                }
                Node::Return(source) => values[source].clone(),
            };
            values.push(trim_polynomial(polynomial));
        }
        Ok(values[self.output].clone())
    }

    pub fn evaluate(&self, inputs: &[Quantity]) -> Evaluation {
        if let Err(reason) = self.validate() {
            return Evaluation::Open {
                completed: Vec::new(),
                at: 0,
                reason,
            };
        }
        let mut values = Vec::with_capacity(self.nodes.len());
        let mut path = Vec::with_capacity(self.nodes.len());
        for (at, node) in self.nodes.iter().enumerate() {
            let result = evaluate_node(node, inputs, &values);
            let output = match result {
                Ok(output) => output,
                Err(reason) => {
                    return Evaluation::Open {
                        completed: path,
                        at,
                        reason,
                    };
                }
            };
            path.push(Step {
                node: at,
                operation: node.operation(),
                antecedents: node.antecedents(),
                output,
            });
            values.push(output);
        }
        Evaluation::Closed {
            output: values[self.output],
            path,
        }
    }

    pub fn encode(&self) -> Result<Vec<AlgorithmWord>, String> {
        self.validate()?;
        let coordinate = vec![self.id];
        let mut words = vec![
            AlgorithmWord::at(PROGRAM_SCHEMA_TAG, coordinate.clone(), PROGRAM_SCHEMA),
            AlgorithmWord::at(PROGRAM_DOMAIN_TAG, coordinate.clone(), self.domain.encode()),
            AlgorithmWord::at(
                PROGRAM_NODE_COUNT_TAG,
                coordinate.clone(),
                self.nodes.len() as u64,
            ),
            AlgorithmWord::at(PROGRAM_OUTPUT_TAG, coordinate, self.output as u64),
        ];
        for (at, node) in self.nodes.iter().enumerate() {
            let route = vec![self.id, at as u64];
            words.push(AlgorithmWord::at(
                NODE_KIND_TAG,
                route.clone(),
                node_kind(node),
            ));
            match *node {
                Node::Input(slot) => {
                    words.push(AlgorithmWord::at(NODE_INPUT_TAG, route, slot as u64))
                }
                Node::Constant(quantity) => {
                    encode_constant(&mut words, route, quantity)?;
                }
                Node::Add(left, right)
                | Node::Subtract(left, right)
                | Node::Multiply(left, right)
                | Node::Divide(left, right) => {
                    words.push(AlgorithmWord::at(NODE_LEFT_TAG, route.clone(), left as u64));
                    words.push(AlgorithmWord::at(NODE_RIGHT_TAG, route, right as u64));
                }
                Node::ShiftLeft { source, places } => {
                    words.push(AlgorithmWord::at(
                        NODE_LEFT_TAG,
                        route.clone(),
                        source as u64,
                    ));
                    words.push(AlgorithmWord::at(NODE_SHIFT_TAG, route, u64::from(places)));
                }
                Node::Return(source) => {
                    words.push(AlgorithmWord::at(NODE_LEFT_TAG, route, source as u64))
                }
            }
        }
        Ok(words)
    }

    pub fn decode<F>(id: u64, name: String, mut word: F) -> Result<Self, String>
    where
        F: FnMut(u64, &[u64]) -> Result<u64, String>,
    {
        let root = [id];
        if word(PROGRAM_SCHEMA_TAG, &root)? != PROGRAM_SCHEMA {
            return Err(format!("program {id} schema changed"));
        }
        let domain_word = word(PROGRAM_DOMAIN_TAG, &root)?;
        let domain = ValueDomain::decode(domain_word)?;
        let count = usize::try_from(word(PROGRAM_NODE_COUNT_TAG, &root)?)
            .map_err(|error| format!("{error:?}"))?;
        let output = usize::try_from(word(PROGRAM_OUTPUT_TAG, &root)?)
            .map_err(|error| format!("{error:?}"))?;
        let mut nodes = Vec::with_capacity(count);
        for at in 0..count {
            let route = [id, at as u64];
            let node = match word(NODE_KIND_TAG, &route)? {
                1 => Node::Input(
                    usize::try_from(word(NODE_INPUT_TAG, &route)?)
                        .map_err(|error| format!("{error:?}"))?,
                ),
                2 => Node::Constant(decode_constant(domain_word, &route, &mut word)?),
                3 => Node::Add(
                    read_index(&mut word, NODE_LEFT_TAG, &route)?,
                    read_index(&mut word, NODE_RIGHT_TAG, &route)?,
                ),
                4 => Node::Subtract(
                    read_index(&mut word, NODE_LEFT_TAG, &route)?,
                    read_index(&mut word, NODE_RIGHT_TAG, &route)?,
                ),
                5 => Node::Multiply(
                    read_index(&mut word, NODE_LEFT_TAG, &route)?,
                    read_index(&mut word, NODE_RIGHT_TAG, &route)?,
                ),
                6 => Node::ShiftLeft {
                    source: read_index(&mut word, NODE_LEFT_TAG, &route)?,
                    places: u8::try_from(word(NODE_SHIFT_TAG, &route)?)
                        .map_err(|error| format!("{error:?}"))?,
                },
                7 => Node::Divide(
                    read_index(&mut word, NODE_LEFT_TAG, &route)?,
                    read_index(&mut word, NODE_RIGHT_TAG, &route)?,
                ),
                8 => Node::Return(read_index(&mut word, NODE_LEFT_TAG, &route)?),
                kind => return Err(format!("program {id} node {at} has unknown kind {kind}")),
            };
            nodes.push(node);
        }
        let program = Self {
            id,
            name,
            domain,
            nodes,
            output,
        };
        program.validate()?;
        Ok(program)
    }
}

fn polynomial_add(left: &[u64], right: &[u64], mask: u64, subtract: bool) -> Vec<u64> {
    let extent = left.len().max(right.len());
    (0..extent)
        .map(|at| {
            let left = left.get(at).copied().unwrap_or(0);
            let right = right.get(at).copied().unwrap_or(0);
            if subtract {
                left.wrapping_sub(right) & mask
            } else {
                left.wrapping_add(right) & mask
            }
        })
        .collect()
}

fn polynomial_multiply(left: &[u64], right: &[u64], mask: u64) -> Vec<u64> {
    let mut product = vec![0u64; left.len() + right.len() - 1];
    for (left_at, left) in left.iter().copied().enumerate() {
        for (right_at, right) in right.iter().copied().enumerate() {
            let at = left_at + right_at;
            product[at] = product[at].wrapping_add(left.wrapping_mul(right)) & mask;
        }
    }
    trim_polynomial(product)
}

fn trim_polynomial(mut polynomial: Vec<u64>) -> Vec<u64> {
    while polynomial.len() > 1 && polynomial.last() == Some(&0) {
        polynomial.pop();
    }
    polynomial
}

fn read_index<F>(word: &mut F, tag: u64, route: &[u64]) -> Result<usize, String>
where
    F: FnMut(u64, &[u64]) -> Result<u64, String>,
{
    usize::try_from(word(tag, route)?).map_err(|error| format!("{error:?}"))
}

fn node_kind(node: &Node) -> u64 {
    match node {
        Node::Input(_) => 1,
        Node::Constant(_) => 2,
        Node::Add(_, _) => 3,
        Node::Subtract(_, _) => 4,
        Node::Multiply(_, _) => 5,
        Node::ShiftLeft { .. } => 6,
        Node::Divide(_, _) => 7,
        Node::Return(_) => 8,
    }
}

fn encode_constant(
    words: &mut Vec<AlgorithmWord>,
    route: Vec<u64>,
    quantity: Quantity,
) -> Result<(), String> {
    match quantity.value {
        ExactValue::Word { bits, value } => {
            words.push(AlgorithmWord::at(
                NODE_CONST_KIND_TAG,
                route.clone(),
                100 + u64::from(bits),
            ));
            words.push(AlgorithmWord::at(
                NODE_CONST_MAGNITUDE_TAG,
                route.clone(),
                value,
            ));
            words.push(AlgorithmWord::at(
                NODE_CONST_DENOMINATOR_TAG,
                route.clone(),
                1,
            ));
            words.push(AlgorithmWord::at(NODE_CONST_SIGN_TAG, route.clone(), 1));
        }
        ExactValue::Rational(value) => {
            let (sign, magnitude) = encode_i128(value.numerator)?;
            words.push(AlgorithmWord::at(
                NODE_CONST_KIND_TAG,
                route.clone(),
                VALUE_RATIONAL,
            ));
            words.push(AlgorithmWord::at(NODE_CONST_SIGN_TAG, route.clone(), sign));
            words.push(AlgorithmWord::at(
                NODE_CONST_MAGNITUDE_TAG,
                route.clone(),
                magnitude,
            ));
            words.push(AlgorithmWord::at(
                NODE_CONST_DENOMINATOR_TAG,
                route.clone(),
                u64::try_from(value.denominator).map_err(|error| format!("{error:?}"))?,
            ));
        }
    }
    for (axis, exponent) in quantity.unit.exponents.iter().copied().enumerate() {
        words.push(AlgorithmWord::at(
            NODE_CONST_UNIT_TAG,
            vec![route[0], route[1], axis as u64],
            encode_i8(exponent),
        ));
    }
    Ok(())
}

fn decode_constant<F>(domain: u64, route: &[u64], word: &mut F) -> Result<Quantity, String>
where
    F: FnMut(u64, &[u64]) -> Result<u64, String>,
{
    let kind = word(NODE_CONST_KIND_TAG, route)?;
    if kind != domain {
        return Err("constant and program exact domains disagree".to_owned());
    }
    let sign = word(NODE_CONST_SIGN_TAG, route)?;
    let magnitude = word(NODE_CONST_MAGNITUDE_TAG, route)?;
    let denominator = word(NODE_CONST_DENOMINATOR_TAG, route)?;
    let value = if kind >= 100 {
        ExactValue::word(
            u8::try_from(kind - 100).map_err(|error| format!("{error:?}"))?,
            magnitude,
        )?
    } else if kind == VALUE_RATIONAL {
        ExactValue::rational(decode_i128(sign, magnitude)?, i128::from(denominator))?
    } else {
        return Err(format!("unknown exact constant kind {kind}"));
    };
    let mut exponents = [0i8; 4];
    for (axis, exponent) in exponents.iter_mut().enumerate() {
        let unit_route = [route[0], route[1], axis as u64];
        *exponent = decode_i8(word(NODE_CONST_UNIT_TAG, &unit_route)?)?;
    }
    Ok(Quantity {
        value,
        unit: Unit { exponents },
    })
}

fn encode_i128(value: i128) -> Result<(u64, u64), String> {
    let sign = if value < 0 {
        2
    } else if value == 0 {
        0
    } else {
        1
    };
    let magnitude = u64::try_from(
        value
            .checked_abs()
            .ok_or_else(|| "signed exact magnitude overflowed".to_owned())?,
    )
    .map_err(|error| format!("{error:?}"))?;
    Ok((sign, magnitude))
}

fn decode_i128(sign: u64, magnitude: u64) -> Result<i128, String> {
    let magnitude = i128::from(magnitude);
    match sign {
        0 if magnitude == 0 => Ok(0),
        1 => Ok(magnitude),
        2 => Ok(-magnitude),
        _ => Err("signed exact representation is inconsistent".to_owned()),
    }
}

fn encode_i8(value: i8) -> u64 {
    u64::from((i16::from(value) + 128) as u8)
}

fn decode_i8(value: u64) -> Result<i8, String> {
    let value = u8::try_from(value).map_err(|error| format!("{error:?}"))?;
    i8::try_from(i16::from(value) - 128).map_err(|error| format!("{error:?}"))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StepShape {
    pub operation: &'static str,
    pub antecedents: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Step {
    pub node: usize,
    pub operation: &'static str,
    pub antecedents: Vec<usize>,
    pub output: Quantity,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Evaluation {
    Closed {
        path: Vec<Step>,
        output: Quantity,
    },
    Open {
        completed: Vec<Step>,
        at: usize,
        reason: String,
    },
}

impl Evaluation {
    pub fn output(&self) -> Option<Quantity> {
        match self {
            Self::Closed { output, .. } => Some(*output),
            Self::Open { .. } => None,
        }
    }

    pub fn path(&self) -> &[Step] {
        match self {
            Self::Closed { path, .. } => path,
            Self::Open { completed, .. } => completed,
        }
    }
}

fn evaluate_node(
    node: &Node,
    inputs: &[Quantity],
    values: &[Quantity],
) -> Result<Quantity, String> {
    match *node {
        Node::Input(slot) => inputs
            .get(slot)
            .copied()
            .ok_or_else(|| format!("input slot {slot} is absent")),
        Node::Constant(quantity) => Ok(quantity),
        Node::Add(left, right) => checked_add(values[left], values[right]),
        Node::Subtract(left, right) => checked_sub(values[left], values[right]),
        Node::Multiply(left, right) => checked_mul(values[left], values[right]),
        Node::ShiftLeft { source, places } => checked_shift(values[source], places),
        Node::Divide(left, right) => checked_div(values[left], values[right]),
        Node::Return(source) => Ok(values[source]),
    }
}

fn checked_add(left: Quantity, right: Quantity) -> Result<Quantity, String> {
    require_same_unit(left, right, "addition")?;
    let value = match (left.value, right.value) {
        (
            ExactValue::Word {
                bits: left_bits,
                value: left,
            },
            ExactValue::Word {
                bits: right_bits,
                value: right,
            },
        ) if left_bits == right_bits => ExactValue::Word {
            bits: left_bits,
            value: left.wrapping_add(right) & word_mask(left_bits),
        },
        (ExactValue::Rational(left), ExactValue::Rational(right)) => {
            ExactValue::Rational(left.checked_add(right)?)
        }
        _ => return Err("addition crossed exact value domains".to_owned()),
    };
    Ok(Quantity {
        value,
        unit: left.unit,
    })
}

fn checked_sub(left: Quantity, right: Quantity) -> Result<Quantity, String> {
    require_same_unit(left, right, "subtraction")?;
    let value = match (left.value, right.value) {
        (
            ExactValue::Word {
                bits: left_bits,
                value: left,
            },
            ExactValue::Word {
                bits: right_bits,
                value: right,
            },
        ) if left_bits == right_bits => ExactValue::Word {
            bits: left_bits,
            value: left.wrapping_sub(right) & word_mask(left_bits),
        },
        (ExactValue::Rational(left), ExactValue::Rational(right)) => {
            ExactValue::Rational(left.checked_sub(right)?)
        }
        _ => return Err("subtraction crossed exact value domains".to_owned()),
    };
    Ok(Quantity {
        value,
        unit: left.unit,
    })
}

fn checked_mul(left: Quantity, right: Quantity) -> Result<Quantity, String> {
    let value = match (left.value, right.value) {
        (
            ExactValue::Word {
                bits: left_bits,
                value: left,
            },
            ExactValue::Word {
                bits: right_bits,
                value: right,
            },
        ) if left_bits == right_bits => ExactValue::Word {
            bits: left_bits,
            value: left.wrapping_mul(right) & word_mask(left_bits),
        },
        (ExactValue::Rational(left), ExactValue::Rational(right)) => {
            ExactValue::Rational(left.checked_mul(right)?)
        }
        _ => return Err("multiplication crossed exact value domains".to_owned()),
    };
    Ok(Quantity {
        value,
        unit: left.unit.checked_mul(right.unit)?,
    })
}

fn checked_shift(source: Quantity, places: u8) -> Result<Quantity, String> {
    if source.unit != Unit::DIMENSIONLESS {
        return Err("bit shift received a dimensional quantity".to_owned());
    }
    let value = match source.value {
        ExactValue::Word { bits, value } => ExactValue::Word {
            bits,
            value: value.wrapping_shl(u32::from(places)) & word_mask(bits),
        },
        ExactValue::Rational(_) => return Err("bit shift received a rational value".to_owned()),
    };
    Ok(Quantity {
        value,
        unit: source.unit,
    })
}

fn checked_div(left: Quantity, right: Quantity) -> Result<Quantity, String> {
    let value = match (left.value, right.value) {
        (ExactValue::Rational(left), ExactValue::Rational(right)) => {
            ExactValue::Rational(left.checked_div(right)?)
        }
        _ => return Err("division requires the exact rational chart".to_owned()),
    };
    Ok(Quantity {
        value,
        unit: left.unit.checked_div(right.unit)?,
    })
}

fn require_same_unit(left: Quantity, right: Quantity, operation: &str) -> Result<(), String> {
    if left.unit == right.unit {
        Ok(())
    } else {
        Err(format!("{operation} crossed nonidentical unit axes"))
    }
}
