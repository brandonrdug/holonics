(function (root, factory) {
  const api = factory();
  if (typeof module === "object" && module.exports) module.exports = api;
  root.SomaExactSeries = api;
})(typeof globalThis !== "undefined" ? globalThis : this, function () {
  "use strict";

  function invariant(condition, message) {
    if (!condition) throw new Error(message);
  }

  function integer(value) {
    if (typeof value === "bigint") return value;
    if (typeof value === "string" && /^[-+]?\d+$/.test(value)) return BigInt(value);
    if (typeof value === "number" && Number.isSafeInteger(value)) return BigInt(value);
    throw new Error(`${String(value)} is not one exact integer`);
  }

  function gcd(left, right) {
    let a = left < 0n ? -left : left;
    let b = right < 0n ? -right : right;
    while (b !== 0n) [a, b] = [b, a % b];
    return a;
  }

  function ratio(numerator, denominator) {
    let n = integer(numerator);
    let d = integer(denominator === undefined ? 1 : denominator);
    invariant(d !== 0n, "an exact ratio has a nonzero denominator");
    if (d < 0n) {
      n = -n;
      d = -d;
    }
    const divisor = gcd(n, d) || 1n;
    return Object.freeze({ n: n / divisor, d: d / divisor });
  }

  const ZERO = ratio(0n, 1n);
  const ONE = ratio(1n, 1n);

  function fromDecimal(value) {
    const text = String(value).trim();
    const match = /^([+-]?)(\d+)(?:\.(\d*))?(?:[eE]([+-]?\d+))?$/.exec(text);
    invariant(match, `${text} is not one exact decimal inscription`);
    const sign = match[1] === "-" ? -1n : 1n;
    const whole = match[2];
    const fraction = match[3] || "";
    const exponent = match[4] ? BigInt(match[4]) : 0n;
    let numerator = sign * BigInt(`${whole}${fraction}`);
    let denominator = 10n ** BigInt(fraction.length);
    if (exponent > 0n) numerator *= 10n ** exponent;
    if (exponent < 0n) denominator *= 10n ** (-exponent);
    return ratio(numerator, denominator);
  }

  function add(left, right) {
    return ratio(left.n * right.d + right.n * left.d, left.d * right.d);
  }

  function sub(left, right) {
    return ratio(left.n * right.d - right.n * left.d, left.d * right.d);
  }

  function mul(left, right) {
    return ratio(left.n * right.n, left.d * right.d);
  }

  function div(left, right) {
    invariant(right.n !== 0n, "exact ratio division refuses zero");
    return ratio(left.n * right.d, left.d * right.n);
  }

  function neg(value) {
    return ratio(-value.n, value.d);
  }

  function abs(value) {
    return value.n < 0n ? neg(value) : value;
  }

  function compare(left, right) {
    const delta = left.n * right.d - right.n * left.d;
    return delta < 0n ? -1 : delta > 0n ? 1 : 0;
  }

  function minimum(left, right) {
    return compare(left, right) <= 0 ? left : right;
  }

  function maximum(left, right) {
    return compare(left, right) >= 0 ? left : right;
  }

  function power(value, exponent) {
    const degree = integer(exponent);
    invariant(degree >= 0n, "exact ratio power receives a nonnegative exponent");
    return ratio(value.n ** degree, value.d ** degree);
  }

  function factorial(value) {
    const extent = integer(value);
    invariant(extent >= 0n, "factorial receives a nonnegative integer");
    let product = 1n;
    for (let at = 2n; at <= extent; at += 1n) product *= at;
    return product;
  }

  function floor(value) {
    let quotient = value.n / value.d;
    if (value.n < 0n && value.n % value.d !== 0n) quotient -= 1n;
    return quotient;
  }

  function ceil(value) {
    let quotient = value.n / value.d;
    if (value.n > 0n && value.n % value.d !== 0n) quotient += 1n;
    return quotient;
  }

  function text(value) {
    return value.d === 1n ? value.n.toString() : `${value.n}/${value.d}`;
  }

  function read(value) {
    return Object.freeze({ numerator: value.n.toString(), denominator: value.d.toString(), ratio: text(value) });
  }

  function interval(lower, upper) {
    invariant(compare(lower, upper) <= 0, "an exact interval has ordered endpoints");
    return Object.freeze({ lo: lower, hi: upper });
  }

  function point(value) {
    return interval(value, value);
  }

  function intervalRead(value) {
    return Object.freeze({ lower: read(value.lo), upper: read(value.hi) });
  }

  function intervalAdd(left, right) {
    return interval(add(left.lo, right.lo), add(left.hi, right.hi));
  }

  function intervalSub(left, right) {
    return interval(sub(left.lo, right.hi), sub(left.hi, right.lo));
  }

  function intervalMul(left, right) {
    const products = [
      mul(left.lo, right.lo),
      mul(left.lo, right.hi),
      mul(left.hi, right.lo),
      mul(left.hi, right.hi),
    ];
    return interval(
      products.reduce((held, value) => minimum(held, value)),
      products.reduce((held, value) => maximum(held, value))
    );
  }

  function intervalScale(value, scalar) {
    return compare(scalar, ZERO) < 0
      ? interval(mul(value.hi, scalar), mul(value.lo, scalar))
      : interval(mul(value.lo, scalar), mul(value.hi, scalar));
  }

  function enclosure(partial, error) {
    const magnitude = abs(error);
    return interval(sub(partial, magnitude), add(partial, magnitude));
  }

  function seriesRead(kind, input, terms, partial, remainder, bounds, extras) {
    return Object.freeze(Object.assign({
      kind,
      input,
      terms: terms.map((term) => Object.freeze({ ordinal: term.ordinal, value: read(term.value) })),
      partial_sum: read(partial),
      remainder_bound: read(remainder),
      enclosure: intervalRead(bounds),
    }, extras || {}));
  }

  function atanSeries(input, termCount) {
    const x = input;
    const count = integer(termCount);
    invariant(compare(abs(x), ONE) <= 0, "the retained arctangent series receives |x|<=1");
    invariant(count > 0n, "the retained arctangent series has at least one term");
    const terms = [];
    let partial = ZERO;
    for (let ordinal = 0n; ordinal < count; ordinal += 1n) {
      const sign = ordinal % 2n === 0n ? 1n : -1n;
      const value = ratio(sign * (x.n ** (2n * ordinal + 1n)), (x.d ** (2n * ordinal + 1n)) * (2n * ordinal + 1n));
      terms.push({ ordinal: ordinal.toString(), value });
      partial = add(partial, value);
    }
    const omitted = count;
    const remainder = ratio(
      abs(x.n) ** (2n * omitted + 1n),
      x.d ** (2n * omitted + 1n) * (2n * omitted + 1n)
    );
    return seriesRead("atan-rational-alternating", read(x), terms, partial, remainder, enclosure(partial, remainder), {
      tail_law: "the first omitted alternating term encloses the remainder",
    });
  }

  function internalInterval(value) {
    return interval(
      ratio(value.enclosure.lower.numerator, value.enclosure.lower.denominator),
      ratio(value.enclosure.upper.numerator, value.enclosure.upper.denominator)
    );
  }

  function machinPi(termCount) {
    const count = integer(termCount);
    const fifth = atanSeries(ratio(1n, 5n), count);
    const twoThirtyNinth = atanSeries(ratio(1n, 239n), count);
    const combined = intervalSub(
      intervalScale(internalInterval(fifth), ratio(16n, 1n)),
      intervalScale(internalInterval(twoThirtyNinth), ratio(4n, 1n))
    );
    return Object.freeze({
      kind: "machin-pi-rational-series",
      identity: "pi=16*atan(1/5)-4*atan(1/239)",
      term_count_per_arm: count.toString(),
      arms: Object.freeze({ one_fifth: fifth, one_two_hundred_thirty_ninth: twoThirtyNinth }),
      enclosure: intervalRead(combined),
    });
  }

  function atanhLogUnit(input, termCount) {
    const z = input;
    const count = integer(termCount);
    invariant(compare(z, ZERO) >= 0 && compare(z, ONE) < 0, "the retained logarithm series receives 0<=z<1");
    invariant(count > 0n, "the retained logarithm series has at least one term");
    const terms = [];
    let partial = ZERO;
    for (let ordinal = 0n; ordinal < count; ordinal += 1n) {
      const degree = 2n * ordinal + 1n;
      const value = mul(ratio(2n, degree), power(z, degree));
      terms.push({ ordinal: ordinal.toString(), value });
      partial = add(partial, value);
    }
    const firstOmittedDegree = 2n * count + 1n;
    const denominator = mul(ratio(firstOmittedDegree, 1n), sub(ONE, mul(z, z)));
    const remainder = div(mul(ratio(2n, 1n), power(z, firstOmittedDegree)), denominator);
    return seriesRead("log-rational-atanh", read(z), terms, partial, remainder, interval(partial, add(partial, remainder)), {
      identity: "log((1+z)/(1-z))=2*sum(z^(2j+1)/(2j+1))",
      tail_law: "positive tail bounded by its first power over (2N+1)(1-z^2)",
    });
  }

  function logIntegerSeries(value, termCount) {
    const source = integer(value);
    const count = integer(termCount);
    invariant(source > 0n, "integer logarithm receives a positive source");
    let binaryExponent = 0n;
    let powerOfTwo = 1n;
    while (powerOfTwo * 2n <= source) {
      powerOfTwo *= 2n;
      binaryExponent += 1n;
    }
    const mantissa = ratio(source, powerOfTwo);
    const mantissaZ = div(sub(mantissa, ONE), add(mantissa, ONE));
    const logTwo = atanhLogUnit(ratio(1n, 3n), count);
    const logMantissa = atanhLogUnit(mantissaZ, count);
    const combined = intervalAdd(
      intervalScale(internalInterval(logTwo), ratio(binaryExponent, 1n)),
      internalInterval(logMantissa)
    );
    return Object.freeze({
      kind: "integer-log-rational-series",
      source: source.toString(),
      exact_factorization: `${source}=${powerOfTwo}*${text(mantissa)}`,
      binary_exponent: binaryExponent.toString(),
      mantissa: read(mantissa),
      mantissa_transform: read(mantissaZ),
      components: Object.freeze({ log_two: logTwo, log_mantissa: logMantissa }),
      enclosure: intervalRead(combined),
    });
  }

  function logRationalSeries(value, termCount) {
    invariant(value.n > 0n, "rational logarithm receives a positive source");
    const numerator = logIntegerSeries(value.n, termCount);
    const denominator = logIntegerSeries(value.d, termCount);
    const bounds = intervalSub(internalInterval(numerator), internalInterval(denominator));
    return Object.freeze({
      kind: "rational-log-series-difference",
      source: read(value),
      identity: `log(${text(value)})=log(${value.n})-log(${value.d})`,
      components: Object.freeze({ numerator, denominator }),
      enclosure: intervalRead(bounds),
    });
  }

  function complex(real, imaginary) {
    return Object.freeze({ re: real, im: imaginary });
  }

  function complexAdd(left, right) {
    return complex(add(left.re, right.re), add(left.im, right.im));
  }

  function complexMul(left, right) {
    return complex(
      sub(mul(left.re, right.re), mul(left.im, right.im)),
      add(mul(left.re, right.im), mul(left.im, right.re))
    );
  }

  function complexScale(value, scalar) {
    return complex(mul(value.re, scalar), mul(value.im, scalar));
  }

  function complexPower(value, exponent) {
    const degree = integer(exponent);
    invariant(degree >= 0n, "complex ratio power receives a nonnegative exponent");
    let held = complex(ONE, ZERO);
    let base = value;
    let remaining = degree;
    while (remaining > 0n) {
      if (remaining % 2n === 1n) held = complexMul(held, base);
      remaining /= 2n;
      if (remaining > 0n) base = complexMul(base, base);
    }
    return held;
  }

  function complexRead(value) {
    return Object.freeze({ real: read(value.re), imaginary: read(value.im) });
  }

  function expSeries(input, termCount) {
    const x = input;
    const count = integer(termCount);
    invariant(count > 0n, "the retained exponential series has at least one term");
    const terms = [];
    let partial = ZERO;
    let term = ONE;
    for (let ordinal = 0n; ordinal < count; ordinal += 1n) {
      if (ordinal > 0n) term = div(mul(term, x), ratio(ordinal, 1n));
      terms.push({ ordinal: ordinal.toString(), value: term });
      partial = add(partial, term);
    }
    const firstOmitted = div(mul(term, x), ratio(count, 1n));
    const tailRatio = div(abs(x), ratio(count + 1n, 1n));
    invariant(compare(tailRatio, ONE) < 0, "exponential tail needs N+1>|x|");
    const remainder = div(abs(firstOmitted), sub(ONE, tailRatio));
    return seriesRead("exp-rational", read(x), terms, partial, remainder, enclosure(partial, remainder), {
      identity: "exp(x)=sum(x^j/j!)",
      tail_law: "the omitted absolute terms are bounded by a geometric tail with ratio |x|/(N+1)",
    });
  }

  function sineSeries(input, termCount) {
    const x = input;
    const count = integer(termCount);
    invariant(count > 0n, "the retained sine series has at least one term");
    const terms = [];
    let partial = ZERO;
    for (let ordinal = 0n; ordinal < count; ordinal += 1n) {
      const degree = 2n * ordinal + 1n;
      const sign = ordinal % 2n === 0n ? 1n : -1n;
      const value = ratio(sign * (x.n ** degree), (x.d ** degree) * factorial(degree));
      terms.push({ ordinal: ordinal.toString(), value });
      partial = add(partial, value);
    }
    const remainderDegree = 2n * count;
    const remainder = ratio(abs(x.n) ** remainderDegree, x.d ** remainderDegree * factorial(remainderDegree));
    return seriesRead("sin-rational-taylor", read(x), terms, partial, remainder, enclosure(partial, remainder), {
      tail_law: "Lagrange enclosure with every derivative bounded by one",
    });
  }

  function cosineSeries(input, termCount) {
    const x = input;
    const count = integer(termCount);
    invariant(count > 0n, "the retained cosine series has at least one term");
    const terms = [];
    let partial = ZERO;
    for (let ordinal = 0n; ordinal < count; ordinal += 1n) {
      const degree = 2n * ordinal;
      const sign = ordinal % 2n === 0n ? 1n : -1n;
      const value = ratio(sign * (x.n ** degree), (x.d ** degree) * factorial(degree));
      terms.push({ ordinal: ordinal.toString(), value });
      partial = add(partial, value);
    }
    const remainderDegree = 2n * count - 1n;
    const remainder = ratio(abs(x.n) ** remainderDegree, x.d ** remainderDegree * factorial(remainderDegree));
    return seriesRead("cos-rational-taylor", read(x), terms, partial, remainder, enclosure(partial, remainder), {
      tail_law: "Lagrange enclosure with every derivative bounded by one",
    });
  }

  function applySign(value, sign) {
    return sign < 0n ? interval(neg(value.hi), neg(value.lo)) : value;
  }

  function cyclotomicPhase(axisValue, residueValue, termCount, piRecord) {
    const axis = integer(axisValue);
    const residue = ((integer(residueValue) % axis) + axis) % axis;
    invariant(axis > 1n, "a cyclotomic phase has axis greater than one");
    const fourResidue = 4n * residue;
    const quadrant = fourResidue / axis;
    const localNumerator = fourResidue - quadrant * axis;
    const localPiFactor = ratio(localNumerator, 2n * axis);
    const pi = piRecord || machinPi(termCount);
    const piBounds = interval(
      ratio(pi.enclosure.lower.numerator, pi.enclosure.lower.denominator),
      ratio(pi.enclosure.upper.numerator, pi.enclosure.upper.denominator)
    );
    const localAngle = intervalScale(piBounds, localPiFactor);
    const sinLower = internalInterval(sineSeries(localAngle.lo, termCount));
    const sinUpper = internalInterval(sineSeries(localAngle.hi, termCount));
    const cosLower = internalInterval(cosineSeries(localAngle.lo, termCount));
    const cosUpper = internalInterval(cosineSeries(localAngle.hi, termCount));
    const sine = interval(sinLower.lo, sinUpper.hi);
    const cosine = interval(cosUpper.lo, cosLower.hi);
    let real;
    let imaginary;
    if (quadrant === 0n) {
      real = cosine;
      imaginary = sine;
    } else if (quadrant === 1n) {
      real = applySign(sine, -1n);
      imaginary = cosine;
    } else if (quadrant === 2n) {
      real = applySign(cosine, -1n);
      imaginary = applySign(sine, -1n);
    } else {
      real = sine;
      imaginary = applySign(cosine, -1n);
    }
    return Object.freeze({
      kind: "cyclotomic-phase",
      element: `zeta_${axis}^${residue}`,
      axis: axis.toString(),
      residue: residue.toString(),
      turn: read(ratio(residue, axis)),
      quadrant: quadrant.toString(),
      local_turn_numerator: localNumerator.toString(),
      local_pi_factor: read(localPiFactor),
      real: intervalRead(real),
      imaginary: intervalRead(imaginary),
      embedding_series: Object.freeze({ pi: pi.kind, sine: "sin-rational-taylor", cosine: "cos-rational-taylor", terms: integer(termCount).toString() }),
    });
  }

  function integerPixel(value, scale) {
    const scaled = mul(value, ratio(integer(scale), 1n));
    const lower = floor(scaled);
    const upper = ceil(scaled);
    return Object.freeze({ lower: lower.toString(), upper: upper.toString() });
  }

  function intervalPixel(value, scale) {
    return Object.freeze({
      lower: floor(mul(value.lo, ratio(integer(scale), 1n))).toString(),
      upper: ceil(mul(value.hi, ratio(integer(scale), 1n))).toString(),
    });
  }

  return Object.freeze({
    ratio,
    fromDecimal,
    add,
    sub,
    mul,
    div,
    neg,
    abs,
    compare,
    power,
    floor,
    ceil,
    text,
    read,
    interval,
    point,
    intervalRead,
    intervalAdd,
    intervalSub,
    intervalMul,
    intervalScale,
    atanSeries,
    machinPi,
    logIntegerSeries,
    logRationalSeries,
    expSeries,
    sineSeries,
    cosineSeries,
    cyclotomicPhase,
    complex,
    complexAdd,
    complexMul,
    complexScale,
    complexPower,
    complexRead,
    integerPixel,
    intervalPixel,
  });
});
