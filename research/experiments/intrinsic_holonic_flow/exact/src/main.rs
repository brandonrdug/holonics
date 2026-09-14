//! Actual rational-enclosure execution of the declared phase map.
//! Existing series/interval owners are composed; no float enters an operation or comparison.
use holonic_engine::{CertifiedSeries, ExactInterval as Iv};
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use serde_json::{Value, json};
use std::{error::Error, fs, time::Instant};
const N: usize = 6;
const GRAIN: u32 = 96;
const TERMS: usize = 40;
fn r(n: i64, d: i64) -> Rat {
    Rat::new(n.into(), d.into())
}
fn pt(n: i64, d: i64) -> Iv {
    Iv::point(r(n, d))
}
fn held(a: Iv) -> Iv {
    a.round_out(GRAIN).unwrap()
}
fn add(a: &Iv, b: &Iv) -> Iv {
    held(Iv::new(&a.lower + &b.lower, &a.upper + &b.upper).unwrap())
}
fn neg(a: &Iv) -> Iv {
    Iv::new(-&a.upper, -&a.lower).unwrap()
}
fn sub(a: &Iv, b: &Iv) -> Iv {
    add(a, &neg(b))
}
fn mul(a: &Iv, b: &Iv) -> Iv {
    held(a.times(b).unwrap())
}
fn scale(a: &Iv, b: &Rat) -> Iv {
    mul(a, &Iv::point(b.clone()))
}
fn div(a: &Iv, b: &Iv) -> Iv {
    mul(a, &b.reciprocal().unwrap())
}
fn floor(a: &Rat) -> BigInt {
    let n = a.to_integer();
    if a.is_negative() && Rat::from_integer(n.clone()) != *a {
        n - BigInt::one()
    } else {
        n
    }
}
fn clip_unit(a: Iv) -> Iv {
    Iv::new(a.lower.max(r(-1, 1)), a.upper.min(r(1, 1))).unwrap()
}
fn circle_point(a: &Rat) -> (Iv, Iv) {
    let mut small = a.clone();
    let mut doubles = 0;
    while small.abs() > Rat::one() {
        small /= r(2, 1);
        doubles += 1;
    }
    let (c, s) = CertifiedSeries::circular_series(&small, 24).unwrap();
    let (mut c, mut s) = (held(c.enclosure()), held(s.enclosure()));
    for _ in 0..doubles {
        let nextc = sub(&mul(&c, &c), &mul(&s, &s));
        let nexts = scale(&mul(&c, &s), &r(2, 1));
        c = clip_unit(nextc);
        s = clip_unit(nexts);
    }
    (c, s)
}
fn phase_circle(phase: &Iv, pi: &Iv) -> (Iv, Iv) {
    // Integer rebase retains the real lift; this is not a midpoint branch verdict.
    let k = floor(&((&phase.lower + &phase.upper) / r(2, 1) + r(1, 2)));
    let reduced = phase.translated(&(-Rat::from_integer(k)));
    let angle = scale(&mul(pi, &reduced), &r(2, 1));
    let middle = (&angle.lower + &angle.upper) / r(2, 1);
    let radius = (&angle.upper - &angle.lower) / r(2, 1);
    if radius >= r(2, 1) {
        return (
            Iv::new(r(-1, 1), r(1, 1)).unwrap(),
            Iv::new(r(-1, 1), r(1, 1)).unwrap(),
        );
    }
    let (c, s) = circle_point(&middle);
    // Global |sin'|,|cos'|<=1 keeps the complete interval argument.
    (
        clip_unit(held(Iv::new(c.lower - &radius, c.upper + &radius).unwrap())),
        clip_unit(held(Iv::new(s.lower - &radius, s.upper + radius).unwrap())),
    )
}
fn exponential(a: &Iv) -> Iv {
    // The exact absolute-geometric certificate is valid when |x|/(terms+1)<1.
    let lo = CertifiedSeries::exponential_series(&a.lower, TERMS)
        .unwrap()
        .enclosure();
    let hi = CertifiedSeries::exponential_series(&a.upper, TERMS)
        .unwrap()
        .enclosure();
    held(Iv::new(lo.lower, hi.upper).unwrap())
}
fn pi_mode() -> Iv {
    let a = holonic_engine::reopening::arctan_unit_fraction(5, 48)
        .unwrap()
        .enclosure();
    let b = holonic_engine::reopening::arctan_unit_fraction(239, 48)
        .unwrap()
        .enclosure();
    sub(&scale(&a, &r(16, 1)), &scale(&b, &r(4, 1)))
}
fn wire(a: &Iv) -> Value {
    json!({"lower":a.lower.to_string(),"upper":a.upper.to_string()})
}
fn pieces(a: &Iv) -> Vec<Iv> {
    if &a.upper - &a.lower >= Rat::one() {
        return vec![Iv::new(r(0, 1), r(1, 1)).unwrap()];
    }
    let k = floor(&a.lower);
    let l = floor(&a.upper);
    let first = a.translated(&(-Rat::from_integer(k.clone())));
    if k == l {
        vec![first]
    } else {
        vec![
            Iv::new(first.lower, r(1, 1)).unwrap(),
            Iv::new(r(0, 1), &a.upper - Rat::from_integer(l)).unwrap(),
        ]
    }
}
fn coordinate_status(a: &Iv, lo: Rat, hi: Rat) -> i8 {
    let p = pieces(a);
    if p.iter().all(|x| x.lower >= lo && x.upper < hi) {
        1
    } else if p.iter().all(|x| x.upper < lo || x.lower >= hi) {
        -1
    } else {
        0
    }
}
fn detector(q: &Iv, p: &Iv) -> i8 {
    let a = coordinate_status(q, r(1, 5), r(17, 50));
    let b = coordinate_status(p, r(2, 25), r(1, 5));
    if a == -1 || b == -1 {
        -1
    } else if a == 1 && b == 1 {
        1
    } else {
        0
    }
}
fn force(q: &[Iv], pi: &Iv, mask: &[[bool; N]; N]) -> Vec<Iv> {
    let mut f = Vec::new();
    for i in 0..N {
        let (c, s) = phase_circle(&q[i], pi);
        f.push(div(&s, &add(&pt(1, 1), &exponential(&c))));
    }
    let mut cosine = vec![vec![pt(1, 1); N]; N];
    let mut sine = vec![vec![pt(0, 1); N]; N];
    for i in 0..N {
        for j in i + 1..N {
            if mask[i][j] {
                let (c, s) = phase_circle(&sub(&sub(&q[i], &q[j]), &pt(1, 8)), pi);
                cosine[i][j] = c.clone();
                cosine[j][i] = c;
                sine[i][j] = s.clone();
                sine[j][i] = neg(&s);
            }
        }
    }
    for beta in [1, 4] {
        let mut a = vec![vec![pt(0, 1); N]; N];
        for i in 0..N {
            let mut sum = pt(0, 1);
            for j in 0..N {
                if mask[i][j] {
                    a[i][j] = exponential(&scale(&cosine[i][j], &r(beta, 1)));
                    sum = add(&sum, &a[i][j]);
                }
            }
            for j in 0..N {
                if mask[i][j] {
                    a[i][j] = div(&a[i][j], &sum);
                }
            }
        }
        for i in 0..N {
            for j in 0..N {
                if mask[i][j] && i != j {
                    f[i] = add(
                        &f[i],
                        &scale(&mul(&add(&a[i][j], &a[j][i]), &sine[i][j]), &r(7, 40)),
                    );
                }
            }
        }
    }
    f.iter().map(|x| scale(x, &r(27, 100))).collect()
}
fn main() -> Result<(), Box<dyn Error>> {
    let start = Instant::now();
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let data: Value = serde_json::from_str(&fs::read_to_string(root.join("../receipt.json"))?)?;
    let mut mask = [[false; N]; N];
    for i in 0..N {
        for j in 0..N {
            mask[i][j] = data["mask"][i][j].as_i64().unwrap() != 0;
        }
    }
    let pi = pi_mode();
    let mut reports = Vec::new();
    for seed in [359, 361] {
        let mut q: Vec<_> = (0..N).map(|i| pt(7 + 13 * i as i64, 100)).collect();
        let mut p: Vec<_> = (0..N).map(|i| pt(11 + 9 * i as i64, 100)).collect();
        q[0] = pt(seed, 384);
        p[0] = pt(73, 384);
        let mut steps = Vec::new();
        let mut status = "no-arrival-through-window";
        let mut stop = 96;
        for k in 0..=96 {
            let decision = detector(&q[0], &p[0]);
            steps.push(json!({"step":k,"q":q.iter().map(wire).collect::<Vec<_>>(),"p":p.iter().map(wire).collect::<Vec<_>>(),"detector":decision}));
            if decision >= 0 {
                status = if decision == 1 {
                    "certified-first-arrival"
                } else {
                    "receiver-family-undecided"
                };
                stop = k;
                break;
            }
            if k == 96 {
                break;
            }
            eprintln!("seed {seed}: exact step {k}");
            let nextq: Vec<_> = (0..N)
                .map(|i| add(&q[i], &scale(&phase_circle(&p[i], &pi).1, &r(27, 100))))
                .collect();
            let grad = force(&nextq, &pi, &mask);
            p = (0..N).map(|i| sub(&p[i], &grad[i])).collect();
            q = nextq;
        }
        reports.push(json!({"seed":[format!("{seed}/384"),"73/384".to_string()],"status":status,"step":stop,"steps":steps}));
    }
    let out = json!({"schema":"holonics.exact-phase-receiver.v1","pi_mode":"16 atan(1/5)-4 atan(1/239); lifted Machin constraint","pi_enclosure":wire(&pi),"dyadic_octaves":GRAIN,"exponential_terms":TERMS,"circular_terms":24,"float_operations":false,"scope":"actual unchanged analytic map; complete rational enclosures, no midpoint arrival verdict; lifted phases retain integer winding","results":reports,"elapsed_ms":start.elapsed().as_millis()});
    fs::write(
        root.join("trajectory.json"),
        serde_json::to_string_pretty(&out)? + "\n",
    )?;
    for entry in out["results"].as_array().unwrap() {
        println!(
            "{} {} step {}",
            entry["seed"][0], entry["status"], entry["step"]
        );
    }
    Ok(())
}
