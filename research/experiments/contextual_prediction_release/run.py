"""Exercise public prediction/code releases; all fitting and application use shared owners."""
from fractions import Fraction as Q
import importlib.util
import json
from pathlib import Path
import statistics
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
spec = importlib.util.spec_from_file_location("native_performance", ROOT / "research/experiments/native_performance_benchmark/benchmark.py")
benchmark = importlib.util.module_from_spec(spec)
spec.loader.exec_module(benchmark)


def wire(x):
    x = Q(x)
    return {"numerator": str(x.numerator), "denominator": str(x.denominator)}


def rational(x):
    return Q(int(x["numerator"]), int(x["denominator"]))


def rows(values):
    return [[wire(x) for x in row] for row in values]


def main():
    requests, labels = [], []

    def add(label, **body):
        labels.append(label)
        requests.append({"schema": "org.holonics.hna.stream-request.v1", "command": {
            "action": "mathematical-request", "request": body}})

    add("source restriction", operation="construct-linear", coefficients=rows([
        [1,0,0,0,0,0], [0,1,0,0,0,0], [0,0,1,0,0,0], [0,0,0,1,0,0]]))
    add("condition restriction", operation="construct-linear", coefficients=rows([
        [0,0,0,0,1,0], [0,0,0,0,0,1]]))
    add("found predictor", operation="construct-predictor", source_operator=0, condition_operator=1,
        target_complex=2, fractional_bits=32)
    for i, (a,b,c,y,z) in enumerate([(1,0,1,1,0), (1,0,-1,0,1), (0,1,1,0,1), (0,1,-1,1,0)]):
        add(f"development prediction {i}", operation="predict-section", predictor=0,
            preparation={"kind":"values", "values":[wire(x) for x in [a,0,b,0,c,0]]}, retain_prediction=True)
        add(f"actual return {i}", operation="observe-section", predictor=0, prediction=i,
            observed=[wire(x) for x in [y,0,z,0]])
    for i in range(33):
        condition = 1 if i % 2 == 0 else -1
        add("query warmup" if i == 0 else f"held-out query {i}", operation="predict-section", predictor=0,
            preparation={"kind":"values", "values":[wire(x) for x in [2,0,-1,0,condition,0]]}, retain_prediction=False)
    for name,condition in [("zero difference mode",[0,0]),("quarter-turn difference mode",[0,1])]:
        add(name,operation="predict-section",predictor=0,
            preparation={"kind":"values","values":[wire(x) for x in [2,0,-1,0,*condition]]},retain_prediction=False)

    forms = rows([[1,0], [0,1], [1,1]])
    add("infer complex product", operation="construct-bilinear", target={"left_extent":2,"right_extent":2,
        "coefficients":rows([[1,0,0,-1], [0,1,1,0]])}, construction={"kind":"search",
        "left_forms":forms,"right_forms":forms,"min_products":1,"max_products":3,"max_candidates":1000})
    add("release complex code", operation="emit-rust", operator=2)
    x, z = [Q(2,3), Q(-5,4)], [Q(7,5), Q(3,2)]
    add("resident complex product", operation="apply", operator=2, left=list(map(wire,x)),
        right=list(map(wire,z)), retain_product=True)
    add("change receiver", operation="compose-receiver", operator=2, matrix=rows([[1,1],[1,-1]]))
    add("release changed code", operation="emit-rust", operator=3)
    add("resident changed receiver", operation="read-product", operator=3, product=0)
    add("construct recurrence", operation="construct-linear", coefficients=rows([[1,1],[1,0]]))
    add("infer fifth power", operation="power", operator=4, exponent=5)
    add("release linear code", operation="emit-rust", operator=5)
    add("resident linear power", operation="apply", operator=5, left=list(map(wire,x)), retain_product=False)

    payload = "".join(json.dumps(x) + "\n" for x in requests)
    (HERE / "requests.jsonl").write_text(payload)
    process, wall, resources = benchmark.measured_process([
        str(ROOT / "target/debug/holonics"), "hna", "mathematical-session", "--input", "-"], payload)
    (HERE / "responses.jsonl").write_text(process.stdout)
    if process.returncode:
        raise RuntimeError(process.stderr)
    events = [json.loads(x) for x in process.stdout.splitlines() if x.strip()]
    assert len(events) == len(requests)
    for label,event in zip(labels, events):
        assert event.get("event") == "mathematical-return", (label,event)
    values = {label:event["value"] for label,event in zip(labels,events)}
    assert values["found predictor"]["feature_complex"] == 5
    zero = values["development prediction 0"]["output"]
    assert rational(zero["radius"]) == 0
    assert all(rational(v["real"]) == rational(v["imaginary"]) == 0 for v in zero["center"])
    queries = []
    for i in range(1,33):
        value = values[f"held-out query {i}"]
        output = value["output"]
        expected = [Q(4,3), Q(-2,3)] if i % 2 == 0 else [Q(-2,3), Q(4,3)]
        radius = rational(output["radius"])
        error = sum((rational(v["real"])-e)**2 + rational(v["imaginary"])**2 for v,e in zip(output["center"],expected))
        assert error <= radius**2 and radius < Q(1,1000), value
        assert value["intermediate_section_readouts"] == 0
        assert value["observations"] == 4
        target=[Q(3,2)*x for x in expected]
        difference=[{"real":wire(rational(v["real"])-t),"imaginary":v["imaginary"]} for v,t in zip(output["center"],target)]
        task_square=sum(rational(v["real"])**2+rational(v["imaginary"])**2 for v in difference)
        queries.append({"index":i,"expected_real":list(map(wire,expected)),"output":output,"cost":value["cost"],
            "exchange_target_real":list(map(wire,target)),"prediction_minus_exchange_target":difference,
            "exchange_discrepancy_square":wire(task_square),"normal_enclosure_contains_exchange_target":task_square<=radius**2})
    phase_queries=[]
    for name,imaginary in [("zero difference mode",[Q(0),Q(0)]),("quarter-turn difference mode",[Q(1),Q(-1)])]:
        value=values[name]
        output=value["output"]
        error=sum((rational(v["real"])-Q(1,3))**2+(rational(v["imaginary"])-i)**2 for v,i in zip(output["center"],imaginary))
        assert error<=rational(output["radius"])**2 and rational(output["radius"])<Q(1,1000)
        assert value["intermediate_section_readouts"]==0 and value["observations"]==4
        phase_queries.append({"condition":name,"expected_real":[wire(Q(1,3))]*2,"expected_imaginary":list(map(wire,imaginary)),"return":value})

    complex_result = [x[0]*z[0]-x[1]*z[1], x[0]*z[1]+x[1]*z[0]]
    expected = {"base":complex_result, "changed":[sum(complex_result),complex_result[0]-complex_result[1]],
        "linear":[8*x[0]+5*x[1],5*x[0]+3*x[1]]}
    for name,label in [("base","resident complex product"),("changed","resident changed receiver"),("linear","resident linear power")]:
        assert list(map(rational,values[label]["output"])) == expected[name]
    assert values["resident changed receiver"]["source_products_recomputed"] is False
    target = HERE / "target_program"
    for module,label in [("base","release complex code"),("changed","release changed code"),("linear","release linear code")]:
        (target / "src" / f"{module}.rs").write_text(values[label]["source"])
    # This harness supplies new inputs and reads outputs. It does not contain the generated algorithm.
    (target / "src/main.rs").write_text('''mod base; mod changed; mod linear;
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
''')
    build, build_wall, build_resources = benchmark.measured_process([
        "cargo","build","--offline","--manifest-path",str(target / "Cargo.toml"),
        "--target-dir",str(ROOT / "target/hephaestus-function-check")])
    if build.returncode:
        raise RuntimeError(build.stderr)
    run, run_wall, run_resources = benchmark.measured_process([
        str(ROOT / "target/hephaestus-function-check/debug/hephaestus-function-check")])
    if run.returncode:
        raise RuntimeError(run.stderr)
    decoded = {name:list(map(Q,data.split(","))) for name,data in (line.split(":") for line in run.stdout.splitlines())}
    assert decoded == expected
    times = [q["cost"]["elapsed_microseconds"] for q in queries]
    result = {"scope":"declared preparation restrictions; native unit-prior bilinear-feature prediction; exact factor-code release",
        "native_process":{"wall_ns":wall,"resources":resources,"stderr":process.stderr},
        "development_observations":4,"queries":queries,"additional_phase_queries":phase_queries,
        "query_measurement":{"receiver":"one two-complex-component normal-reference enclosure","count":32,
            "clock":"public request body, microseconds; first query excluded", "median_us":statistics.median(times),
            "sum_us":sum(times),"rate_numerator":32*1000000,"rate_denominator":sum(times),
            "rate_unit":"delivered sections per request-body second"},
        "target_build":{"wall_ns":build_wall,"resources":build_resources,"stderr":build.stderr},
        "target_execution":{"wall_ns":run_wall,"resources":run_resources,"stdout":run.stdout},
        "target_expected":{name:list(map(wire,value)) for name,value in expected.items()},
        "artifacts":{name:values[label]["graph"] for name,label in [("base","release complex code"),("changed","release changed code"),("linear","release linear code")]}}
    (HERE / "result.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"verified_contextual_sections":34,"executed_generated_functions":3,
        "native_process_ns":wall,"median_query_us":statistics.median(times),"target_build_ns":build_wall,"target_execution_ns":run_wall}))


if __name__ == "__main__":
    main()
