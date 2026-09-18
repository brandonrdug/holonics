"""Public fitted-reaction word release. Driver supplies examples, never model weights."""
import importlib.util
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
spec=importlib.util.spec_from_file_location("performance",ROOT/"research/experiments/native_performance_benchmark/benchmark.py")
performance=importlib.util.module_from_spec(spec);spec.loader.exec_module(performance)

def row(v): return [{"numerator":str(x),"denominator":"1"} for x in v]

def main():
    requests=[];labels=[]
    def add(label,**request):
        labels.append(label);requests.append({"schema":"org.holonics.hna.stream-request.v1","command":{"action":"mathematical-request","request":request}})
    a=[[0]*10 for _ in range(12)]
    for j in range(4):a[j][j]=-1;a[j][4+j]=1;a[4+j][4+j]=1;a[8+j][j]=1
    c=[[0]*10 for _ in range(2)];c[0][8]=c[1][9]=1
    add("source",operation="construct-linear",coefficients=list(map(row,a)))
    add("condition",operation="construct-linear",coefficients=list(map(row,c)))
    add("model",operation="construct-predictor",source_operator=0,condition_operator=1,target_complex=2,fractional_bits=8)
    prediction=0
    for _ in range(4):
        for p in range(2):
            for current in range(2):
                for h in [1,-1]:
                    x=[0]*10;x[2*p]=x[4+2*current]=1;x[8]=h
                    target=current if h==1 else 1-current
                    eta=[0]*4;eta[2*target]+=1;eta[2*current]-=1
                    add(f"prediction-{prediction}",operation="predict-section",predictor=0,preparation={"kind":"values","values":row(x)},retain_prediction=True)
                    add(f"return-{prediction}",operation="observe-section",predictor=0,prediction=prediction,observed=row(eta))
                    prediction+=1
    add("bind",operation="bind-predictor-wave",predictor=0,previous=row([1,0,0,0]),current=row([1,0,0,0]),condition=row([1,0]),
        alphabet={"octets":[[97],[98]],"identities":["a","b"]})
    add("repeat",operation="predict-wave",predictor=0,steps=3)
    add("alternate",operation="predict-wave",predictor=0,steps=3,condition=row([-1,0]))
    add("release",operation="predict-wave",predictor=0,steps=3,condition=row([-1,0]),commit=True,retain_prediction=True)
    add("later-forecast",operation="predict-wave",predictor=0,steps=1)
    add("late-return",operation="observe-wave",predictor=0,prediction=32,observed=row([1,0,0,0]))
    add("returned-continuation",operation="predict-wave",predictor=0,steps=1,commit=True)
    payload="".join(json.dumps(v)+"\n" for v in requests)
    (HERE/"requests.jsonl").write_text(payload)
    process,elapsed,resources=performance.measured_process([str(ROOT/"target/debug/holonics"),"hna","mathematical-session","--input","-"],payload)
    (HERE/"responses.jsonl").write_text(process.stdout)
    if process.returncode:raise RuntimeError(process.stderr)
    events=[json.loads(line) for line in process.stdout.splitlines() if line.strip()]
    assert len(events)==len(requests)
    for label,event in zip(labels,events):assert event.get("event")=="mathematical-return",(label,event)
    values={label:event["value"] for label,event in zip(labels,events)}
    assert values["repeat"]["text"]=="aaa"
    assert values["alternate"]["text"]==values["release"]["text"]=="bab"
    assert values["alternate"]["joint"]==values["release"]["joint"]
    assert values["repeat"]["successor_epoch"]==values["alternate"]["successor_epoch"]==0
    assert values["release"]["successor_epoch"]==1
    assert values["late-return"]["observations"]==33
    assert values["returned-continuation"]["successor_epoch"]==2
    assert values["later-forecast"]["endpoint"]!=values["returned-continuation"]["endpoint"]
    result={"scope":"two-symbol conditional transition task; applied stored coefficients; whole joint decoder; no interleaved self-reception",
        "development_observations":32,"native_process_wall_ns":elapsed,"process_resources":resources,"process_stderr":process.stderr,
        "outputs":{name:values[name] for name in ["bind","repeat","alternate","release","later-forecast","late-return","returned-continuation"]}}
    (HERE/"result.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"repeat":values["repeat"]["text"],"alternate":values["alternate"]["text"],"released":values["release"]["text"],
        "after_return":values["returned-continuation"]["text"],"native_process_wall_ns":elapsed}))

if __name__=="__main__":main()
