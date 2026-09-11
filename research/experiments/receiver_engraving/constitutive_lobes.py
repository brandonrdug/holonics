"""Small exact two-domain conformation source.

This is a bounded constitutive witness, not a protein sequence model or a continuous-time solver.
Two domains carry the exact ``a+q^2`` response and are coupled through a quadratic contact term.
Every state and receipt is a Fraction wire; no target matching or fitted answer is used.
"""
from fractions import Fraction as Q
import json
from pathlib import Path

A=Q(1,2); KAPPA=Q(1); DRIVE=Q(1); ETA=Q(1,8); STEPS=4

def wire(q): return [str(q.numerator),str(q.denominator)]
def conformation(q): return A+q*q
def domain_response(q): return 2*q*conformation(q)
def internal_gradient(q1,q2):
    return (domain_response(q1)+KAPPA*(q1+q2), domain_response(q2)+KAPPA*(q1+q2))
def gradient(q1,q2):
    g=internal_gradient(q1,q2)
    return (g[0]-DRIVE,g[1])
def energy(q1,q2):
    return Q(1,2)*conformation(q1)**2+Q(1,2)*conformation(q2)**2+Q(1,2)*KAPPA*(q1+q2)**2-DRIVE*q1
def hessian_diag(q): return 2*A+6*q*q+KAPPA
def rotation(q):
    den=1+q*q
    return [[wire((1-q*q)/den),wire(2*q/den)],
            [wire(-2*q/den),wire((1-q*q)/den)]]
def state(q1,q2,prev_energy=None,grad=None):
    e=energy(q1,q2)
    row={"q":[wire(q1),wire(q2)],"conformation":[wire(conformation(q1)),wire(conformation(q2))],
         "gradient":[wire(x) for x in gradient(q1,q2)],
         "internal_gradient":[wire(x) for x in internal_gradient(q1,q2)],
         "source_force":[wire(DRIVE),wire(Q(0))],
         "stiffness":[wire(hessian_diag(q1)),wire(hessian_diag(q2))],
         "rotation_q1":rotation(q1),"rotation_q2":rotation(q2),"energy":wire(e),
         "stored_energy":wire(e+DRIVE*q1)}
    if prev_energy is not None:
        diss=ETA*(grad[0]*grad[0]+grad[1]*grad[1])
        row.update({"energy_drop":wire(prev_energy-e),"gradient_work":wire(diss),
                    "bookkeeping_residual":wire((prev_energy-e)-diss)})
    return row

def contact_off():
    q=Q(0); rows=[]
    def e(x): return Q(1,2)*conformation(x)**2-DRIVE*x
    def g(x): return domain_response(x)-DRIVE
    prev=e(q)
    for step in range(STEPS+1):
        row={"step":step,"q1":wire(q),"q2":["0","1"],"energy":wire(e(q)),"gradient":wire(g(q)),
             "contact":"off","q2_response": ["0","1"]}
        if step:
            row["energy_drop"]=wire(prev-e(q)); row["gradient_work"]=wire(work)
        rows.append(row)
        if step<STEPS:
            work=ETA*g(q)*g(q); prev=e(q); q=q-ETA*g(q)
    assert all(Q(int(rows[i]["energy_drop"][0]),int(rows[i]["energy_drop"][1]))>0 for i in range(1,len(rows)))
    return rows

def build():
    assert ETA < Q(4,9)  # 2/(9/2), exact stability-step inequality
    q1=q2=Q(0); rows=[]; prev=None; pending_grad=None
    for step in range(STEPS+1):
        g=gradient(q1,q2) if step<STEPS else gradient(q1,q2)
        rows.append(dict(step=step,**state(q1,q2,prev,pending_grad if pending_grad is not None else g)))
        if step<STEPS:
            prev=energy(q1,q2); pending_grad=g; q1,q2=q1-ETA*g[0],q2-ETA*g[1]
    drops=[rows[i]["energy_drop"] for i in range(1,len(rows))]
    assert all(Q(int(d[0]),int(d[1]))>0 for d in drops)
    assert all(abs(Q(int(q[0]),int(q[1])))<=Q(1,2) for r in rows for q in r["q"])
    for r in rows:
        for matrix in (r["rotation_q1"],r["rotation_q2"]):
            a=Q(int(matrix[0][0][0]),int(matrix[0][0][1])); b=Q(int(matrix[0][1][0]),int(matrix[0][1][1]))
            c=Q(int(matrix[1][0][0]),int(matrix[1][0][1])); d=Q(int(matrix[1][1][0]),int(matrix[1][1][1]))
            assert a*a+b*b==1 and c*c+d*d==1 and a*c+b*d==0 and a*d-b*c==1
    for i in range(1,len(rows)):
        qprev=Q(int(rows[i-1]["q"][0][0]),int(rows[i-1]["q"][0][1])); qnow=Q(int(rows[i]["q"][0][0]),int(rows[i]["q"][0][1]))
        stored_prev=Q(int(rows[i-1]["stored_energy"][0]),int(rows[i-1]["stored_energy"][1])); stored_now=Q(int(rows[i]["stored_energy"][0]),int(rows[i]["stored_energy"][1]))
        work=DRIVE*(qnow-qprev); heat=work-(stored_now-stored_prev)
        rows[i]["external_work"]=wire(work); rows[i]["finite_heat_receipt"]=wire(heat)
        assert heat==Q(int(rows[i]["energy_drop"][0]),int(rows[i]["energy_drop"][1])) and heat>0
    off=contact_off()
    assert Q(int(rows[-1]["q"][1][0]),int(rows[-1]["q"][1][1]))<0 and all(r["q2"]==["0","1"] for r in off)
    return {"schema":"holonics.receiver-engraving.constitutive-lobes.v1",
            "parameters":{"a":wire(A),"kappa":wire(KAPPA),"drive_F":wire(DRIVE),"eta":wire(ETA),"steps":STEPS,
                          "stability_aperture":"|q_i| <= 1/2; Hessian operator bound L <= 9/2; eta < 2/L"},
            "scope":"exact bounded gradient passage for four discrete steps; not a continuous-flow or calibrated biological law",
            "source_rules":["source force is fixed F on domain 1","contact is quadratic kappa/2*(q1+q2)^2",
                            "q is a conformation coordinate, not a literal rotation angle","no target matching or fitted values"],
            "states":rows,"contact_off_ablation":contact_off(),
            "remote_sign_pair":{"q_plus":[wire(Q(1,4)),wire(Q(0))],"q_minus":[wire(Q(-1,4)),wire(Q(0))],
                                 "response_plus":wire(domain_response(Q(1,4))),"response_minus":wire(domain_response(Q(-1,4))),
                                 "even_receiver_q_squared":wire(Q(1,16))},
            "energy_law":"E = 1/2(a+q1^2)^2 + 1/2(a+q2^2)^2 + kappa/2(q1+q2)^2 - F*q1",
            "gradient_law":"g1=2*q1*(a+q1^2)+kappa*(q1+q2)-F; g2=2*q2*(a+q2^2)+kappa*(q1+q2)",
            "rotation_law":"R(q)=[[ (1-q^2)/(1+q^2), 2q/(1+q^2)],[-2q/(1+q^2),(1-q^2)/(1+q^2)]]"}

def main():
    out=Path(__file__).with_name("constitutive_lobes_receipt.json")
    out.write_text(json.dumps(build(),indent=2)+"\n")
    print("returned exact constitutive lobe receipt: 4 coupled steps; energy descent verified")
if __name__=="__main__": main()
