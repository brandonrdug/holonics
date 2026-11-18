import sys, math
def layout(A,D,H,n,still,f,K,frames,reach,lanes,depth=0,carry=0,triads=0,opening=0,junction=0,mark=0,loud=0,closed=0):
    m2=2*H*n
    moment_modes=sum(1 for h in range(H) if h%frames>=still)*n
    paced=sum(1 for h in range(H) if h%frames>=still)
    fams=[]; at=0
    def push(name,l,g,tail=False):
        nonlocal at
        if l>0 or not tail: fams.append((name,at,l,g))
        at+=l
    a1=A+1
    for nm,l,g in [("enc",a1*D,16),("before",a1*D,16),("after",a1*D,16),("q",m2*D,24),("q_bias",m2,16),("v",m2*D,24),("v_bias",m2,16),
        ("out",D*m2,24),("out_bias",D,16),("a",f*D,24),("a_bias",f,16),("b",f*D,24),("b_bias",f,16),("w",D*f,24),("w_bias",D,16),
        ("read",D*D,24),("read_bias",A,16),("moment_before",a1*2*moment_modes,16),("moment_after",a1*2*moment_modes,16),("temper",2*H,24),
        ("probe",m2*D,24),("probe_bias",m2,16),("pace",paced*a1,24),("moment_face",D*m2,24),("moment_face_bias",D,16),("lift_bias",D,16)]:
        push(nm,l,g)
    for nm,l,g in [("carry",2*carry*D,24),("carry_bias",2*carry,16),("triad",6*triads*D,24),("triad_bias",6*triads,16),("w_triad",D*2*triads,24),
        ("opening",opening*D*D,24),("opening_bias",opening*D,16),("junction",junction*D,24),("junction_bias",junction,16),("mark",mark*3,24),("loud",loud*(lanes+1),16)]:
        push(nm,l,g,True)
    return fams,at
if __name__=="__main__":
    f,at=layout(244,128,4,8,2,128,4,4,3771,4,0,32,10,1,0,1,0)
    print(at)
    f2,at2=layout(2,64,4,8,2,128,2,4,3771,2)
    print(at2)
