import R35_TRACE_CHARACTER_REBASES

namespace Soma.Holonics.R35

def held0 : TraceChart := {a:=3,b:=4,c:=4,d:=10,e:=10,f:=15,t:=38}
def held1 : TraceChart := applyRebase3 held0
def held2 : TraceChart := applyRebase0 held1
def held3 : TraceChart := applyRebase1 held2
def held4 : TraceChart := applyRebase2 held3
def held5 : TraceChart := applyRebase4 held4
def held6 : TraceChart := applyRebase1 held5
def held7 : TraceChart := applyRebase3 held6
def held8 : TraceChart := applyRebase0 held7
def held9 : TraceChart := applyRebase4 held8
def heldSource : TraceChart := {a:=15,b:=2,c:=4,d:=10,e:=56,f:=15,t:=38}

theorem heldoutTraceRebaseTransport : held9 = heldSource := by
  norm_num [heldSource, held0, held1, held2, held3, held4, held5, held6, held7, held8, held9, applyRebase0, applyRebase1, applyRebase2, applyRebase3, applyRebase4, r35m0c0, r35m0c1, r35m0c2, r35m0c3, r35m0c4, r35m0c5, r35m0c6, r35m1c0, r35m1c1, r35m1c2, r35m1c3, r35m1c4, r35m1c5, r35m1c6, r35m2c0, r35m2c1, r35m2c2, r35m2c3, r35m2c4, r35m2c5, r35m2c6, r35m3c0, r35m3c1, r35m3c2, r35m3c3, r35m3c4, r35m3c5, r35m3c6, r35m4c0, r35m4c1, r35m4c2, r35m4c3, r35m4c4, r35m4c5, r35m4c6]

theorem generated_heldout_trace_rebase : held9 = heldSource := heldoutTraceRebaseTransport

end Soma.Holonics.R35

#check Soma.Holonics.R35.generated_heldout_trace_rebase
