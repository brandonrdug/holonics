import sys,re
cur=None
want=('field_contact_rows','field_contact_l4','field_contact_columns','field_pace_skin_back','field_exposure','field_skin_fill','field_spread','field_pair_gate_back','field_pair_scan_back','field_pair_scan_pre','field_pair_gamma','field_pair_scan')
st=ss=sl=0
for l in open(sys.argv[1]):
    m=re.search(r"Compiling entry function '(\w+)'",l)
    if m: cur=m.group(1); st=ss=sl=0; continue
    m=re.search(r"(\d+) bytes stack frame, (\d+) bytes spill stores, (\d+) bytes spill loads",l)
    if m and cur: st,ss,sl=map(int,m.groups()); continue
    m=re.search(r"Used (\d+) registers",l)
    if m and cur:
        if cur in want: print(f"{cur:26s} regs={m.group(1):>4s} stack={st:4d} spill_st={ss:5d} spill_ld={sl:5d}")
        cur=None
