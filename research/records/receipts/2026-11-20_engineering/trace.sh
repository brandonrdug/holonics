#!/bin/bash
# Reading A4 of the engineering report (§11): the card's idle share of a plain section. Nsight Systems (/opt/cuda-12.9/bin/nsys) traces 40
# sections of train-store from the line's Y70 end (width 224, pumped; the build lanebin/athena at 657099e79) under the card's lock between the
# line's steps; the trace's kernels and copies are joined as intervals and their union is set against the wall from the 11th section's first
# launch to the 40th's last. A reading: no state is kept, nothing enters the line. Projection: 40 sections at 532 to 717 ms plus the trace's
# own cost, under 2 minutes; timeout 600 s.
set -u
R=$REPO; L=$R/.local/wt/lead; W=$L/.local/run; D=$W/front; O=$W/eng; LOCK=$R/.local/gpu.lock
S=$R/.local/corpus/store-2026-11-12; ST=$S/STORE.tsv
K=$R/.local/wt/field-card/.local/run/KEYS8; U0=$R/.local/wt/section-edge/.local/run/gsm8k/UNITS0; R2=$R/.local/wt/store-trainer/.local/run/p48
C2=$R2/g115r2/CODEC; H=$R/.local/data/python-codes-25k/passage/HELD128.txt
BIN=$W/lanebin/athena; NSYS=/opt/cuda-12.9/bin/nsys
sha() { sha256sum "$1" | cut -c1-64; }
src=$D/arm_Y70/STATE.3000
rm -rf $O/trace_out $O/trace.nsys-rep $O/trace.sqlite
( flock -w 14400 9 || exit 75; echo "# trace: lock taken $(date -u +%H:%M:%S) $(nvidia-smi --query-compute-apps=pid --format=csv,noheader | wc -l) other runs"
  env -i HOME=$HOME PATH=/opt/cuda/bin:/usr/bin:/bin timeout 600 $NSYS profile --trace=cuda,osrt --sample=none --cpuctxsw=none --output=$O/trace --force-overwrite=true \
    $BIN train complete-language train-store $U0 $(sha $U0) $S $(sha $ST) prefix $K $(sha $K) $C2 $(sha $C2) $H $(sha $H) 40 40 1800000 $O/trace_out $src $(sha $src) > $O/trace_run.log 2>&1
  echo "# trace: exit $? released $(date -u +%H:%M:%S)" ) 9>$LOCK
$NSYS export --type=sqlite --output=$O/trace.sqlite --force-overwrite=true $O/trace.nsys-rep > /dev/null 2>&1
python3 -I - <<'PY'
import sqlite3
db=sqlite3.connect('$REPO/.local/wt/lead/.local/run/eng/trace.sqlite')
def rows(q):
    try: return db.execute(q).fetchall()
    except Exception as e: return []
k=rows("select start,end from CUPTI_ACTIVITY_KIND_KERNEL order by start")
m=rows("select start,end from CUPTI_ACTIVITY_KIND_MEMCPY order by start")+rows("select start,end from CUPTI_ACTIVITY_KIND_MEMSET order by start")
print('TRACE kernels', len(k), 'copies_and_sets', len(m))
if k:
    n=len(k); a=k[n//4][0]; b=k[-1][1]   # skip the first quarter of launches as the warm-up
    iv=sorted([(s,e) for s,e in k+m if s>=a and e<=b])
    busy=0; cs,ce=None,None
    for s,e in iv:
        if cs is None: cs,ce=s,e
        elif s<=ce: ce=max(ce,e)
        else: busy+=ce-cs; cs,ce=s,e
    if cs is not None: busy+=ce-cs
    ksum=sum(e-s for s,e in k if s>=a and e<=b)
    wall=b-a
    print(f'TRACE_IDLE window_ms={wall/1e6:.1f} busy_ms={busy/1e6:.1f} kernels_sum_ms={ksum/1e6:.1f} idle_share={1-busy/wall:.4f} overlap_of_kernels={(ksum-busy)/wall:.4f}')
    # the gaps between consecutive busy spans, by size
    gaps=[]; cs,ce=None,None
    for s,e in iv:
        if cs is None: cs,ce=s,e
        elif s<=ce: ce=max(ce,e)
        else: gaps.append(s-ce); cs,ce=s,e
    gaps.sort()
    if gaps:
        tot=sum(gaps)
        big=[g for g in gaps if g>=50000]
        print(f'TRACE_GAPS count={len(gaps)} median_us={gaps[len(gaps)//2]/1e3:.1f} p99_us={gaps[int(len(gaps)*0.99)]/1e3:.1f} sum_ms={tot/1e6:.1f} over_50us={len(big)} their_ms={sum(big)/1e6:.1f}')
PY
grep -E '^STORE_SECTION ' $O/trace_run.log | tail -n 30 | awk '{for(j=1;j<=NF;j++){split($j,a,"="); if(a[1]=="ms"){m+=a[2]; c++}}} END{printf "TRACE_SECTIONS last30 ms_mean=%.1f\n", m/c}'
echo "TRACE_ALL_DONE $(date -u +%H:%M:%S)"
