#!/usr/bin/env python3
"""Test the stronger zero-wall left-half obligation, retaining exact support."""
import json,pathlib,time,z3
ROOT=pathlib.Path(__file__).resolve().parent

def run(w,h,timeout=10000):
    s=z3.Solver();s.set(timeout=timeout,random_seed=0)
    init={i:z3.Bool('l%d'%i) for i in range(1,w+1)}
    row={0:z3.BoolVal(False),**{i:init.get(i,z3.BoolVal(False)) for i in range(1,h+2)}}
    for t in range(h+1):
        if t%2==0:s.add(row[1])
        if t<h:
            nxt={0:z3.BoolVal(False)}
            for k in range(1,h+1-t):
                v=z3.Bool('l%d_%d'%(t+1,k));nxt[k]=v
                s.add(v==z3.Xor(row[k+1],z3.Or(row[k],row[k-1])))
            row=nxt
    start=time.monotonic();ans=s.check()
    rec={'width':w,'horizon_inclusive':h,'result':str(ans),'solve_seconds':round(time.monotonic()-start,3)}
    if ans==z3.sat:
        m=s.model();rec['ones']=[i for i,v in init.items() if z3.is_true(m.eval(v,model_completion=True))]
        active=set(rec['ones']);vals=[];first=None
        for t in range(8*h+64):
            v=int(1 in active);vals.append(v)
            if t%2==0 and v==0:
                first=t;break
            active={k for k in range(1,w+t+2) if ((k+1 in active)!=((k in active)or(k-1 in active)))}
        assert first is None or first>h
        rec.update(first_even_white=first,independent_witness_check=True,col1=vals)
    if ans==z3.unknown:rec['reason']=s.reason_unknown()
    return rec

if __name__=='__main__':
    out={'target':'every finite zero-wall left half turns its first cell white at an even time',
         'universal_target_proved':False,'records':[]}
    for w in [40,48,52,56,64,80,96]:
        rec=run(w,2*w+2);out['records'].append(rec)
        (ROOT/'left-results.json').write_text(json.dumps(out,indent=2)+'\n')
        print(json.dumps(rec),flush=True)
