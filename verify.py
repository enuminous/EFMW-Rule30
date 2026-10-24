#!/usr/bin/env python3
"""Separate simulations and boundary controls for the SMT encoding."""
import json,pathlib,z3
from search import solver_cone, trace, direct_trace

ROOT=pathlib.Path(__file__).resolve().parent
out={'checks':[],'passed':False}
# Exact maxima recomputed from individual expanding infinite-line rows.
for r in range(7):
    deaths=[]
    for seed in range(1<<(2*r+1)):
        a=trace(seed,r,24)
        death=next(t for t,v in enumerate(a) if v!=1-t%2)
        deaths.append(death)
    maximum=max(deaths)
    for horizon,expected in [(maximum-1,z3.sat),(maximum,z3.unsat)]:
        s,initial=solver_cone(r,horizon,10000)
        ans=s.check()
        assert ans==expected,(r,horizon,ans,expected)
    witness=deaths.index(maximum)
    assert trace(witness,r,maximum)==direct_trace(witness,r,maximum)
    out['checks'].append({'control':'exhaustive_crosscheck','radius':r,
                          'configurations':len(deaths),'maximum_first_failure':maximum})
# The known ether is infinite, but this control uses an honest finite truncation.
r=21
p=[0,1,0,0,1,1,0]
p=[p[(i-1)%7]^(p[i]|p[(i+1)%7]) for i in range(7)]
seed=sum(p[i%7]<<(i+r) for i in range(-r,r+1))
a=direct_trace(seed,r,100)
death=next(t for t,v in enumerate(a) if v!=1-t%2)
assert death==22
for h,expected in [(21,z3.sat),(22,z3.unsat)]:
    s,initial=solver_cone(r,h,10000)
    for i,v in initial.items():s.add(v==bool(seed>>(i+r)&1))
    assert s.check()==expected
out['checks'].append({'control':'truncated_ether','radius':r,'first_failure':death})
# The rank obstruction is checked with dictionary evolution and local window counts.
seed=108;r=3
assert direct_trace(seed,r,2)==[1,0,1]
active={i-r for i in range(2*r+1) if seed>>i&1}
before=active.copy()
for t in range(2):
    active={i for i in range(-r-t-1,r+t+2)
            if ((i-1 in active)!=((i in active)or(i+1 in active)))}
after=active
assert after=={i-5 for i in range(11) if 1772>>i&1}
def counts(cells,k):
    ans={}
    for start in range(min(cells)-k+1,max(cells)+1):
        word=sum(int(start+j in cells)<<j for j in range(k))
        if word:ans[word]=ans.get(word,0)+1
    return ans
for k in range(1,7):
    a,b=counts(before,k),counts(after,k)
    assert all(b.get(p,0)>=n for p,n in a.items())
    out['checks'].append({'control':'rank_obstruction','length':k,'before':a,'after':b})
out['passed']=True
(ROOT/'verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'passed':True,'checks':len(out['checks'])}))
