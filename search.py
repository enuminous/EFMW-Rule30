#!/usr/bin/env python3
"""Exact finite-cone SMT search; SAT witnesses are independently simulated.

Unknown is never promoted to UNSAT. No finite result proves the universal target.
"""
import argparse, json, pathlib, time
import z3

ROOT = pathlib.Path(__file__).resolve().parent

def trace(seed, radius, horizon):
    row = seed
    ans = []
    for t in range(horizon + 1):
        ans.append((row >> (radius + t)) & 1)
        row = (row << 2) ^ ((row << 1) | row)
    return ans

def direct_trace(seed, radius, horizon):
    active = {i-radius for i in range(2*radius+1) if seed >> i & 1}
    ans = []
    for t in range(horizon+1):
        ans.append(int(0 in active))
        active = {i for i in range(-radius-t-1, radius+t+2)
                  if ((i-1 in active) != ((i in active) or (i+1 in active)))}
    return ans

def solver_cone(radius, horizon, timeout):
    solver = z3.Solver()
    solver.set(timeout=timeout, random_seed=0)
    initial = {i: z3.Bool('x_'+str(i)) for i in range(-radius,radius+1)}
    row = {i: initial.get(i,z3.BoolVal(False)) for i in range(-horizon,horizon+1)}
    for t in range(horizon+1):
        solver.add(row[0] == z3.BoolVal(t % 2 == 0))
        if t < horizon:
            nxt = {}
            for i in range(-horizon+t+1,horizon-t):
                v = z3.Bool('v_%d_%d' % (t+1,i))
                solver.add(v == z3.Xor(row[i-1],z3.Or(row[i],row[i+1])))
                nxt[i] = v
            row = nxt
    return solver,initial

def attack(radius, horizon, timeout):
    start = time.monotonic()
    solver, initial = solver_cone(radius,horizon,timeout)
    outcome = solver.check()
    rec = {'radius':radius,'horizon_inclusive':horizon,'solver':str(outcome),
           'elapsed_seconds':round(time.monotonic()-start,3)}
    if outcome == z3.sat:
        m = solver.model()
        seed = sum(1 << (i+radius) for i,v in initial.items() if z3.is_true(m.eval(v,model_completion=True)))
        a = trace(seed,radius,max(4*horizon+64,horizon))
        b = direct_trace(seed,radius,horizon)
        assert a[:horizon+1] == b
        assert all(v == 1-t%2 for t,v in enumerate(b))
        first = next((t for t,v in enumerate(a) if v != 1-t%2),None)
        rec.update(seed=seed,ones=[i for i in range(-radius,radius+1) if seed>>(i+radius)&1],
                   first_failure=first,trace=a[:(first+1 if first is not None else len(a))],
                   independent_witness_check=True)
    elif outcome == z3.unknown:
        rec['reason_unknown'] = solver.reason_unknown()
    return rec

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--radii',default='11,12,13,14,15,16,20,24,32')
    ap.add_argument('--timeout-ms',type=int,default=10000)
    ap.add_argument('--output',default='sat-results.json')
    args=ap.parse_args()
    out={'target':'H(R) <= 2R+2','classification':'conjecture under attack',
         'solver_version':z3.get_version_string(),'records':[],
         'universal_theorem_proved':False,'problem1_solved':False}
    for r in map(int,args.radii.split(',')):
        rec=attack(r,2*r+2,args.timeout_ms)
        out['records'].append(rec)
        if rec['solver']=='sat': out['classification']='REFUTED'
        (ROOT/args.output).write_text(json.dumps(out,indent=2)+'\n')
        print(json.dumps(rec),flush=True)
    print(json.dumps({'classification':out['classification']}),flush=True)

if __name__=='__main__': main()
