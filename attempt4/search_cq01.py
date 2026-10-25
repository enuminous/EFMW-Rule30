#!/usr/bin/env python3
"""Exact, bounded exploration. No finite result is a CQ01Empty proof."""
import argparse
import hashlib
import json
from pathlib import Path


def reconstruction(n):
    # Integer bit p is the right-half position p, including the forced center.
    r, apack, u = 1, 0, []
    for t in range(n):
        q = (r >> 1) & 1
        if t & 1:
            u.append(q)
        a = 1 if t % 2 == 0 else 1 ^ q
        apack |= a << t
        r = ((r << 1) ^ (r | (r >> 1))) & ~1
        r |= int((t + 1) % 2 == 0)
    # recon(k+2,t)=recon(k+1,t+1) XOR (recon(k+1,t) OR recon(k,t)).
    previous, current, length = 0, apack, n
    psi = [0]
    for depth in range(1, n + 1):
        psi.append(current & 1)
        length -= 1
        previous, current = current, ((current >> 1) ^ (current | previous)) & ((1 << length) - 1)
    return psi, u


def independent_arrays(n):
    row = [1] + [0] * (n + 2)
    a, u = [], []
    for t in range(n):
        a.append(1 if not t % 2 else 1 - row[1])
        if t % 2:
            u.append(row[1])
        nxt = [int((t + 1) % 2 == 0)] + [0] * (n + 2)
        for p in range(1, n + 2):
            nxt[p] = (row[p - 1] + max(row[p], row[p + 1])) % 2
        row = nxt
    cols = [[0] * n, a]
    psi = [0, a[0]]
    for k in range(2, n + 1):
        prev, prevprev = cols[-1], cols[-2]
        nxt = [(prev[t + 1] + max(prev[t], prevprev[t])) % 2 for t in range(len(prev) - 1)]
        cols.append(nxt)
        psi.append(nxt[0])
    return psi, u


def death_by_forward(psi, width, horizon):
    row = 1 << width
    for k in range(1, width + 1):
        row |= psi[k] << (width - k)
    for t in range(horizon + 1):
        if ((row >> (width + t)) & 1) != int(t % 2 == 0):
            return t
        row = (row << 2) ^ ((row << 1) | row)
    return None


def affine_prediction(psi, n, mask):
    features = [1, psi[n - 1], psi[n], psi[n + 1], n % 2]
    return sum(v for j, v in enumerate(features) if mask & (1 << j)) % 2


def run(n=16384, output_dir=None):
    psi, u = reconstruction(n)
    check, check_u = independent_arrays(256)
    assert psi[:257] == check and u[:128] == check_u
    controls = []
    for width in range(128):
        d = next(k for k in range(width + 1, n + 1) if psi[k])
        observed = death_by_forward(psi, width, d)
        assert observed == d, (width, d, observed)
        controls.append(dict(width=width, predicted=d, observed=observed))
    periodic = []
    for period in range(1, 65):
        for transient in range(257):
            if all(u[t] == u[t + period] for t in range(transient, 1024 - period)):
                periodic.append(dict(period=period, transient=transient,
                    holdout_pass=all(u[t] == u[t + period] for t in range(1024 - period, len(u) - period))))
    affine = []
    rejections = []
    for phase in [0, 1]:
        for mask in range(32):
            bad = next((j for j in range(2, (1024 - phase) // 2 + 1)
                        if affine_prediction(psi, j, mask) != psi[2 * j + phase]), None)
            if bad is not None:
                rejections.append(dict(phase=phase, mask=mask, first_counterexample_n=bad))
            else:
                held_bad = next((j for j in range((1024 - phase) // 2 + 1, (n - phase) // 2 + 1)
                                 if affine_prediction(psi, j, mask) != psi[2 * j + phase]), None)
                affine.append(dict(phase=phase, mask=mask, first_holdout_counterexample_n=held_bad))
    ones = [k for k in range(1, n + 1) if psi[k]]
    gaps = [(b-a-1, a+1, b-1) for a, b in zip(ones, ones[1:])]
    maxgap = max(gaps)
    out = dict(target="CQ01Empty",target_solved=False,depth=n,
               psi_sha256=hashlib.sha256(bytes(psi)).hexdigest(),
               psi_first128="".join(map(str, psi[1:129])),
               u_first128="".join(map(str, u[:128])),
               black_count=len(ones), last_black_depth=ones[-1],
               largest_internal_zero_gap=dict(length=maxgap[0],start=maxgap[1],end=maxgap[2]),
               independent_array_prefix=256, truncation_controls=controls,
               periodic_training_candidates=periodic,affine_training_survivors=affine,
               affine_rejections=rejections,
               status="FINITE_EXPLORATION_ONLY")
    folder=Path(output_dir).resolve() if output_dir is not None else Path(__file__).resolve().parent
    folder.mkdir(parents=True, exist_ok=True)
    (folder/'results.json').write_text(json.dumps(out, indent=2)+'\n')
    (folder/'psi-prefix.txt').write_text(''.join(map(str,psi[1:]))+'\n')
    (folder/'right-trace.txt').write_text(''.join(map(str,u))+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ['truncation_controls','affine_rejections']},indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir')
    args = parser.parse_args()
    run(output_dir=args.output_dir)
