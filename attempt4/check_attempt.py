#!/usr/bin/env python3
"""Compile and independently replay Attempt 4; reject a full-prize claim."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

PIN = '3eca23c0a9fa6b153313655e6d51835406c2d06e'
MODULE = 'Rule30CQ01Attempt4'
ROOT = Path(__file__).resolve().parent


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--kit', required=True)
    ap.add_argument('--lean-bin', default='')
    ap.add_argument('--output-dir', default=str(ROOT))
    args = ap.parse_args()
    kit = Path(args.kit).resolve()
    core = kit / 'lean'
    destination = Path(args.output_dir).resolve()
    output = destination / 'verification'
    output.mkdir(parents=True, exist_ok=True)
    lake = str(Path(args.lean_bin) / 'lake') if args.lean_bin else 'lake'
    lean = str(Path(args.lean_bin) / 'lean') if args.lean_bin else 'lean'
    env = os.environ.copy()
    env['LEAN_PATH'] = str(core) + (os.pathsep + env['LEAN_PATH'] if env.get('LEAN_PATH') else '')
    status = dict(target='CQ01Empty', target_solved=False, problem1_solved=False,
                  official_kit_commit=PIN, steps=[])

    def run(label, command, expected=0, cwd=core):
        p = subprocess.run(command, cwd=cwd, env=env, text=True,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
        (output / (label + '.log')).write_text(p.stdout)
        status['steps'].append(dict(label=label, exit_code=p.returncode))
        if p.returncode != expected:
            raise RuntimeError(f'{label}: exit {p.returncode}, expected {expected}: {p.stdout[-1200:]}')
        return p.stdout

    def parse_checker(text):
        items = [json.loads(line) for line in text.splitlines() if line.startswith('{')]
        assert len(items) == 1
        return items[0]

    try:
        assert run('kit-head', ['git', 'rev-parse', 'HEAD'], cwd=kit).strip() == PIN
        assert not run('kit-tracked-diff', ['git', 'diff', '--name-only', 'HEAD'], cwd=kit).strip()
        status['lean_version'] = run('lean-version', [lean, '--version']).strip()
        run('dependencies', [lake, 'build', 'Ruliology.CellularAutomata.Rule30PeriodTwoSideways'])
        source = (ROOT / (MODULE + '.lean')).read_text()
        status['source_sha256'] = hashlib.sha256(source.encode()).hexdigest()
        shutil.copyfile(ROOT / (MODULE + '.lean'), core / (MODULE + '.lean'))
        run('compile', [lake, 'env', 'lean', '-o', MODULE + '.olean', MODULE + '.lean'])
        headlines = [MODULE + '.' + n for n in re.findall(r'^theorem (\w+)', source, re.M)]
        cmd = [lake, 'env', 'lean', '--run', str(kit / 'Check.lean'), MODULE, '--claim', 'partial']
        for h in headlines:
            cmd.extend(['--headline', h])
        replay = parse_checker(run('kernel-replay', cmd))
        assert replay['verdict'] == 'pass' and replay['replay']['ok']
        assert not replay['newAxioms']
        assert all(h['ok'] for h in replay['headlines'])
        status['headline_count'] = len(headlines)
        status['replay'] = replay
        negative = parse_checker(run('full-prize-negative-control',
            [lake, 'env', 'lean', '--run', str(kit / 'Check.lean'), MODULE, '--claim', 'problem1'], expected=1))
        assert negative['verdict'] == 'fail' and not negative['verifiedTargets']
        status['full_prize_claim_rejected'] = True
        status['status'] = 'PARTIAL_RESULTS_KERNEL_REPLAYED_TARGET_OPEN'
    except Exception as exc:
        status['status'] = 'FAILED_OR_BLOCKED'
        status['error'] = str(exc)
    (destination / 'formal-status.json').write_text(json.dumps(status, indent=2) + '\n')
    print(json.dumps({k:v for k,v in status.items() if k != 'replay'}, indent=2))
    return int(status['status'] != 'PARTIAL_RESULTS_KERNEL_REPLAYED_TARGET_OPEN')


if __name__ == '__main__':
    raise SystemExit(main())
