#!/usr/bin/env python3
"""Build and replay own declarations; demand rejection as a full solution."""
import argparse,hashlib,json,os,pathlib,re,shutil,subprocess
ROOT=pathlib.Path(__file__).resolve().parent
PIN='3eca23c0a9fa6b153313655e6d51835406c2d06e'

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--kit',required=True)
    ap.add_argument('--output-dir',default=str(ROOT))
    args=ap.parse_args();kit=pathlib.Path(args.kit).resolve();core=kit/'lean'
    output=pathlib.Path(args.output_dir).resolve();output.mkdir(parents=True,exist_ok=True)
    out={'official_kit_commit':PIN,'problem1_solved':False,
         'uniform_escape_proved':False,'linear_escape_proved':False,'steps':[]}
    def run(label,cmd,cwd=core,expected=0):
        p=subprocess.run(cmd,cwd=cwd,text=True,stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT,timeout=180)
        (output/(label+'.log')).write_text(p.stdout)
        out['steps'].append({'label':label,'exit_code':p.returncode})
        assert p.returncode==expected,(label,p.returncode,p.stdout[-1000:])
        return p.stdout
    def result(text):
        js=[json.loads(l) for l in text.splitlines() if l.startswith('{')]
        assert len(js)==1
        return js[0]
    try:
        assert run('kit-head',['git','rev-parse','HEAD'],kit).strip()==PIN
        assert run('kit-tracked-diff',['git','diff','--name-only','HEAD'],kit).strip()==''
        out['lean_version']=run('lean-version',['lean','--version']).strip()
        run('core-build',['lake','build','Ruliology.CellularAutomata.Rule30Realization',
                          'Ruliology.CellularAutomata.Rule30Prize'])
        out['modules']=[]
        for name in ['Rule30SearchV2','Rule30AttemptV3']:
            source=(ROOT/(name+'.lean')).read_text()
            shutil.copyfile(ROOT/(name+'.lean'),core/(name+'.lean'))
            run('compile-'+name,['lake','env','lean','-o',name+'.olean',name+'.lean'])
            heads=[name+'.'+n for n in re.findall(r'^theorem (\w+)',source,re.M)]
            old=os.environ.get('LEAN_PATH','');os.environ['LEAN_PATH']=str(core)+(os.pathsep+old if old else '')
            cmd=['lake','env','lean','--run',str(kit/'Check.lean'),name,'--claim','partial']
            for h in heads:cmd+=['--headline',h]
            replay=result(run('kernel-'+name,cmd))
            assert replay['verdict']=='pass' and replay['replay']['ok']
            assert all(h['ok'] for h in replay['headlines'])
            out['modules'].append({'module':name,'theorem_count':len(heads),
                'source_sha256':hashlib.sha256(source.encode()).hexdigest(),'replay':replay})
        neg=result(run('full-goal-rejection',['lake','env','lean','--run',str(kit/'Check.lean'),
            'Rule30AttemptV3','--claim','problem1'],expected=1))
        assert neg['verdict']=='fail' and neg['verifiedTargets']==[]
        out['full_goal_rejected']=True
        out['status']='PARTIAL_AND_CONDITIONAL_LEMMAS_KERNEL_REPLAYED'
    except Exception as e:
        out['status']='FAILED_OR_BLOCKED';out['error']=str(e)
    (output/'formal-status.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='modules'},indent=2))
    return 0 if out['status']=='PARTIAL_AND_CONDITIONAL_LEMMAS_KERNEL_REPLAYED' else 1

if __name__=='__main__':raise SystemExit(main())
