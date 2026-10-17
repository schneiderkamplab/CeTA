#!/usr/bin/env python3
"""Fresh oracle-only replay, independent root audit, twice production check and HPC.
All paths and outputs are inside the isolated worktree. No live parent executables.
"""
import argparse,concurrent.futures,gzip,hashlib,json,math,os,pathlib,shutil,signal,subprocess,sys,time
from run_logged import memory_used
from root_audit import compare as audit_root
from oracle_audit import audit as audit_oracle
ROOT=pathlib.Path(__file__).resolve().parents[2];BUILD=ROOT/'target/consolidation-build';CORPUS=ROOT/'target/consolidation-corpus';SNAP=ROOT/'target/consolidation-snapshot'
sys.path.insert(0,str(pathlib.Path(__file__).parent/'vendor'))
import audit_trs_root_correspondence as trs
import audit_csr_root_correspondence as csr

def sha(p):
    with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def write(p,obj):p.write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')
def execute(cmd,cwd,env,prefix,timeout):
    if memory_used()>2*1024**4:raise RuntimeError('Memory launch ceiling exceeded; no new process launched')
    start=time.monotonic();timed_out=False
    with prefix.with_suffix('.stdout').open('wb') as out,prefix.with_suffix('.stderr').open('wb') as err:
        proc=subprocess.Popen(cmd,cwd=cwd,env=env,stdout=out,stderr=err,start_new_session=True)
        try:rc=proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out=True;os.killpg(proc.pid,signal.SIGKILL);rc=proc.wait()
    return dict(command=cmd,returncode=rc,timed_out=timed_out,elapsed_seconds=time.monotonic()-start)
def certified(result,prefix):return result['returncode']==0 and not result['timed_out'] and prefix.with_suffix('.stdout').read_text().strip()=='CERTIFIED'
def main():
    p=argparse.ArgumentParser();p.add_argument('--stage',required=True);p.add_argument('--jobs',type=int,default=16);p.add_argument('--smoke',action='store_true')
    p.add_argument('--checker',type=pathlib.Path,default=SNAP/'artifacts/production_checker')
    p.add_argument('--hpc-checker',type=pathlib.Path,default=BUILD/'bin/ceta-hpc-o2')
    p.add_argument('--checker-source-revision',default='17dbee4b822733cd25235a64178db2ccf590a10e')
    p.add_argument('--input-manifest',type=pathlib.Path,default=CORPUS/'input-manifest.json')
    p.add_argument('--input-directory',type=pathlib.Path,default=CORPUS/'frozen-inputs')
    p.add_argument('--checker-timeout',type=float,default=600)
    p.add_argument('--hpc-timeout',type=float,default=1200)
    p.add_argument('--oracle-time-scale-percent',type=int)
    a=p.parse_args()
    if a.jobs<1 or a.checker_timeout<=0 or a.hpc_timeout<=0:p.error('Jobs and timeouts must be positive')
    if a.oracle_time_scale_percent is not None and a.oracle_time_scale_percent<=0:p.error('Oracle time scale must be positive')
    if pathlib.Path(a.stage).name!=a.stage or a.stage in {'.','..'}:p.error('Stage must be a single directory name')
    rows=json.loads(a.input_manifest.read_text())['roots']
    if len({r['root'] for r in rows})!=len(rows) or len({r['id'] for r in rows})!=len(rows):raise ValueError('Duplicate root identities')
    if a.smoke:
        chosen={}
        for row in sorted(rows,key=lambda r:(r['prior_replay_seconds'],r['root'])):
            key=(row['category'],row['answer']);chosen.setdefault(key,row)
        rows=list(chosen.values())
    rows.sort(key=lambda r:(-r['prior_replay_seconds'],r['root']))
    stage=CORPUS/a.stage
    stage.mkdir(exist_ok=False)
    ferrum=BUILD/'cargo-producing/release/ferrum';checker=a.checker.resolve();hpc=a.hpc_checker.resolve();oracle=SNAP/'artifacts/current_oracle'
    audit=audit_oracle(oracle);write(stage/'oracle-audit.json',audit)
    if audit['forbidden'] or audit['unresolved_aliases'] or audit['sha256']!=sha(oracle):raise RuntimeError('Frozen oracle audit failed')
    profile=json.loads((SNAP/'manifests/srs-native-20261013/unified-final-v593/environment.json').read_text())
    if a.oracle_time_scale_percent is not None:profile['FERRUM_ORACLE_TIME_SCALE_PERCENT']=str(a.oracle_time_scale_percent)
    profile['FERRUM_LP_PYTHONPATH']=str(BUILD/'lp-tools');profile['CETA_CSR_BIN']=str(checker);profile['PYTHONDONTWRITEBYTECODE']='1'
    env={k:v for k,v in os.environ.items() if not k.startswith(('FERRUM_','CETA_','HPCTIX'))};env.update(profile)
    meta=dict(ferrum_sha256=sha(ferrum),checker_sha256=sha(checker),hpc_sha256=sha(hpc),oracle_sha256=sha(oracle),source_revision=json.loads((ROOT/'docs/consolidation/snapshot.json').read_text())['latest_producing_source_revision'],profile=profile,roots=[dict(root=r['root'],answer=r['answer'],input_sha256=r.get('input_sha256')) for r in rows],hpc_source_revision=a.checker_source_revision,runner_sha256=sha(pathlib.Path(__file__)),root_ceiling_policy='max(2880 seconds, 1.2 * retained measured runtime + 60 seconds)',checker_ceiling_seconds=a.checker_timeout,hpc_ceiling_seconds=a.hpc_timeout,input_manifest_sha256=sha(a.input_manifest))
    for entry,row in zip(meta['roots'],rows):entry['oracle_time_scale_percent']=int(row.get('oracle_time_scale_percent',profile['FERRUM_ORACLE_TIME_SCALE_PERCENT']))
    write(stage/'metadata.json',meta)
    def one(row):
        run=stage/row['id'];run.mkdir();result=dict(id=row['id'],root=row['root'],expected_answer=row['answer'],category=row['category'],eligible=False)
        try:
            src=a.input_directory.resolve()/row['root']
            if not src.resolve().is_relative_to(a.input_directory.resolve()):raise ValueError('Root escapes input directory')
            if not src.is_file():raise ValueError('Frozen input unavailable')
            inp=stage/'inputs'/row['root'];inp.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,inp)
            if sha(inp)!=row['input_sha256']:raise ValueError('Frozen input hash changed')
            proof=run/'proof.cpf.xml';events=run/'processor-events.jsonl';ceiling=max(2880,math.ceil(row['prior_replay_seconds']*1.2+60))
            cmd=[str(ferrum),'prove',str(inp),'--cpf',str(proof),'--cpf-mode','auto','--strategy',f'timeout({ceiling}s,fail)','--utility-guidance-manifest',str(oracle),'--no-top-level-llm','--processor-events',str(events)]
            localenv=env|{'FERRUM_PROGRESS_LOG':str(run/'progress.jsonl')}
            scale=int(row.get('oracle_time_scale_percent',profile['FERRUM_ORACLE_TIME_SCALE_PERCENT']))
            if scale<=0:raise ValueError('Invalid per-root search budget')
            localenv['FERRUM_ORACLE_TIME_SCALE_PERCENT']=str(scale);result['oracle_time_scale_percent']=scale
            result['replay']=execute(cmd,run,localenv,run/'ferrum',ceiling+30)
            if result['replay']['returncode']!=0 or not proof.exists():raise ValueError('Fresh replay produced no successful certificate')
            result['input_sha256']=sha(inp);result['cpf_sha256']=sha(proof)
            result['correspondence']=audit_root(inp.read_text(),proof,row['answer'],row['category'])
            result['checks']=[]
            for i in [1,2]:
                prefix=run/f'production-{i}';c=execute([str(checker),str(proof)],run,env,prefix,a.checker_timeout);c['certified']=certified(c,prefix);result['checks'].append(c)
            hp=run/'hpc';henv=env|{'HPCTIXFILE':str(run/'coverage.tix')}
            c=execute([str(hpc),str(proof)],run,henv,hp,a.hpc_timeout);c['certified']=certified(c,hp);result['hpc']=c
            if not all(c['certified'] for c in result['checks']) or not c['certified']:raise ValueError('Production/HPC acceptance gate failed')
            cov=execute([str(BUILD/'bin/export-tix'),str(run/'coverage.tix')],run,env,run/'coverage-export',60)
            if cov['returncode']!=0:raise ValueError('HPC coverage export failed')
            with (run/'coverage-export.stdout').open('rb') as f,(run/'coverage.tsv.gz').open('wb') as out,gzip.GzipFile(filename='',mode='wb',fileobj=out,mtime=0) as z:shutil.copyfileobj(f,z)
            for name in ['coverage-export.stdout','coverage.tix']:(run/name).unlink()
            result['coverage_sha256']=sha(run/'coverage.tsv.gz');result['eligible']=True
        except Exception as e:result['error']=type(e).__name__+': '+str(e)
        write(run/'result.json',result);return result
    results=[];start=time.monotonic()
    with (stage/'results.jsonl').open('w') as log,concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs) as pool:
        fs=[pool.submit(one,r) for r in rows]
        for f in concurrent.futures.as_completed(fs):
            r=f.result();results.append(r);log.write(json.dumps(r,sort_keys=True)+'\n');log.flush()
            if len(results)%25==0 or not r['eligible']:print(json.dumps(dict(done=len(results),total=len(rows),eligible=sum(r['eligible'] for r in results),last=r['root'],error=r.get('error'))),flush=True)
    summary=dict(roots=len(rows),eligible=sum(r['eligible'] for r in results),losses=[dict(root=r['root'],answer=r['expected_answer'],error=r.get('error')) for r in results if not r['eligible']],elapsed_seconds=time.monotonic()-start)
    write(stage/'summary.json',summary);print(json.dumps(summary));raise SystemExit(bool(summary['losses']))
if __name__=='__main__':main()
