#!/usr/bin/env python3
"""Repeat instrumentation gate without discarding earlier failures or fresh replay provenance."""
import argparse,concurrent.futures,gzip,json,os,pathlib,shutil,time
from replay import ROOT,BUILD,CORPUS,execute,certified,sha,write

def main():
 p=argparse.ArgumentParser();p.add_argument('--source',required=True);p.add_argument('--stage',required=True);p.add_argument('--checker',type=pathlib.Path,required=True);p.add_argument('--jobs',type=int,default=16);p.add_argument('--follow',action='store_true');a=p.parse_args()
 source=CORPUS/a.source;stage=CORPUS/a.stage;stage.mkdir(exist_ok=False);checker=a.checker.resolve()
 prior=json.loads((source/'metadata.json').read_text());meta=prior|dict(hpc_sha256=sha(checker),prior_stage=a.source,prior_hpc_sha256=prior['hpc_sha256'],hpc_repeat_reason='Resolve unoptimized instrumentation timeouts with separately compiled O2 instrumentation.',hpc_ceiling_seconds=1200,runner_sha256=sha(pathlib.Path(__file__)))
 write(stage/'metadata.json',meta);env={k:v for k,v in os.environ.items() if not k.startswith('HPCTIX')};results=[];seen=set();pending={};start=time.monotonic()
 def one(row):
  run=stage/row['id'];run.mkdir();r=row.copy();r['prior_hpc']=r.pop('hpc',None);r['prior_gate_error']=r.pop('error',None);r['eligible']=False
  try:
   if len(r.get('checks',[]))!=2 or not all(x['certified'] for x in r['checks']) or not r.get('correspondence'):raise ValueError('Prior production/input audit gates did not pass')
   proof=source/row['id']/'proof.cpf.xml'
   if sha(proof)!=r['cpf_sha256']:raise ValueError('Proof hash changed since prior certification')
   (run/'proof.cpf.xml').symlink_to(proof)
   c=execute([str(checker),str(proof)],run,env|{'HPCTIXFILE':str(run/'coverage.tix')},run/'hpc',1200);c['certified']=certified(c,run/'hpc');r['hpc']=c
   if not c['certified']:raise ValueError('Optimized HPC acceptance gate failed')
   c=execute([str(BUILD/'bin/export-tix'),str(run/'coverage.tix')],run,env,run/'coverage-export',60)
   if c['returncode']!=0:raise ValueError('Coverage export failed')
   with (run/'coverage-export.stdout').open('rb') as f,(run/'coverage.tsv.gz').open('wb') as out,gzip.GzipFile(fileobj=out,mode='wb',filename='',mtime=0) as z:shutil.copyfileobj(f,z)
   (run/'coverage-export.stdout').unlink();(run/'coverage.tix').unlink();r['coverage_sha256']=sha(run/'coverage.tsv.gz');r['eligible']=True
  except Exception as e:r['error']=type(e).__name__+': '+str(e)
  write(run/'result.json',r);return r
 with (stage/'results.jsonl').open('w') as log,concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs) as pool:
  while True:
   for path in sorted(source.glob('*/result.json')):
    if path.parent.name in seen:continue
    try:row=json.loads(path.read_text())
    except json.JSONDecodeError:continue
    seen.add(row['id']);pending[pool.submit(one,row)]=row['id']
   done,_=concurrent.futures.wait(pending,timeout=5,return_when=concurrent.futures.FIRST_COMPLETED) if pending else (set(),set())
   for f in done:
    pending.pop(f);r=f.result();results.append(r);log.write(json.dumps(r,sort_keys=True)+'\n');log.flush()
    if len(results)%25==0 or not r['eligible']:print(json.dumps(dict(done=len(results),eligible=sum(x['eligible'] for x in results),last=r['root'],error=r.get('error'))),flush=True)
   complete=(source/'summary.json').exists()
   if not pending and (complete or not a.follow):break
   if not pending:time.sleep(5)
 expected=len(prior['roots']);summary=dict(roots=expected,checked=len(results),eligible=sum(r['eligible'] for r in results),losses=[dict(root=r['root'],answer=r['expected_answer'],error=r.get('error')) for r in results if not r['eligible']],elapsed_seconds=time.monotonic()-start,prior_failures_preserved=True)
 if len(results)!=expected:summary['losses'].append(dict(error='Incomplete root set',expected=expected,observed=len(results)))
 write(stage/'summary.json',summary);print(json.dumps(summary));raise SystemExit(bool(summary['losses']))
if __name__=='__main__':main()
