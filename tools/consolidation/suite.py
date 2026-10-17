#!/usr/bin/env python3
"""Run committed proof artifacts with strict hash, root, acceptance and rejection gates."""
import argparse,gzip,json,os,pathlib,re,shutil,statistics,sys,time
from replay import execute,certified,sha,write
sys.path.insert(0,str(pathlib.Path(__file__).parent/'vendor'))
import audit_trs_root_correspondence as trs
import audit_csr_root_correspondence as csr

def inside(base,name):
 p=(base/name).resolve()
 if not p.is_relative_to(base.resolve()):raise ValueError('Artifact escapes suite directory')
 return p

def main():
 p=argparse.ArgumentParser();p.add_argument('--manifest',type=pathlib.Path,required=True);p.add_argument('--checker',type=pathlib.Path,required=True);p.add_argument('--hpc-checker',type=pathlib.Path);p.add_argument('--export-tix',type=pathlib.Path);p.add_argument('--output',type=pathlib.Path,required=True);a=p.parse_args()
 if bool(a.hpc_checker)!=bool(a.export_tix):raise SystemExit('HPC checker and exporter must be supplied together')
 base=a.manifest.resolve().parent;manifest=json.loads(a.manifest.read_text());output=a.output.resolve();output.mkdir(parents=True,exist_ok=False);checker=a.checker.resolve();env=dict(os.environ);results=[];observed=set();denpath=base/'coverage-denominator.json'
 if sha(denpath)!=manifest['coverage_denominator_sha256']:raise ValueError('Coverage denominator changed')
 denominator=json.loads(denpath.read_text());modules=denominator['modules'];source_ids=denominator['structural_features']
 from coverage import inspect
 reg=json.loads((base/'processor-registry.json').read_text())
 for row in manifest['positives']:
  run=output/row['id'];run.mkdir();r=dict(id=row['id'],kind='positive',passed=False)
  try:
   cert=inside(base,row['certificate']);inp=inside(base,row['input'])
   if sha(cert)!=row['compressed_sha256'] or sha(inp)!=row['input_sha256']:raise ValueError('Artifact hash mismatch')
   proof=run/'proof.cpf.xml'
   with gzip.open(cert,'rb') as src,proof.open('wb') as dst:shutil.copyfileobj(src,dst)
   if sha(proof)!=row['cpf_sha256']:raise ValueError('Uncompressed proof hash mismatch')
   if row['category']=='TRS_Contextsensitive':csr.compare(inp.read_text(),proof.read_text(),row['answer'])
   else:trs.compare(inp.read_text(),trs.root_metadata(proof),row['answer'],row['category'])
   r['checks']=[];timeout=max(60,1.5*max(x['elapsed_seconds'] for x in row['reference_checks'])+30)
   for i in [1,2]:
    prefix=run/f'check-{i}';c=execute([str(checker),str(proof)],run,env,prefix,timeout);c['certified']=certified(c,prefix);r['checks'].append(c)
   if not all(x['certified'] for x in r['checks']):raise ValueError('Positive acceptance failed')
   reference=statistics.mean(x['elapsed_seconds'] for x in row['reference_checks']);actual=statistics.mean(x['elapsed_seconds'] for x in r['checks']);r['slowdown_candidate']=actual>reference*1.2;r['reference_mean_seconds']=reference
   structural=inspect(proof,row['category'],reg)
   if structural['unknown_proof_tags']:raise ValueError('Unknown proof nodes: '+str(structural['unknown_proof_tags']))
   for feature in structural['features']+['root-kind|'+row['category']+'|'+row['answer']]:
    if feature not in source_ids:raise ValueError('Unmapped structural obligation '+feature)
    observed.add(source_ids[feature])
   if a.hpc_checker:
    prefix=run/'hpc';c=execute([str(a.hpc_checker.resolve()),str(proof)],run,env|{'HPCTIXFILE':str(run/'coverage.tix')},prefix,max(120,1.5*row['reference_hpc']['elapsed_seconds']+30));c['certified']=certified(c,prefix);r['hpc']=c
    if not c['certified']:raise ValueError('HPC/production agreement failed')
    c=execute([str(a.export_tix.resolve()),str(run/'coverage.tix')],run,env,run/'coverage',60)
    if c['returncode']!=0:raise ValueError('HPC export failed')
    for line in (run/'coverage.stdout').read_text().splitlines():
     name,digest,count,ticks=line.split('\t');m=modules.get(name)
     if m is None or m['hash']!=digest or m['count']!=int(count):raise ValueError('Instrumentation changed; explicit coverage mapping required for '+name)
     observed.update(m['offset']+int(i) for i in ticks.split(',') if i)
   r['passed']=True
  except Exception as e:r['error']=type(e).__name__+': '+str(e)
  results.append(r);write(run/'result.json',r)
 for row in manifest['negatives']:
  run=output/row['id'];run.mkdir();r=dict(id=row['id'],kind='negative',passed=False)
  try:
   cert=inside(base,row['certificate']);proof=run/'proof.cpf.xml'
   if sha(cert)!=row['compressed_sha256']:raise ValueError('Negative compressed hash mismatch')
   with gzip.open(cert,'rb') as src,proof.open('wb') as dst:shutil.copyfileobj(src,dst)
   if sha(proof)!=row['mutation_sha256']:raise ValueError('Negative proof hash mismatch')
   import xml.etree.ElementTree as ET
   ET.parse(proof);r['checks']=[]
   for i in [1,2]:
    prefix=run/f'check-{i}';c=execute([str(checker),str(proof)],run,env,prefix,120);text=prefix.with_suffix('.stdout').read_text()+prefix.with_suffix('.stderr').read_text();c['semantic_rejection']=c['returncode']==1 and not c['timed_out'] and text.startswith('REJECTED') and bool(re.search(row['expected_diagnostic_regex'],text,re.S|re.I));r['checks'].append(c)
   if not all(x['semantic_rejection'] for x in r['checks']):raise ValueError('Intended semantic rejection not observed')
   r['passed']=True
  except Exception as e:r['error']=type(e).__name__+': '+str(e)
  results.append(r);write(run/'result.json',r)
 required=set(denominator['required_obligations']);missing=sorted(required-observed) if a.hpc_checker else None
 summary=dict(scope=manifest['scope'],checker_sha256=sha(checker),hpc_checker_sha256=sha(a.hpc_checker) if a.hpc_checker else None,results=results,missing_coverage=missing,acceptance_passed=all(r['passed'] for r in results),coverage_passed=not missing if missing is not None else None,slowdown_candidates=[r['id'] for r in results if r.get('slowdown_candidate')],performance_status='Controlled reference repeats required for listed slowdown candidates; timings alone do not establish a regression.')
 write(output/'summary.json',summary);print(json.dumps({k:v for k,v in summary.items() if k!='results'}));raise SystemExit(not summary['acceptance_passed'] or bool(missing))
if __name__=='__main__':main()
