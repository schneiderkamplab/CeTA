#!/usr/bin/env python3
"""Certification only; one unified binary, frozen jobs, exact hashes and verdicts."""
import argparse,collections,concurrent.futures,gzip,hashlib,json,shutil,subprocess,tempfile,time,zipfile,tarfile
from pathlib import Path

def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def memory_ok():
 m={r.split(':')[0]:int(r.split()[1]) for r in Path('/proc/meminfo').read_text().splitlines()}
 return (m['MemTotal']-m['MemAvailable'])*1024<2*1024**4

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--binary',type=Path,required=True);p.add_argument('--provenance',type=Path,required=True);p.add_argument('--baseline-results',type=Path,required=True);p.add_argument('--archive',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--workers',type=int,default=32);p.add_argument('--child-spec',type=Path,default=Path(__file__).parent/'compact-children.json');a=p.parse_args()
 source_binary=a.binary.resolve();digest=sha(source_binary)
 cache=a.output.parent/'checkers';cache.mkdir(exist_ok=True);binary=cache/digest
 if not binary.exists():
  with tempfile.NamedTemporaryFile(dir=cache,delete=False) as f:temporary=Path(f.name)
  shutil.copy2(source_binary,temporary);assert sha(temporary)==digest;temporary.replace(binary)
 assert sha(binary)==digest
 meta=json.loads(a.provenance.read_text());assert sha(a.archive)==meta['archive_sha256']
 baseline=json.loads(gzip.decompress(a.baseline_results.read_bytes()));previous={r['root']:r for r in baseline['results']}
 assert set(previous)=={r['root'] for r in meta['jobs']}
 child_spec=json.loads((Path(__file__).parent/'children.json').read_text())
 assert child_spec['children']==meta['child_sha256']
 compact_spec=json.loads(a.child_spec.read_text())
 assert compact_spec['original_archive_sha256']==child_spec['archive_sha256']
 assert set(compact_spec['children'])==set(child_spec['children'])
 child_archive=a.child_spec.with_suffix('.tar.gz');assert sha(child_archive)==compact_spec['archive_sha256']
 children=a.output.parent/(a.child_spec.stem+'-'+compact_spec['archive_sha256'][:12]);children.mkdir(exist_ok=True)
 with tarfile.open(child_archive,'r:gz') as bundle:
  for member in bundle.getmembers():
   assert member.isfile() and member.name in child_spec['children'] and Path(member.name).name==member.name
   child=children/member.name
   if not child.exists() or sha(child)!=compact_spec['children'][member.name]:child.write_bytes(bundle.extractfile(member).read())
   assert sha(child)==compact_spec['children'][member.name]
 mapping={}
 for original,entry in meta['binaries'].items():
  name=Path(original).name
  category={'ceta-relative':'cpf','ceta-cycle':'cycle','ceta-conditional':'conditional','ceta-conditional-erasure':'conditional-erasure','ceta-lp-seg':'lp','ceta-higher-order':'higher-order','ceta-ho-delegation':'higher-order-delegation'}.get(name)
  if category:mapping[entry['sha256']]=category
 def check(row):
  category=mapping[Path(row['binary']).name];start=time.monotonic()
  old=previous[row['root']];assert old['status']=='accepted'
  assert all(old[k]==row[k] for k in ['input_sha256','answer'])
  assert old['proof_sha256']==row.get('original_proof_sha256',row['proof_sha256'])
  expected=old['checks'][0]['verdict']
  result={k:row[k] for k in ['root','answer','input_sha256','proof_sha256']};result['category']=category
  if 'original_proof_sha256' in row:result['original_proof_sha256']=row['original_proof_sha256']
  try:
   with zipfile.ZipFile(a.archive) as z:inp=z.read(row['input']);proof=z.read(row['proof'])
   if row['proof'].endswith('.gz'):proof=gzip.decompress(proof)
   assert hashlib.sha256(inp).hexdigest()==row['input_sha256'] and hashlib.sha256(proof).hexdigest()==row['proof_sha256']
   with tempfile.TemporaryDirectory(prefix='ceta-unified-') as d:
    f=Path(d)/'proof';f.write_bytes(proof);cmd=[str(binary),'--category',category,*row['flags'],str(f)]
    if row['child']:
     child=children/Path(row['child']).name;assert sha(child)==compact_spec['children'][child.name];cmd.append(str(child))
     result.update(child_original_sha256=meta['child_sha256'][child.name],child_compact_sha256=compact_spec['children'][child.name])
    result['preparation_seconds']=time.monotonic()-start;t=time.monotonic();r=subprocess.run(cmd,capture_output=True,text=True)
    result.update(returncode=r.returncode,stdout=r.stdout,stderr=r.stderr,native_seconds=time.monotonic()-t,status='accepted' if r.returncode==0 and r.stdout.strip()==expected else 'failed')
  except Exception as e:result.update(status='error',reason=repr(e))
  result['seconds']=time.monotonic()-start;return result
 started=time.monotonic();results=[];todo=iter(meta['jobs']);pending=set();exhausted=False;last=started
 with concurrent.futures.ThreadPoolExecutor(max_workers=a.workers) as pool,a.output.with_suffix('.progress.jsonl').open('w') as log:
  while pending or not exhausted:
   while not exhausted and len(pending)<a.workers and memory_ok():
    row=next(todo,None)
    if row is None:exhausted=True;break
    pending.add(pool.submit(check,row))
   if not pending and not exhausted:time.sleep(5);continue
   done,pending=concurrent.futures.wait(pending,timeout=5,return_when=concurrent.futures.FIRST_COMPLETED) if pending else (set(),set())
   for task in done:
    r=task.result();results.append(r);log.write(json.dumps(r)+'\n');log.flush()
   if time.monotonic()-last>=30:
    print(len(results),'/',len(meta['jobs']),dict(collections.Counter(r['status'] for r in results)),round(time.monotonic()-started,1),flush=True);last=time.monotonic()
 assert sha(binary)==digest
 assert len(results)==len(meta['jobs']) and {r['root'] for r in results}=={r['root'] for r in meta['jobs']}
 report=dict(binary_sha256=digest,provenance_sha256=sha(a.provenance),baseline_results_sha256=sha(a.baseline_results),archive_sha256=meta['archive_sha256'],child_archive_sha256=compact_spec['archive_sha256'],workers=a.workers,checks_per_root=1,seconds=time.monotonic()-started,counts=dict(collections.Counter(r['status'] for r in results)),results=results)
 a.output.write_bytes(gzip.compress(json.dumps(report).encode(),mtime=0));print(report['counts'],report['seconds'],flush=True);assert all(r['status']=='accepted' for r in results)
if __name__=='__main__':main()
