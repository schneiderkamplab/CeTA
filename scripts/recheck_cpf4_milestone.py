#!/usr/bin/env python3
"""Recheck every retained first-order certificate; no search or coverage inference."""
import argparse,concurrent.futures,hashlib,json,os,subprocess,time
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--campaign',type=Path,required=True);p.add_argument('--checker',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--workers',type=int,default=16);p.add_argument('--timeout',type=int,default=600);a=p.parse_args()
assert 1<=a.workers<=32
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
a.out.mkdir(parents=True,exist_ok=True)
checker=a.checker.resolve();identity=sha(checker)
baseline=json.loads((a.campaign/'results.json').read_text());required={r['root']:r for r in baseline if r['certified']}
jobs=[]
for f in sorted(a.campaign.glob('*/*/result.json')):
 r=json.loads(f.read_text())
 if not r.get('certified'):continue
 old=required[r['root']];assert r['certificate_sha256']==old['certificate_sha256']
 command_file=f.parent/'check-0-command.json'
 if command_file.exists():
  cmd=json.loads(command_file.read_text());proof=Path(cmd[-1])
 else:
  from lxml import etree as E
  candidates=[p for p in f.parent.glob('proof*') if p.is_file() and sha(p)==old['certificate_sha256']]
  assert len(candidates)==1,(str(f),candidates)
  proof=candidates[0].resolve();doc=E.parse(str(proof),E.XMLParser(huge_tree=True));tag=doc.getroot().find('proof')[0].tag
  category='conditional-erasure' if tag=='conditionalErasureProof' else ('conditional' if tag in ['ConditionalCycle','ConditionalLoop'] else 'cpf')
  flags=['--ordinary'] if category=='conditional' and r['category']=='TRS_Conditional_Termination' else []
  cmd=[str(checker),'--category',category,*flags,str(proof)]
 assert sha(proof)==old['certificate_sha256']
 jobs.append(dict(root=r['root'],category=r['category'],certificate=str(proof),certificate_sha256=sha(proof),command=[str(checker),*cmd[1:]],source_sha256=r['source_sha256']))
assert len(jobs)==len(required) and {j['root'] for j in jobs}==set(required)
pins=dict(checker=str(checker),checker_sha256=identity,baseline_sha256=sha(a.campaign/'results.json'),workers=a.workers,timeout=a.timeout,passes=2,jobs=jobs)
manifest=a.out/'manifest.json'
if manifest.exists():assert json.loads(manifest.read_text())==pins
else:manifest.write_text(json.dumps(pins,indent=2)+'\n')
journal=a.out/'results.jsonl';done={}
if journal.exists():
 for line in journal.read_text().splitlines():
  r=json.loads(line);assert r['root'] not in done;done[r['root']]=r

def run(j):
 r=dict(j);checks=[]
 try:
  assert sha(Path(j['certificate']))==j['certificate_sha256']
  for repeat in [1,2]:
   start=time.monotonic()
   q=subprocess.run(j['command'],capture_output=True,text=True,timeout=a.timeout)
   checks.append(dict(repeat=repeat,exit=q.returncode,stdout=q.stdout,stderr=q.stderr,seconds=time.monotonic()-start,accepted=q.returncode==0 and q.stdout.strip()=='CERTIFIED'))
  r['passed']=all(c['accepted'] for c in checks)
 except Exception as e:r.update(passed=False,error=repr(e))
 r['checks']=checks;return r
with journal.open('a') as f,concurrent.futures.ThreadPoolExecutor(max_workers=a.workers) as pool:
 for r in pool.map(run,[j for j in jobs if j['root'] not in done]):
  done[r['root']]=r;f.write(json.dumps(r)+'\n');f.flush()
  if len(done)%100==0:print(len(done),'/',len(jobs),flush=True)
assert sha(checker)==identity
summary=dict(required=len(required),completed=len(done),passed=sum(r['passed'] for r in done.values()),failures=[r['root'] for r in done.values() if not r['passed']],checker_sha256=identity,unresolved_inputs=len(baseline)-len(required),scope='Retained first-order CPF4 corpus; not an exhaustive CPF3/4 constructor audit')
(a.out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary));assert summary['passed']==len(required)
