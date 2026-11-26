#!/usr/bin/env python3
"""Check all twenty CPF5 higher-order roots and nested semantic regressions."""
import argparse, concurrent.futures, copy, gzip, hashlib, json, subprocess, time
from pathlib import Path
from lxml import etree as E
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--checker',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
p.add_argument('--workers',type=int,default=8)
a=p.parse_args();assert 1<=a.workers<=32
a.output.mkdir(parents=True,exist_ok=False)
root=Path(__file__).resolve().parents[2];fixtures=root/'tests/unified/cpf5-higher-order-regressions'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
checker=a.checker.resolve();identity=sha(checker)
manifest=json.loads((fixtures/'manifest.json').read_text());jobs=[];examples={}
schemas={v:E.XMLSchema(E.parse(str(root/f'xml/cpf{v}.xsd'))) for v in [5,6]}
for row in manifest['cases']:
 data=gzip.decompress((fixtures/row['file']).read_bytes());assert hashlib.sha256(data).hexdigest()==row['sha256']
 doc=E.fromstring(data)
 if row['expected']:
  schemas[int(doc.findtext('cpfVersion').split('.')[0])].assertValid(doc)
  if doc.findtext('cpfVersion')=='5.0':examples.setdefault(row['constructor'],doc)
 jobs.append(dict(row,data=data))
assert set(examples)==set(manifest['constructors'])
for constructor,doc in examples.items():
 for mutation in ['old-version','future-version','wrong-answer','wrong-property']:
  bad=copy.deepcopy(doc)
  if mutation=='old-version':bad.find('cpfVersion').text='4.0'
  elif mutation=='future-version':bad.find('cpfVersion').text='7.0'
  elif mutation=='wrong-answer':bad.find('answer')[0].tag='no' if doc.find('answer/yes') is not None else 'yes'
  else:bad.find('property')[0].tag='confluence'
  jobs.append(dict(case=constructor+'/'+mutation,constructor=constructor,expected=False,data=E.tostring(bad)))
for i,j in enumerate(jobs):
 path=a.output/f'{i:04d}.xml';path.write_bytes(j.pop('data'));j.update(path=str(path.resolve()),sha256=sha(path))
(a.output/'manifest.json').write_text(json.dumps(dict(checker_sha256=identity,fixture_manifest_sha256=sha(fixtures/'manifest.json'),jobs=jobs),indent=2)+'\n')
def run(j):
 category='higher-order-delegation' if j['constructor'].startswith('ho-ceta-') else 'higher-order';checks=[]
 for repeat in [1,2]:
  command=[str(checker),'--category',category,j['path']];start=time.monotonic()
  try:
   q=subprocess.run(command,capture_output=True,text=True,timeout=300)
   accepted=q.returncode==0 and q.stdout.startswith('CERTIFIED')
   checks.append(dict(command=command,repeat=repeat,seconds=time.monotonic()-start,exit=q.returncode,stdout=q.stdout,stderr=q.stderr,passed=accepted==j['expected']))
  except subprocess.TimeoutExpired:checks.append(dict(command=command,repeat=repeat,passed=False,error='timeout'))
 return dict(**j,checks=checks,passed=all(c['passed'] for c in checks))
with concurrent.futures.ThreadPoolExecutor(max_workers=a.workers) as pool:rows=list(pool.map(run,jobs))
result=dict(checker_sha256=identity,checker_stable=sha(checker)==identity,passed=all(r['passed'] for r in rows),cases=len(rows),constructors=len(examples),results=rows)
(a.output/'validation.json').write_text(json.dumps(result,indent=2)+'\n');print(result['cases'],result['constructors'],result['passed']);assert result['passed'] and result['checker_stable']
