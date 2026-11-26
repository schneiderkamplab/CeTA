#!/usr/bin/env python3
"""Schema inheritance plus old/new verdict preservation on every CPF3 example and compact fixture."""
import argparse,concurrent.futures,gzip,hashlib,json,subprocess,time
from pathlib import Path
from lxml import etree as E
p=argparse.ArgumentParser();p.add_argument('--before',type=Path,required=True);p.add_argument('--after',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();a.out.mkdir(parents=True,exist_ok=False)
root=Path(__file__).resolve().parents[1];schemas=[E.XMLSchema(E.parse(str(root/'xml'/f'cpf{v}.xsd'))) for v in [3,4]]
sha=lambda b:hashlib.sha256(b).hexdigest();cases=[];excluded=[];seen=set()
paths=list((root/'examples').glob('*.xml'))+list((root/'tests/certification/compact').glob('*/*.xml.gz'))
for path in sorted(paths):
 raw=path.read_bytes();raw=gzip.decompress(raw) if path.suffix=='.gz' else raw
 try:
  doc=E.fromstring(raw,E.XMLParser(huge_tree=True));version=doc.find('cpfVersion')
  if version is None or version.text not in ['3','3.0']:excluded.append(dict(path=str(path),reason='not CPF3'));continue
  if not schemas[0].validate(doc):excluded.append(dict(path=str(path),reason='not CPF3-schema valid',diagnostic=str(schemas[0].error_log.last_error)));continue
  assert schemas[1].validate(doc),str(path)
  digest=sha(raw)
  if digest in seen:continue
  seen.add(digest);version.text='4.0';cpf4=E.tostring(doc);assert schemas[1].validate(doc)
  f3=a.out/(digest+'-3.xml');f4=a.out/(digest+'-4.xml');f3.write_bytes(raw);f4.write_bytes(cpf4)
  external=[];external_hashes={}
  if doc.find('input') is None:
   stem=path.name.removesuffix('.cpf.xml')
   for option,suffix in [('--inputf','.input.xml'),('--propertyf','.property'),('--answerf','.answer')]:
    companion=path.with_name(stem+suffix)
    if companion.exists():external.extend([option,str(companion)]);external_hashes[str(companion)]=sha(companion.read_bytes())
  cases.append(dict(source=str(path),sha256=digest,cpf3=str(f3.resolve()),cpf4=str(f4.resolve()),external_arguments=external,external_hashes=external_hashes))
 except E.XMLSyntaxError as e:excluded.append(dict(path=str(path),reason='malformed XML',diagnostic=str(e)))
before=a.before.resolve();after=a.after.resolve();pins={str(x):sha(x.read_bytes()) for x in [before,after]}
(a.out/'manifest.json').write_text(json.dumps(dict(binaries=pins,cases=cases,excluded=excluded),indent=2)+'\n')
def run(row):
 runs=[]
 for label,binary,path in [('old3',before,row['cpf3']),('new3',after,row['cpf3']),('new4',after,row['cpf4'])]:
  for repeat in [1,2]:
   t=time.monotonic()
   try:
    q=subprocess.run([str(binary),*row['external_arguments'],path],capture_output=True,text=True,timeout=300)
    runs.append(dict(label=label,repeat=repeat,exit=q.returncode,stdout=q.stdout,stderr=q.stderr,seconds=time.monotonic()-t))
   except subprocess.TimeoutExpired:runs.append(dict(label=label,repeat=repeat,exit=None,stdout='TIMEOUT',seconds=time.monotonic()-t))
 expected=(runs[0]['exit'],runs[0]['stdout']);passed=expected[0] in [0,1] and all((r['exit'],r['stdout'])==expected for r in runs)
 return dict(**row,passed=passed,checks=runs)
rows=[]
with (a.out/'results.jsonl').open('x') as log,concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
 for r in pool.map(run,cases):rows.append(r);log.write(json.dumps(r)+'\n');log.flush()
assert {str(x):sha(x.read_bytes()) for x in [before,after]}==pins
summary=dict(total=len(rows),passed=sum(r['passed'] for r in rows),failed=[r['source'] for r in rows if not r['passed']],excluded=len(excluded),binaries=pins)
(a.out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary));assert all(r['passed'] for r in rows)
