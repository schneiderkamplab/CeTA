#!/usr/bin/env python3
"""Real-source CPF6 constructor and malformed-envelope checking regressions."""
import argparse,copy,gzip,hashlib,json,subprocess
from pathlib import Path
from lxml import etree as E
p=argparse.ArgumentParser();p.add_argument('--inventory',type=Path,help='Optional complete retained inventory; otherwise use bundled regression fixtures');p.add_argument('--ceta',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
root=Path(__file__).resolve().parents[2];schema=E.XMLSchema(E.parse(str(root/'xml/cpf6.xsd')))
a.out.mkdir(parents=True,exist_ok=False);samples={}
if a.inventory:
 inventory=json.loads(a.inventory.read_text())
else:
 bundle=root/'tests/unified/cpf6-source-forms';inventory=[]
 for fixture in json.loads((bundle/'manifest.json').read_text())['fixtures']:
  content=gzip.decompress((bundle/fixture['file']).read_bytes());assert hashlib.sha256(content).hexdigest()==fixture['sha256']
  path=a.out/fixture['file'].removesuffix('.gz');path.write_bytes(content)
  inventory.append(dict(fixture,cpf=str(path),disposition='converted'))
for r in inventory:
 if r['disposition']!='converted':continue
 tag=r['constructor']
 if tag not in samples or Path(r['cpf']).stat().st_size<Path(samples[tag]['cpf']).stat().st_size:samples[tag]=r
rows=[]
for index,(tag,r) in enumerate(sorted(samples.items())):
 d=E.parse(r['cpf'],E.XMLParser(huge_tree=True)).getroot();schema.assertValid(d)
 cases=[('positive',d,True)]
 for version in ['3.0','4.0','5.0','7.0']:
  x=copy.deepcopy(d);x.find('cpfVersion').text=version;cases.append(('version-'+version,x,False))
 x=copy.deepcopy(d);x.find('answer')[0].tag='no' if r['answer'].lower()=='yes' else 'yes';cases.append(('polarity',x,False))
 x=copy.deepcopy(d);x.find('property')[0].tag='confluence';cases.append(('property',x,False))
 x=copy.deepcopy(d);x.find('proof')[0].append(E.Element('unexpected'));cases.append(('extra-evidence',x,False))
 x=copy.deepcopy(d);x.find('proof')[0].clear();cases.append(('missing-evidence',x,False))
 x=copy.deepcopy(d);x.find('input').append(copy.deepcopy(x.find('input')[0]));cases.append(('duplicate-input',x,False))
 if r['category']=='Prolog':
  x=copy.deepcopy(d);x.find('input/prologInput/executionProfile').text='unsupported-profile';cases.append(('profile',x,False))
 for label,doc,expected in cases:
  path=a.out/f'{index:03d}-{label}.xml';path.write_bytes(E.tostring(doc))
  q=subprocess.run([str(a.ceta.resolve()),'--category','prolog' if r['category']=='Prolog' else 'lp',str(path.resolve())],capture_output=True,text=True,timeout=300)
  accepted=q.returncode==0 and q.stdout.startswith('CERTIFIED')
  row=dict(constructor=tag,case=label,expected=expected,accepted=accepted,exit=q.returncode,stdout=q.stdout,stderr=q.stderr,sha256=hashlib.sha256(path.read_bytes()).hexdigest());rows.append(row)
  (a.out/'results.json').write_text(json.dumps(rows,indent=2)+'\n')
  assert accepted==expected,row
summary=dict(passed=True,constructors=len(samples),cases=len(rows),checker_sha256=hashlib.sha256(a.ceta.read_bytes()).hexdigest())
(a.out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(summary)
