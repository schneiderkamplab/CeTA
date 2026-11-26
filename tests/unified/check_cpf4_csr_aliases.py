#!/usr/bin/env python3
"""Check canonical/legacy CSR names and conservative coverage side conditions."""
import argparse,copy,hashlib,json,subprocess
from pathlib import Path
from lxml import etree as E
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--checker',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
a.output.mkdir(parents=True,exist_ok=False);checker=a.checker.resolve()
root=Path(__file__).resolve().parents[2];schema=E.XMLSchema(E.parse(str(root/'xml/cpf4.xsd')))
base=E.parse(str(Path(__file__).with_name('cpf4-csr-aliases')/'conservative.xml'))
rows=[]
def check(doc,name,expected):
 schema.assertValid(doc);path=a.output/(name+'.xml');path.write_bytes(E.tostring(doc))
 for repeat in [1,2]:
  q=subprocess.run([str(checker),str(path)],capture_output=True,text=True,timeout=30)
  accepted=q.returncode==0 and q.stdout.strip()=='CERTIFIED'
  rows.append(dict(name=name,repeat=repeat,expected=expected,accepted=accepted,exit=q.returncode,stdout=q.stdout,stderr=q.stderr,certificate_sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
for tag in ['conservativeCsrTerminationProof','nativeConservativeCsrTerminationProof']:
 d=copy.deepcopy(base);d.find('proof')[0].tag=tag;check(d,tag,True)
 for name,index in [('missing-original-rule',0),('missing-marking-rule',1)]:
  m=copy.deepcopy(d);rules=m.find('proof')[0].find('csrConservativeDependencyPairs/auxiliaryRules/rules');rules.remove(rules[index]);check(m,tag+'-'+name,False)
for tag in ['csrTerminationProof','nativeCsrTerminationProof']:
 d=copy.deepcopy(base);proof=d.find('proof');proof.clear();proof.append(E.fromstring(f'<{tag}><csrDependencyPairs><dps><rules/></dps><csrDpProof><pIsEmpty/></csrDpProof></csrDependencyPairs></{tag}>'));check(d,tag,True)
 m=copy.deepcopy(d);rule=m.find('input/trsInput/trs/rules/rule');rule[1].find('name').text='a';check(m,tag+'-omitted-self-loop-pair',False)
d=copy.deepcopy(base);proof=d.find('proof');proof.clear();proof.append(E.fromstring('<csrGuardedTerminationProof><csrGuardedDependencyPairs><dps><rules/></dps><csrGuardedExistingDpProof><csrDpProof><pIsEmpty/></csrDpProof></csrGuardedExistingDpProof></csrGuardedDependencyPairs></csrGuardedTerminationProof>'));check(d,'guarded-dependency-pairs',True)
m=copy.deepcopy(d);m.find('input/trsInput/trs/rules/rule')[1].find('name').text='a';check(m,'guarded-omitted-self-loop-pair',False)
r=dict(checker_sha256=hashlib.sha256(checker.read_bytes()).hexdigest(),checks=rows,passed=all(r['expected']==r['accepted'] for r in rows));(a.output/'validation.json').write_text(json.dumps(r,indent=2)+'\n');print(len(rows),r['passed']);assert r['passed']
