#!/usr/bin/env python3
"""Exercise all five nonrecursive/native RFC forms on a nonempty string TRS."""
import argparse,copy,hashlib,json,subprocess
from pathlib import Path
from lxml import etree as E
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--checker',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();a.output.mkdir(parents=True,exist_ok=False)
root=Path(__file__).resolve().parents[2];checker=a.checker.resolve();schema=E.XMLSchema(E.parse(str(root/'xml/cpf4.xsd')))
base=E.parse(str(Path(__file__).with_name('cpf4-rfc-variants')/'positive.xml'));rows=[]
for tag in ['rfcBounds','rfcAutomatonClosedBounds','rfcRelativeBounds','rfcAutomatonClosedRelativeBounds','rfcNativeMatchboxRelativeBounds']:
 d=copy.deepcopy(base);step=d.find('proof/trsTerminationProof')[0];step.tag=tag
 if tag not in ['rfcBounds','rfcAutomatonClosedBounds']:
  step.append(copy.deepcopy(d.find('input/trsInput/trs')));step.append(E.fromstring('<trsTerminationProof><rIsEmpty/></trsTerminationProof>'))
 for mutation in ['positive','missing-initial-language','missing-transition','false-source']:
  m=copy.deepcopy(d);node=m.find('proof/trsTerminationProof')[0]
  if mutation=='missing-initial-language':node.find('initialTerms').clear()
  elif mutation=='missing-transition':
   t=node.find('bounds/treeAutomaton/transitions');t.remove(t[0])
  elif mutation=='false-source':m.find('input/trsInput/trs/rules/rule')[1].find('name').text='a'
  schema.assertValid(m);path=a.output/(tag+'-'+mutation+'.xml');path.write_bytes(E.tostring(m));expected=mutation=='positive'
  for repeat in [1,2]:
   q=subprocess.run([str(checker),str(path)],capture_output=True,text=True,timeout=30);accepted=q.returncode==0 and q.stdout.strip()=='CERTIFIED'
   rows.append(dict(tag=tag,mutation=mutation,repeat=repeat,expected=expected,accepted=accepted,exit=q.returncode,stdout=q.stdout,stderr=q.stderr,certificate_sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
r=dict(checker_sha256=hashlib.sha256(checker.read_bytes()).hexdigest(),checks=rows,passed=all(r['expected']==r['accepted'] for r in rows));(a.output/'validation.json').write_text(json.dumps(r,indent=2)+'\n');print(len(rows),r['passed']);assert r['passed']
