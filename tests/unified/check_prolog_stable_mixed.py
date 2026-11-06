#!/usr/bin/env python3
"""Check the mixed constructor numeric compatibility case and missing obligations.

This does not cover structural children or relational Split contracts.
"""
import argparse,copy,hashlib,json,subprocess
from pathlib import Path
import xml.etree.ElementTree as E
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source',type=Path,required=True)
parser.add_argument('--checker',type=Path,required=True)
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args()
source=args.source.resolve()
out=args.output.resolve()
out.mkdir(parents=True,exist_ok=False)
r=E.parse(source).getroot()
assert r.tag=='prologEstablishedStableSEGGuardedProof'
r.tag='prologEstablishedStableSEGMixedProof'
blocks=r.find('components'); descents=r.find('guardedDescents')
assert len(blocks)==len(descents)
pairs=list(zip(list(blocks),list(descents))); blocks.clear()
for block,descent in pairs:
 w=E.SubElement(blocks,'existingComponent');w.extend([block,descent])
r.remove(descents)
projection=r.find('argumentProjection');child=r.find('prologStableNumericComponent')
r.remove(projection);r.remove(child)
routing=E.SubElement(r,'routing')
names=sorted({n.text for n in r.findall('observedTriples/triple/head/atom/predicate')+r.findall('observedTriples/triple/call/atom/predicate')})
for name in names:
 entry=E.SubElement(routing,'entry');E.SubElement(entry,'predicate').text=name;E.SubElement(entry,'rank').text='0'
backends=E.SubElement(r,'backends');backend=E.SubElement(backends,'numericBackend');backend.extend([projection,child])
E.ElementTree(r).write(out/'positive.xml',encoding='unicode')
mutations={'missing-backend':'backends','missing-routing':'routing','missing-component':'components','missing-root':'roots','missing-child':'backends/numericBackend/prologStableNumericComponent/ltsTerminationProof','missing-descent':'components/existingComponent/guardedRegion','missing-observed-row':'observedTriples'}
for name,xpath in mutations.items():
 m=copy.deepcopy(r);node=m.find(xpath);assert node is not None,(name,xpath)
 if name=='missing-component' or name=='missing-observed-row':
  assert len(node);node.remove(node[0])
 else:node.clear()
 E.ElementTree(m).write(out/(name+'.xml'),encoding='unicode')
(out/'manifest.json').write_text(json.dumps({'scope':'Checker compatibility wrapper and mutations; no native replay or benchmark gain','source':str(source),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'expected':{'positive':True,**{n:False for n in mutations}}},indent=2)+'\n')

checker=args.checker.resolve()
checker_hash=hashlib.sha256(checker.read_bytes()).hexdigest()
results=[]
for name,expected in {'positive':True,**{n:False for n in mutations}}.items():
 for repeat in range(2):
  artifact=out/(name+'.xml')
  run=subprocess.run([str(checker),'--category','prolog',str(artifact)],capture_output=True,text=True,timeout=60)
  (out/f'{name}-{repeat}.log').write_text(run.stdout+run.stderr)
  accepted=run.returncode==0 and 'CERTIFIED SOURCE-BOUND PROLOG' in run.stdout
  results.append(dict(case=name,repeat=repeat,expected=expected,accepted=accepted,exit_code=run.returncode,artifact_sha256=hashlib.sha256(artifact.read_bytes()).hexdigest()))
(out/'results.json').write_text(json.dumps(dict(checker=str(checker),checker_sha256=checker_hash,results=results),indent=2)+'\n')
assert hashlib.sha256(checker.read_bytes()).hexdigest()==checker_hash,'checker changed during validation'
assert all(r['accepted']==r['expected'] for r in results),results
print(f'{len(results)} mixed numeric compatibility checks passed')
