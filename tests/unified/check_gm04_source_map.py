from pathlib import Path
import json,subprocess,hashlib,xml.etree.ElementTree as E,time
import argparse,gzip
parser=argparse.ArgumentParser();parser.add_argument('--checker',type=Path,required=True);parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
O=args.output.resolve();O.mkdir(parents=True,exist_ok=True);C=args.checker.resolve();D=O/'mutations';D.mkdir(exist_ok=True);records=[]
fixture=Path(__file__).resolve().parent/'gm04-source-map/positive.cpf.xml.gz'
positive=O/'positive.cpf.xml';positive.write_bytes(gzip.decompress(fixture.read_bytes()))
def check(p,expected,label):
 t=time.monotonic();q=subprocess.run([str(C),str(p)],capture_output=True,text=True,timeout=180);accepted=q.returncode==0 and q.stdout.strip()=='CERTIFIED';records.append(dict(file=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),expected=expected,accepted=accepted,label=label,stdout=q.stdout,stderr=q.stderr,seconds=time.monotonic()-t));(O/'source-map-validation.json').write_text(json.dumps(dict(checker_sha256=hashlib.sha256(C.read_bytes()).hexdigest(),checks=records,passed=all(x['expected']==x['accepted'] for x in records)),indent=2));print(label,accepted,flush=True);assert accepted==expected,q.stdout+q.stderr
for p in [positive]:
 for i in range(2):check(p,True,p.parent.name+':positive:'+str(i))
 for mutation in ['ambient-proof-map','outer-map','missing-proof-map','false-source','false-q']:
  tree=E.parse(p);root=tree.getroot();gm=root.find('.//gm04StandaloneDpProof');assert gm is not None
  if mutation in ['ambient-proof-map','outer-map']:
   base=gm.find('sourceReplacementMap/contextSensitive');entry=next(e for e in base if int(e.findtext('arity'))>0);name=entry.findtext('name');assert name is not None;target=entry if mutation=='outer-map' else next(e for e in gm.findall('sourceProofReplacementMap/contextSensitive/replacementMapEntry') if e.findtext('name')==name)
   positions=target.findall('position')
   if positions:target.remove(positions[0])
   else:E.SubElement(target,'position').text='1'
  elif mutation=='missing-proof-map':gm.remove(gm.find('sourceProofReplacementMap'))
  elif mutation=='false-source':
   proof=gm.find('sourceProof');proof.clear();E.SubElement(proof,'rIsEmpty')
  else:
   q=gm.find('.//transformedProof/dpProof/finitenessAssumption/dpInput/strategy/innermostLhss');assert q is not None
   for t in list(q):
    if t.tag!='nfs':q.remove(t)
  out=D/(p.parent.name+'-'+mutation+'.xml');tree.write(out,encoding='unicode')
  expected=False
  check(out,expected,p.parent.name+':'+mutation)
assert len(records)==7
