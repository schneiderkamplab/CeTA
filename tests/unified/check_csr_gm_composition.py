"""Direct certificate-file checks, including semantic mutations of GM composition."""
import argparse,hashlib,json,subprocess,time,xml.etree.ElementTree as ET
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--checker',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
O=a.output.resolve();O.mkdir(parents=True,exist_ok=True);FIXTURES=Path(__file__).resolve().parent/'csr-gm-composition';C=a.checker.resolve();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
records=[]
def check(path,accepted,label):
 started=time.monotonic();r=subprocess.run([str(C),str(path)],capture_output=True,text=True,timeout=120)
 records.append(dict(file=str(path),certificate_sha256=sha(path),label=label,expected_acceptance=accepted,accepted=(r.returncode==0 and r.stdout.strip()=='CERTIFIED'),returncode=r.returncode,seconds=time.monotonic()-started,stdout=r.stdout,stderr=r.stderr))
 (O/'certificate-validation.json').write_text(json.dumps(dict(checker=str(C),checker_sha256=sha(C),checks=records,passed=all(x['accepted']==x['expected_acceptance'] for x in records)),indent=2)+'\n')
 print(label,r.returncode,flush=True)
mutations=O/'mutations';mutations.mkdir(exist_ok=True)
for source in sorted(FIXTURES.glob('removal-gm.cpf*.xml')):
 for i in range(2):check(source,True,source.name+':positive:'+str(i))
 for mutation in ['missing-prefix','false-child','unknown-constant','missing-active-map','false-source']:
  tree=ET.parse(source);root=tree.getroot();gm=root.find('.//csrGmTransformation');assert gm is not None
  if mutation=='missing-prefix':
   for item in list(gm.findall('ruleRemoval')):gm.remove(item)
  elif mutation=='false-child':
   child=gm.find('trsTerminationProof');assert child is not None;child.clear();ET.SubElement(child,'rIsEmpty')
  elif mutation=='unknown-constant':
   child=gm.find('groundConstant');assert child is not None;child.clear();ET.SubElement(child,'name').text='absentFromSourceSignature'
  elif mutation=='missing-active-map':
   active=gm.find('activeSymbol');assert active is not None;gm.remove(active)
  else:
   rule=root.find('./input/trsInput/trs/rules/rule');assert rule is not None
   terms=list(rule);assert len(terms)==2
   rule.remove(terms[1]);rule.append(ET.fromstring(ET.tostring(terms[0])))
  dest=mutations/(source.stem+'-'+mutation+'.xml');tree.write(dest,encoding='unicode');check(dest,False,source.name+':'+mutation)
assert len(records)==28, len(records)
assert all(x['accepted']==x['expected_acceptance'] for x in records)
