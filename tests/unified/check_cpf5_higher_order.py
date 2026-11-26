"""Direct CPF5/6 acceptance and version/claim rejection; no legacy adapter."""
import argparse
import json
import gzip
from pathlib import Path
import subprocess
import tempfile
from lxml import etree
p=argparse.ArgumentParser();p.add_argument('--checker',type=Path,required=True);a=p.parse_args()
root=Path(__file__).resolve().parents[2]
source=(root/'tests/unified/cpf5-higher-order/empty.xml').read_text()
schema=etree.XMLSchema(etree.parse(str(root/'xml/cpf5.xsd')))
assert schema.validate(etree.fromstring(source.encode())),schema.error_log
cases=[('cpf5',source,True),('cpf6',source.replace('<cpfVersion>5.0','<cpfVersion>6.0'),True),('cpf4',source.replace('<cpfVersion>5.0','<cpfVersion>4.0'),False),('future',source.replace('<cpfVersion>5.0','<cpfVersion>7.0'),False),('wrong-answer',source.replace('<yes/>','<no/>'),False),('wrong-property',source.replace('<termination/>','<operationalTermination/>'),False)]
with tempfile.TemporaryDirectory() as d:
 for name,text,accepted in cases:
  f=Path(d)/(name+'.xml');f.write_text(text)
  r=subprocess.run([str(a.checker.resolve()),'--category','higher-order',str(f)],capture_output=True,text=True,timeout=30)
  assert (r.returncode==0)==accepted,(name,r.stdout,r.stderr)
  print(json.dumps(dict(case=name,accepted=accepted,exit_code=r.returncode)))

with tempfile.TemporaryDirectory() as d:
 for fixture in sorted((root/'tests/unified/cpf5-higher-order').glob('*.xml.gz')):
  text=gzip.decompress(fixture.read_bytes()).decode()
  doc=etree.fromstring(text.encode());assert schema.validate(doc),schema.error_log
  wrong=etree.fromstring(text.encode());child=wrong.find('.//firstOrderProof');child.clear()
  bad=etree.fromstring(text.encode());node=bad.find('.//firstOrderProof');node.getparent().remove(node)
  tests=[('positive',text,True),('empty-child',etree.tostring(wrong).decode(),False),('missing-child',etree.tostring(bad).decode(),False),('old-version',text.replace('<cpfVersion>5.0','<cpfVersion>4.0'),False)]
  for name,content,accepted in tests:
   f=Path(d)/'proof.xml';f.write_text(content)
   r=subprocess.run([str(a.checker.resolve()),'--category','higher-order-delegation',str(f)],capture_output=True,text=True,timeout=300)
   assert (r.returncode==0)==accepted,(fixture.name,name,r.stdout,r.stderr)
   print(json.dumps(dict(family=fixture.name,case=name,accepted=accepted,exit_code=r.returncode)))
