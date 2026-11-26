#!/usr/bin/env python3
"""CPF6 LP schema, envelope binding and generated-checker regressions."""
from pathlib import Path
from lxml import etree as E
import argparse,copy,json,subprocess,tempfile,hashlib
root=Path(__file__).resolve().parents[2]
p=argparse.ArgumentParser();p.add_argument('--ceta',type=Path);p.add_argument('--codec',type=Path,required=True);p.add_argument('--leta',type=Path);a=p.parse_args()
if not (a.ceta or a.leta):p.error('provide --ceta and/or --leta')
schema=E.XMLSchema(E.parse(str(root/'xml/cpf6.xsd')))
base=E.parse(str(root/'tests/unified/lp-finite.xml')).getroot()
def wrap(fragment):
 tag=fragment.tag
 doc=E.Element('certificationProblem');E.SubElement(doc,'cpfVersion').text='6.0';E.SubElement(doc,'lookupTables')
 inp=E.SubElement(E.SubElement(doc,'input'),'logicProgramInput')
 E.SubElement(inp,'resolutionSemantics').text='finiteTerms' if tag=='lpFiniteTerminationProof' else 'infiniteTrees'
 inp.extend([copy.deepcopy(fragment.find('program')),copy.deepcopy(fragment.find('query'))])
 E.SubElement(E.SubElement(doc,'property'),'termination');E.SubElement(E.SubElement(doc,'answer'),'yes')
 proof=E.SubElement(E.SubElement(doc,'proof'),tag)
 proof.extend(copy.deepcopy(c) for c in fragment if c.tag not in ['program','query'])
 return doc
results=[]
with tempfile.TemporaryDirectory() as directory:
 d=Path(directory)
 for tag in ['lpFiniteTerminationProof','lpTocl09TerminationProof']:
  fragment=copy.deepcopy(base);fragment.tag=tag
  native=d/'fragment.xml';native.write_bytes(E.tostring(fragment))
  cpf=d/'encoded.xml'
  subprocess.run([str(a.codec.resolve()),'encode',str(native),str(cpf)],check=True,capture_output=True)
  doc=E.parse(str(cpf)).getroot()
  assert schema.validate(doc),schema.error_log
  decoded=d/'decoded.xml';subprocess.run([str(a.codec.resolve()),'decode',str(cpf),str(decoded)],check=True,capture_output=True)
  assert E.tostring(E.parse(str(decoded),E.XMLParser(remove_blank_text=True)),method='c14n')==E.tostring(E.parse(str(native),E.XMLParser(remove_blank_text=True)),method='c14n')
  cases=[('legacy',fragment,True),('cpf6',doc,True),('legacy-comment',fragment,True),('legacy-pi-comment',fragment,True),('cpf6-comment',doc,True),('cpf6-pi-comment',doc,True)]
  for version in ['3.0','4.0','5.0']:
   bad=copy.deepcopy(doc);bad.find('cpfVersion').text=version;cases.append(('old-version-'+version,bad,False))
  for label,path,value in [('wrong-semantics','input/logicProgramInput/resolutionSemantics','infiniteTrees' if tag=='lpFiniteTerminationProof' else 'finiteTerms'),('query-arity','input/logicProgramInput/query/arity','2'),('ground-index','input/logicProgramInput/query/ground/index','999')]:
   bad=copy.deepcopy(doc);bad.find(path).text=value;cases.append((label,bad,False))
  bad=copy.deepcopy(doc);bad.find('answer/yes').tag='no';cases.append(('wrong-answer',bad,False))
  bad=copy.deepcopy(doc);bad.find('property/termination').tag='confluence';cases.append(('wrong-property',bad,False))
  bad=copy.deepcopy(doc);proof=bad.find('proof')[0];proof.append(copy.deepcopy(doc.find('input/logicProgramInput/program')));cases.append(('duplicated-source',bad,False))
  bad=copy.deepcopy(doc);child=bad.find('proof')[0].find('trsTerminationProof');child.clear();E.SubElement(child,'rIsEmpty');cases.append(('false-child',bad,False))
  bad=copy.deepcopy(doc);inp=bad.find('input/logicProgramInput');inp.remove(inp.find('query'));cases.append(('missing-query',bad,False))
  for label,value,expected in cases:
   path=d/'check.xml'
   prefix=(b'<?xml version="1.0"?>\n' if 'pi-comment' in label else b'')+(b'<!-- leading comment -->\n' if label.endswith('comment') else b'')
   path.write_bytes(prefix+E.tostring(value))
   commands=[('ceta',[str(a.ceta.resolve()),'--category','lp',str(path)])] if a.ceta else []
   if a.leta and not label.startswith('legacy'):commands.append(('leta',[str(a.leta.resolve()),str(path)]))
   for checker,command in commands:
    q=subprocess.run(command,capture_output=True,text=True,timeout=60)
    row=dict(checker=checker,constructor=tag,case=label,exit=q.returncode,stdout=q.stdout,stderr=q.stderr,sha256=hashlib.sha256(path.read_bytes()).hexdigest())
    print(json.dumps(row),flush=True);results.append(row)
    assert (q.returncode==0)==expected,row
print(f'{len(results)} CPF6 LP checker cases passed',flush=True)
