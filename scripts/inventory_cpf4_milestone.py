#!/usr/bin/env python3
"""Inventory added named XML elements across retained fixtures; occurrences are not semantic coverage."""
from lxml import etree as E
from pathlib import Path
import json,gzip,collections
n={'s':'http://www.w3.org/2001/XMLSchema'}
def declarations(p,seen=None):
 seen=set() if seen is None else seen
 if p in seen:return {}
 seen.add(p);d=E.parse(str(p));out={e.get('name'):str(p) for e in d.xpath('//s:element[@name]',namespaces=n)}
 for inc in d.xpath('/s:schema/s:include/@schemaLocation',namespaces=n):out.update(declarations(p.parent/inc,seen))
 return out
a=declarations(Path('xml/cpf3.xsd'));b=declarations(Path('xml/cpf4.xsd'));added=set(b)-set(a);counts=collections.Counter();examples={};errors=[]
m=json.loads(Path('target/cpf4-milestone-recheck/manifest.json').read_text());files=[Path(j['certificate']) for j in m['jobs']]+list(Path('tests').rglob('*.xml'))+list(Path('tests').rglob('*.xml.gz'))+list(Path('examples').glob('*.xml'))
for p in files:
 try:
  if p.suffix=='.gz':
   import io
   source=io.BytesIO(gzip.decompress(p.read_bytes()))
  else:source=str(p)
  tags=set()
  for _,e in E.iterparse(source,events=('end',),huge_tree=True):
   if e.tag in added:tags.add(e.tag)
   e.clear()
  for tag in tags:counts[tag]+=1;examples.setdefault(tag,str(p))
 except Exception as e:errors.append(dict(path=str(p),error=str(e)))
rows=[dict(name=k,schema=b[k],occurrences=counts[k],example=examples.get(k)) for k in sorted(added)]
report=dict(scope='Named-element syntactic occurrence inventory, not semantic coverage',rows=rows,errors=errors)
Path('target/cpf4-milestone-element-inventory.json').write_text(json.dumps(report,indent=2));print('added',len(rows),'unseen',[r['name'] for r in rows if not r['occurrences']], 'parse_errors',len(errors))
