#!/usr/bin/env python3
"""Schema coverage for finite Prolog syntax; does not claim semantic acceptance."""
from pathlib import Path
from lxml import etree as E
import re,json,copy
root=Path(__file__).resolve().parents[1]
schema=E.XMLSchema(E.parse(str(root/'xml/cpf6.xsd')))
base=E.parse(str(root/'tests/fixtures/cpf6-finite-triples/constructor.xml'))
count=0
for file,container in [('cpf_prolog_evaluation_actions.lean','actions'),('cpf_prolog_finite_triple_syntax.lean','components')]:
 text=(root.parent/'CeTA-Lean/tests'/file).read_text()
 for raw in re.findall(r'private def fixture\d+ := (".*")',text):
  item=E.fromstring(json.loads(raw).encode());doc=copy.deepcopy(base)
  parent=doc.find('.//prologEvaluationControl/actions') if container=='actions' else doc.find('.//prologEstablishedFiniteSEGConstructorTriplesProof/components')
  parent.clear();parent.append(item)
  schema.assertValid(doc);count+=1
  item.append(E.Element('unexpected'))
  assert not schema.validate(doc);count+=1
print(count,'schema checks passed; syntax only')
