"""Stable guarded schema tests; structural acceptance is not certification."""
from pathlib import Path
import re,json
from lxml import etree as E
root=Path(__file__).resolve().parents[1]
schema=E.XMLSchema(E.parse(str(root/'xml/cpf6.xsd')))
fixture=E.parse(str(root/'tests/fixtures/cpf6-stable-guarded/positive.xml'))
assert schema.validate(fixture),schema.error_log
count=1
conditions=json.loads((root/'tests/fixtures/cpf6-stable-guarded/conditions.json').read_text())
for literal in conditions:
    condition=E.fromstring(literal.encode())
    doc=E.fromstring(E.tostring(fixture))
    rows=doc.find('.//prologStableNumericComponent/rows')
    row=E.SubElement(rows,'row')
    for tag in ['facts','ground','inputs','outputs','tests','bindings','formula']:E.SubElement(row,tag)
    row.find('tests').append(condition);E.SubElement(row.find('formula'),'conjunction')
    assert schema.validate(doc),(condition.tag,schema.error_log)
    count+=1
    E.SubElement(condition,'unknown')
    assert not schema.validate(doc),condition.tag
    count+=1
print(count,'stable guarded schema checks passed; syntax only')
