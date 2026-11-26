"""Contextual CPF6 structural tests, not source termination checks."""
from pathlib import Path
import copy
from lxml import etree as E
root=Path(__file__).resolve().parents[1]
schema=E.XMLSchema(E.parse(str(root/'xml/cpf6.xsd')))
fixture=E.parse(str(root/'tests/fixtures/cpf6-context-composed/positive.xml'))
schema.assertValid(fixture);checks=1
path='./proof/prologContextComposedDependencyTriplesProof'
for field in fixture.find(path):
    bad=copy.deepcopy(fixture);proof=bad.find(path);proof.remove(proof.find(field.tag))
    assert not schema.validate(bad),field.tag;checks+=1
for tag in ['nodes','returnStates','contexts','typings','prologSuccessTransferContract','actions','residual','predicateEncoding','dataEncoding']:
    bad=copy.deepcopy(fixture);bad.find(path+'/'+tag).append(E.Element('unexpected'))
    assert not schema.validate(bad),tag;checks+=1
for tag in ['boundary','unknown']:
    bad=copy.deepcopy(fixture);bad.find(path+'/actions').append(E.Element(tag))
    assert not schema.validate(bad),tag;checks+=1
for tag in ['fuel','root','returnArity']:
    bad=copy.deepcopy(fixture);bad.find(path+'/'+tag).text='-1'
    assert not schema.validate(bad),tag;checks+=1
print(checks,'contextual schema checks passed')

# Structural split coverage only; the empty modules do not prove termination.
split=E.parse(str(root/'tests/fixtures/cpf6-context-composed/split-action.xml')).getroot()
positive=copy.deepcopy(fixture);positive.find(path+'/actions').append(copy.deepcopy(split))
schema.assertValid(positive)
for i in range(len(split)):
    bad=copy.deepcopy(positive);row=bad.find(path+'/actions/returnSplit');row.remove(row[i])
    assert not schema.validate(bad),i
print('split schema: one positive and ten missing-field rejections passed')
