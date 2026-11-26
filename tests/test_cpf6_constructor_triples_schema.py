"""Constructor triple schema tests; schema acceptance is not certification."""
from pathlib import Path
from lxml import etree as E
import copy
root=Path(__file__).resolve().parents[1]
schema=E.XMLSchema(E.parse(str(root/'xml/cpf6.xsd')))
fixture=E.parse(str(root/'tests/fixtures/cpf6-constructor-triples/positive.xml'))
schema.assertValid(fixture);checks=1
path='./proof/prologEstablishedSEGConstructorTriplesProof/certificationProblem/proof/lpDependencyTriplesConstructorProof'
for tag in ['returns','fallback','tripleContinuations','programContinuations','marks','argumentFilter','seed','dpProof']:
    bad=copy.deepcopy(fixture);p=bad.find(path);p.remove(p.find(tag))
    assert not schema.validate(bad),tag;checks+=1
bad=copy.deepcopy(fixture);p=bad.find(path);p.remove(p.find('normalSubstitutions'))
schema.assertValid(bad);checks+=1
for text in ['true','false']:
    bad=copy.deepcopy(fixture);bad.find(path+'/normalSubstitutions').text=text
    schema.assertValid(bad);checks+=1
bad=copy.deepcopy(fixture);bad.find(path+'/normalSubstitutions').text='invalid'
assert not schema.validate(bad);checks+=1
print(checks,'constructor triple schema checks passed')
