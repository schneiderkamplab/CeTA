"""Structural conformance only; mathematical validity is checked separately.

Action/component fixtures mirror CeTA-Lean's CPF parser tests. Preserve all
nested structured evidence and reject unknown or incomplete fields.
"""
from pathlib import Path
import copy
import json
from lxml import etree as E
ROOT=Path(__file__).resolve().parents[1]
XS='{http://www.w3.org/2001/XMLSchema}'
fixtures=ROOT/'tests/fixtures/cpf6-established'
schema=E.XMLSchema(E.parse(str(ROOT/'xml/cpf6.xsd')))
positive=E.parse(str(fixtures/'positive.xml'))
schema.assertValid(positive)
checks=1
# Keep full claims intact while corrupting nested structures.
for path in ['.//prologEstablishedSEGDependencyTriplesProof', './/sourceContext',
             './/prologContextControl', './/prologSuccessTransferContract',
             './/tripleRoot', './/tripleConnection', './/clauseReceipt']:
    mutated=copy.deepcopy(positive);mutated.find(path).append(E.Element('unknown'))
    assert not schema.validate(mutated),path
    checks+=1
for path in ['.//prologContextControl/fuel', './/prologContextControl/actions',
             './/prologEstablishedSEGDependencyTriplesProof/contexts',
             './/prologEstablishedSEGDependencyTriplesProof/certificationProblem']:
    mutated=copy.deepcopy(positive);node=mutated.find(path);node.getparent().remove(node)
    assert not schema.validate(mutated),path
    checks+=1
# Test groups directly without misrepresenting syntactic fixtures as certificates.
def harness(group):
    root=E.Element(XS+'schema',nsmap={'xs':XS[1:-1]})
    E.SubElement(root,XS+'include',schemaLocation=str(ROOT/'xml/cpf6.xsd'))
    element=E.SubElement(root,XS+'element',name='fixture')
    seq=E.SubElement(E.SubElement(element,XS+'complexType'),XS+'sequence')
    E.SubElement(seq,XS+'group',ref=group)
    return E.XMLSchema(root)
cases=json.loads((fixtures/'syntax.json').read_text())
assert len(cases['actions'])==12 and len(cases['components'])==4
for kind,group in [('actions','lp6PrologContextAction'),('components','lp6PrologTripleComponent')]:
    test=harness(group)
    for text in cases[kind]:
        wrapper=E.fromstring(('<fixture>'+text+'</fixture>').encode())
        test.assertValid(wrapper);checks+=1
        bad=copy.deepcopy(wrapper);bad[0].append(E.Element('unknown'))
        assert not test.validate(bad);checks+=1
        bad=copy.deepcopy(wrapper);bad[0].clear()
        assert not test.validate(bad);checks+=1
# The shared variable token at the term/expression boundary must be unambiguous.
test=harness('lp6PrologContextAction')
for text in cases['actions']:
    if text.startswith('<integerComparison>'):
        text=text.replace('<integer>2</integer>','<var>Y</var>')
        test.assertValid(E.fromstring(('<fixture>'+text+'</fixture>').encode()));checks+=1
print(checks,'established CPF6 schema checks passed (not semantic certification)')
# Nonempty transfer and context evidence: include each fact/guard/observation.
def typed(kind, body):
    root=E.Element(XS+'schema',nsmap={'xs':XS[1:-1]})
    E.SubElement(root,XS+'include',schemaLocation=str(ROOT/'xml/cpf6.xsd'))
    E.SubElement(root,XS+'element',name='fixture',type=kind)
    test=E.XMLSchema(root);value=E.fromstring(('<fixture>'+body+'</fixture>').encode())
    test.assertValid(value)
    value.append(E.Element('unknown'));assert not test.validate(value)
atom='<atom><predicate>p</predicate><arguments><var>X</var></arguments></atom>'
facts=['<inputFact><argument>0</argument><var>X</var></inputFact>',
 '<baseFact><guardFact><guard>0</guard><var>X</var></guardFact></baseFact>',
 '<baseFact><helperFact><call>0</call><argument>0</argument><var>X</var></helperFact></baseFact>',
 '<baseFact><evaluationFact><guard>0</guard><integer>1</integer><result>X</result></evaluationFact></baseFact>',
 '<helperTransferFact><call>0</call><rule>0</rule><argument>0</argument><var>X</var><inputs><var>X</var><integer>2</integer></inputs></helperTransferFact>']
guards=['<integerGuard><var>X</var></integerGuard>',
 '<evaluationGuard><var>X</var><var>Y</var></evaluationGuard>',
 '<numericSuccessGuard><comparison>0</comparison><var>X</var><var>Y</var></numericSuccessGuard>',
 '<opaqueGuard><var>X</var></opaqueGuard>']
contract='<summaries><summary><predicate>p</predicate><arity>1</arity><contexts><context><required><position>0</position></required><outputs><position>0</position></outputs></context></contexts></summary></summaries><successProgram><clause><head>'+atom+'</head><body>'+atom+'</body><guards>'+''.join(guards)+'</guards></clause></successProgram><proofs><clause><contexts><context><facts>'+''.join(facts)+'</facts><outputs><var>X</var><integer>1</integer></outputs></context></contexts></clause></proofs>'
typed('lp6PrologTransferContract',contract);checks+=2
observations=['<integerGuard><var>X</var></integerGuard>', '<groundGuard><var>X</var></groundGuard>',
 '<sourceEquation><var>X</var><var>Y</var></sourceEquation>',
 '<evaluationGuard><var>X</var><var>Y</var></evaluationGuard>',
 '<comparisonGuard><funapp><user>&lt;</user><var>X</var><var>Y</var></funapp></comparisonGuard>',
 '<returnShape><grammar><shapeNode><production><symbol><user>f</user></symbol><arguments><any/><ground/><node>0</node></arguments></production></shapeNode></grammar><shape><node>0</node></shape><term><var>X</var></term></returnShape>']
typed('lp6PrologSourceContext','<facts>'+atom+'</facts><guards>'+''.join(guards)+'</guards><observations>'+''.join(observations)+'</observations>');checks+=2
print(checks,'total schema checks including nonempty transfer/context evidence')
