"""Check every expression shape independently of arithmetic truth."""
from pathlib import Path
from lxml import etree as E
schema=E.XMLSchema(E.parse(str(Path(__file__).resolve().parents[1]/'xml/cpf6.xsd')))
def valid(e):
 xml=f'<certificationProblem><cpfVersion>6.0</cpfVersion><lookupTables/><input><prologInput><executionProfile>iso-rational-libraries-v1</executionProfile><program/><query><predicate>0:p</predicate><modes/></query></prologInput></input><property><termination/></property><answer><no/></answer><proof><prologGroundIntegerSourceNonterminationProof><fuel>10</fuel><arguments/><core><var>X</var></core><before/><after/><prefix/><loop><step><integerComparison><left>{e}</left><right><integer>0</integer></right><holds>false</holds></integerComparison><state/></step></loop></prologGroundIntegerSourceNonterminationProof></proof></certificationProblem>'
 return schema.validate(E.fromstring(xml.encode()))
a='<integer>7</integer>';b='<integer>-3</integer>'
positive=[a,'<var>X</var>']+[f'<{t}>{a}</{t}>' for t in ['positive','negate']]+[f'<{t}>{a}{b}</{t}>' for t in ['add','subtract','multiply']]+[f'<{t}>{a}<divisor>-3</divisor></{t}>' for t in ['divide','modulo']]
positive+=['<multiply><negate>'+a+'</negate><add>'+a+b+'</add></multiply>','<divide>'+a+'<divisor>0</divisor></divide>']
negative=['<integer>1.5</integer>','<integer><var>X</var></integer>',f'<add>{a}</add>',f'<add>{a}{a}{a}</add>',f'<divide>{a}{b}</divide>',f'<divide>{a}<divisor>NaN</divisor></divide>',f'<positive>{a}{b}</positive>',f'<power>{a}{b}</power>']
for e in positive:assert valid(e),e
for e in negative:assert not valid(e),e
print(len(positive)+len(negative),'schema checks passed; zero divisor is structurally valid and requires semantic rejection')
