#!/usr/bin/env python3
"""Structured CPF6 Prolog source and static bridge forms."""
from pathlib import Path
import copy
from lxml import etree as E
NS='http://www.w3.org/2001/XMLSchema'
def node(parent,tag,**attrs):return E.SubElement(parent,'{'+NS+'}'+tag,**attrs)
s=E.Element('{'+NS+'}schema',nsmap={'xs':NS},elementFormDefault='qualified')
node(node(s,'annotation'),'documentation').text='Prolog source certificates. Schema validity is not certification.'
def element(p,name,kind=None,**attrs):return node(p,'element',name=name,**({'type':kind} if kind else {}),**attrs)
def sequence(p,name):return node(node(element(p,name),'complexType'),'sequence')
a=sequence(s,'prologInput');element(a,'executionProfile','xs:string');element(a,'program','lp6CutProgram');element(a,'query','lp6CutQuery')
a=node(node(s,'complexType',name='lp6PrologSignature'),'sequence');element(a,'name','xs:string');element(a,'arity','xs:nonNegativeInteger')
for name in ['prologStaticSEGProof','prologStaticNonterminationProof','prologStaticUniformRecursionProof']:
 a=sequence(s,name);p=sequence(a,'predicates');element(p,'signature','lp6PrologSignature',minOccurs='0',maxOccurs='unbounded');node(a,'element',ref='certificationProblem')
a=sequence(s,'prologUndefinedQueryProof');p=sequence(a,'definitions');element(p,'signature','lp6PrologSignature',minOccurs='0',maxOccurs='unbounded')

def group(p,ref,**attrs):return node(p,'group',ref=ref,**attrs)
def terms(p,name):return group(sequence(p,name),'lp6CutTerm',minOccurs='0',maxOccurs='unbounded')
g=node(node(s,'group',name='lp6PrologReturnAction'),'choice')
group(sequence(g,'cut'),'lp6CutReturnAction')
for tag,count in [('variableTest',1),('identityTest',2)]:
 a=sequence(g,tag);element(a,'predicate','xs:string')
 for _ in range(count):group(a,'lp6CutTerm')
 group(sequence(a,'goals'),'lp6CutGoal',minOccurs='0',maxOccurs='unbounded')
 terms(a,'active');element(a,'returnState','lp6CutReturnState')
 element(a,'link','lp6CutLink');element(a,'link','lp6CutLink')
cut=E.parse(str(Path(__file__).resolve().parents[1]/'xml/cpf6-cut.xsd'))
r=copy.deepcopy(cut.find("{"+NS+"}element[@name='lpCutReturnDependencyTriplesProof']"))
r.set('name','prologVarReturnDependencyTriplesProof')
for n in r.iter('{'+NS+'}group'):
 if n.get('ref')=='lp6CutReturnAction':n.set('ref','lp6PrologReturnAction')
s.append(r)
g=copy.deepcopy(cut.find("{"+NS+"}group[@name='lp6CutReturnModuleAction']"))
g.set('name','lp6PrologReturnModuleAction')
for n in g.iter('{'+NS+'}group'):
 if n.get('ref')=='lp6CutReturnAction':n.set('ref','lp6PrologReturnAction')
s.append(g)
r=copy.deepcopy(r);r.set('name','prologModularReturnDependencyTriplesProof')
for n in r.iter('{'+NS+'}group'):
 if n.get('ref')=='lp6PrologReturnAction':n.set('ref','lp6PrologReturnModuleAction')
s.append(r)
g=node(node(s,'group',name='lp6PrologNoAction'),'choice')
group(sequence(g,'ordinary'),'lp6CutNoAction');element(g,'test','lp6CutEmpty')
t=copy.deepcopy(cut.find("{"+NS+"}complexType[@name='lp6CutNoTrace']"));t.set('name','lp6PrologNoTrace')
for n in t.iter('{'+NS+'}group'):
 if n.get('ref')=='lp6CutNoAction':n.set('ref','lp6PrologNoAction')
s.append(t)
r=copy.deepcopy(cut.find("{"+NS+"}element[@name='lpCutSourceNonterminationProof']"))
r.set('name','prologTestSourceNonterminationProof')
seq=r.find('{'+NS+'}complexType/{'+NS+'}sequence')
predicates=E.Element('{'+NS+'}element',name='predicates')
predseq=node(node(predicates,'complexType'),'sequence')
element(predseq,'signature','lp6PrologSignature',minOccurs='0',maxOccurs='unbounded')
seq.insert(0,predicates)
for n in seq:
 if n.get('name')=='prefix':n.set('type','lp6PrologNoTrace')
s.append(r)

g=node(node(s,'group',name='lp6RationalGoal'),'choice')
for tag in ['atom','meta'] : element(sequence(g,tag),'ref','xs:nonNegativeInteger')
a=sequence(g,'unify');element(a,'ref','xs:nonNegativeInteger',minOccurs='2',maxOccurs='2')
element(g,'cut','xs:nonNegativeInteger')
for tag in ['true','fail']:element(g,tag,'lp6CutEmpty')
g=node(node(s,'group',name='lp6RationalEntry'),'choice')
group(sequence(g,'goals'),'lp6RationalGoal',minOccurs='0',maxOccurs='unbounded')
a=sequence(g,'clauseChoice');group(sequence(a,'goals'),'lp6RationalGoal',minOccurs='0',maxOccurs='unbounded');element(a,'index','xs:nonNegativeInteger');element(a,'scope','xs:nonNegativeInteger')
element(g,'barrier','xs:nonNegativeInteger')
g=node(node(s,'group',name='lp6RationalClash'),'choice')
element(sequence(g,'constructorClash'),'index','xs:nonNegativeInteger',minOccurs='0',maxOccurs='unbounded')
a=sequence(g,'repeatedVariableClash')
for tag in ['left','right']:element(sequence(a,tag),'index','xs:nonNegativeInteger',minOccurs='0',maxOccurs='unbounded')
g=node(node(s,'group',name='lp6RationalAction'),'choice');element(g,'admin','lp6CutEmpty');element(sequence(g,'case'),'scope','xs:nonNegativeInteger')
a=sequence(g,'resolve');b=node(node(element(sequence(a,'environment'),'binding',minOccurs='0',maxOccurs='unbounded'),'complexType'),'sequence');element(b,'var','xs:string');element(b,'ref','xs:nonNegativeInteger');group(sequence(a,'body'),'lp6RationalGoal',minOccurs='0',maxOccurs='unbounded')
group(sequence(g,'backtrack'),'lp6RationalClash')
a=sequence(s,'prologRationalSourceNonterminationProof');element(sequence(a,'predicates'),'signature','lp6PrologSignature',minOccurs='0',maxOccurs='unbounded')
element(a,'fuel','xs:nonNegativeInteger');terms(a,'arguments')
b=node(node(element(sequence(a,'graph'),'node',minOccurs='0',maxOccurs='unbounded'),'complexType'),'sequence');group(b,'lp6CutSymbol');element(sequence(b,'children'),'ref','xs:nonNegativeInteger',minOccurs='0',maxOccurs='unbounded')
terms(a,'anchors');element(a,'variable','xs:string');group(sequence(a,'rhs'),'lp6CutTerm');element(a,'bindingRoot','xs:nonNegativeInteger');group(sequence(a,'call'),'lp6CutTerm');element(a,'callRoot','xs:nonNegativeInteger')
group(sequence(a,'before'),'lp6CutEntry',minOccurs='0',maxOccurs='unbounded');group(sequence(a,'after'),'lp6RationalEntry',minOccurs='0',maxOccurs='unbounded');element(a,'prefix','lp6CutNoTrace')
b=node(node(element(sequence(a,'loop'),'step',minOccurs='0',maxOccurs='unbounded'),'complexType'),'sequence');group(b,'lp6RationalAction');group(sequence(b,'state'),'lp6RationalEntry',minOccurs='0',maxOccurs='unbounded')

g=node(node(s,'group',name='lp6IntegerNoAction'),'choice');group(g,'lp6PrologNoAction');element(sequence(g,'integerIdentity'),'integer','xs:integer')
t=copy.deepcopy(cut.find("{"+NS+"}complexType[@name='lp6CutNoTrace']"));t.set('name','lp6IntegerNoTrace')
for n in t.iter('{'+NS+'}group'):
 if n.get('ref')=='lp6CutNoAction':n.set('ref','lp6IntegerNoAction')
s.append(t)
r=copy.deepcopy(cut.find("{"+NS+"}element[@name='lpCutSourceNonterminationProof']"));r.set('name','prologIntegerSourceNonterminationProof')
for n in r.iter('{'+NS+'}element'):
 if n.get('name') in ['prefix','loop']:n.set('type','lp6IntegerNoTrace')
s.append(r)
g=node(node(s,'group',name='lp6IntegerExpression'),'choice')
element(g,'integer','xs:integer');element(g,'var','xs:string')
for name in ['positive','negate']:
 group(sequence(g,name),'lp6IntegerExpression')
for name in ['add','subtract','multiply']:
 group(sequence(g,name),'lp6IntegerExpression',minOccurs='2',maxOccurs='2')
for name in ['divide','modulo']:
 a=sequence(g,name);group(a,'lp6IntegerExpression');element(a,'divisor','xs:integer')
g=node(node(s,'group',name='lp6GroundIntegerNoAction'),'choice');group(g,'lp6IntegerNoAction')
a=sequence(g,'integerComparison');group(sequence(a,'left'),'lp6IntegerExpression');group(sequence(a,'right'),'lp6IntegerExpression');element(a,'holds','xs:boolean')
t=copy.deepcopy(t);t.set('name','lp6GroundIntegerNoTrace')
for n in t.iter('{'+NS+'}group'):
 if n.get('ref')=='lp6IntegerNoAction':n.set('ref','lp6GroundIntegerNoAction')
s.append(t)
r=copy.deepcopy(r);r.set('name','prologGroundIntegerSourceNonterminationProof')
for n in r.iter('{'+NS+'}element'):
 if n.get('name') in ['prefix','loop']:n.set('type','lp6GroundIntegerNoTrace')
s.append(r)
from cpf6_prolog_established_schema import extend
extend(s, cut, node, element, sequence, group)
from cpf6_prolog_finite_schema import extend as extend_finite
extend_finite(s)
from cpf6_prolog_stable_schema import extend as extend_stable
extend_stable(s)
E.indent(s, space="  ")
(Path(__file__).resolve().parents[1]/'xml/cpf6-prolog.xsd').write_bytes(E.tostring(s,pretty_print=True,xml_declaration=True,encoding='UTF-8'))
