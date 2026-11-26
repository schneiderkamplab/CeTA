#!/usr/bin/env python3
"""Extract the additional Prolog XML syntax from the Isabelle parser combinators.

Only syntax is translated. Semantic predicates and soundness remain in CeTA.
Unknown combinators fail rather than producing a wildcard schema.
"""
from pathlib import Path
import re,json,copy
from lxml import etree as E
ROOT=Path(__file__).resolve().parents[1]
NS='http://www.w3.org/2001/XMLSchema'; Q=lambda n:'{'+NS+'}'+n
specs=json.loads((ROOT/'xml/cpf6-prolog-source-forms.json').read_text())
def node(n,**kw):return E.Element(Q(n),**kw)
def seq(items):
 e=node('sequence');e.extend(items);return e
def wrap(name,items):
 e=node('element',name=name);c=E.SubElement(e,Q('complexType'));c.append(seq(items));return e
# Every named parser is resolved to its source definition or an explicit existing
# schema declaration. The source parser remains the authority for acceptance.
definitions={}
parameters={}
for path in sorted((ROOT/'thys').rglob('*.thy')):
 text=path.read_text(errors="replace")
 for m in re.finditer(r'"(\w+parser)\s+(tag)\s*=\s*([^"\n]*(?:\n[^"\n]*)*)"',text):parameters[m[1]]=(m[2],m[3])
 for m in re.finditer(r'"([a-zA-Z][\w]*parser)\s*(?:x\s*)?=\s*([^"\n]*(?:\n[^"\n]*)*)"',text):
  name,body=m.groups()
  if name in definitions and definitions[name]!=body:continue
  definitions[name]=body
aliases={
 'lpc_term_parser':('group','lp6CutTerm'),'lpc_goal_parser':('group','lp6CutGoal'),
 'lpc_symbol_parser':('group','lp6CutSymbol'),'lpc_entry_parser':('group','lp6CutEntry'),
 'lpc_return_state_parser':('element','returnState','lp6CutReturnState'),
 'lpp_transfer_contract_parser':('element','prologSuccessTransferContract','lp6PrologTransferContract'),
 'lpp_integer_expression_parser':('group','lp6IntegerExpression'),
 'lpp_numeric_comparison_parser':('group','lp6PrologComparison'),
 'symbol_parser':('group','symbol'),
 'formula_parser':('group','formula'),
 'ia4_lts_input_parser':('element','lts','lts'),
 'ia4_lts_termination_proof_parser':('group','ltsTerminationProof'),
 'lts_parser':('element','lts','lts'),
 'its4_cpf_parser':('ref','certificationProblem'),
}
schema=node('schema',elementFormDefault='qualified');schema.nsmap
active=set();done=set();origins={}
def balanced(s,start,op='(',cl=')'):
 level=0
 for i in range(start,len(s)):
  if s[i]==op:level+=1
  elif s[i]==cl:
   level-=1
   if level==0:return i
 raise ValueError('unbalanced '+s[start:start+100])
def strip(s):
 s=s.strip()
 while s.startswith('('):
  end=balanced(s,0)
  if s[end+1:].strip() not in ['', 'x']:break
  s=s[1:end].strip()
 return s

def split_top(s,separator):
 parts=[];depth=0;start=0;i=0
 while i<len(s):
  if depth==0 and s.startswith(separator,i):parts.append(s[start:i]);i+=len(separator);start=i;continue
  if s[i] in '({[':depth+=1
  if s[i] in ')}]':depth-=1
  i+=1
 parts.append(s[start:]);return parts

def atom(s):
 s=s.lstrip()
 if s.startswith('('):
  end=balanced(s,0);return s[1:end],s[end+1:]
 m=re.match(r'\w+',s)
 if not m:raise ValueError('expected parser atom '+s[:100])
 return m[0],s[m.end():]
def ref(name):
 if name=='lpp_transfer_contract_parser':
  choice=node('choice');choice.extend([node('element',name='prologSuccessTransferContract',type='lp6PrologTransferContract'),wrap('enclosingTransferContract',[])]);return choice
 if name in aliases:
  a=aliases[name]
  return node('group',ref=a[1]) if a[0]=='group' else node('element',**({'ref':a[1]} if a[0]=='ref' else {'name':a[1],'type':a[2]}))
 key='lp6Source_'+name
 if name not in done and name not in active:
  if name not in definitions:raise ValueError('unresolved parser '+name)
  active.add(name);body=parse(definitions[name]);active.remove(name);done.add(name)
  g=node('group',name=key);g.append(body if body.tag in [Q('choice'),Q('sequence')] else seq([body]));schema.append(g)
 return node('group',ref=key)
def parse(s):
 s=strip(s)
 if s.startswith('CPF_Proof_Parser.afs '):return node('element',ref='argumentFilter')
 if s.startswith('xml2dp_termination_proof '):return node('element',ref='dpProof')
 if s.startswith('xml2trs_termination_proof '):return node('element',ref='trsTerminationProof')
 if s.startswith('CPF_Input_Parser.term '):return node('group',ref='term')
 choices=split_top(s,'XMLor')
 if len(choices)>1:
  e=node('choice');e.extend(parse(x) for x in choices);return e
 if s.startswith('xml_change'):
  a,_=atom(s[len('xml_change'):]);return parse(a)
 if s.startswith('XMLdo'):
  m=re.match(r"XMLdo\s*\(STR\s*''([^']+)''\)\s*\{",s)
  if not m:raise ValueError('XMLdo '+s[:100])
  end=balanced(s,m.end()-1,'{','}');fields=[]
  for part in split_top(s[m.end():end],';'):
   if '\\<leftarrow>' not in part:continue
   expr=part.split('\\<leftarrow>',1)[1].strip();optional=expr.startswith('[')
   if optional:expr=expr[balanced(expr,0,'[',']')+1:].strip()
   field=parse(expr)
   if optional:field.set('minOccurs','0')
   fields.append(field)
  return wrap(m[1],fields)
 m=re.match(r"xml_pair\s*\(STR\s*''([^']+)''\)",s)
 if m:
  a,rest=atom(s[m.end():]);b,_=atom(rest);return wrap(m[1],[parse(a),parse(b)])
 m=re.match(r"(xml_text|xml_nat|xml_int|xml_bool|xml_leaf|xml_many|xml_singleton|xml_many1)\s*\(STR\s*''([^']+)''\)",s)
 if m:
  op,name=m.groups();rest=s[m.end():]
  if op in ['xml_text','xml_nat','xml_int','xml_bool']:return node('element',name=name,type={'xml_text':'xs:string','xml_nat':'xs:nonNegativeInteger','xml_int':'xs:integer','xml_bool':'xs:boolean'}[op])
  if op=='xml_leaf':return wrap(name,[])
  child,_=atom(rest);e=parse(child)
  if op in ['xml_many','xml_many1']:e.set('minOccurs','0' if op=='xml_many' else '1');e.set('maxOccurs','unbounded')
  return wrap(name,[e])
 m=re.match(r"lpp_evaluation_types_parser\s*\(STR\s*''([^']+)''\)",s)
 if m:return parse("xml_many (STR ''"+m[1]+"'') lpp_transfer_fact_parser id")
 m=re.match(r"(\w+parser)\s*\(STR\s*''([^']+)''\)",s)
 if m and m[1] in parameters:
  param,body=parameters[m[1]];return parse(re.sub(r'\b'+param+r'\b',"(STR ''"+m[2]+"'')",body))
 m=re.match(r'(\w+parser)\b',s)
 if m:return ref(m[1])
 raise ValueError('unsupported parser expression '+s[:180])
for spec in specs:
 path=ROOT/spec['parser'];text=path.read_text(errors="replace")
 m=re.search(r'"(\w+parser)\s*=\s*XMLdo\s*\(STR\s*\'\''+spec['root']+r"''\)",text)
 assert m,spec['root']
 native=parse(definitions[m[1]])
 sequence=native.find(Q('complexType')+'/'+Q('sequence'))
 for field in list(sequence):
  if field.get('name') in ['profile','program','predicate','modes']:sequence.remove(field)
 schema.append(native)
# xs prefix must be available for built-in type references.
result=E.Element(Q('schema'),nsmap={'xs':NS},elementFormDefault='qualified');result.extend(schema)
E.indent(result,space='  ')
(ROOT/'xml/cpf6-prolog-source.xsd').write_bytes(E.tostring(result,pretty_print=True,xml_declaration=True,encoding='UTF-8'))
print(len(specs),'source roots;',len(done),'resolved parser groups')
