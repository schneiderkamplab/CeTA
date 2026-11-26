#!/usr/bin/env python3
"""Generate the structured higher-order certificate extension from its data grammar."""
import json
from pathlib import Path
from lxml import etree as E
ROOT=Path(__file__).resolve().parents[1]
g=json.loads((ROOT/'src/Haskell/Ceta/Input/cpf4-native.json').read_text())
NS='http://www.w3.org/2001/XMLSchema'
def el(parent,tag,**attrs):return E.SubElement(parent,'{'+NS+'}'+tag,**attrs)
schema=E.Element('{'+NS+'}schema',nsmap={'xs':NS},elementFormDefault='qualified')
used=set()
def typ(node,t):
 if isinstance(t,str):
  if t in ('natural','string'):node.set('type',{'natural':'xs:nonNegativeInteger','string':'xs:string'}[t])
  elif t=='boolean':
   r=el(el(node,'simpleType'),'restriction',base='xs:string')
   for v in ['True','False']:el(r,'enumeration',value=v)
  else:node.set('type','hoNative'+t);used.add(t)
  return
 ct=node if E.QName(node).localname=='complexType' else el(node,'complexType')
 if 'list' in t:typ(el(el(ct,'sequence'),'element',name='item',minOccurs='0',maxOccurs='unbounded'),t['list'])
 elif 'tuple' in t:
  seq=el(ct,'sequence')
  for n,t in t['tuple']:typ(el(seq,'element',name=n),t)
 else:
  seq=el(ct,'choice')
  for n,fs in t['sum'].items():typ(el(seq,'element',name=n),{'tuple':fs})
inputs={}
for n,r in g['roots'].items():
 if r['category'] not in ('higherOrder',):continue
 node=el(schema,'element',name=n)
 typ(node,{'tuple':[(n,t) for n,t in r['fields'] if n not in r['inputs']]})
 if n.startswith('ho-ceta-'):
  seq=node.find('{'+NS+'}complexType/{'+NS+'}sequence')
  wrapper=el(el(el(seq,'element',name='firstOrderProof'),'complexType'),'sequence')
  el(wrapper,'element',name='trsTerminationProof',type='ferrumTrsProofBody')
 source=[(n,t) for n,t in r['fields'] if n in r['inputs']]
 assert r['category'] not in inputs or inputs[r['category']]==source
 inputs[r['category']]=source
for n,fs in inputs.items():typ(el(schema,'element',name=n+'Input'),{'tuple':fs})
done=set()
while used-done:
 n=sorted(used-done)[0];done.add(n);typ(el(schema,'complexType',name='hoNative'+n),g['types'][n])
(ROOT/'xml/cpf5-higher-order.xsd').write_bytes(E.tostring(schema,pretty_print=True,xml_declaration=True,encoding='UTF-8'))
