"""Check structural schema inheritance, not executable checker completeness.

Every old global declaration must remain, with only choice alternatives,
optional sequence members or widened occurrence bounds added. Named types can
replace inline complex types. Other changes fail closed for manual review.
"""
from pathlib import Path
import copy
import unittest
from lxml import etree as E
ROOT=Path(__file__).resolve().parents[1]/'xml'
XS='{http://www.w3.org/2001/XMLSchema}'

def declarations(path,seen=None):
    seen=set() if seen is None else seen
    path=path.resolve()
    if path in seen:return {}
    seen.add(path);result={}
    tree=E.parse(str(path),E.XMLParser(remove_blank_text=True,remove_comments=True))
    for node in tree.getroot():
        if node.tag==XS+'include':
            result.update(declarations(path.parent/node.get('schemaLocation'),seen))
        elif node.get('name'):
            key=(node.tag,node.get('name'))
            assert key not in result,('duplicate declaration',key)
            result[key]=node
    return result

def body(node,decls):
    node=copy.deepcopy(node)
    # Resolve a named complex type only at its use, leaving element identity.
    typ=node.get('type')
    if typ and (XS+'complexType',typ) in decls:
        del node.attrib['type']
        child=copy.deepcopy(decls[(XS+'complexType',typ)])
        child.attrib.pop('name',None);node.append(child)
    return node

def children(node):
    return [n for n in node if n.tag!=XS+'annotation']

def bound(value):return float('inf') if value=='unbounded' else int(value)

def extends(old,new,older,newer,path=''):
    if old.get("type") != new.get("type"):
        old,new=body(old,older),body(new,newer)
    here=path+'/'+old.tag.removeprefix(XS)+':'+(old.get('name') or old.get('ref') or '')
    assert old.tag==new.tag,(here,'kind changed')
    oa,na=dict(old.attrib),dict(new.attrib)
    for key,default,relation in [('minOccurs','1',lambda a,b:b<=a),('maxOccurs','1',lambda a,b:b>=a)]:
        a,b=bound(oa.pop(key,default)),bound(na.pop(key,default))
        assert relation(a,b),(here,key,a,b)
    assert oa==na,(here,'attributes',oa,na)
    oc,nc=children(old),children(new)
    if old.tag==XS+'choice':
        for a in oc:
            errors=[]
            for b in nc:
                try:extends(a,b,older,newer,here);break
                except AssertionError as e:errors.append(str(e))
            else:raise AssertionError((here,'missing or narrowed choice',a.attrib,errors[:2]))
    elif old.tag==XS+'sequence':
        j=0
        for a in oc:
            while j<len(nc):
                b=nc[j];j+=1
                try:extends(a,b,older,newer,here);break
                except AssertionError:
                    if b.get('minOccurs','1')!='0':raise
            else:raise AssertionError((here,'missing sequence member',a.attrib))
        assert all(n.get('minOccurs','1')=='0' for n in nc[j:]),(here,'new required sequence members')
    else:
        assert len(oc)==len(nc),(here,'structure changed',len(oc),len(nc))
        for a,b in zip(oc,nc):extends(a,b,older,newer,here)

class Inheritance(unittest.TestCase):
    def test_rejects_narrowing(self):
        def node(body):return E.fromstring(('<xs:sequence xmlns:xs="http://www.w3.org/2001/XMLSchema">'+body+'</xs:sequence>').encode())
        old=node('<xs:element name="old" minOccurs="0" maxOccurs="unbounded"/>')
        for narrowed in ['<xs:element name="old" minOccurs="1" maxOccurs="unbounded"/>',
                         '<xs:element name="old" minOccurs="0" maxOccurs="1"/>',
                         '<xs:element name="new" minOccurs="0" maxOccurs="unbounded"/>',
                         '<xs:element name="old" minOccurs="0" maxOccurs="unbounded"/><xs:element name="required"/>']:
            with self.assertRaises(AssertionError):extends(old,node(narrowed),{},{})
        extends(old,node('<xs:element name="optional" minOccurs="0"/><xs:element name="old" minOccurs="0" maxOccurs="unbounded"/>'),{},{})

    def test_schemas_compile(self):
        for version in [3,4,5,6]:E.XMLSchema(E.parse(str(ROOT/f'cpf{version}.xsd')))

    def test_version_chain(self):
        for previous,current in [(3,4),(4,5),(5,6)]:
            old_root=E.parse(str(ROOT/f'cpf{previous}.xsd')).getroot()
            new_root=E.parse(str(ROOT/f'cpf{current}.xsd')).getroot()
            self.assertEqual({k:v for k,v in old_root.attrib.items() if k!='version'},
                             {k:v for k,v in new_root.attrib.items() if k!='version'})
            older,newer=declarations(ROOT/f'cpf{previous}.xsd'),declarations(ROOT/f'cpf{current}.xsd')
            for key,old in older.items():
                with self.subTest(previous=previous,current=current,declaration=key[1]):
                    self.assertIn(key,newer)
                    extends(old,newer[key],older,newer)

if __name__=='__main__':unittest.main()
