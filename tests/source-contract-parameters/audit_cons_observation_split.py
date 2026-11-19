"""Check actual retained cons shadow decomposition and child routing."""
import copy
import hashlib
import json
from pathlib import Path
import xml.etree.ElementTree as ET
ROOT=Path(__file__).resolve().parents[3]/'ferrum-prolog-release/target'
rename_path=ROOT/'checkpoint-full-residual-renamed-20261118/transformation.json'
reverse={v:k for k,v in json.loads(rename_path.read_text())['symbols'].items()}

def name(e,renamed):
    raw=e.findtext('name'); parts=raw.split('_'); assert len(parts)==4
    text=bytes.fromhex(parts[2]).decode()
    if renamed:text=reverse[text]
    if text.startswith('__prolog_symbol_'):text=bytes.fromhex(text[len('__prolog_symbol_'):]).decode()
    return text,int(parts[3])

def args(e):return list(e)[1:]
def var(e):assert e.tag=='var';return e.text

def check(c,renamed,arity):
    h=c.find('head/funapp'); body=c.find('body');assert len(body)==1
    b=body[0]; hs,bs=args(h),args(b);half=arity//2;targethalf=half+2
    assert len(hs)==arity and len(bs)==arity+4
    tree=hs[half]
    assert name(tree,renamed)==('\0prolog.structure.node',2) and len(args(tree))==2
    label,spine=args(tree)
    assert name(label,renamed)==('\0prolog.structure.label:2:prolog_data_2e',0) and len(args(label))==0
    assert name(spine,renamed)==('\0prolog.structure.cons',2) and len(args(spine))==2
    head,tailcell=args(spine)
    assert name(tailcell,renamed)==('\0prolog.structure.cons',2) and len(args(tailcell))==2
    tail,nil=args(tailcell)
    assert name(nil,renamed)==('\0prolog.structure.nil',0) and len(args(nil))==0
    assert var(head)!=var(tail)
    assert var(bs[targethalf])==var(head) and var(bs[targethalf+3])==var(tail)
    assert var(bs[targethalf+1])==var(hs[half+1]) and var(bs[targethalf+4])==var(hs[half+2])
    assert var(bs[targethalf+2]) not in [var(head),var(tail),var(hs[half+1]),var(hs[half+2])]

records=[]
for variant,path in [('original',ROOT/'checkpoint-full-residual-20261118/child.xml'),('renamed',ROOT/'checkpoint-full-residual-renamed-20261118/result/child.xml')]:
    renamed=variant=='renamed'; root=ET.parse(path).getroot()
    for row,arity in [('seg_region_0_23',10),('seg_region_35_3',6)]:
        found=[(i,c) for i,c in enumerate(root.find('program')) if name(c.find('head/funapp'),renamed)==(row,arity) and args(c.find('head/funapp'))[arity//2].tag=='funapp']
        assert len(found)==1;i,c=found[0];check(c,renamed,arity)
        mutations=[]
        for change in ['wrong_label','missing_nil','swapped_children','wrong_child_route','missing_child']:
            bad=copy.deepcopy(c);hs=args(bad.find('head/funapp'));bs=args(bad.find('body')[0]);tree=hs[arity//2];label,spine=args(tree);head,cell=args(spine);tail,nil=args(cell)
            if change=='wrong_label':label.find('name').text=tree.findtext('name')
            elif change=='missing_nil':cell.remove(nil)
            elif change=='swapped_children':head.text,tail.text=tail.text,head.text
            elif change=='wrong_child_route':bs[arity//2+2].text=bs[arity//2+5].text
            else:bad.find('body')[0].remove(bs[-1])
            try:check(bad,renamed,arity)
            except (AssertionError,ValueError,IndexError,AttributeError,KeyError):mutations.append(change)
            else:raise AssertionError(change)
        records.append(dict(variant=variant,row=row,clause=i,rejected=mutations,artifact=str(path),sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
print(json.dumps(dict(scope='Cons shadow decomposition and child routing only; full residual step remains open',records=records),indent=2))
