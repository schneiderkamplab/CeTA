#!/usr/bin/env python3
"""Exercise source-rational NO premises using an independently built checker."""
import argparse, copy, hashlib, json, subprocess, time
from pathlib import Path
import xml.etree.ElementTree as E
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--checker',type=Path,required=True)
p.add_argument('--certificate',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
a=p.parse_args();a.output.mkdir(parents=True,exist_ok=False)
root=E.parse(a.certificate).getroot()
assert root.tag=='prologRationalSourceNonterminationProof'
cases={'positive':root}
def mutation(name,edit):
 r=copy.deepcopy(root);edit(r);cases[name]=r
mutation('missing_graph',lambda r:r.remove(r.find('graph')))
mutation('missing_anchor',lambda r:r.find('anchors').remove(r.find('anchors')[0]))
mutation('wrong_binding_anchor',lambda r:setattr(r.find('anchors')[int(r.findtext('bindingRoot'))],'text','unbound-replacement'))
mutation('dangling_edge',lambda r:setattr(r.find('graph/node/children/ref'),'text',str(len(r.find('graph')))))
mutation('missing_prefix_step',lambda r:r.find('prefix').remove(r.find('prefix')[-1]))
mutation('missing_loop_step',lambda r:r.find('loop').remove(r.find('loop')[1]))
mutation('empty_loop',lambda r:r.find('loop').clear())
mutation('wrong_call_root',lambda r:setattr(r.find('callRoot'),'text',str(len(r.find('graph')))))
mutation('missing_saved_alternative',lambda r:r.find('loop/step/state').remove(r.find('loop/step/state/clauseChoice')))
mutation('missing_matching_environment',lambda r:r.find('loop/step/resolve/environment').clear())
mutation('wrong_clash_observation',lambda r:r.find('loop/step/backtrack/repeatedVariableClash/right').clear())
mutation('wrong_source_profile',lambda r:setattr(r.find('profile'),'text','wrong'))
mutation('missing_predicates',lambda r:r.find('predicates').clear())
mutation('missing_source_clause',lambda r:r.find('program').remove(r.find('program')[-1]))
mutation('missing_prefix_pending_stack',lambda r:r.find('before').clear())
def equal_constants(r):
 leaves=[node.find('user').text for node in r.find('graph') if len(node.find('children'))==0]
 assert len(set(leaves))>=2
 old,new=leaves[1],leaves[0]
 for node in r.iter('user'):
  if node.text==old:node.text=new
mutation('successful_cut_cannot_be_skipped',equal_constants)
def fresh_body_variable(r):
 clause=r.find('program')[-1]
 vars=list(clause.find('body').iter('var'));assert vars
 vars[0].text='fresh-body-variable'
mutation('fresh_body_variable_not_in_head',fresh_body_variable)
records=[]
for name,r in cases.items():
 path=a.output/(name+'.xml');path.write_bytes(E.tostring(r,encoding='utf-8'))
 passes=[]
 for n in (1,2):
  start=time.monotonic();out=subprocess.run([str(a.checker.resolve()),'--category','prolog',str(path.resolve())],capture_output=True,text=True,timeout=30)
  (a.output/(name+f'-{n}.stdout')).write_text(out.stdout)
  (a.output/(name+f'-{n}.stderr')).write_text(out.stderr)
  accepted=out.returncode==0 and out.stdout.strip()=='CERTIFIED SOURCE-BOUND PROLOG NO'
  passes.append(dict(pass_number=n,accepted=accepted,exit_code=out.returncode,seconds=time.monotonic()-start))
 records.append(dict(name=name,expected=name=='positive',sha256=hashlib.sha256(path.read_bytes()).hexdigest(),checks=passes))
report=dict(schema='ceta.prolog-rational-no-mutations.v1',checker_sha256=hashlib.sha256(a.checker.read_bytes()).hexdigest(),source_certificate_sha256=hashlib.sha256(a.certificate.read_bytes()).hexdigest(),cases=records)
(a.output/'result.json').write_text(json.dumps(report,indent=2)+'\n')
assert all(all(p['accepted']==r['expected'] for p in r['checks']) for r in records)
print(f'{len(records)} cases checked twice')
