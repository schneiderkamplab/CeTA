#!/usr/bin/env python3
"""Semantic rejection probes derived from real selected positive certificates.
Transformation pairs, graph children, usable closure and automaton-state
obligations are handled here; other side conditions remain explicit gaps.
"""
import argparse,hashlib,json,os,pathlib,re,xml.etree.ElementTree as ET
from replay import ROOT,CORPUS,SNAP,execute,sha,write
CASES=[
 ('omitted-dp-pairs','.//dpTrans/dps/rules',r'the DP .*does not appear in the DP problem'),
 ('omitted-csr-pairs','.//csrImprovedDependencyPairs/dps/rules',r'missing replacement-map dependency pair'),
 ('omitted-graph-components','.//depGraphProc',r'(?:Dependency Pair|CSR dependency pair).*is missing in decomposition'),
 ('omitted-usable-rules','.//usableRulesProc/usableRules/rules',r'is not closed under usable rules'),
 ('omitted-automaton-transitions','.//trsTerminationProof/bounds/treeAutomaton/transitions',r'did not find mentioned final state in TA'),
 ('omitted-rfc-automaton-transitions','.//rfcMatchboxRelativeBounds/bounds/treeAutomaton/transitions',r'RFC Matchbox-relative tail states must occur as automaton right-hand-side states')]
def main():
 p=argparse.ArgumentParser();p.add_argument('--stage',required=True);a=p.parse_args();stage=CORPUS/a.stage;selected=json.loads((stage/'selection.json').read_text())['selected_ids'];out=stage/'negatives';out.mkdir(exist_ok=False);results=[]
 for rid in selected:
  proof=stage/rid/'proof.cpf.xml';positive=json.loads((stage/rid/'result.json').read_text())
  if positive['expected_answer']!='yes' or proof.stat().st_size>10_000_000:continue
  for kind,xpath,diagnostic in CASES:
   tree=ET.parse(proof);node=tree.getroot().find(xpath)
   if node is None or not len(node):continue
   if kind=='omitted-graph-components' and not all(c.tag=='component' for c in node):continue
   run=out/(rid+'-'+kind);run.mkdir();removed=len(node);node.clear();dest=run/'proof.cpf.xml';tree.write(dest,encoding='utf-8',xml_declaration=True);ET.parse(dest)
   # The original input is unchanged: only proof obligations are removed.
   assert ET.tostring(tree.getroot().find('input'))==ET.tostring(ET.parse(proof).getroot().find('input'))
   record=dict(id=run.name,source_id=rid,source_sha256=sha(proof),mutation_sha256=sha(dest),kind=kind,xpath=xpath,removed_obligations=removed,expected_diagnostic_regex=diagnostic,well_formed_xml=True,checks=[],validated=False)
   for i in [1,2]:
    prefix=run/f'check-{i}';c=execute([str(SNAP/'artifacts/production_checker'),str(dest)],run,os.environ,prefix,120)
    text=prefix.with_suffix('.stdout').read_text()+prefix.with_suffix('.stderr').read_text();c['semantic_rejection']=c['returncode']==1 and not c['timed_out'] and text.startswith('REJECTED') and bool(re.search(diagnostic,text,re.S|re.I));record['checks'].append(c)
   record['validated']=all(c['semantic_rejection'] for c in record['checks']);write(run/'result.json',record);results.append(record)
 write(out/'manifest.json',dict(mutations=results,gaps=['map/Q preservation','mode-specific usable rules','minimality','freshness','order obligations','automaton closure and coverage beyond final-state validity'],scope='Only listed mutations whose intended semantic diagnostics are confirmed count as negative coverage.'))
 print(json.dumps(dict(generated=len(results),validated=sum(r['validated'] for r in results))));raise SystemExit(any(not r['validated'] for r in results))
if __name__=='__main__':main()
