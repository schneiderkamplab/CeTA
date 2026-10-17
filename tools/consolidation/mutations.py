#!/usr/bin/env python3
"""Semantic rejection probes derived from real selected positive certificates.
Transformation pairs, graph children, usable closure and automaton-state
obligations are handled here; other side conditions remain explicit gaps.
"""
import argparse,copy,hashlib,json,os,pathlib,re,xml.etree.ElementTree as ET
from replay import ROOT,CORPUS,SNAP,execute,sha,write
CASES=[
 ('gm04-innermost-freshness-collision','.//gm04CompleteTransformation',r'GM04 administrative symbols are not fresh'),
 ('gm04-full-freshness-collision','.//gm04CompleteFullTransformation',r'GM04 administrative symbols are not fresh'),
 ('omitted-dp-pairs','.//dpTrans/dps/rules',r'the DP .*does not appear in the DP problem'),
 ('omitted-csr-pairs','.//csrImprovedDependencyPairs/dps/rules',r'missing replacement-map dependency pair'),
 ('omitted-graph-components','.//depGraphProc',r'(?:Dependency Pair|CSR dependency pair).*is missing in decomposition'),
 ('omitted-usable-rules','.//usableRulesProc/usableRules/rules',r'is not closed under usable rules'),
 ('omitted-automaton-transitions','.//trsTerminationProof/bounds/treeAutomaton/transitions',r'did not find mentioned final state in TA'),
 ('omitted-rfc-automaton-transitions','.//rfcMatchboxRelativeBounds/bounds/treeAutomaton/transitions',r'RFC Matchbox-relative tail states must occur as automaton right-hand-side states'),
 ('zero-polynomial-offsets','.//ruleRemoval/interpretation',r'problem when orienting TRS.*could not ensure'),
 ('zero-matrix-monotonicity','.//ruleRemoval/interpretation',r'problem with monotonicity.*problem in ensuring monotonicity of strict relation')]
def main():
 p=argparse.ArgumentParser();p.add_argument('--stage',required=True);p.add_argument('--output',type=pathlib.Path);p.add_argument('--kinds',nargs='+');p.add_argument('--checker',type=pathlib.Path,default=SNAP/'artifacts/production_checker');a=p.parse_args();stage=CORPUS/a.stage;selected=json.loads((stage/'selection.json').read_text())['selected_ids'];out=(a.output or stage/'negatives').resolve();out.mkdir(exist_ok=False);results=[];skipped=[]
 for rid in selected:
  proof=stage/rid/'proof.cpf.xml';positive=json.loads((stage/rid/'result.json').read_text())
  if positive['expected_answer']!='yes' or proof.stat().st_size>10_000_000:
   skipped.append(dict(source_id=rid,reason='Nontermination mutation semantics not implemented' if positive['expected_answer']!='yes' else 'Streaming mutation implementation needed for this large proof',bytes=proof.stat().st_size));continue
  for kind,xpath,diagnostic in CASES:
   if a.kinds and kind not in a.kinds:continue
   tree=ET.parse(proof);node=tree.getroot().find(xpath)
   if node is None or not len(node):continue
   criterion=None
   if kind=='omitted-usable-rules':
    parents={c:p for p in tree.getroot().iter() for c in p};cursor=node;ancestors=[]
    while cursor in parents:cursor=parents[cursor];ancestors.append(cursor.tag)
    wrapper=next((t for t in ancestors if t in {'dpProof','csrDpProof','csrMutermTypedDpProof'}),None)
    if wrapper=='csrDpProof' and any(t in ancestors for t in {'csrImprovedDependencyPairs','csrRuleRemovalsThenImproved'}):
     kind='omitted-improved-qcs-usable-rules';diagnostic=r'error when checking improved QCS usable-rule closure';criterion=dict(checker='csr_improved_qcs_usable_rules_proc',theorem='csr_improved_qcs_usable_rules_proc_sound',theory='thys/CSR_Checker/Extensions/CSR_Conservative_Checker.thy',violated_condition='improved_qcs_csr_ur_closed_check')
    elif wrapper=='csrDpProof' and 'csrDependencyPairs' in ancestors:
     kind='omitted-qcs-usable-rules';diagnostic=r'error when checking QCS usable-rule closure';criterion=dict(checker='csr_qcs_usable_rules_proc',theorem='csr_qcs_usable_rules_proc_sound',theory='thys/CSR_Checker/Extensions/CSR_Minimal_CSDP_Proofs.thy',violated_condition='qcs_csr_ur_closed_check')
   if kind=='omitted-graph-components' and not all(c.tag=='component' for c in node):continue
   if kind in {'zero-polynomial-offsets','zero-matrix-monotonicity'}:
    removed_rules=tree.getroot().find('.//ruleRemoval/trs/rules')
    if removed_rules is None or not len(removed_rules):continue
   if kind.endswith('freshness-collision'):
    active=node.find('activeSymbol');mark=node.find('markSymbol')
    if active is None or mark is None:continue
    active.clear()
    for child in mark:active.append(copy.deepcopy(child))
    removed=0
    criterion=dict(checker='check_gm04_complete_transformation_proof',theorem='check_gm04_complete_transformation_proof_sound',theory='thys/Proof_Checker/GM04_Complete_Checker.thy',violated_condition='gm04_roles_fresh_list',explanation='Distinct administrative roles active and mark are identified; freshness is a required premise before either constructor can certify.')
   elif kind=='zero-polynomial-offsets':
    if node.find('type/polynomial/domain/naturals') is None:continue
    integers=node.findall('interpret//integer')
    # Preserve all unit variable coefficients: only direct affine offsets are
    # changed, so the intended failure is strict orientation, not monotonicity.
    offsets=node.findall('interpret/sum/integer')
    if not integers or set(integers)!=set(offsets) or node.findall('interpret//product'):continue
    removed=sum((n.text or '').strip()!='0' for n in integers)
    if not removed:continue
    for n in integers:n.text='0'
   elif kind=='zero-matrix-monotonicity':
    if node.find('type/matrixInterpretation') is None:continue
    if not any(int(n.findtext('arity','0'))>0 for n in node.findall('interpret')):continue
    integers=node.findall('interpret//integer');removed=sum((n.text or '').strip()!='0' for n in integers)
    if not removed:continue
    for n in integers:n.text='0'
   else:removed=len(node);node.clear()
   run=out/(rid+'-'+kind);run.mkdir();dest=run/'proof.cpf.xml';tree.write(dest,encoding='utf-8',xml_declaration=True);ET.parse(dest)
   # The original input is unchanged: only proof-side data is changed.
   assert ET.tostring(tree.getroot().find('input'))==ET.tostring(ET.parse(proof).getroot().find('input'))
   record=dict(id=run.name,source_id=rid,source_sha256=sha(proof),mutation_sha256=sha(dest),kind=kind,xpath=xpath,removed_obligations=removed,expected_diagnostic_regex=diagnostic,well_formed_xml=True,checks=[],validated=False)
   if criterion:record['criterion']=criterion
   for i in [1,2]:
    prefix=run/f'check-{i}';c=execute([str(a.checker.resolve()),str(dest)],run,os.environ,prefix,120)
    text=prefix.with_suffix('.stdout').read_text()+prefix.with_suffix('.stderr').read_text();c['semantic_rejection']=c['returncode']==1 and not c['timed_out'] and text.startswith('REJECTED') and bool(re.search(diagnostic,text,re.S|re.I));record['checks'].append(c)
   record['validated']=all(c['semantic_rejection'] for c in record['checks']);write(run/'result.json',record);results.append(record)
 write(out/'manifest.json',dict(mutations=results,skipped_sources=skipped,selected_sources_without_mutations=sorted(set(selected)-{r['source_id'] for r in results}),gaps=['map/Q preservation','mode-specific usable rules','minimality','freshness beyond GM04 administrative-role collisions','order obligations beyond the listed polynomial/matrix cases','automaton closure and coverage beyond final-state validity'],scope='Only listed mutations whose intended semantic diagnostics are confirmed count as negative coverage.'))
 print(json.dumps(dict(generated=len(results),validated=sum(r['validated'] for r in results))));raise SystemExit(any(not r['validated'] for r in results))
if __name__=='__main__':main()
