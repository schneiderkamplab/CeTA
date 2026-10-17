#!/usr/bin/env python3
"""Record source callers and unchanged interfaces for the retirement batch.

This is a lexical dependency audit, not a replacement for Isabelle checking.
"""
import hashlib,json,pathlib,re,subprocess
ROOT=pathlib.Path(__file__).resolve().parents[2]
BASE='1b655c5d18dbfc801e6529f4df26ed04841687d5'
MEASURE='thys/CSR_Checker/Guarded_List_Measure_Check/CSR_Guarded_List_Measure.thy'
COVER='thys/CSR_Checker/Extensions/CSR_Improved_CSDP_Proofs.thy'
NAMES=['SN_rel_min_endpoint_order','finite_conservative_csdp_coverage_imp']+[
 prefix+name+suffix for name in ['csr_guard_normal_pair_rank','csr_guard_pair_rank','csr_guard_rank']
 for prefix,suffix in [('SN_','_gt'),('SN_rel_','')]]
def sha(s):return hashlib.sha256(s.encode()).hexdigest()
def statement(source,name):
 match=re.search(r'^lemma '+re.escape(name)+r':\n(.*?)(?=^proof\b|^  using\b|^  unfolding\b|^  by\b|^  apply\b)',source,re.M|re.S)
 if not match:raise ValueError('Missing statement: '+name)
 return match.group(1)
def main():
 paths=subprocess.check_output(['git','ls-files','thys','dev','src'],cwd=ROOT,text=True).splitlines()
 sources={p:(ROOT/p).read_text(errors='surrogateescape') for p in paths if p.endswith('.thy')}
 results=[]
 for name in NAMES:
  path=COVER if name=='finite_conservative_csdp_coverage_imp' else MEASURE
  before=subprocess.check_output(['git','show',BASE+':'+path],cwd=ROOT,text=True)
  old,new=statement(before,name),statement(sources[path],name)
  assert old==new,name+' changed statement'
  references=[dict(path=p,line=i,text=line.strip()) for p,s in sources.items()
   for i,line in enumerate(s.splitlines(),1) if re.search(r'\b'+re.escape(name)+r'\b',line)]
  results.append(dict(theorem=name,path=path,statement_sha256=sha(new),unchanged_statement=True,references=references))
 # Every pre-existing non-proof declaration in the guarded theory is identical.
 old=subprocess.check_output(['git','show',BASE+':'+MEASURE],cwd=ROOT,text=True)
 def declarations(s):
  return re.findall(r'^(?:definition|fun|datatype)\b.*?(?=^(?:lemma|theorem|text|definition|fun|datatype|end)\b)',s,re.M|re.S)
 assert declarations(old)==declarations(sources[MEASURE])
 old_cover=subprocess.check_output(['git','show',BASE+':'+COVER],cwd=ROOT,text=True)
 old_formula=re.search(r'  "(finite_conservative_csdp_coverage[^\"]*)"',old_cover).group(1)
 new_formula=re.search(r'lemma finite_conservative_csdp_coverage_iff:\n  "([^\"]*)"',sources[COVER]).group(1)
 assert old_formula==new_formula,'Coverage characterization changed'
 def other_declarations(s):
  return [x for x in declarations(s) if not x.startswith('definition finite_conservative_csdp_coverage ')]
 assert other_declarations(old_cover)==other_declarations(sources[COVER])
 retained_names=['csr_min_pair_step','finite_min_csr_dpp','finite_mode_csr_dpp',
  'improved_csdp_coverage','conservative_csdp_coverage','muterm_typed_pair_step',
  'muterm_min_typed_pair_step','muterm_innermost_min_typed_pair_step',
  'muterm_i4_good_pair_step','muterm_eb_min_typed_pair_step',
  'csr_switch_overlay_innermost_termination','aaecc_innermost_termination',
  'SN_from_RFC_delete_and_absolute_residual','check_standalone_nonminimal_csr_dp',
  'check_standalone_minimal_csr_dp','check_standalone_muterm_typed_dp']
 retained=[]
 for name in retained_names:
  matches=[dict(path=p,line=s[:m.start()].count('\n')+1,source_sha256=sha(s))
   for p,s in sources.items() for m in re.finditer(r'^(?:definition|lemma|theorem) '+re.escape(name)+r'\b',s,re.M)]
  assert matches,name+' not found'
  retained.append(dict(name=name,decision='keep distinct contract',declarations=matches))
 result=dict(base_commit=subprocess.check_output(['git','rev-parse',BASE],cwd=ROOT,text=True).strip(),
  scope='Lexical references in tracked theory files; all integration builds check actual dependencies.',
  proof_implementations_replaced=results,guarded_nonproof_declarations_unchanged=True,
  retained_contracts=retained,coverage_characterization_preserves_original_formula=True,
  other_conservative_nonproof_declarations_unchanged=True,
  source_sha256={p:sha(sources[p]) for p in [MEASURE,COVER]},
  semantic_replacement=dict(name='finite_conservative_csdp_coverage',replacement='conservative_csdp_coverage with restrict_mu_to_sig F mu',equivalence='finite_conservative_csdp_coverage_iff',parser_forms_removed=[]))
 out=ROOT/'docs/consolidation/theorem-retirement-audit.json'
 out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(f'Audited {len(results)} unchanged theorem interfaces and their source references')
if __name__=='__main__':main()
