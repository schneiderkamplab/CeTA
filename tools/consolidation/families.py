#!/usr/bin/env python3
"""Review-level family classification. No semantic equivalence is inferred."""
import json,pathlib
ROOT=pathlib.Path(__file__).resolve().parents[2]; OUT=ROOT/'docs/consolidation'
# Ordered selectors; every remaining theory is explicitly deferred.
FAMILIES=[
 ('standalone_csr','compatibility adapter','keep',['CSR_Standalone_DP_Checker'],['CSR minimality distinct from ordinary DP M','exact unhiding B for typed MU-TERM','marked replacement-map equality','source well-formedness and freshness']),
 ('standalone_gm04','compatibility adapter','keep',['GM04_Standalone'],['one unconditional DP assumption','explicit source CSR child','Q normal-form equivalence','global proof for extended signature']),
 ('gm04','general theorem plus special-case corollaries candidate','keep',['GM04_','CSR_GM_Transformation'],['full versus complete schema','sanitizing phase','administrative role freshness','signature and Q restrictions','terminal versus residual']),
 ('relative_adp','semantically necessary','keep',['Relative_ADP','Finite_Branching_Dichotomy'],['main/base ADPs and annotations','fixed selected witness and VRF','exact graph child family','erasure versus Com laws','DRP1 flat base']),
 ('outermost','semantically necessary','defer restructuring',['Outermost_'],['quasi-left-linearity','fresh grounding and automaton marker','exact flat-map coverage','non-redex pattern validity','automaton cover']),
 ('rfc','semantically necessary criteria with refinement candidates','keep',['RFC_','Matchbounds_Impl'],['initial language','automaton closure','right-linearity','relative versus absolute residual','terminal versus recursive deletion']),
 ('rule_strengthening','general theorem plus SRS application','keep',['Rule_Strengthening'],['empty Q','no weak rules','one rewrite step per original rule']),
 ('qdp_to_srs','semantically necessary specialized transformation','keep',['QDP_To_SRS'],['empty Pw Q R Rw','productive or transfer pair shapes','arbitrary nfs and minimality']),
 ('switch','general theorem plus special-case corollaries candidate','defer equivalence',['Switch'],['full/innermost source strategy','Q preservation','residual context']),
 ('guarded','general theorem plus special-case corollaries candidate','unify only after proof',['Guarded_List'],['guard truth and backwards closure','measure obligations','root terminal versus nested improved DP']),
 ('labeling','semantically necessary representations','keep',['Semantic_Labeling'],['finite versus ordinary representation','model obligations','signature/map preservation']),
 ('usable','executable optimization with distinct semantic criteria','unify only after refinement',['Usable'],['full versus innermost','ambient R preservation','closure and conservative premises','collapsing pair bridges']),
 ('typed_muterm','semantically necessary','keep',['Muterm_Typed','Muterm_Extended','Muterm_Innermost'],['typed minimal chains','exact unhiding','marked map','recursive order domain']),
 ('innermost_unhiding','semantically necessary pending equivalence','defer restructuring',['Innermost_Unhiding','Innermost_DP'],['collapsing and hidden pairs','active positions','projection and marking','full versus innermost']),
 ('csr_subterm_sct','semantically necessary criteria','keep',['Subterm','Active_SCT'],['frozen/hybrid/mixed positions','active SCT','minimality','recursive graph context']),
 ('minimal_improved','semantically necessary criteria','keep',['Minimal_CSDP','Improved_CSDP','Conservative_Checker'],['minimal versus nonminimal','RTA08 versus improved construction','fresh unhiding symbol','QCS usable-rule closure']),
 ('csr_core','semantically necessary','keep',['CSR_Checker','CSR_Check_Loops'],['map preservation','root versus nested','graph child completeness','nontermination versus termination']),
 ('ordinary_checkers','semantically necessary criteria','keep',['Check_Termination','Check_Nontermination','Check_AC_Termination','Check_CRP','Check_Completion','Check_Complexity','Check_Quasi_Reductive'],['ordinary and relative Q contexts','terminal versus residual','acceptance and rejection modes','preserve existing integration behavior']),
 ('integration','compatibility adapter','keep',['Proof_Checker','CPF_','Ceta_Problem_Spec','Code_CSR'],['input meaning','unknown nodes are errors','assumptions explicitly discharged','CLI behavior']),
]
def main():
 inv=json.loads((OUT/'source-inventory.json').read_text());families=[]
 for fid,classification,decision,selectors,obligations in FAMILIES:
  families.append(dict(id=fid,classification=classification,decision=decision,selectors=selectors,obligations=obligations,theory_variants=[],eligible_positive_proofs=[],validated_rejection_tests=[],coverage_status='gap: not yet mapped and measured'))
 families.append(dict(id='unclassified',classification='unresolved development implementation',decision='defer',selectors=[],obligations=['manual semantics and caller assessment'],theory_variants=[],eligible_positive_proofs=[],validated_rejection_tests=[],coverage_status='gap: unclassified'))
 for v in inv['variants']:
  stem=pathlib.Path(v['path']).stem
  fam=next((f for f in families[:-1] if any(s in stem for s in f['selectors'])),families[-1])
  fam['theory_variants'].append(dict(path=v['path'],blob=v['blob'],checker_candidates=[x['name'] for x in v['checker_candidates']],supporting_theorem_candidates=[x['name'] for x in v['soundness_candidates']],parser_tags_lexical=v['xml_tags_lexical'],generated_module=v['generated_module']))
 data=dict(schema_version=1,status='review proposal only',mapping_method='Filename selectors classify review families only. Declaration and parser links are lexical candidates; no accepted proof or runtime branch is inferred.',required_modes=['root','nested','standalone','full','innermost','CSR','relative','SRS','minimal','nonminimal','empty/nonempty/reduced P Q R','map preservation','terminal','residual','recursive composition','order domain','certificate representation','signature restriction'],families=families)
 (OUT/'families.json').write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
 print(json.dumps({f['id']:len(f['theory_variants']) for f in families}))
if __name__=='__main__':main()
