theory LP_Cut_Domain_SEG_Triple_Graph
 imports LP_Cut_Domain_SEG_Triple_Split_Check
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

theorem precise_triple_component_checked_lower:
  fixes P :: "('f,string) lp_cut_program"
    and eta :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
  assumes checked: "lpc_triple_check_component fuel P triples Q roots entry component"
    and program: "lp_cut_source_program P"
    and known: "knowledge (set (lpcn_ground (lpctr_node entry))) (lpcn_guards (lpctr_node entry)) eta"
    and free: "lpc_free_knowledge (set (lpctr_free entry)) eta"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input entry) eta,b)\<in>lp_triple_calls (set triples) Q \<Longrightarrow>
      precise_triple_root_rep roots us b ret \<Longrightarrow> precise_triple_answer_contract P us Q ret"
  shows "precise_triple_answer_contract P (lpc_return_eval eta (lpc_triple_root_state entry)) Q
    (lp_atom_eval (lpctr_output entry))"
  using checked by (cases component)
    (auto intro: precise_triple_region_checked_lower[OF _ program known free lower]
      precise_triple_split_checked_lower[OF _ program known free lower])


theorem precise_triple_graph_contract:
  assumes checked: "lpc_triple_check_graph fuel P triples Q roots blocks q modes chain_pred"
    and sn: "SN_on (lp_triple_calls (set triples) Q) {a}"
    and represented: "precise_triple_root_rep roots ss a ret"
  shows "precise_triple_answer_contract P ss Q ret"
proof (rule precise_triple_answer_contract_modular[where rep="precise_triple_root_rep roots", OF sn represented])
  fix us b out
  assume rep: "precise_triple_root_rep roots us b out"
    and lower: "\<And>vs c final. (b,c)\<in>lp_triple_calls (set triples) Q \<Longrightarrow>
      precise_triple_root_rep roots vs c final \<Longrightarrow> precise_triple_answer_contract P vs Q final"
  obtain i eta where index: "i<length roots"
    and known: "knowledge (set (lpcn_ground (lpctr_node (roots!i))))
      (lpcn_guards (lpctr_node (roots!i))) eta"
    and free: "lpc_free_knowledge (set (lpctr_free (roots!i))) eta"
    and source: "us=lpc_return_eval eta (lpc_triple_root_state (roots!i))"
    and call: "b=lp_atom_eval (lpctr_input (roots!i)) eta"
    and output_atom: "out=lp_atom_eval (lpctr_output (roots!i))"
    using rep by (auto simp: precise_triple_root_rep_def)
  have local: "lpc_triple_check_component fuel P triples Q roots (roots!i) (blocks!i)"
    and program: "lp_cut_source_program P"
    using checked index by (auto simp: lpc_triple_check_graph_def list_all_iff)
  show "precise_triple_answer_contract P us Q out"
    unfolding source output_atom
    by (rule precise_triple_component_checked_lower[OF local program known free])
      (use lower in \<open>auto simp only: call\<close>)
qed


theorem precise_triple_graph_root_sound:
  fixes ts :: "('f lp_cut_symbol,string) lp_iterm list"
  assumes checked: "lpc_triple_check_graph fuel P triples Q roots blocks q modes chain_pred"
    and sn: "SN_on (lp_triple_calls (set triples) Q) {(chain_pred,ts)}"
    and len: "length ts=length modes"
    and ground: "\<forall>(t,b)\<in>set (zip ts modes). b \<longrightarrow> lp_seg_ground t"
    and domains: "list_all D ts"
  shows "SN_on (precise_source P) {[LPCGoals [LPCAtom (LPIFun (LPCUser q) ts)]]}"
proof -
  let ?entry = "roots!0"
  let ?nd = "lpctr_node ?entry"
  let ?vs = "lpcn_vars ?nd"
  let ?eta = "lp_cut_query_env ?vs ts"
  have nonempty: "roots\<noteq>[]"
    and root_check: "lp_cut_check_root q modes ?vs (lpcn_state ?nd) (lpcn_ground ?nd) (lpcn_guards ?nd)"
    and input_atom: "lpctr_input ?entry=(chain_pred,map Var ?vs)"
    and root_free: "lpctr_free ?entry=[]"
    using checked by (auto simp: lpc_triple_check_graph_def Let_def)
  have lengths: "length ?vs=length ts" and distinct: "distinct ?vs"
    using root_check len by (auto simp: lp_cut_check_root_def)
  have vals: "map ?eta ?vs=ts" by (rule lp_cut_query_env_values[OF lengths distinct])
  have finite_values: "\<forall>(t,b)\<in>set (zip (map ?eta ?vs) modes). b \<longrightarrow> lp_seg_ground t"
    using ground by (simp only: vals)
  have envD: "\<forall>x. D (?eta x)"
    by (intro allI; rule query_env_domain) (use domains in \<open>auto simp: list_all_iff\<close>)
  have known: "knowledge (set (lpcn_ground ?nd)) (lpcn_guards ?nd) ?eta"
    using root_check finite_values envD by (auto simp: lp_cut_check_root_def knowledge_def zip_map1)
  have free: "lpc_free_knowledge (set (lpctr_free ?entry)) ?eta"
    by (simp add: root_free lpc_free_knowledge_def)
  have rep: "precise_triple_root_rep roots (lpc_return_eval ?eta (lpc_triple_root_state ?entry))
      (chain_pred,ts) (lp_atom_eval (lpctr_output ?entry))"
    unfolding precise_triple_root_rep_def
    by (rule exI[of _ 0], rule exI[of _ ?eta])
      (use nonempty known free in \<open>simp add: input_atom lp_atom_eval_def vals map_map o_def\<close>)
  have contract: "precise_triple_answer_contract P (lpc_return_eval ?eta (lpc_triple_root_state ?entry)) Q
      (lp_atom_eval (lpctr_output ?entry))"
    by (rule precise_triple_graph_contract[OF checked sn rep])
  have source: "SN_on (precise_source P) {lp_cut_state_eval (lpcn_state ?nd) ?eta}"
    using precise_triple_answer_contract_SN[OF contract]
    by (simp add: lpc_return_eval_erases lpc_triple_root_state_def map_map o_def)
  show ?thesis using source root_check vals
    by (simp add: lp_cut_check_root_def lp_cut_state_map_def map_map o_def)
qed


end
end
