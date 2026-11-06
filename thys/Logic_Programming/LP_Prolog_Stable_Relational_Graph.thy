theory LP_Prolog_Stable_Relational_Graph
 imports LP_Prolog_Stable_Relational_Component
begin
hide_const (open) Tree_Automata_Containment.entry

definition lpp_check_stable_relational_graph where
  "lpp_check_stable_relational_graph fuel P SP D Q T (roots::string lpc_triple_root list) contexts blocks q modes chain_pred OD =
    (lp_cut_source_program P \<and> roots\<noteq>[] \<and> length blocks=length roots \<and> length contexts=length roots \<and> contexts!0=([],[],[]) \<and>
      (let entry=roots!0; nd=lpctr_node entry; vs=lpcn_vars nd in
        lp_cut_check_root q modes vs (lpcn_state nd) (lpcn_ground nd) (lpcn_guards nd) \<and>
        lpctr_free entry=[] \<and> lpctr_input entry=(chain_pred,map Var vs)) \<and>
      list_all (\<lambda>i. lpp_check_stable_relational_component fuel P SP D Q T roots contexts (contexts!i) (roots!i) OD (blocks!i))
        [0..<length roots])"

theorem lpp_stable_relational_graph_checked_contract:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_stable_relational_graph fuel P SP D Q T roots contexts blocks q modes chain_pred OD"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and sn: "SN_on (inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom) {a}"
    and represented: "lpp_stable_triple_root_rep operation SP contexts roots ss a ret"
  shows "lpp_stable_triple_answer_contract operation P ss Q ret"
proof (rule lpp_stable_triple_answer_contract_modular[where rep="lpp_stable_triple_root_rep operation SP contexts roots", OF sn represented])
  fix us b out
  assume rep: "lpp_stable_triple_root_rep operation SP contexts roots us b out"
    and lower: "\<And>vs c final. (b,c)\<in>inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom \<Longrightarrow>
      lpp_stable_triple_root_rep operation SP contexts roots vs c final \<Longrightarrow> lpp_stable_triple_answer_contract operation P vs Q final"
  obtain i eta where index: "i<length roots"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node (roots!i))))
      (lpcn_guards (lpctr_node (roots!i))) eta"
    and free: "lpc_free_knowledge (set (lpctr_free (roots!i))) eta"
    and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
    and source: "us=lpc_return_eval eta (lpc_triple_root_state (roots!i))"
    and call: "b=lp_atom_eval (lpctr_input (roots!i)) eta"
    and output_atom: "out=lp_atom_eval (lpctr_output (roots!i))"
    using rep by (auto simp: lpp_stable_triple_root_rep_def)
  have local: "lpp_check_stable_relational_component fuel P SP D Q T roots contexts (contexts!i) (roots!i) OD (blocks!i)"
    and program: "lp_cut_source_program P"
    using checked index by (auto simp: lpp_check_stable_relational_graph_def list_all_iff)
  show "lpp_stable_triple_answer_contract operation P us Q out"
    unfolding source output_atom
    by (rule lpp_stable_relational_component_checked_lower[OF compatible local program transfer observed known free])
      (use lower in \<open>auto simp only: call\<close>)
qed

theorem lpp_stable_relational_graph_root_sound:
  fixes ts :: "(string lp_cut_symbol,string) lp_iterm list"
    and SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_stable_relational_graph fuel P SP D Q T roots contexts blocks q modes chain_pred OD"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and sn: "SN_on (inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom) {(chain_pred,ts)}"
    and len: "length ts=length modes"
    and ground: "\<forall>(t,b)\<in>set (zip ts modes). b \<longrightarrow> lp_seg_ground t"
  shows "SN_on (lpp_domain_source P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) {[LPCGoals [LPCAtom (LPIFun (LPCUser q) ts)]]}"
proof -
  let ?entry = "roots!0"
  let ?nd = "lpctr_node ?entry"
  let ?vs = "lpcn_vars ?nd"
  let ?eta = "lp_cut_query_env ?vs ts"
  have nonempty: "roots\<noteq>[]"
    and root_check: "lp_cut_check_root q modes ?vs (lpcn_state ?nd) (lpcn_ground ?nd) (lpcn_guards ?nd)"
    and input_atom: "lpctr_input ?entry=(chain_pred,map Var ?vs)"
    and root_free: "lpctr_free ?entry=[]"
    and context_length: "length contexts=length roots"
    and initial_context: "contexts!0=([],[],[])"
    using checked by (auto simp: lpp_check_stable_relational_graph_def Let_def)
  have lengths: "length ?vs=length ts" and distinct: "distinct ?vs"
    using root_check len by (auto simp: lp_cut_check_root_def)
  have vals: "map ?eta ?vs=ts" by (rule lp_cut_query_env_values[OF lengths distinct])
  have finite_values: "\<forall>(t,b)\<in>set (zip (map ?eta ?vs) modes). b \<longrightarrow> lp_seg_ground t"
    using ground by (simp only: vals)
  have known: "lp_cut_knowledge (set (lpcn_ground ?nd)) (lpcn_guards ?nd) ?eta"
    using root_check finite_values by (auto simp: lp_cut_check_root_def lp_cut_knowledge_def zip_map1)
  have free: "lpc_free_knowledge (set (lpctr_free ?entry)) ?eta"
    by (simp add: root_free lpc_free_knowledge_def)
  have rep: "lpp_stable_triple_root_rep operation SP contexts roots (lpc_return_eval ?eta (lpc_triple_root_state ?entry))
      (chain_pred,ts) (lp_atom_eval (lpctr_output ?entry))"
    unfolding lpp_stable_triple_root_rep_def
    by (rule exI[of _ 0], rule exI[of _ ?eta])
      (use nonempty known free context_length initial_context in \<open>simp add: input_atom lp_atom_eval_def vals map_map o_def lpp_stable_context_holds_def lpp_evaluation_context_holds_def\<close>)
  have contract: "lpp_stable_triple_answer_contract operation P (lpc_return_eval ?eta (lpc_triple_root_state ?entry)) Q
      (lp_atom_eval (lpctr_output ?entry))"
    by (rule lpp_stable_relational_graph_checked_contract[OF compatible checked transfer sn rep])
  have source: "SN_on (lpp_domain_source P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) {lp_cut_state_eval (lpcn_state ?nd) ?eta}"
    using lpp_stable_triple_answer_contract_SN[OF contract]
    by (simp add: lpc_return_eval_erases lpc_triple_root_state_def map_map o_def)
  show ?thesis using source root_check vals
    by (simp add: lp_cut_check_root_def lp_cut_state_map_def map_map o_def)
qed



lemma lpp_stable_relational_graph_legacy:
  assumes checked: "lpp_check_finite_guarded_graph fuel P D Q T roots contexts blocks q modes chain_pred OD descents"
  shows "lpp_check_stable_relational_graph fuel P SP D Q T roots contexts
    (map (\<lambda>(component,descent). LPPSExisting component descent) (zip blocks descents))
    q modes chain_pred OD"
  using checked
  by (auto simp: lpp_check_stable_relational_graph_def lpp_check_finite_guarded_graph_def
    lpp_finite_triple_check_graph_def list_all_iff nth_map nth_zip)

ML \<open>
val checked = [@{thm lpp_stable_relational_graph_legacy}, 
  @{thm lpp_stable_relational_graph_checked_contract}, @{thm lpp_stable_relational_graph_root_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable graph dependency" else ();
\<close>
end
