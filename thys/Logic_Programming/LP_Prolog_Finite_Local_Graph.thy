theory LP_Prolog_Finite_Local_Graph
 imports LP_Prolog_Finite_Local_Component
begin

theorem lpp_finite_local_graph_checked_contract:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_finite_local_graph A fuel P D Q T roots contexts blocks q modes chain_pred OD descents"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and sn: "SN_on (inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom) {a}"
    and finite: "lpp_finite_direct_invariant A ss"
    and represented: "lpp_stable_triple_root_rep operation SP contexts roots ss a ret"
  shows "lpp_stable_triple_answer_contract operation P ss Q ret"
proof (rule lpp_stable_triple_answer_contract_modular[where rep="\<lambda>us b out. lpp_stable_triple_root_rep operation SP contexts roots us b out \<and> lpp_finite_direct_invariant A us", OF sn conjI[OF represented finite]])
  fix us b out
  assume rep: "lpp_stable_triple_root_rep operation SP contexts roots us b out \<and> lpp_finite_direct_invariant A us"
    and lower: "\<And>vs c final. (b,c)\<in>inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom \<Longrightarrow>
      lpp_stable_triple_root_rep operation SP contexts roots vs c final \<and> lpp_finite_direct_invariant A vs \<Longrightarrow> lpp_stable_triple_answer_contract operation P vs Q final"
  obtain i eta where index: "i<length roots"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node (roots!i))))
      (lpcn_guards (lpctr_node (roots!i))) eta"
    and free: "lpc_free_knowledge (set (lpctr_free (roots!i))) eta"
    and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
    and source: "us=lpc_return_eval eta (lpc_triple_root_state (roots!i))"
    and call: "b=lp_atom_eval (lpctr_input (roots!i)) eta"
    and output_atom: "out=lp_atom_eval (lpctr_output (roots!i))"
    using rep by (auto simp: lpp_stable_triple_root_rep_def)
  have local: "lpp_check_finite_local_component A fuel P D Q T roots contexts (contexts!i) (roots!i) (blocks!i)"
    and descent: "lpp_check_finite_component_descent OD roots (contexts!i) (roots!i) (blocks!i) (descents!i)"
    and program: "lp_cut_source_program P"
    and signature: "\<And>f n. (f,n)\<in>A \<Longrightarrow> (f,n)\<in>lpp_builtin_signature \<Longrightarrow> lpp_direct_arithmetic_name f"
    using checked index by (auto simp: lpp_check_finite_local_graph_def list_all_iff)
  show "lpp_stable_triple_answer_contract operation P us Q out"
    unfolding source output_atom
    by (rule lpp_finite_local_component_checked_lower[OF compatible local descent program transfer observed known free _ signature])
      (use rep lower in \<open>auto simp only: source call\<close>)
qed

theorem lpp_finite_local_graph_root_sound:
  fixes ts :: "(string lp_cut_symbol,string) lp_iterm list"
    and SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_finite_local_graph A fuel P D Q T roots contexts blocks q modes chain_pred OD descents"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and sn: "SN_on (inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom) {(chain_pred,ts)}"
    and finite: "list_all lpp_finite_term ts"
    and len: "length ts=length modes"
    and ground: "\<forall>(t,b)\<in>set (zip ts modes). b \<longrightarrow> lp_seg_ground t"
  shows "SN_on (lpp_domain_source P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) {[LPCGoals [LPCAtom (LPIFun (LPCUser q) ts)]]}"
proof -
  let ?entry = "roots!0"
  let ?nd = "lpctr_node ?entry"
  let ?vs = "lpcn_vars ?nd"
  let ?eta = "lp_cut_query_env ?vs ts"
  have nonempty: "roots\<noteq>[]"
    and signature: "(q,length modes)\<in>A"
    and root_check: "lp_cut_check_root q modes ?vs (lpcn_state ?nd) (lpcn_ground ?nd) (lpcn_guards ?nd)"
    and input_atom: "lpctr_input ?entry=(chain_pred,map Var ?vs)"
    and root_free: "lpctr_free ?entry=[]"
    and context_length: "length contexts=length roots"
    and initial_context: "contexts!0=([],[],[])"
    using checked by (auto simp: lpp_check_finite_local_graph_def Let_def)
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
  have initial: "lpp_finite_direct_invariant A (lpc_return_eval ?eta (lpc_triple_root_state ?entry))"
    using finite signature len root_check
    by (simp add: lpc_triple_root_state_def lp_cut_check_root_def lpc_return_eval_def
      map_map o_def vals lpp_finite_direct_invariant_def lpp_finite_direct_state_def lpp_static_state_def)
  have contract: "lpp_stable_triple_answer_contract operation P (lpc_return_eval ?eta (lpc_triple_root_state ?entry)) Q
      (lp_atom_eval (lpctr_output ?entry))"
    by (rule lpp_finite_local_graph_checked_contract[OF compatible checked transfer sn initial rep])
  have source: "SN_on (lpp_domain_source P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) {lp_cut_state_eval (lpcn_state ?nd) ?eta}"
    using lpp_stable_triple_answer_contract_SN[OF contract]
    by (simp add: lpc_return_eval_erases lpc_triple_root_state_def map_map o_def)
  show ?thesis using source root_check vals
    by (simp add: lp_cut_check_root_def lp_cut_state_map_def map_map o_def)
qed


ML \<open>
val checked = [@{thm lpp_finite_local_graph_checked_contract}, @{thm lpp_finite_local_graph_root_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable graph dependency" else ();
\<close>
end
