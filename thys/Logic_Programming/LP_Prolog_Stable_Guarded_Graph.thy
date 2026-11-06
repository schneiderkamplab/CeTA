theory LP_Prolog_Stable_Guarded_Graph
 imports LP_Prolog_Stable_Guarded_Split_Descent LP_Prolog_Finite_Guarded_Graph
begin
hide_const (open) Tree_Automata_Containment.entry

theorem lpp_stable_guarded_component_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_finite_triple_check_component fuel P D Q T roots contexts incoming entry component"
    and descent: "lpp_check_finite_component_descent OD roots incoming entry component evidence"
    and program: "lp_cut_source_program P"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and observed: "lpp_stable_context_holds operation SP incoming eta"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node entry))) (lpcn_guards (lpctr_node entry)) eta"
    and free: "lpc_free_knowledge (set (lpctr_free entry)) eta"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input entry) eta,b)\<in>
        inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom \<Longrightarrow>
      lpp_stable_triple_root_rep operation SP contexts roots us b ret \<Longrightarrow> lpp_stable_triple_answer_contract operation P us Q ret"
  shows "lpp_stable_triple_answer_contract operation P (lpc_return_eval eta (lpc_triple_root_state entry)) Q
    (lp_atom_eval (lpctr_output entry))"
proof (cases component)
  case (LPPFTRegion region)
  obtain connections where shape: "evidence=LPPFGRegion connections"
    using descent by (cases evidence) (auto simp: LPPFTRegion)
  have local: "lpp_finite_triple_check_region fuel P D Q T roots contexts incoming entry region"
    and guarded: "lpp_check_finite_guarded_region_descent OD roots entry region connections"
    using checked descent by (simp_all add: LPPFTRegion shape)
  show ?thesis by (rule lpp_stable_guarded_region_checked_lower[OF compatible local guarded program transfer observed known free lower])
next
  case (LPPFTSplit ft st receipt)
  obtain first_call second_call where shape: "evidence=LPPFGSplit first_call second_call"
    using descent by (cases evidence) (auto simp: LPPFTSplit)
  have local: "lpp_finite_triple_check_preserved_split T ft st fuel D Q roots contexts incoming entry receipt"
    and guarded: "lpp_check_finite_guarded_split_descent OD incoming (incoming) entry receipt first_call second_call"
    using checked descent by (simp_all add: LPPFTSplit shape)
  have first: "(lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_first_in receipt) eta)\<in>
      inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom"
    by (rule lpp_stable_guarded_split_first_descent[OF guarded observed])
  show ?thesis by (rule lpp_stable_guarded_preserved_split_checked_lower[OF compatible transfer local program known observed free first _ lower])
    (use lpp_stable_guarded_split_return_descent[OF guarded] in blast)
next
  case (LPPFTIntegerSplit ft st receipt return_evidence)
  obtain first_call second_call where shape: "evidence=LPPFGSplit first_call second_call"
    using descent by (cases evidence) (auto simp: LPPFTIntegerSplit)
  have local: "lpp_finite_triple_check_integer_split T ft st fuel P D Q roots contexts incoming entry receipt return_evidence"
    and guarded: "lpp_check_finite_guarded_split_descent OD incoming (lpp_context_add_integers incoming (lppsir_integers return_evidence)) entry receipt first_call second_call"
    using checked descent by (simp_all add: LPPFTIntegerSplit shape)
  have first: "(lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_first_in receipt) eta)\<in>
      inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom"
    by (rule lpp_stable_guarded_split_first_descent[OF guarded observed])
  show ?thesis by (rule lpp_stable_guarded_integer_split_checked_lower[OF compatible transfer local program known observed free first _ lower])
    (use lpp_stable_guarded_split_return_descent[OF guarded] in blast)
next
  case (LPPFTGroundSplit ft st receipt return_evidence)
  obtain first_call second_call where shape: "evidence=LPPFGSplit first_call second_call"
    using descent by (cases evidence) (auto simp: LPPFTGroundSplit)
  have local: "lpp_finite_triple_check_ground_split T ft st fuel P D Q roots contexts incoming entry receipt return_evidence"
    and guarded: "lpp_check_finite_guarded_split_descent OD incoming (lpp_context_add_ground incoming (lppsgr_ground return_evidence)) entry receipt first_call second_call"
    using checked descent by (simp_all add: LPPFTGroundSplit shape)
  have first: "(lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_first_in receipt) eta)\<in>
      inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom"
    by (rule lpp_stable_guarded_split_first_descent[OF guarded observed])
  show ?thesis by (rule lpp_stable_guarded_ground_split_checked_lower[OF compatible transfer local program known observed free first _ lower])
    (use lpp_stable_guarded_split_return_descent[OF guarded] in blast)
next
  case (LPPFTShapeSplit ft st receipt return_evidence)
  obtain first_call second_call where shape: "evidence=LPPFGSplit first_call second_call"
    using descent by (cases evidence) (auto simp: LPPFTShapeSplit)
  have local: "lpp_finite_triple_check_shape_split T ft st fuel P D Q roots contexts incoming entry receipt return_evidence"
    and guarded: "lpp_check_finite_guarded_split_descent OD incoming (lpp_shape_receipt_context incoming return_evidence) entry receipt first_call second_call"
    using checked descent by (simp_all add: LPPFTShapeSplit shape)
  have first: "(lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_first_in receipt) eta)\<in>
      inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom"
    by (rule lpp_stable_guarded_split_first_descent[OF guarded observed])
  show ?thesis by (rule lpp_stable_guarded_shape_split_checked_lower[OF compatible transfer local program known observed free first _ lower])
    (use lpp_stable_guarded_split_return_descent[OF guarded] in blast)
qed

theorem lpp_stable_guarded_graph_checked_contract:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_finite_guarded_graph fuel P D Q T roots contexts blocks q modes chain_pred OD descents"
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
  have local: "lpp_finite_triple_check_component fuel P D Q T roots contexts (contexts!i) (roots!i) (blocks!i)"
    and descent: "lpp_check_finite_component_descent OD roots (contexts!i) (roots!i) (blocks!i) (descents!i)"
    and program: "lp_cut_source_program P"
    using checked index by (auto simp: lpp_check_finite_guarded_graph_def lpp_finite_triple_check_graph_def list_all_iff)
  show "lpp_stable_triple_answer_contract operation P us Q out"
    unfolding source output_atom
    by (rule lpp_stable_guarded_component_checked_lower[OF compatible local descent program transfer observed known free])
      (use lower in \<open>auto simp only: call\<close>)
qed

theorem lpp_stable_guarded_graph_root_sound:
  fixes ts :: "(string lp_cut_symbol,string) lp_iterm list"
    and SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_finite_guarded_graph fuel P D Q T roots contexts blocks q modes chain_pred OD descents"
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
    using checked by (auto simp: lpp_check_finite_guarded_graph_def lpp_finite_triple_check_graph_def Let_def)
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
    by (rule lpp_stable_guarded_graph_checked_contract[OF compatible checked transfer sn rep])
  have source: "SN_on (lpp_domain_source P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) {lp_cut_state_eval (lpcn_state ?nd) ?eta}"
    using lpp_stable_triple_answer_contract_SN[OF contract]
    by (simp add: lpc_return_eval_erases lpc_triple_root_state_def map_map o_def)
  show ?thesis using source root_check vals
    by (simp add: lp_cut_check_root_def lp_cut_state_map_def map_map o_def)
qed


ML \<open>
val checked = [@{thm lpp_stable_guarded_component_checked_lower},
  @{thm lpp_stable_guarded_graph_checked_contract}, @{thm lpp_stable_guarded_graph_root_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable graph dependency" else ();
\<close>
end
