theory LP_Prolog_Finite_Triple_Graph
  imports LP_Prolog_Finite_Triple_Returns LP_Prolog_Finite_Triple_Region LP_Dependency_Triple_Roles
begin

hide_const (open) Tree_Automata_Containment.entry

datatype lpp_finite_triple_component =
  LPPFTRegion lpp_finite_triple_region | LPPFTSplit lpp_link_types lpp_link_types "string lpc_triple_split"
  | LPPFTIntegerSplit lpp_link_types lpp_link_types "string lpc_triple_split" lpp_source_integer_receipt
  | LPPFTGroundSplit lpp_link_types lpp_link_types "string lpc_triple_split" lpp_source_ground_receipt

fun lpp_finite_triple_check_component where
  "lpp_finite_triple_check_component fuel P D Q T roots contexts incoming_context entry (LPPFTRegion region) =
    lpp_finite_triple_check_region fuel P D Q T roots contexts incoming_context entry region"
| "lpp_finite_triple_check_component fuel P D Q T roots contexts incoming_context entry (LPPFTSplit first_types second_types receipt) =
    lpp_finite_triple_check_preserved_split T first_types second_types fuel D Q roots contexts incoming_context entry receipt"
| "lpp_finite_triple_check_component fuel P D Q T roots contexts incoming_context entry (LPPFTIntegerSplit first_types second_types receipt evidence) =
    lpp_finite_triple_check_integer_split T first_types second_types fuel P D Q roots contexts incoming_context entry receipt evidence"

| "lpp_finite_triple_check_component fuel P D Q T roots contexts incoming_context entry (LPPFTGroundSplit first_types second_types receipt evidence) =
    lpp_finite_triple_check_ground_split T first_types second_types fuel P D Q roots contexts incoming_context entry receipt evidence"

definition lpp_finite_triple_check_graph where
  "lpp_finite_triple_check_graph fuel P D Q T (roots::string lpc_triple_root list) contexts blocks q modes chain_pred =
    (lp_cut_source_program P \<and> roots\<noteq>[] \<and> length blocks=length roots \<and> length contexts=length roots \<and> contexts!0=([],[],[]) \<and>
      (let entry=roots!0; nd=lpctr_node entry; vs=lpcn_vars nd in
        lp_cut_check_root q modes vs (lpcn_state nd) (lpcn_ground nd) (lpcn_guards nd) \<and>
        lpctr_free entry=[] \<and> lpctr_input entry=(chain_pred,map Var vs)) \<and>
      list_all (\<lambda>i. lpp_finite_triple_check_component fuel P D Q T roots contexts (contexts!i) (roots!i) (blocks!i))
        [0..<length roots])"

theorem lpp_finite_triple_component_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes checked: "lpp_finite_triple_check_component fuel P D Q T roots contexts incoming_context entry component"
    and program: "lp_cut_source_program P"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and observed: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP incoming_context eta"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node entry))) (lpcn_guards (lpctr_node entry)) eta"
    and free: "lpc_free_knowledge (set (lpctr_free entry)) eta"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input entry) eta,b)\<in>lp_triple_calls (set D) Q \<Longrightarrow>
      lpp_finite_triple_root_rep SP contexts roots us b ret \<Longrightarrow> lpp_finite_triple_answer_contract P us Q ret"
  shows "lpp_finite_triple_answer_contract P (lpc_return_eval eta (lpc_triple_root_state entry)) Q
    (lp_atom_eval (lpctr_output entry))"
  using checked by (cases component)
    (auto intro: lpp_finite_triple_region_checked_lower[OF _ program transfer observed known free lower]
      lpp_finite_triple_preserved_split_checked_lower[OF transfer _ program known observed free lower]
      lpp_finite_triple_integer_split_checked_lower[OF transfer _ program known observed free lower]
      lpp_finite_triple_ground_split_checked_lower[OF transfer _ program known observed free lower])

theorem lpp_finite_triple_graph_contract:
  fixes SP :: "string lpp_success_clause list"
  assumes checked: "lpp_finite_triple_check_graph fuel P D Q T roots contexts blocks q modes chain_pred"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and sn: "SN_on (lp_triple_calls (set D) Q) {a}"
    and represented: "lpp_finite_triple_root_rep SP contexts roots ss a ret"
  shows "lpp_finite_triple_answer_contract P ss Q ret"
proof (rule lpp_finite_triple_answer_contract_modular[where rep="lpp_finite_triple_root_rep SP contexts roots", OF sn represented])
  fix us b out
  assume rep: "lpp_finite_triple_root_rep SP contexts roots us b out"
    and lower: "\<And>vs c final. (b,c)\<in>lp_triple_calls (set D) Q \<Longrightarrow>
      lpp_finite_triple_root_rep SP contexts roots vs c final \<Longrightarrow> lpp_finite_triple_answer_contract P vs Q final"
  obtain i eta where index: "i<length roots"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node (roots!i))))
      (lpcn_guards (lpctr_node (roots!i))) eta"
    and free: "lpc_free_knowledge (set (lpctr_free (roots!i))) eta"
    and observed: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP (contexts!i) eta"
    and source: "us=lpc_return_eval eta (lpc_triple_root_state (roots!i))"
    and call: "b=lp_atom_eval (lpctr_input (roots!i)) eta"
    and output_atom: "out=lp_atom_eval (lpctr_output (roots!i))"
    using rep by (auto simp: lpp_finite_triple_root_rep_def)
  have local: "lpp_finite_triple_check_component fuel P D Q T roots contexts (contexts!i) (roots!i) (blocks!i)"
    and program: "lp_cut_source_program P"
    using checked index by (auto simp: lpp_finite_triple_check_graph_def list_all_iff)
  show "lpp_finite_triple_answer_contract P us Q out"
    unfolding source output_atom
    by (rule lpp_finite_triple_component_checked_lower[OF local program transfer observed known free])
      (use lower in \<open>auto simp only: call\<close>)
qed

theorem lpp_finite_triple_graph_root_sound:
  fixes ts :: "(string lp_cut_symbol,string) lp_iterm list"
    and SP :: "string lpp_success_clause list"
  assumes checked: "lpp_finite_triple_check_graph fuel P D Q T roots contexts blocks q modes chain_pred"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and sn: "SN_on (lp_triple_calls (set D) Q) {(chain_pred,ts)}"
    and len: "length ts=length modes"
    and ground: "\<forall>(t,b)\<in>set (zip ts modes). b \<longrightarrow> lp_seg_ground t"
  shows "SN_on (lpp_domain_source P lpp_builtin_signature lpp_finite_source_builtin lpp_finite_source_domain) {[LPCGoals [LPCAtom (LPIFun (LPCUser q) ts)]]}"
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
    using checked by (auto simp: lpp_finite_triple_check_graph_def Let_def)
  have lengths: "length ?vs=length ts" and distinct: "distinct ?vs"
    using root_check len by (auto simp: lp_cut_check_root_def)
  have vals: "map ?eta ?vs=ts" by (rule lp_cut_query_env_values[OF lengths distinct])
  have finite_values: "\<forall>(t,b)\<in>set (zip (map ?eta ?vs) modes). b \<longrightarrow> lp_seg_ground t"
    using ground by (simp only: vals)
  have known: "lp_cut_knowledge (set (lpcn_ground ?nd)) (lpcn_guards ?nd) ?eta"
    using root_check finite_values by (auto simp: lp_cut_check_root_def lp_cut_knowledge_def zip_map1)
  have free: "lpc_free_knowledge (set (lpctr_free ?entry)) ?eta"
    by (simp add: root_free lpc_free_knowledge_def)
  have rep: "lpp_finite_triple_root_rep SP contexts roots (lpc_return_eval ?eta (lpc_triple_root_state ?entry))
      (chain_pred,ts) (lp_atom_eval (lpctr_output ?entry))"
    unfolding lpp_finite_triple_root_rep_def
    by (rule exI[of _ 0], rule exI[of _ ?eta])
      (use nonempty known free context_length initial_context in \<open>simp add: input_atom lp_atom_eval_def vals map_map o_def lpp_evaluation_context_holds_def\<close>)
  have contract: "lpp_finite_triple_answer_contract P (lpc_return_eval ?eta (lpc_triple_root_state ?entry)) Q
      (lp_atom_eval (lpctr_output ?entry))"
    by (rule lpp_finite_triple_graph_contract[OF checked transfer sn rep])
  have source: "SN_on (lpp_domain_source P lpp_builtin_signature lpp_finite_source_builtin lpp_finite_source_domain) {lp_cut_state_eval (lpcn_state ?nd) ?eta}"
    using lpp_finite_triple_answer_contract_SN[OF contract]
    by (simp add: lpc_return_eval_erases lpc_triple_root_state_def map_map o_def)
  show ?thesis using source root_check vals
    by (simp add: lp_cut_check_root_def lp_cut_state_map_def map_map o_def)
qed


ML \<open>
val checked = [@{thm lpp_finite_triple_graph_root_sound}, @{thm lpp_finite_triple_graph_contract}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted finite arithmetic triple graph dependency" else ();
\<close>
end
