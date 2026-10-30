theory LP_Prolog_Triple_Graph
  imports LP_Prolog_Triple_Split_Check LP_Prolog_Triple_Integer_Return LP_Prolog_Triple_Region LP_Dependency_Triple_Roles
begin

hide_const (open) Tree_Automata_Containment.entry

datatype lpp_triple_component =
  LPPTRegion lpp_triple_region | LPPTSplit "(string * nat) list" "string lpc_triple_split"
  | LPPTIntegerSplit "string lpc_triple_split" lpp_source_integer_receipt

fun lpp_triple_check_component where
  "lpp_triple_check_component fuel P D Q T roots contexts incoming_context entry (LPPTRegion region) =
    lpp_triple_check_region fuel P D Q T roots contexts incoming_context entry region"
| "lpp_triple_check_component fuel P D Q T roots contexts incoming_context entry (LPPTSplit A receipt) =
    lpp_triple_check_split fuel P D Q roots contexts incoming_context A entry receipt"
| "lpp_triple_check_component fuel P D Q T roots contexts incoming_context entry (LPPTIntegerSplit receipt evidence) =
    lpp_triple_check_integer_split fuel P D Q roots contexts incoming_context entry receipt evidence"

definition lpp_triple_check_graph where
  "lpp_triple_check_graph fuel P D Q T (roots::string lpc_triple_root list) contexts blocks q modes chain_pred =
    (lp_cut_source_program P \<and> roots\<noteq>[] \<and> length blocks=length roots \<and> length contexts=length roots \<and> contexts!0=([],[],[]) \<and>
      (let entry=roots!0; nd=lpctr_node entry; vs=lpcn_vars nd in
        lp_cut_check_root q modes vs (lpcn_state nd) (lpcn_ground nd) (lpcn_guards nd) \<and>
        lpctr_free entry=[] \<and> lpctr_input entry=(chain_pred,map Var vs)) \<and>
      list_all (\<lambda>i. lpp_triple_check_component fuel P D Q T roots contexts (contexts!i) (roots!i) (blocks!i))
        [0..<length roots])"

theorem lpp_triple_component_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes checked: "lpp_triple_check_component fuel P D Q T roots contexts incoming_context entry component"
    and program: "lp_cut_source_program P"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and observed: "lpp_source_context_holds SP incoming_context eta"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node entry))) (lpcn_guards (lpctr_node entry)) eta"
    and free: "lpc_free_knowledge (set (lpctr_free entry)) eta"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input entry) eta,b)\<in>lp_triple_calls (set D) Q \<Longrightarrow>
      lpp_triple_root_rep SP contexts roots us b ret \<Longrightarrow> lpp_triple_answer_contract P us Q ret"
  shows "lpp_triple_answer_contract P (lpc_return_eval eta (lpc_triple_root_state entry)) Q
    (lp_atom_eval (lpctr_output entry))"
  using checked by (cases component)
    (auto intro: lpp_triple_region_checked_lower[OF _ program transfer observed known free lower]
      lpp_triple_split_checked_lower[OF _ program known observed free lower]
      lpp_triple_integer_split_checked_lower[OF _ program known observed free lower])

theorem lpp_triple_graph_contract:
  fixes SP :: "string lpp_success_clause list"
  assumes checked: "lpp_triple_check_graph fuel P D Q T roots contexts blocks q modes chain_pred"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and sn: "SN_on (lp_triple_calls (set D) Q) {a}"
    and represented: "lpp_triple_root_rep SP contexts roots ss a ret"
  shows "lpp_triple_answer_contract P ss Q ret"
proof (rule lpp_triple_answer_contract_modular[where rep="lpp_triple_root_rep SP contexts roots", OF sn represented])
  fix us b out
  assume rep: "lpp_triple_root_rep SP contexts roots us b out"
    and lower: "\<And>vs c final. (b,c)\<in>lp_triple_calls (set D) Q \<Longrightarrow>
      lpp_triple_root_rep SP contexts roots vs c final \<Longrightarrow> lpp_triple_answer_contract P vs Q final"
  obtain i eta where index: "i<length roots"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node (roots!i))))
      (lpcn_guards (lpctr_node (roots!i))) eta"
    and free: "lpc_free_knowledge (set (lpctr_free (roots!i))) eta"
    and observed: "lpp_source_context_holds SP (contexts!i) eta"
    and source: "us=lpc_return_eval eta (lpc_triple_root_state (roots!i))"
    and call: "b=lp_atom_eval (lpctr_input (roots!i)) eta"
    and output_atom: "out=lp_atom_eval (lpctr_output (roots!i))"
    using rep by (auto simp: lpp_triple_root_rep_def)
  have local: "lpp_triple_check_component fuel P D Q T roots contexts (contexts!i) (roots!i) (blocks!i)"
    and program: "lp_cut_source_program P"
    using checked index by (auto simp: lpp_triple_check_graph_def list_all_iff)
  show "lpp_triple_answer_contract P us Q out"
    unfolding source output_atom
    by (rule lpp_triple_component_checked_lower[OF local program transfer observed known free])
      (use lower in \<open>auto simp only: call\<close>)
qed

theorem lpp_triple_graph_root_sound:
  fixes ts :: "(string lp_cut_symbol,string) lp_iterm list"
    and SP :: "string lpp_success_clause list"
  assumes checked: "lpp_triple_check_graph fuel P D Q T roots contexts blocks q modes chain_pred"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and sn: "SN_on (lp_triple_calls (set D) Q) {(chain_pred,ts)}"
    and len: "length ts=length modes"
    and ground: "\<forall>(t,b)\<in>set (zip ts modes). b \<longrightarrow> lp_seg_ground t"
  shows "SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) {[LPCGoals [LPCAtom (LPIFun (LPCUser q) ts)]]}"
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
    using checked by (auto simp: lpp_triple_check_graph_def Let_def)
  have lengths: "length ?vs=length ts" and distinct: "distinct ?vs"
    using root_check len by (auto simp: lp_cut_check_root_def)
  have vals: "map ?eta ?vs=ts" by (rule lp_cut_query_env_values[OF lengths distinct])
  have finite_values: "\<forall>(t,b)\<in>set (zip (map ?eta ?vs) modes). b \<longrightarrow> lp_seg_ground t"
    using ground by (simp only: vals)
  have known: "lp_cut_knowledge (set (lpcn_ground ?nd)) (lpcn_guards ?nd) ?eta"
    using root_check finite_values by (auto simp: lp_cut_check_root_def lp_cut_knowledge_def zip_map1)
  have free: "lpc_free_knowledge (set (lpctr_free ?entry)) ?eta"
    by (simp add: root_free lpc_free_knowledge_def)
  have rep: "lpp_triple_root_rep SP contexts roots (lpc_return_eval ?eta (lpc_triple_root_state ?entry))
      (chain_pred,ts) (lp_atom_eval (lpctr_output ?entry))"
    unfolding lpp_triple_root_rep_def
    by (rule exI[of _ 0], rule exI[of _ ?eta])
      (use nonempty known free context_length initial_context in \<open>simp add: input_atom lp_atom_eval_def vals map_map o_def lpp_path_context_holds_def\<close>)
  have contract: "lpp_triple_answer_contract P (lpc_return_eval ?eta (lpc_triple_root_state ?entry)) Q
      (lp_atom_eval (lpctr_output ?entry))"
    by (rule lpp_triple_graph_contract[OF checked transfer sn rep])
  have source: "SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) {lp_cut_state_eval (lpcn_state ?nd) ?eta}"
    using lpp_triple_answer_contract_SN[OF contract]
    by (simp add: lpc_return_eval_erases lpc_triple_root_state_def map_map o_def)
  show ?thesis using source root_check vals
    by (simp add: lp_cut_check_root_def lp_cut_state_map_def map_map o_def)
qed

end
