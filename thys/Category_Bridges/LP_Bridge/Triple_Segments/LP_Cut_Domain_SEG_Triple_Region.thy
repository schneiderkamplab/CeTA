theory LP_Cut_Domain_SEG_Triple_Region
 imports LP_Cut_Domain_SEG_Triple_Connection
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

theorem precise_triple_region_checked_lower:
  fixes entry
    and P :: "('f,string) lp_cut_program"
    and eta :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
  assumes checked: "lpc_triple_check_region fuel P triples Q roots entry region"
    and program: "lp_cut_source_program P"
    and known: "knowledge (set (lpcn_ground (lpctr_node entry))) (lpcn_guards (lpctr_node entry)) eta"
    and free: "lpc_free_knowledge (set (lpctr_free entry)) eta"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input entry) eta,b)\<in>lp_triple_calls (set triples) Q \<Longrightarrow>
      precise_triple_root_rep roots us b ret \<Longrightarrow> precise_triple_answer_contract P us Q ret"
  shows "precise_triple_answer_contract P (lpc_return_eval eta (lpc_triple_root_state entry)) Q
    (lp_atom_eval (lpctr_output entry))"
proof -
  let ?data = "lpctg_control region"
  let ?nds = "lpcsc_nodes ?data"
  let ?states = "lpcsc_states ?data"
  let ?Fs = "lpctg_free region"
  let ?nd = "lpctr_node entry"
  let ?inp = "lpc_triple_position_atom (lpcn_vars ?nd) (lpctr_input entry)"
  let ?a = "lp_atom_eval (lpctr_input entry) eta"
  let ?ss = "lpc_return_eval eta (lpc_triple_root_state entry)"
  have control: "lpc_seg_free_check_control fuel P (lpcsc_program ?data) ?nds ?states ?Fs
      (lpcsc_returned ?data) (lpcsc_arity ?data) (lpcsc_actions ?data)"
    and ranked: "lpc_seg_ranked_control (lpc_seg_control_rank ?data) (lpcsc_program ?data)"
    and nonempty: "?nds\<noteq>[]"
    and first: "?nds!0=?nd" "?states!0=lpc_triple_root_state entry" "?Fs!0=lpctr_free entry"
    and distinct: "distinct (lpcn_vars ?nd)"
    and variables: "set (lp_atom_vars (lpctr_input entry)) \<subseteq> set (lpcn_vars ?nd)"
    using checked by (auto simp: lpc_triple_check_region_def Let_def)
  have equal: "lp_atom_eval ?inp (lpc_return_env (map Var (lpcn_vars ?nd)) eta)=?a"
    by (rule lpc_triple_position_atom_eval[OF distinct variables])
  have inv: "lpc_triple_instance_invariant ?a ?inp ?ss"
    unfolding lpc_triple_instance_invariant_def lpc_triple_root_state_def lpc_return_eval_def
    by (auto simp: list_all_iff equal intro!: exI[of _ LPIVar])
  have rep: "precise_return_free_module_rep ?nds ?states ?Fs ?ss
      [(lpcn_pred ?nd,map eta (lpcn_vars ?nd))]"
    unfolding precise_return_free_module_rep_def
    by (rule exI[of _ "[]"], simp only: lpc_return_scope_word.simps precise_return_free_rep_def,
      rule exI[of _ 0], rule exI[of _ eta])
      (use control nonempty first known free in \<open>auto simp: lpc_seg_free_check_control_def\<close>)
  show ?thesis
  proof (rule precise_triple_observed_control[OF control ranked program inv rep])
    fix i rho assume index: "i<length ?nds" and boundary_node: "lpcsc_actions ?data!i=None"
      and known': "knowledge (set (lpcn_ground (?nds!i))) (lpcn_guards (?nds!i)) rho"
      and free': "lpc_free_knowledge (set (?Fs!i)) rho"
      and inv': "lpc_triple_instance_invariant ?a ?inp (lpc_return_eval rho (?states!i))"
    have connection: "lpc_triple_check_connection fuel triples Q roots (?nds!i) (?Fs!i) (?states!i)
      ?inp (lpctr_output entry) (lpctg_connections region!i)"
      using checked index boundary_node by (auto simp: lpc_triple_check_region_def Let_def list_all_iff)
    show "precise_triple_answer_contract P (lpc_return_eval rho (?states!i)) Q (lp_atom_eval (lpctr_output entry))"
      by (rule precise_triple_connection_checked_lower[OF connection program known' free' inv' lower])
  next
    fix i assume "i<length ?nds"
    then show "lpc_triple_check_emit Q (lpctr_output entry) (?states!i)
        (fst (lpctg_emits region!i)) (snd (lpctg_emits region!i))"
      using checked by (auto simp: lpc_triple_check_region_def Let_def list_all_iff)
  qed
qed


end
end
