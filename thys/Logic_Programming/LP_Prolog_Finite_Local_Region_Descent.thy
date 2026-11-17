theory LP_Prolog_Finite_Local_Region_Descent
 imports LP_Prolog_Finite_Local_Region LP_Prolog_Stable_Guarded_Region_Descent
begin
hide_const (open) NthRoot.root Term.root

theorem lpp_finite_local_region_descent_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_finite_local_region A fuel P D Q T roots root_contexts incoming_context root region (lppftr_contexts region)"
    and descent: "lpp_check_finite_guarded_region_descent OD roots root region connections"
    and program: "lp_cut_source_program P"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and observed: "lpp_stable_context_holds operation SP incoming_context eta"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node root))) (lpcn_guards (lpctr_node root)) eta"
    and free: "lpc_free_knowledge (set (lpctr_free root)) eta"
    and finite: "lpp_finite_direct_invariant A (lpc_return_eval eta (lpc_triple_root_state root))"
    and signature: "\<And>f n. (f,n)\<in>A \<Longrightarrow> (f,n)\<in>lpp_builtin_signature \<Longrightarrow> lpp_direct_arithmetic_name f"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input root) eta,b)\<in>inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom \<Longrightarrow>
      lpp_stable_triple_root_rep operation SP root_contexts roots us b ret \<Longrightarrow> lpp_finite_direct_invariant A us \<Longrightarrow> lpp_stable_triple_answer_contract operation P us Q ret"
  shows "lpp_stable_triple_answer_contract operation P (lpc_return_eval eta (lpc_triple_root_state root)) Q
    (lp_atom_eval (lpctr_output root))"
  by (rule lpp_finite_local_region_checked_lower[where R="inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom", OF compatible checked _ program transfer observed known free finite signature _ lower])
    (assumption | use lpp_stable_guarded_region_descent_checked[OF descent] in \<open>blast\<close>)+

ML \<open>
val checked = [@{thm lpp_finite_local_region_descent_checked_lower}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite local region descent" else ();
\<close>
end
