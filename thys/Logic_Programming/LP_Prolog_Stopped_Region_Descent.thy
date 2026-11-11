theory LP_Prolog_Stopped_Region_Descent
 imports LP_Prolog_Stopped_Guarded_Region LP_Prolog_Stable_Guarded_Region_Descent
begin
hide_const (open) NthRoot.root Term.root

theorem lpp_stopped_guarded_region_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_stopped_check_region_contexts fuel P D Q T roots root_contexts incoming_context root region actions (lppftr_contexts region)"
    and descent: "lpp_check_guarded_region_descent OD roots root region connections (\<lambda>i. actions!i=None)"
    and program: "lp_cut_source_program P"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and observed: "lpp_stable_context_holds operation SP incoming_context eta"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node root))) (lpcn_guards (lpctr_node root)) eta"
    and free: "lpc_free_knowledge (set (lpctr_free root)) eta"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input root) eta,b)\<in>inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom \<Longrightarrow>
      lpp_stable_triple_root_rep operation SP root_contexts roots us b ret \<Longrightarrow> lpp_stopped_triple_answer_contract operation P us Q ret"
  shows "lpp_stopped_triple_answer_contract operation P (lpc_return_eval eta (lpc_triple_root_state root)) Q
    (lp_atom_eval (lpctr_output root))"
  by (rule lpp_stopped_guarded_region_contexts_checked_lower[where R="inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom", OF compatible checked _ program transfer observed known free _ lower])
    (assumption | use lpp_stable_guarded_region_descent_general[OF descent] in blast)+

ML \<open>
val checked = [@{thm lpp_stopped_guarded_region_checked_lower}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stopped region descent dependency" else ();
\<close>
end
