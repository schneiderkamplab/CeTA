theory LP_Prolog_Observer_Fresh_Univ_Invariants
 imports LP_Prolog_Observer_Block_Contract LP_Prolog_Finite_Operation_Outcome
begin

lemma lpp_checked_fresh_univ_actual_invariants:
 fixes SP :: "string lpp_success_clause list"
 and ret :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes checked: "lpp_check_separation_head P nd ctx a c witness"
 and fresh: "lpp_check_fresh_univ_clause (fst (P!c)) (snd (P!c)) input_variable name_variable arguments_variable"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and observed: "lpp_stable_context_holds operation SP ctx eta"
 and resolution: "lpc_mgu_resolve (lp_ieval a eta)
   (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t ret)) rest) (fst (P!c)) (snd (P!c)) sigma rho"
 and finite_call: "lpp_finite_term (lp_ieval a eta)"
 and finite_rest: "lpp_finite_goals (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t ret)) rest)"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and initial: "\<And>slot shape. (slot,shape)\<in>set specs \<Longrightarrow>
   lpp_runtime_leaf_effect {u. vars_term u={}} shape (ret slot)"
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [rho input_variable,
     LPIFun (LPCUser ''2:prolog_data_2e'') [rho name_variable,rho arguments_variable]])#pending_goals),
     \<lambda>slot. lp_isubst (ret slot) sigma)#saved) event tt"
 and invariant: "lpp_leaf_stack_invariant {u. vars_term u={}} specs
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [rho input_variable,
     LPIFun (LPCUser ''2:prolog_data_2e'') [rho name_variable,rho arguments_variable]])#pending_goals),
     \<lambda>slot. lp_isubst (ret slot) sigma)#saved)"
 and finite_state: "lpp_finite_execution
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [rho input_variable,
     LPIFun (LPCUser ''2:prolog_data_2e'') [rho name_variable,rho arguments_variable]])#pending_goals),
     \<lambda>slot. lp_isubst (ret slot) sigma)#saved)"
 shows "lpp_finite_execution tt \<and> lpp_leaf_stack_invariant {u. vars_term u={}} specs tt"
proof -
 have decomposition: "lpp_check_fresh_decomposition (fst (P!c)) (snd (P!c)) input_variable name_variable arguments_variable"
  using fresh by (simp add: lpp_check_fresh_univ_clause_def)
 have leaf: "lpp_leaf_stack_invariant {u. vars_term u={}} specs tt"
  by (rule lpp_checked_fresh_univ_leaf_from_finite[OF checked decomposition known observed resolution
   finite_call finite_rest covered initial step invariant])
 have finite_head: "lpp_finite_term (lp_ieval (fst (P!c)) rho)"
  by (rule lpp_checked_head_actual_finite_instance[OF checked known observed resolution finite_call])
 have finite_resolved: "lpp_finite_term (lp_isubst (lp_ieval a eta) sigma)"
  using resolution finite_head by (simp add: lpc_mgu_resolve_def)
 have finite_result: "lpp_finite_execution tt"
 proof (rule lpp_finite_domain_answer_step[OF step finite_state])
  fix ev us
  assume base: "lpc_answer_transition P
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [rho input_variable,
     LPIFun (LPCUser ''2:prolog_data_2e'') [rho name_variable,rho arguments_variable]])#pending_goals),
     \<lambda>slot. lp_isubst (ret slot) sigma)#saved) ev us"
  show "lpp_finite_execution us"
   by (rule lpp_finite_base_answer_step[OF base finite_state]) auto
 next
  fix f ts more_goals env alternatives outcome
  assume same: "((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [rho input_variable,
     LPIFun (LPCUser ''2:prolog_data_2e'') [rho name_variable,rho arguments_variable]])#pending_goals),
     \<lambda>slot. lp_isubst (ret slot) sigma)#saved) =
    (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#more_goals),env)#alternatives"
  and outcome: "lpp_univ_source_builtin names operation f ts outcome"
  have view: "lpp_univ_view_outcome names (rho input_variable)
   (LPIFun (LPCUser ''2:prolog_data_2e'') [rho name_variable,rho arguments_variable]) outcome"
   using same outcome by (auto simp: lpp_univ_source_builtin_def)
  have goals: "lpp_finite_goals more_goals"
   using finite_state same by (auto simp: lpp_finite_execution_def lpp_finite_goals_def)
  show "lpp_finite_execution_outcome more_goals outcome"
   by (rule lpp_fresh_clause_finite_execution_outcome[OF fresh resolution finite_resolved view goals])
 qed
 show ?thesis using finite_result leaf by simp
qed

ML \<open>
val checked = @{thms lpp_checked_fresh_univ_actual_invariants};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted actual fresh-univ invariants" else ();
\<close>
end
