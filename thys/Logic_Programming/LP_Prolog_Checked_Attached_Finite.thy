theory LP_Prolog_Checked_Attached_Finite
 imports LP_Prolog_Observer_Checked_Boundaries
begin

text \<open>The existing checked head witness also discharges finite execution
of the actual attached continuation. This includes matching, anchored ground
and observed list-spine heads; no general rational unifier is assumed finite.\<close>

lemma lpp_checked_head_actual_finite_instance:
 fixes SP :: "string lpp_success_clause list"
 assumes checked: "lpp_check_separation_head P nd ctx a c witness"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and observed: "lpp_stable_context_holds operation SP ctx eta"
 and mgu: "lpc_mgu_resolve (lp_ieval a eta) pending_goals (fst (P!c)) (snd (P!c)) sigma rho"
 and finite: "lpp_finite_term (lp_ieval a eta)"
 shows "lpp_finite_term (lp_ieval (fst (P!c)) rho)"
 using lpp_checked_head_actual_return_effect[OF checked known observed mgu]
  lpp_matching_head_finite_instance[OF mgu _ finite]
 by (blast intro: lpp_ground_finite_term)

lemma lpp_checked_head_attached_finite_step:
 fixes SP :: "string lpp_success_clause list"
 assumes checked: "lpp_check_separation_head P nd ctx a c witness"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and observed: "lpp_stable_context_holds operation SP ctx eta"
 and step: "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCClause (LPCAtom (lp_ieval a eta)#gs) c m,ret)#saved)) event result"
 and finite: "lpp_finite_execution
   (lpc_attach_answers rest ((LPCClause (LPCAtom (lp_ieval a eta)#gs) c m,ret)#saved))"
 shows "lpp_finite_execution result"
proof (rule lpp_finite_base_answer_step[OF step finite])
 fix call pending clause mark env alternatives sigma rho
 assume shape: "lpc_attach_answers rest ((LPCClause (LPCAtom (lp_ieval a eta)#gs) c m,ret)#saved)=
   (LPCClause (LPCAtom call#pending) clause mark,env)#alternatives"
 and bound: "clause<length P"
 and mgu: "lpc_mgu_resolve call pending (fst (P!clause)) (snd (P!clause)) sigma rho"
 have actual: "lpc_mgu_resolve (lp_ieval a eta) pending (fst (P!c)) (snd (P!c)) sigma rho"
 and same_clause: "clause=c"
  using shape mgu by (auto simp: lpc_attach_answers_def)
 have finite_call: "lpp_finite_term (lp_ieval a eta)"
  using finite by (auto simp: lpc_attach_answers_def lpp_finite_execution_def lpp_finite_goals_def)
 show "lpp_finite_term (lp_ieval (fst (P!clause)) rho)"
  unfolding same_clause by (rule lpp_checked_head_actual_finite_instance[OF checked known observed actual finite_call])
qed (auto simp: lpc_attach_answers_def)

lemma lpp_checked_head_attached_invariants:
 fixes SP :: "string lpp_success_clause list"
 and ret :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes checked: "lpp_check_separation_head P nd ctx a c witness"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and observed: "lpp_stable_context_holds operation SP ctx eta"
 and step: "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCClause (LPCAtom (lp_ieval a eta)#gs) c m,ret)#saved)) event tt"
 and invariant: "lpp_leaf_stack_invariant {u. vars_term u={}} specs
   ((LPCClause (LPCAtom (lp_ieval a eta)#gs) c m,ret)#saved)"
 and finite: "lpp_finite_execution
   (lpc_attach_answers rest ((LPCClause (LPCAtom (lp_ieval a eta)#gs) c m,ret)#saved))"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 shows "lpp_finite_execution tt \<and> lpp_leaf_stack_invariant {u. vars_term u={}} specs tt"
proof -
 have finite_call: "lpp_finite_term (lp_ieval a eta)"
 and finite_rest: "lpp_finite_goals (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t ret)) rest)"
  using finite by (auto simp: lpc_attach_answers_def lpp_finite_execution_def lpp_finite_goals_def)
 have next_finite: "lpp_finite_execution tt"
  by (rule lpp_checked_head_attached_finite_step[OF checked known observed step finite])
 have next_leaf: "lpp_leaf_stack_invariant {u. vars_term u={}} specs tt"
  by (rule lpp_checked_head_attached_leaf_step[OF checked known observed step invariant finite_call finite_rest covered])
 show ?thesis using next_finite next_leaf by simp
qed

lemma lpp_checked_fresh_univ_leaf_from_finite:
 fixes SP :: "string lpp_success_clause list"
 and ret :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes checked: "lpp_check_separation_head P nd ctx a c witness"
 and fresh: "lpp_check_fresh_decomposition (fst (P!c)) (snd (P!c)) input_variable name_variable arguments_variable"
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
 shows "lpp_leaf_stack_invariant {u. vars_term u={}} specs tt"
proof -
 have finite_head: "lpp_finite_term (lp_ieval (fst (P!c)) rho)"
  by (rule lpp_checked_head_actual_finite_instance[OF checked known observed resolution finite_call])
 have finite_resolved: "lpp_finite_term (lp_isubst (lp_ieval a eta) sigma)"
  using resolution finite_head by (simp add: lpc_mgu_resolve_def)
 show ?thesis by (rule lpp_checked_fresh_clause_univ_leaf_step[OF checked fresh known observed resolution
   finite_call finite_resolved finite_rest covered initial step invariant])
qed

ML \<open>
val checked = @{thms lpp_checked_head_actual_finite_instance lpp_checked_head_attached_finite_step
 lpp_checked_head_attached_invariants lpp_checked_fresh_univ_leaf_from_finite};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted checked attached finite resolution" else ();
\<close>
end
