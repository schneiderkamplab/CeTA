theory LP_Prolog_Observer_Fresh_Univ_Block
 imports LP_Prolog_Observer_Fresh_Univ_Invariants
begin

lemma lpp_checked_resolution_univ_block_invariants:
 fixes SP :: "string lpp_success_clause list"
 and ret :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes checked: "lpp_check_separation_head P nd ctx a c (LPPSMatching matching)"
 and fresh: "lpp_check_fresh_univ_clause (fst (P!c)) (snd (P!c)) input_variable name_variable arguments_variable"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and observed: "lpp_stable_context_holds operation SP ctx eta"
 and first: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_attach_answers rest ((LPCClause (LPCAtom (lp_ieval a eta)#gs) c m,ret)#saved)) first_event middle"
 and second: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   middle second_event result"
 and finite: "lpp_finite_execution
   (lpc_attach_answers rest ((LPCClause (LPCAtom (lp_ieval a eta)#gs) c m,ret)#saved))"
 and invariant: "lpp_leaf_stack_invariant {u. vars_term u={}} specs
   ((LPCClause (LPCAtom (lp_ieval a eta)#gs) c m,ret)#saved)"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 shows "first_event=None \<and> lpp_finite_execution result \<and>
   lpp_leaf_stack_invariant {u. vars_term u={}} specs result"
proof -
 let ?pending = "gs @ map (lp_cut_map (\<lambda>t. lp_ieval t ret)) rest"
 have base: "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCClause (LPCAtom (lp_ieval a eta)#gs) c m,ret)#saved)) first_event middle"
  using first by (auto simp: lpc_attach_answers_def intro: lpp_observer_clause_base)
 have matching_check: "lp_cut_check_match a (fst (P!c)) matching" using checked by simp
 have possible: "\<exists>sigma::string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm. \<exists>rho.
   lp_isubst (lp_ieval a eta) sigma=lp_ieval (fst (P!c)) rho"
  by (rule lp_cut_check_match_sound[OF matching_check])
 obtain sigma rho where resolution: "lpc_mgu_resolve (lp_ieval a eta) ?pending (fst (P!c)) (snd (P!c)) sigma rho"
 and silent: "first_event=None"
 and resolved: "middle=(LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) (snd (P!c)) @
   map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ?pending),\<lambda>slot. lp_isubst (ret slot) sigma)#lpc_attach_answers rest saved"
  using base[unfolded lpc_attach_answers_def, simplified] possible
  by (cases rule: lpc_answer_transition.cases) (auto simp: lpc_attach_answers_def)
 obtain body_rest where body: "snd (P!c)=LPCAtom (Fun (LPCUser ''2:=..'') [Var input_variable,
   Fun (LPCUser ''2:prolog_data_2e'') [Var name_variable,Var arguments_variable]])#body_rest"
  using fresh by (auto simp: lpp_check_fresh_univ_clause_def)
 let ?after = "map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) body_rest @
   map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ?pending"
 have middle_shape: "middle=(LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [rho input_variable,
    LPIFun (LPCUser ''2:prolog_data_2e'') [rho name_variable,rho arguments_variable]])#?after),
    \<lambda>slot. lp_isubst (ret slot) sigma)#lpc_attach_answers rest saved"
  using resolved by (simp add: body)
 have middle_finite: "lpp_finite_execution middle"
 and middle_leaf: "lpp_leaf_stack_invariant {u. vars_term u={}} specs middle"
  using lpp_checked_head_attached_invariants[OF checked known observed base invariant finite covered] by auto
 have finite_call: "lpp_finite_term (lp_ieval a eta)"
 and finite_rest: "lpp_finite_goals ?pending"
  using finite by (auto simp: lpc_attach_answers_def lpp_finite_execution_def lpp_finite_goals_def)
 have initial: "lpp_runtime_leaf_effect {u. vars_term u={}} shape (ret slot)"
  if "(slot,shape)\<in>set specs" for slot shape
  by (rule lpp_leaf_stack_head[OF invariant that])
 have result: "lpp_finite_execution result \<and> lpp_leaf_stack_invariant {u. vars_term u={}} specs result"
  by (rule lpp_checked_fresh_univ_actual_invariants[OF checked fresh known observed resolution
   finite_call finite_rest covered initial second[unfolded middle_shape]
   middle_leaf[unfolded middle_shape] middle_finite[unfolded middle_shape]])
 show ?thesis using silent result by simp
qed

ML \<open>
val checked = @{thms lpp_checked_resolution_univ_block_invariants};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted resolution-univ block invariants" else ();
\<close>
end
