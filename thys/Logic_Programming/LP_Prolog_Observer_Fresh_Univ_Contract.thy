theory LP_Prolog_Observer_Fresh_Univ_Contract
 imports LP_Prolog_Observer_Univ_Path
begin

lemma lpp_checked_fresh_univ_observer_contract:
 fixes SP :: "string lpp_success_clause list"
 and combined_env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes checked: "lpp_check_separation_head P nd ctx a c (LPPSMatching matching)"
 and fresh: "lpp_check_fresh_univ_clause (fst (P!c)) (snd (P!c)) x y z"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and observed: "lpp_stable_context_holds operation SP ctx eta"
 and shape: "runtime=(LPCClause (LPCAtom (lp_ieval a eta)#gs) c m,combined_env)#combined_saved"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and invariant: "lpp_observer_invariant {u. vars_term u={}} specs rest runtime"

 and source_block: "\<And>helper_middle helper_result.
   lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
    (lpc_reinterface (\<lambda>env x. env (Inl x)) runtime) None helper_middle \<Longrightarrow>
   lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
    helper_middle None helper_result \<Longrightarrow>
   helper_result=[] \<or> (\<exists>u. (subject,u)\<in>R\<^sup>+ \<and>
    lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts node_conditions helper_result u)"
 and lower: "\<And>child u. (subject,u)\<in>R\<^sup>+ \<Longrightarrow>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts node_conditions
    (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<Longrightarrow>
   lpp_observer_invariant {v. vars_term v={}} specs rest child \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) R u returned"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)) R subject returned"
proof (rule lp_answer_contract_intro)
 let ?T = "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain"
 let ?L = "\<lambda>env x. env (Inl x)"
 let ?R = "\<lambda>env x. env (Inr x)"
 fix first_event middle
 assume first: "?T (lpc_attach_answers rest (lpc_reinterface ?R runtime)) first_event middle"
 have active: "lpc_prefix_active runtime" by (simp add: shape)
 have first_silent: "first_event=None"
  using lpp_attached_observer_product_step[OF active first] by blast
 have middle_contract: "lp_answer_contract ?T middle R subject returned"
 proof (rule lp_answer_contract_intro)
  fix second_event result
  assume second: "?T middle second_event result"
  obtain joint_middle joint_result where second_silent: "second_event=None"
  and exact_middle: "middle=lpc_attach_answers rest (lpc_reinterface ?R joint_middle)"
  and exact_result: "result=lpc_attach_answers rest (lpc_reinterface ?R joint_result)"
  and helper_first: "?T (lpc_reinterface ?L runtime) None (lpc_reinterface ?L joint_middle)"
  and helper_second: "?T (lpc_reinterface ?L joint_middle) None (lpc_reinterface ?L joint_result)"
  and final_invariant: "lpp_observer_invariant {v. vars_term v={}} specs rest joint_result"
   using lpp_checked_fresh_univ_observer_product[OF checked fresh known observed shape covered invariant first second] by blast
  have alternatives: "lpc_reinterface ?L joint_result=[] \<or> (\<exists>u. (subject,u)\<in>R\<^sup>+ \<and>
    lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts node_conditions
     (lpc_reinterface ?L joint_result) u)"
   by (rule source_block[OF helper_first helper_second])
  have result_contract: "lp_answer_contract ?T result R subject returned"
  proof (cases "lpc_reinterface ?L joint_result=[]")
   case True
   have empty: "result=[]" using True exact_result by (simp add: lpc_reinterface_def lpc_attach_answers_def)
   show ?thesis unfolding empty by (rule lpp_domain_contract_singletons) simp
  next
   case False
   obtain u where strict: "(subject,u)\<in>R\<^sup>+"
   and represented: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts node_conditions
     (lpc_reinterface ?L joint_result) u"
    using alternatives False by blast
   have child_contract: "lp_answer_contract ?T (lpc_attach_answers rest (lpc_reinterface ?R joint_result)) R u returned"
    by (rule lower[OF strict represented final_invariant])
   show ?thesis unfolding exact_result
    by (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF strict] child_contract])
  qed
  show "(\<forall>rho. second_event=Some rho \<longrightarrow> (subject,returned rho)\<in>R\<^sup>*) \<and>
   lp_answer_contract ?T result R subject returned"
   using second_silent result_contract by simp
 qed
 show "(\<forall>rho. first_event=Some rho \<longrightarrow> (subject,returned rho)\<in>R\<^sup>*) \<and>
   lp_answer_contract ?T middle R subject returned"
  using first_silent middle_contract by simp
qed

ML \<open>
val checked = @{thms lpp_checked_fresh_univ_observer_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted fresh-univ observer contract" else ();
\<close>
end
