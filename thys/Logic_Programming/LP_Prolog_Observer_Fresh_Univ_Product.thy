theory LP_Prolog_Observer_Fresh_Univ_Product
 imports LP_Prolog_Observer_Fresh_Univ_Block
begin

lemma lpp_fresh_matching_resolution_active:
 assumes matching: "lp_cut_check_match a (fst (P!c)) bindings"
 and fresh: "lpp_check_fresh_univ_clause (fst (P!c)) (snd (P!c)) x y z"
 and step: "lpp_domain_answers P B U D
   ((LPCClause (LPCAtom (lp_ieval a eta)#gs) c m,env)#saved) event tt"
 shows "lpc_prefix_active tt"
proof -
 have possible: "\<exists>sigma::string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm. \<exists>rho.
   lp_isubst (lp_ieval a eta) sigma=lp_ieval (fst (P!c)) rho"
  by (rule lp_cut_check_match_sound[OF matching])
 obtain body_rest where body: "snd (P!c)=LPCAtom (Fun (LPCUser ''2:=..'') [Var x,
   Fun (LPCUser ''2:prolog_data_2e'') [Var y,Var z]])#body_rest"
  using fresh by (auto simp: lpp_check_fresh_univ_clause_def)
 have base: "lpc_answer_transition P ((LPCClause (LPCAtom (lp_ieval a eta)#gs) c m,env)#saved) event tt"
  by (rule lpp_observer_clause_base[OF step])
 show ?thesis using base possible by (cases rule: lpc_answer_transition.cases) (auto simp: body)
qed

lemma lpp_checked_fresh_univ_observer_product:
 fixes SP :: "string lpp_success_clause list"
 and combined_env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes checked: "lpp_check_separation_head P nd ctx a c (LPPSMatching matching)"
 and fresh: "lpp_check_fresh_univ_clause (fst (P!c)) (snd (P!c)) x y z"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and observed: "lpp_stable_context_holds operation SP ctx eta"
 and shape: "runtime=(LPCClause (LPCAtom (lp_ieval a eta)#gs) c m,combined_env)#combined_saved"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and invariant: "lpp_observer_invariant {u. vars_term u={}} specs rest runtime"
 and first: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)) first_event middle"
 and second: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   middle second_event result"
 shows "first_event=None \<and> second_event=None \<and> (\<exists>joint_middle joint_result.
   middle=lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) joint_middle) \<and>
   result=lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) joint_result) \<and>
   lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
    (lpc_reinterface (\<lambda>env x. env (Inl x)) runtime) None
    (lpc_reinterface (\<lambda>env x. env (Inl x)) joint_middle) \<and>
   lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
    (lpc_reinterface (\<lambda>env x. env (Inl x)) joint_middle) None
    (lpc_reinterface (\<lambda>env x. env (Inl x)) joint_result) \<and>
   lpp_observer_invariant {u. vars_term u={}} specs rest joint_result)"
proof -
 let ?T = "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain"
 let ?L = "\<lambda>env x. env (Inl x)"
 let ?R = "\<lambda>env x. env (Inr x)"
 have active: "lpc_prefix_active runtime" by (simp add: shape)
 obtain joint_middle where first_silent: "first_event=None"
 and joint_first: "?T runtime None joint_middle"
 and helper_first: "?T (lpc_reinterface ?L runtime) None (lpc_reinterface ?L joint_middle)"
 and exact_middle: "middle=lpc_attach_answers rest (lpc_reinterface ?R joint_middle)"
  using lpp_attached_observer_product_step[OF active first] by blast
 have matching_check: "lp_cut_check_match a (fst (P!c)) matching" using checked by simp
 have next_active: "lpc_prefix_active joint_middle"
  by (rule lpp_fresh_matching_resolution_active[OF matching_check fresh joint_first[unfolded shape]])
 obtain joint_result where second_silent: "second_event=None"
 and helper_second: "?T (lpc_reinterface ?L joint_middle) None (lpc_reinterface ?L joint_result)"
 and exact_result: "result=lpc_attach_answers rest (lpc_reinterface ?R joint_result)"
  using lpp_attached_observer_product_step[OF next_active second[unfolded exact_middle]] by blast
 have caller_first: "?T (lpc_attach_answers rest
   ((LPCClause (LPCAtom (lp_ieval a eta)#gs) c m,?R combined_env)#lpc_reinterface ?R combined_saved)) first_event middle"
  using first by (simp add: shape lpc_reinterface_def)
 have finite: "lpp_finite_execution (lpc_attach_answers rest
   ((LPCClause (LPCAtom (lp_ieval a eta)#gs) c m,?R combined_env)#lpc_reinterface ?R combined_saved))"
 and leaf: "lpp_leaf_stack_invariant {u. vars_term u={}} specs
   ((LPCClause (LPCAtom (lp_ieval a eta)#gs) c m,?R combined_env)#lpc_reinterface ?R combined_saved)"
  using invariant by (simp_all add: lpp_observer_invariant_def shape lpc_reinterface_def)
 have final: "lpp_finite_execution result \<and> lpp_leaf_stack_invariant {u. vars_term u={}} specs result"
  using lpp_checked_resolution_univ_block_invariants[OF checked fresh known observed caller_first second finite leaf covered] by simp
 have final_invariant: "lpp_observer_invariant {u. vars_term u={}} specs rest joint_result"
  using final by (simp add: exact_result lpp_observer_invariant_def lpp_leaf_stack_attachment)
 show ?thesis using first_silent second_silent exact_middle exact_result helper_first helper_second final_invariant by blast
qed

ML \<open>
val checked = @{thms lpp_fresh_matching_resolution_active lpp_checked_fresh_univ_observer_product};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted fresh-univ observer product" else ();
\<close>
end
