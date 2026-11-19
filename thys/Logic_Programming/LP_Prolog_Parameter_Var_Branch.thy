theory LP_Prolog_Parameter_Var_Branch
 imports LP_Prolog_Runtime_Parameter LP_Prolog_Functor_Term_Test
begin

text \<open>The retained parameter-binding rows have an empty free table.
Their opaque var guard is not evidence of freeness. The fact needed by the
restricted equality rule comes from the actual successful test, and only from
that branch. The saved frames and their environments remain unchanged.\<close>

lemma lpp_actual_var_branch:
 assumes step: "lpp_domain_answers P lpp_builtin_signature
  (lpp_univ_source_builtin names operation) lpp_univ_source_domain
  ((LPCGoals (LPCAtom (LPIFun (LPCUser ''1:var'') [a])#gs),eta)#saved) event tt"
 shows "event=None \<and>
  ((\<exists>x. a=LPIVar x) \<and> tt=(LPCGoals gs,eta)#saved \<or>
   (\<not>(\<exists>x. a=LPIVar x)) \<and> tt=saved)"
proof -
 have name: "lpp_var_name ''1:var''" by (simp add: lpp_var_name_def)
 have ni: "''1:var'' \<noteq> ''1:integer''" and ne: "''1:var'' \<noteq> ''2:is''" by simp_all
 have old_domain: "lpp_integer_source_domain ''1:var'' [a]"
  by (simp only: lpp_integer_source_domain.simps ni ne if_False
    lpp_source_comparison_legacy_names option.case) (use name in simp)
 have domain: "lpp_univ_source_domain ''1:var'' [a]"
  using lpp_finite_source_domain_extends[OF old_domain]
  by (simp add: lpp_univ_source_domain_def)
 show ?thesis using step domain
  by (cases a) (auto simp: lpp_domain_answers_def
    lpp_univ_term_test_step[of "''1:var''", simplified lpp_var_name_def]
    lpp_var_holds_def)
qed

lemma lpp_actual_var_success_free:
 assumes step: "lpp_domain_answers P lpp_builtin_signature
  (lpp_univ_source_builtin names operation) lpp_univ_source_domain
  ((LPCGoals (LPCAtom (LPIFun (LPCUser ''1:var'') [a])#gs),eta)#saved)
  event ((LPCGoals gs,eta)#saved)"
 shows "\<exists>x. a=LPIVar x"
 using lpp_actual_var_branch[OF step] by auto

lemma lpp_actual_var_success_parameter:
 assumes step: "lpp_domain_answers P lpp_builtin_signature
  (lpp_univ_source_builtin names operation) lpp_univ_source_domain
  ((LPCGoals (LPCAtom (LPIFun (LPCUser ''1:var'') [lp_ieval a eta])#gs),env)#saved)
  event ((LPCGoals gs,env)#saved)"
 and parameter: "lpp_runtime_parameter c (lp_ieval p eta)"
 shows "(\<exists>x. lp_ieval a eta=LPIVar x) \<and>
  lpp_runtime_parameter c (lp_ieval p eta)"
 using lpp_actual_var_success_free[OF step] parameter by blast

lemma lpp_parameter_cut_branch:
 assumes step: "lpp_domain_answers P B U D
  ((LPCGoals (LPCCut m#gs),env)#saved) event tt"
 shows "event=None \<and> tt=(LPCGoals gs,env)#lpc_answer_prune m saved"
proof -
 have base: "lpc_answer_transition P
  ((LPCGoals (LPCCut m#gs),env)#saved) event tt"
  using step by (auto simp: lpp_domain_answers_def elim: lpp_answer_transition.cases)
 show ?thesis using base by (cases rule: lpc_answer_transition.cases) auto
qed

lemma lpp_parameter_cut_keeps_active_facts:
 assumes step: "lpp_domain_answers P B U D
  ((LPCGoals (LPCCut m#gs),env)#saved) event tt"
 and free: "\<exists>x. env selected=LPIVar x"
 and tracked: "lpp_runtime_parameter c (env parameter)"
 shows "event=None \<and> tt=(LPCGoals gs,env)#lpc_answer_prune m saved \<and>
  (\<exists>x. snd (hd tt) selected=LPIVar x) \<and>
  lpp_runtime_parameter c (snd (hd tt) parameter)"
 using lpp_parameter_cut_branch[OF step] free tracked by auto

lemma lpp_opaque_var_guard_does_not_establish_free:
 fixes eta :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes selected: "eta 0=LPIFun (LPCUser ''compound'') [LPIVar ''shared'']"
 and parameter: "eta 1=LPIFun (LPCUser ''parameter'') []"
 shows "lpp_stable_context_holds operation SP
  ([],[LPPSOpaque (Var 1),LPPSOpaque (Fun (LPCUser ''1:var'') [Var 0])],
   [LPPOGround (Var 1)]) eta \<and>
  lpc_free_knowledge {} eta \<and> \<not>(\<exists>x. eta 0=LPIVar x)"
 using selected parameter
 by (simp add: lpp_stable_context_holds_def lpp_evaluation_context_holds_def
   lpc_free_knowledge_def)

lemma lpp_actual_var_positive:
 "lpp_answer_transition P lpp_builtin_signature (lpp_univ_source_builtin names operation)
  ((LPCGoals (LPCAtom (LPIFun (LPCUser ''1:var'') [LPIVar x])#gs),eta)#saved)
  None ((LPCGoals gs,eta)#saved)"
 by (simp add: lpp_univ_term_test_step[of "''1:var''", simplified lpp_var_name_def]
   lpp_var_holds_def)

lemma lpp_actual_var_compound_cannot_continue:
 "\<not>lpp_answer_transition P lpp_builtin_signature (lpp_univ_source_builtin names operation)
  ((LPCGoals (LPCAtom (LPIFun (LPCUser ''1:var'') [LPIFun f ts])#gs),eta)#saved)
  None ((LPCGoals gs,eta)#saved)"
 by (simp add: lpp_univ_term_test_step[of "''1:var''", simplified lpp_var_name_def]
   lpp_var_holds_def)

ML \<open>
val checked = @{thms lpp_actual_var_branch lpp_actual_var_success_free
 lpp_actual_var_success_parameter lpp_parameter_cut_branch
 lpp_parameter_cut_keeps_active_facts lpp_opaque_var_guard_does_not_establish_free
 lpp_actual_var_positive lpp_actual_var_compound_cannot_continue};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted parameter variable-test branch" else ();
\<close>
end
