theory LP_Prolog_Evaluation_Term_Test
  imports LP_Prolog_Evaluation_Integer_Test
begin

text \<open>Term tests use the existing source operation and preserve the
incoming context on both outcomes. In particular, the failed test resumes
the saved alternative without importing facts from the successful branch.\<close>

definition lpp_check_evaluation_term_test where
  "lpp_check_evaluation_term_test T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context f a gs active saved yes no =
    (lpp_var_name f \<and> ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs),active)#saved \<and>
     list_all (\<lambda>holds. lpp_check_evaluation_link T (if holds then yes_facts else no_facts)
       fuel Q nds states contexts Fs nd (if holds then (LPCGoals gs,active)#saved else saved)
       (lpcn_ground nd) (lpcn_guards nd) [] F source_context (if holds then yes else no))
       (lpp_var_outcomes f (lpcn_ground nd) a))"

lemma lpp_finite_term_test_step:
  assumes name: "lpp_var_name f"
  shows "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin
      ((LPCGoals (LPCAtom (LPIFun (LPCUser f) [a])#gs),eta)#es) event tt =
    (event=None \<and> tt=(if lpp_var_holds f a then (LPCGoals gs,eta)#es else es))"
proof -
  have ne: "f\<noteq>''2:is''" using name by (auto simp: lpp_var_name_def)
  have same: "\<And>outcome. lpp_finite_source_builtin f [a] outcome=lpp_test_builtin f [a] outcome"
    by (simp only: lpp_finite_source_legacy[OF ne] lpp_integer_source_legacy[OF disjI1[OF name]])
  have selected: "(f,length [a])\<in>lpp_builtin_signature"
    using lpp_var_selected[OF name] by simp
  show ?thesis
    by (simp only: lpp_selected_builtin_cong[where U=lpp_finite_source_builtin and V=lpp_test_builtin, OF selected same]
      lpp_test_var_step[OF name] lpp_var_step_exact[OF name])
qed

theorem lpp_evaluation_term_test_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes contract: "lpp_eval_integer_contract TYPE(string) E"
    and evaluation: "\<And>e t. E e t \<Longrightarrow> lp_seg_ground e \<and> lp_seg_ground t"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_term_test T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context f a gs active saved yes no"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_evaluation_context_holds E SP source_context eta"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin (lpc_return_eval eta ss) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_evaluation_rep E SP nds states contexts Fs (lpc_return_scope_word swaps tt) u)"
proof -
  let ?holds = "lpp_var_holds f (lp_ieval a eta)"
  let ?next = "if ?holds then (LPCGoals gs,active)#saved else saved"
  have name: "lpp_var_name f" and shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs),active)#saved"
    using checked by (auto simp: lpp_check_evaluation_term_test_def)
  have coverage: "?holds\<in>set (lpp_var_outcomes f (lpcn_ground nd) a)"
    by (rule lpp_var_outcomes_cover[OF name known])
  have link: "lpp_check_evaluation_link T (if ?holds then yes_facts else no_facts)
    fuel Q nds states contexts Fs nd ?next (lpcn_ground nd) (lpcn_guards nd) [] F source_context
    (if ?holds then yes else no)"
    using checked coverage by (auto simp: lpp_check_evaluation_term_test_def list_all_iff)
  have actual: "event=None \<and> tt=lpc_return_eval eta ?next"
    using step by (auto simp: shape lpc_return_eval_def lpp_finite_term_test_step[OF name] split: if_splits)
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  show ?thesis using lpp_evaluation_link_sound[OF contract evaluation program link equations refl known free observed] actual by auto
qed

lemma lpp_evaluation_term_test_domain:
  assumes checked: "lpp_check_evaluation_term_test T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context f a gs active saved yes no"
  shows "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_finite_source_domain (map fst (lpc_return_eval eta ss))"
proof -
  have name: "lpp_var_name f" and shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs),active)#saved"
    using checked by (auto simp: lpp_check_evaluation_term_test_def)
  have ni: "f\<noteq>''1:integer''" and ne: "f\<noteq>''2:is''"
    using name by (auto simp: lpp_var_name_def)
  have nc: "lpp_source_comparison f=None"
    using name by (auto simp only: lpp_var_name_def lpp_source_comparison_legacy_names)
  have old: "lpp_integer_source_domain f [lp_ieval a eta]"
    by (simp only: lpp_integer_source_domain.simps ni ne if_False nc option.case)
      (use name in simp)
  have domain: "lpp_finite_source_domain f [lp_ieval a eta]"
    by (rule lpp_finite_source_domain_extends[OF old])
  show ?thesis using domain by (simp add: shape lpc_return_eval_def)
qed

ML \<open>
val checked = [@{thm lpp_evaluation_term_test_sound}, @{thm lpp_evaluation_term_test_domain}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted finite term-test dependency" else ();
\<close>
end
