theory LP_Prolog_Integer_Legacy
  imports LP_Prolog_Integer_Return_Actions LP_Prolog_Return_Check
begin

lemma lpp_answer_change_active_builtin:
  assumes step: "lpp_answer_transition P B U ((LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs),eta)#saved) event tt"
    and agrees: "\<And>outcome. U f ts outcome \<Longrightarrow> V f ts outcome"
  shows "lpp_answer_transition P B V ((LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs),eta)#saved) event tt"
  using step by (cases rule: lpp_answer_transition.cases)
    (auto intro: lpp_answer_transition.intros agrees)

lemma lpp_integer_legacy_action_step:
  assumes checked: "lpp_check_return_action fuel P Q nds states nd ss returned arity action"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin (lpc_return_eval eta ss) event tt"
  shows "lpp_answer_transition P lpp_builtin_signature lpp_test_builtin (lpc_return_eval eta ss) event tt"
proof (cases action)
  case (LPPRCut primitive)
  have clear: "lpp_no_builtin_frame ss" using checked LPPRCut by simp
  show ?thesis by (rule lpp_answer_transition.base[OF lpp_no_builtin_frame_sound[OF clear]
    lpp_integer_source_nonbuiltin_base[OF clear step]])
next
  case (LPPRVar f a gs active saved yes no)
  have legacy: "lpp_var_name f" and shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs),active)#saved"
    using checked LPPRVar by (auto simp: lpp_check_var_node_def)
  have exact: "\<And>ts outcome. lpp_integer_source_builtin f ts outcome = lpp_test_builtin f ts outcome"
    by (rule lpp_integer_source_legacy) (use legacy in blast)
  have active_step: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin
    ((LPCGoals (LPCAtom (LPIFun (LPCUser f) [lp_ieval a eta])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved) event tt"
    using step by (simp add: shape lpc_return_eval_def)
  have legacy_step: "lpp_answer_transition P lpp_builtin_signature lpp_test_builtin
    ((LPCGoals (LPCAtom (LPIFun (LPCUser f) [lp_ieval a eta])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved) event tt"
    by (rule lpp_answer_change_active_builtin[OF active_step]) (simp only: exact)
  show ?thesis using legacy_step by (simp add: shape lpc_return_eval_def)
next
  case (LPPRIdentity f a b gs active saved yes no)
  have legacy: "lpp_identity_name f" and shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs),active)#saved"
    using checked LPPRIdentity by (auto simp: lpp_check_identity_node_def)
  have exact: "\<And>ts outcome. lpp_integer_source_builtin f ts outcome = lpp_test_builtin f ts outcome"
    by (rule lpp_integer_source_legacy) (use legacy in blast)
  have active_step: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin
    ((LPCGoals (LPCAtom (LPIFun (LPCUser f) [lp_ieval a eta,lp_ieval b eta])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved) event tt"
    using step by (simp add: shape lpc_return_eval_def)
  have legacy_step: "lpp_answer_transition P lpp_builtin_signature lpp_test_builtin
    ((LPCGoals (LPCAtom (LPIFun (LPCUser f) [lp_ieval a eta,lp_ieval b eta])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved) event tt"
    by (rule lpp_answer_change_active_builtin[OF active_step]) (simp only: exact)
  show ?thesis using legacy_step by (simp add: shape lpc_return_eval_def)
qed

lemma lpp_integer_legacy_domain:
  assumes legacy: "(lpp_var_name f \<and> length ts=1) \<or> (lpp_identity_name f \<and> length ts=2)"
  shows "lpp_integer_source_domain f ts"
proof -
  have ni: "f\<noteq>''1:integer''" and ne: "f\<noteq>''2:is''"
    using legacy by (auto simp: lpp_var_name_def lpp_identity_name_def)
  have nc: "lpp_source_comparison f=None" using legacy
    by (auto simp only: lpp_var_name_def lpp_identity_name_def lpp_source_comparison_legacy_names)
  show ?thesis using legacy by (simp only: lpp_integer_source_domain.simps ni ne if_False nc option.case)
qed

lemma lpp_integer_legacy_action_domain:
  assumes checked: "lpp_check_return_action fuel P Q nds states nd ss returned arity action"
  shows "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_integer_source_domain (map fst (lpc_return_eval eta ss))"
proof (cases action)
  case (LPPRCut primitive)
  have clear: "lpp_no_builtin_frame ss" using checked LPPRCut by simp
  show ?thesis by (rule lpp_no_builtin_domain_bad[OF lpp_no_builtin_frame_sound[OF clear]])
next
  case (LPPRVar f a gs active saved yes no)
  show ?thesis using checked LPPRVar
    by (auto simp: lpp_check_var_node_def lpc_return_eval_def
      simp del: lpp_integer_source_domain.simps intro: lpp_integer_legacy_domain)
next
  case (LPPRIdentity f a b gs active saved yes no)
  show ?thesis using checked LPPRIdentity
    by (auto simp: lpp_check_identity_node_def lpc_return_eval_def
      simp del: lpp_integer_source_domain.simps intro: lpp_integer_legacy_domain)
qed

lemma lpp_integer_legacy_action_sound:
  assumes checked: "lpp_check_return_action fuel P Q nds states nd ss returned arity action"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin (lpc_return_eval eta ss) event tt"
  shows "(\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
      lpc_return_rep nds states (lpc_return_scope_word swaps tt) u) \<and>
    (\<forall>rho. event=Some rho \<longrightarrow>
      ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*)"
  by (rule lpp_return_action_sound[OF checked known lpp_integer_legacy_action_step[OF checked step]])

ML \<open>
val checked = [@{thm lpp_integer_legacy_action_sound}, @{thm lpp_integer_legacy_action_domain}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted legacy action dependency" else ();
\<close>
end
