theory LP_Prolog_Evaluation_Integer_Test
 imports LP_Prolog_Evaluation_Identity
begin

lemma lpp_add_evaluation_integer_holds:
  "lpp_evaluation_context_holds E P source_context eta \<Longrightarrow> lpp_is_integer (lp_ieval a eta) \<Longrightarrow>
    lpp_evaluation_context_holds E P (lpp_add_integer_observation a source_context) eta"
  by (cases source_context) (auto simp: lpp_evaluation_context_holds_def)

definition lpp_check_evaluation_integer_test where
  "lpp_check_evaluation_integer_test T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context a gs active saved yes no =
    (ss=(LPCGoals (LPCAtom (Fun (LPCUser ''1:integer'') [a])#gs),active)#saved \<and>
     lpp_check_evaluation_link T yes_facts fuel Q nds states contexts Fs nd ((LPCGoals gs,active)#saved)
       (lpcn_ground nd@sorted_list_of_set (vars_term a)) (lpcn_guards nd) [] F
       (lpp_add_integer_observation a source_context) yes \<and>
     lpp_check_evaluation_link T no_facts fuel Q nds states contexts Fs nd saved (lpcn_ground nd) (lpcn_guards nd) [] F source_context no)"

theorem lpp_evaluation_integer_test_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes contract: "lpp_eval_integer_contract TYPE(string) E"
    and evaluation: "\<And>e t. E e t \<Longrightarrow> lp_seg_ground e \<and> lp_seg_ground t"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_integer_test T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context a gs active saved yes no"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_evaluation_context_holds E SP source_context eta"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin (lpc_return_eval eta ss) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_evaluation_rep E SP nds states contexts Fs (lpc_return_scope_word swaps tt) u)"
proof -
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser ''1:integer'') [a])#gs),active)#saved"
    using checked by (simp add: lpp_check_evaluation_integer_test_def)
  have exact: "\<And>outcome. lpp_finite_source_builtin ''1:integer'' [lp_ieval a eta] outcome =
    lpp_integer_test_outcome (lp_ieval a eta) outcome" by (simp add: lpp_finite_source_builtin_def)
  have actual: "event=None \<and> tt=(if lpp_is_integer (lp_ieval a eta)
    then lpc_return_eval eta ((LPCGoals gs,active)#saved) else lpc_return_eval eta saved)"
    using step by (simp add: shape lpc_return_eval_def lpp_integer_test_step_exact[where U=lpp_finite_source_builtin, OF exact])
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  show ?thesis
  proof (cases "lpp_is_integer (lp_ieval a eta)")
    case True
    have ground: "lp_seg_ground (lp_ieval a eta)"
      using True by (auto simp: lpp_is_integer_def lpp_integer_value_def)
    have extended: "lp_cut_knowledge (set (lpcn_ground nd@sorted_list_of_set (vars_term a))) (lpcn_guards nd) eta"
      using known ground by (auto simp: lp_cut_knowledge_def lp_seg_ground_eval)
    have facts: "lpp_evaluation_context_holds E SP (lpp_add_integer_observation a source_context) eta"
      by (rule lpp_add_evaluation_integer_holds[OF observed True])
    have link: "lpp_check_evaluation_link T yes_facts fuel Q nds states contexts Fs nd ((LPCGoals gs,active)#saved)
      (lpcn_ground nd@sorted_list_of_set (vars_term a)) (lpcn_guards nd) [] F
      (lpp_add_integer_observation a source_context) yes"
      using checked by (simp add: lpp_check_evaluation_integer_test_def)
    show ?thesis using lpp_evaluation_link_sound[OF contract evaluation program link equations refl extended free facts] actual True by simp
  next
    case False
    have link: "lpp_check_evaluation_link T no_facts fuel Q nds states contexts Fs nd saved
      (lpcn_ground nd) (lpcn_guards nd) [] F source_context no"
      using checked by (simp add: lpp_check_evaluation_integer_test_def)
    show ?thesis using lpp_evaluation_link_sound[OF contract evaluation program link equations refl known free observed] actual False by simp
  qed
qed

ML \<open>
val checked = [@{thm lpp_evaluation_integer_test_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted integer-test context dependency" else ();
\<close>
end
