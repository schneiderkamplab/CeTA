theory LP_Prolog_Context_Integer_Test
  imports LP_Prolog_Context_Table
begin

fun lpp_add_integer_observation where
  "lpp_add_integer_observation a (facts,guards,observations) =
    (facts,guards@[LPPSInteger a],observations@[LPPOInteger a])"

lemma lpp_add_integer_observation_holds:
  "lpp_source_context_holds P source_context eta \<Longrightarrow> lpp_is_integer (lp_ieval a eta) \<Longrightarrow>
    lpp_source_context_holds P (lpp_add_integer_observation a source_context) eta"
  by (cases source_context) (auto simp: lpp_path_context_holds_def)

definition lpp_check_context_integer_test where
  "lpp_check_context_integer_test fuel Q nds states contexts nd ss source_context a gs active saved yes no =
    (ss=(LPCGoals (LPCAtom (Fun (LPCUser ''1:integer'') [a])#gs),active)#saved \<and>
     lpp_check_context_table_link fuel Q nds states contexts nd ((LPCGoals gs,active)#saved)
       (lpcn_ground nd@sorted_list_of_set (vars_term a)) (lpcn_guards nd) []
       (lpp_add_integer_observation a source_context) yes \<and>
     lpp_check_context_table_link fuel Q nds states contexts nd saved (lpcn_ground nd) (lpcn_guards nd) [] source_context no)"

theorem lpp_context_integer_test_sound:
  assumes checked: "lpp_check_context_integer_test fuel Q nds states contexts nd ss source_context a gs active saved yes no"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and observed: "lpp_source_context_holds SP source_context eta"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin (lpc_return_eval eta ss) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_context_return_rep SP nds states contexts (lpc_return_scope_word swaps tt) u)"
proof -
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser ''1:integer'') [a])#gs),active)#saved"
    using checked by (simp add: lpp_check_context_integer_test_def)
  have exact: "\<And>outcome. lpp_integer_source_builtin ''1:integer'' [lp_ieval a eta] outcome =
    lpp_integer_test_outcome (lp_ieval a eta) outcome" by simp
  have actual: "event=None \<and> tt=(if lpp_is_integer (lp_ieval a eta)
    then lpc_return_eval eta ((LPCGoals gs,active)#saved) else lpc_return_eval eta saved)"
    using step by (simp add: shape lpc_return_eval_def lpp_integer_test_step_exact[where U=lpp_integer_source_builtin, OF exact])
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  show ?thesis
  proof (cases "lpp_is_integer (lp_ieval a eta)")
    case True
    have ground: "lp_seg_ground (lp_ieval a eta)"
      using True by (auto simp: lpp_is_integer_def lpp_integer_value_def)
    have extended: "lp_cut_knowledge (set (lpcn_ground nd@sorted_list_of_set (vars_term a))) (lpcn_guards nd) eta"
      using known ground by (auto simp: lp_cut_knowledge_def lp_seg_ground_eval)
    have facts: "lpp_source_context_holds SP (lpp_add_integer_observation a source_context) eta"
      by (rule lpp_add_integer_observation_holds[OF observed True])
    have link: "lpp_check_context_table_link fuel Q nds states contexts nd ((LPCGoals gs,active)#saved)
      (lpcn_ground nd@sorted_list_of_set (vars_term a)) (lpcn_guards nd) []
      (lpp_add_integer_observation a source_context) yes"
      using checked by (simp add: lpp_check_context_integer_test_def)
    show ?thesis using lpp_context_table_link_sound[OF link equations refl extended facts] actual True by simp
  next
    case False
    have link: "lpp_check_context_table_link fuel Q nds states contexts nd saved
      (lpcn_ground nd) (lpcn_guards nd) [] source_context no"
      using checked by (simp add: lpp_check_context_integer_test_def)
    show ?thesis using lpp_context_table_link_sound[OF link equations refl known observed] actual False by simp
  qed
qed

ML \<open>
val checked = [@{thm lpp_context_integer_test_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted integer-test context dependency" else ();
\<close>
end
