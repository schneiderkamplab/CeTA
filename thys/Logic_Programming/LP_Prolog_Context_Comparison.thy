theory LP_Prolog_Context_Comparison
  imports LP_Prolog_Context_Integer_Test
begin

fun lpp_add_numeric_observation where
  "lpp_add_numeric_observation observation (facts,guards,observations) =
    (facts,guards,observations@[observation])"

lemma lpp_add_numeric_observation_holds:
  "lpp_source_context_holds P source_context eta \<Longrightarrow> lpp_numeric_observation_holds eta observation \<Longrightarrow>
    lpp_source_context_holds P (lpp_add_numeric_observation observation source_context) eta"
  by (cases source_context) (auto simp: lpp_path_context_holds_def)

lemma lpp_checked_comparison_actual:
  assumes checked: "lpp_check_integer_comparison_node fuel Q nds states nd ss K f comparison reversed a b ea eb gs active saved yes no"
    and integers: "lpp_integer_known K eta"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin (lpc_return_eval eta ss) event tt"
  defines "observation \<equiv> LPPOComparison comparison (if reversed then b else a) (if reversed then a else b)"
  shows "event=None \<and> tt=(if lpp_numeric_observation_holds eta observation
    then lpc_return_eval eta ((LPCGoals gs,active)#saved) else lpc_return_eval eta saved)"
proof -
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs),active)#saved"
    and descriptor: "lpp_comparison_descriptor f comparison reversed"
    and left_check: "a=lpp_expression_term ea" "lpp_expression_check K ea"
    and right_check: "b=lpp_expression_term eb" "lpp_expression_check K eb"
    using checked by (auto simp: lpp_check_integer_comparison_node_def)
  obtain n m where left: "lpp_integer_evaluation (lp_ieval a eta) n"
    and right: "lpp_integer_evaluation (lp_ieval b eta) m"
    using lpp_checked_expression_finishes[OF left_check(2) integers]
      lpp_checked_expression_finishes[OF right_check(2) integers] left_check(1) right_check(1) by blast
  let ?truth = "lpp_integer_compare comparison (if reversed then m else n) (if reversed then n else m)"
  have selected: "(f,length [lp_ieval a eta,lp_ieval b eta])\<in>lpp_builtin_signature"
    using lpp_comparison_selected[OF descriptor] by (simp add: numeral_2_eq_2)
  have outcomes: "\<And>outcome. lpp_integer_source_builtin f [lp_ieval a eta,lp_ieval b eta] outcome =
    (outcome=(if ?truth then LPPBuiltinSuccess LPIVar else LPPBuiltinFailure))"
    unfolding lpp_integer_source_comparison[OF descriptor left right]
    by (cases reversed) (use lpp_integer_compare_outcome_exact[OF left right]
      lpp_integer_compare_outcome_exact[OF right left] in simp_all)
  have truth: "lpp_numeric_observation_holds eta observation = ?truth"
    unfolding observation_def
    by (cases reversed) (simp_all add: lpp_finite_comparison_integer[OF left right] lpp_finite_comparison_integer[OF right left] lpp_integer_compare_outcome_exact[OF left right]
      lpp_integer_compare_outcome_exact[OF right left])
  show ?thesis using step
    by (simp add: shape lpc_return_eval_def truth
      lpp_fixed_test_step_exact[where U=lpp_integer_source_builtin and P=P, OF selected outcomes])
qed

definition lpp_check_context_comparison where
  "lpp_check_context_comparison fuel Q nds states contexts nd ss source_context K f comparison reversed a b ea eb gs active saved yes no =
    (lpp_check_integer_comparison_node fuel Q nds states nd ss K f comparison reversed a b ea eb gs active saved yes no \<and>
     lpp_check_context_table_link fuel Q nds states contexts nd ((LPCGoals gs,active)#saved)
       (lpcn_ground nd) (lpcn_guards nd) []
       (lpp_add_numeric_observation (LPPOComparison comparison (if reversed then b else a) (if reversed then a else b)) source_context) yes \<and>
     lpp_check_context_table_link fuel Q nds states contexts nd saved (lpcn_ground nd) (lpcn_guards nd) [] source_context no)"

theorem lpp_context_comparison_sound:
  assumes checked: "lpp_check_context_comparison fuel Q nds states contexts nd ss source_context K f comparison reversed a b ea eb gs active saved yes no"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and integers: "lpp_integer_known K eta"
    and observed: "lpp_source_context_holds SP source_context eta"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin (lpc_return_eval eta ss) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_context_return_rep SP nds states contexts (lpc_return_scope_word swaps tt) u)"
proof -
  let ?observation = "LPPOComparison comparison (if reversed then b else a) (if reversed then a else b)"
  have base: "lpp_check_integer_comparison_node fuel Q nds states nd ss K f comparison reversed a b ea eb gs active saved yes no"
    using checked by (simp add: lpp_check_context_comparison_def)
  have actual: "event=None \<and> tt=(if lpp_numeric_observation_holds eta ?observation
    then lpc_return_eval eta ((LPCGoals gs,active)#saved) else lpc_return_eval eta saved)"
    by (rule lpp_checked_comparison_actual[OF base integers step])
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  show ?thesis
  proof (cases "lpp_numeric_observation_holds eta ?observation")
    case True
    have facts: "lpp_source_context_holds SP (lpp_add_numeric_observation ?observation source_context) eta"
      by (rule lpp_add_numeric_observation_holds[OF observed True])
    have link: "lpp_check_context_table_link fuel Q nds states contexts nd ((LPCGoals gs,active)#saved)
      (lpcn_ground nd) (lpcn_guards nd) [] (lpp_add_numeric_observation ?observation source_context) yes"
      using checked by (simp add: lpp_check_context_comparison_def)
    show ?thesis using lpp_context_table_link_sound[OF link equations refl known facts] actual True by simp
  next
    case False
    have link: "lpp_check_context_table_link fuel Q nds states contexts nd saved
      (lpcn_ground nd) (lpcn_guards nd) [] source_context no"
      using checked by (simp add: lpp_check_context_comparison_def)
    show ?thesis using lpp_context_table_link_sound[OF link equations refl known observed] actual False by simp
  qed
qed

ML \<open>
val checked = [@{thm lpp_context_comparison_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted comparison context dependency" else ();
\<close>
end
