theory LP_Prolog_Stable_Primitive
 imports LP_Prolog_Stable_Branch LP_Prolog_Stable_Builtins LP_Prolog_Evaluation_Primitive
begin

theorem lpp_stable_primitive_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_primitive T fuel P Q nds states contexts Fs nd F ss source_context returned arity action"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and step: "lpp_answer_transition P lpp_builtin_signature (lpp_stable_source_builtin operation) (lpc_return_eval eta ss) event tt"
  shows "(\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
      lpp_stable_rep operation SP nds states contexts Fs (lpc_return_scope_word swaps tt) u) \<and>
    (\<forall>rho. event=Some rho \<longrightarrow>
      ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*)"
proof (cases action)
  case (LPPEOrdinary primitive yes_facts no_facts)
  show ?thesis
  proof (cases "primitive=LPCRInconsistent")
    case True
    have "lp_cut_check_inconsistent (lpcn_guards nd)" using checked LPPEOrdinary True by simp
    then show ?thesis using lp_cut_checked_inconsistent known by blast
  next
    case False
    have clear: "lpp_no_builtin_frame ss" and check:
      "lpp_check_evaluation_cut_action T yes_facts no_facts fuel P Q nds states contexts Fs nd F ss source_context returned arity primitive"
      using checked LPPEOrdinary False by auto
    show ?thesis by (rule lpp_stable_cut_action_sound[OF compatible program check known free observed
      lpp_stable_nonbuiltin_base[OF clear step]])
  qed
next
  case (LPPEIntegerTest a gs active saved yes no yes_facts no_facts)
  have check: "lpp_check_evaluation_integer_test T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context a gs active saved yes no"
    using checked LPPEIntegerTest by simp
  show ?thesis using lpp_stable_integer_test_sound[OF compatible program check known free observed step] by auto
next
  case (LPPETermTest f a gs active saved yes no yes_facts no_facts)
  have check: "lpp_check_evaluation_term_test T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context f a gs active saved yes no"
    using checked LPPETermTest by simp
  show ?thesis using lpp_stable_term_test_sound[OF compatible program check known free observed step] by auto
next
  case (LPPEGroundDisequality a b gs active saved yes no yes_facts no_facts)
  have check: "lpp_check_evaluation_ground_disequality T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context a b gs active saved yes no"
    using checked LPPEGroundDisequality by simp
  show ?thesis using lpp_stable_ground_disequality_sound[OF compatible program check known free observed step] by auto
next
  case (LPPERationalDisequality a b gs active saved yes no yes_facts no_facts)
  have check: "lpp_check_evaluation_rational_disequality T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context a b gs active saved yes no"
    using checked LPPERationalDisequality by simp
  show ?thesis using lpp_stable_rational_disequality_sound[OF compatible program check known free observed step] by auto
next
  case (LPPEProbe f g argv m n gs active saved e fs)
  have check: "lpp_check_evaluation_probe T fs fuel Q nds states contexts Fs nd F ss source_context f g argv m n gs active saved e"
    using checked LPPEProbe by simp
  show ?thesis using lpp_stable_probe_sound[OF compatible program check known free observed step] by auto
next
  case (LPPEBranch c y z cs ys zs m n gs active saved e fs)
  have check: "lpp_check_evaluation_branch T fs fuel Q nds states contexts Fs nd F ss source_context c y z cs ys zs m n gs active saved e"
    using checked LPPEBranch by simp
  show ?thesis using lpp_stable_branch_sound[OF compatible program check known free observed step] by auto
next
  case (LPPEIdentity f a b gs active saved yes no yes_facts no_facts)
  have check: "lpp_check_evaluation_identity T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context f a b gs active saved yes no"
    using checked LPPEIdentity by simp
  show ?thesis using lpp_stable_identity_sound[OF compatible program check known free observed step] by auto
next
  case (LPPEComparison evidence yes_facts no_facts error_facts)
  have check: "lpp_check_evaluation_comparison T yes_facts no_facts error_facts fuel Q nds states contexts Fs nd F ss source_context
    (lppfc_predicate evidence) (lppfc_comparison evidence) (lppfc_reversed evidence)
    (lppfc_left evidence) (lppfc_right evidence) (lppfc_goals evidence) (lppfc_active evidence)
    (lppfc_saved evidence) (lppfc_yes evidence) (lppfc_no evidence) (lppfc_error evidence)"
    using checked LPPEComparison by simp
  show ?thesis using lpp_stable_comparison_node_sound[OF compatible program check known free observed step] by auto
qed
ML \<open>
val checked = [@{thm lpp_stable_primitive_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable primitive dependency" else ();
\<close>
end
