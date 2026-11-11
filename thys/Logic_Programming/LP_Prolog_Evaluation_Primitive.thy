theory LP_Prolog_Evaluation_Primitive
  imports LP_Prolog_Evaluation_Choice LP_Prolog_Evaluation_Branch LP_Prolog_Evaluation_Probe LP_Prolog_Evaluation_Rational_Disequality LP_Prolog_Evaluation_Cut_Actions
begin

type_synonym lpp_link_types = "string lpp_transfer_fact list"

datatype lpp_evaluation_primitive =
    LPPEOrdinary "string lpc_return_action" lpp_link_types lpp_link_types
  | LPPEIntegerTest "string lpc_term" "string lpc_term lp_cut_goal list"
      "string lpc_term list" "string lpc_return_state" "string lpc_link" "string lpc_link"
      lpp_link_types lpp_link_types
  | LPPETermTest string "string lpc_term" "string lpc_term lp_cut_goal list"
      "string lpc_term list" "string lpc_return_state" "string lpc_link" "string lpc_link"
      lpp_link_types lpp_link_types
  | LPPEGroundDisequality "string lpc_term" "string lpc_term" "string lpc_term lp_cut_goal list"
      "string lpc_term list" "string lpc_return_state" "string lpc_link" "string lpc_link"
      lpp_link_types lpp_link_types
  | LPPERationalDisequality "string lpc_term" "string lpc_term" "string lpc_term lp_cut_goal list"
      "string lpc_term list" "string lpc_return_state" "string lpc_link" "string lpc_link"
      lpp_link_types lpp_link_types
  | LPPEProbe string string "string lpc_term list" nat nat "string lpc_term lp_cut_goal list"
      "string lpc_term list" "string lpc_return_state" "string lpc_link" lpp_link_types
  | LPPEBranch "string lpc_term" "string lpc_term" "string lpc_term"
      "string lpc_term lp_cut_goal list" "string lpc_term lp_cut_goal list" "string lpc_term lp_cut_goal list"
      nat nat "string lpc_term lp_cut_goal list" "string lpc_term list" "string lpc_return_state" "string lpc_link" lpp_link_types
  | LPPEChoice "string lpc_term" "string lpc_term"
      "string lpc_term lp_cut_goal list" "string lpc_term lp_cut_goal list"
      "string lpc_term lp_cut_goal list" "string lpc_term list" "string lpc_return_state" "string lpc_link" lpp_link_types
  | LPPEIdentity string "string lpc_term" "string lpc_term" "string lpc_term lp_cut_goal list"
      "string lpc_term list" "string lpc_return_state" "string lpc_link" "string lpc_link"
      lpp_link_types lpp_link_types
  | LPPEComparison lpp_finite_comparison_receipt lpp_link_types lpp_link_types lpp_link_types

fun lpp_check_evaluation_primitive where
  "lpp_check_evaluation_primitive T fuel P Q nds states contexts Fs nd F ss source_context returned arity (LPPEOrdinary action yes_facts no_facts) =
    ((lpp_no_builtin_frame ss \<or> action=LPCRInconsistent) \<and>
      lpp_check_evaluation_cut_action T yes_facts no_facts fuel P Q nds states contexts Fs nd F ss source_context returned arity action)"
| "lpp_check_evaluation_primitive T fuel P Q nds states contexts Fs nd F ss source_context returned arity
    (LPPEIntegerTest a gs active saved yes no yes_facts no_facts) =
      lpp_check_evaluation_integer_test T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context a gs active saved yes no"
| "lpp_check_evaluation_primitive T fuel P Q nds states contexts Fs nd F ss source_context returned arity
    (LPPETermTest f a gs active saved yes no yes_facts no_facts) =
      lpp_check_evaluation_term_test T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context f a gs active saved yes no"
| "lpp_check_evaluation_primitive T fuel P Q nds states contexts Fs nd F ss source_context returned arity
    (LPPEGroundDisequality a b gs active saved yes no yes_facts no_facts) =
      lpp_check_evaluation_ground_disequality T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context a b gs active saved yes no"
| "lpp_check_evaluation_primitive T fuel P Q nds states contexts Fs nd F ss source_context returned arity
    (LPPERationalDisequality a b gs active saved yes no yes_facts no_facts) =
      lpp_check_evaluation_rational_disequality T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context a b gs active saved yes no"
| "lpp_check_evaluation_primitive T fuel P Q nds states contexts Fs nd F ss source_context returned arity
    (LPPEProbe f g argv m n gs active saved e fs) =
      lpp_check_evaluation_probe T fs fuel Q nds states contexts Fs nd F ss source_context f g argv m n gs active saved e"
| "lpp_check_evaluation_primitive T fuel P Q nds states contexts Fs nd F ss source_context returned arity
    (LPPEBranch c y z cs ys zs m n gs active saved e fs) =
      lpp_check_evaluation_branch T fs fuel Q nds states contexts Fs nd F ss source_context c y z cs ys zs m n gs active saved e"
| "lpp_check_evaluation_primitive T fuel P Q nds states contexts Fs nd F ss source_context returned arity
    (LPPEChoice a b left right gs active saved e fs) =
      lpp_check_evaluation_choice T fs fuel Q nds states contexts Fs nd F ss source_context a b left right gs active saved e"
| "lpp_check_evaluation_primitive T fuel P Q nds states contexts Fs nd F ss source_context returned arity
    (LPPEIdentity f a b gs active saved yes no yes_facts no_facts) =
      lpp_check_evaluation_identity T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context f a b gs active saved yes no"
| "lpp_check_evaluation_primitive T fuel P Q nds states contexts Fs nd F ss source_context returned arity
    (LPPEComparison evidence yes_facts no_facts error_facts) =
      lpp_check_evaluation_comparison T yes_facts no_facts error_facts fuel Q nds states contexts Fs nd F ss source_context
        (lppfc_predicate evidence) (lppfc_comparison evidence) (lppfc_reversed evidence)
        (lppfc_left evidence) (lppfc_right evidence) (lppfc_goals evidence) (lppfc_active evidence)
        (lppfc_saved evidence) (lppfc_yes evidence) (lppfc_no evidence) (lppfc_error evidence)"

theorem lpp_evaluation_primitive_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_primitive T fuel P Q nds states contexts Fs nd F ss source_context returned arity action"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP source_context eta"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin (lpc_return_eval eta ss) event tt"
  shows "(\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
      lpp_evaluation_rep lpp_finite_evaluation_result SP nds states contexts Fs (lpc_return_scope_word swaps tt) u) \<and>
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
    show ?thesis by (rule lpp_evaluation_cut_action_sound[OF lpp_finite_evaluation_integer_contract
      lpp_finite_evaluation_ground lpp_finite_evaluation_subst program check known free observed
      lpp_finite_source_nonbuiltin_base[OF clear step]])
  qed
next
  case (LPPEIntegerTest a gs active saved yes no yes_facts no_facts)
  have check: "lpp_check_evaluation_integer_test T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context a gs active saved yes no"
    using checked LPPEIntegerTest by simp
  show ?thesis using lpp_evaluation_integer_test_sound[OF lpp_finite_evaluation_integer_contract
    lpp_finite_evaluation_ground program check known free observed step] by auto
next
  case (LPPETermTest f a gs active saved yes no yes_facts no_facts)
  have check: "lpp_check_evaluation_term_test T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context f a gs active saved yes no"
    using checked LPPETermTest by simp
  show ?thesis using lpp_evaluation_term_test_sound[OF lpp_finite_evaluation_integer_contract
    lpp_finite_evaluation_ground program check known free observed step] by auto
next
  case (LPPEGroundDisequality a b gs active saved yes no yes_facts no_facts)
  have check: "lpp_check_evaluation_ground_disequality T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context a b gs active saved yes no"
    using checked LPPEGroundDisequality by simp
  show ?thesis using lpp_evaluation_ground_disequality_sound[OF lpp_finite_evaluation_integer_contract
    lpp_finite_evaluation_ground program check known free observed step] by auto
next
  case (LPPERationalDisequality a b gs active saved yes no yes_facts no_facts)
  have check: "lpp_check_evaluation_rational_disequality T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context a b gs active saved yes no"
    using checked LPPERationalDisequality by simp
  show ?thesis using lpp_evaluation_rational_disequality_sound[OF lpp_finite_evaluation_integer_contract
    lpp_finite_evaluation_ground program check known free observed step] by auto
next
  case (LPPEProbe f g argv m n gs active saved e fs)
  have check: "lpp_check_evaluation_probe T fs fuel Q nds states contexts Fs nd F ss source_context f g argv m n gs active saved e"
    using checked LPPEProbe by simp
  show ?thesis using lpp_evaluation_probe_sound[OF lpp_finite_evaluation_integer_contract
    lpp_finite_evaluation_ground program check known free observed step] by auto
next
  case (LPPEBranch c y z cs ys zs m n gs active saved e fs)
  have check: "lpp_check_evaluation_branch T fs fuel Q nds states contexts Fs nd F ss source_context c y z cs ys zs m n gs active saved e"
    using checked LPPEBranch by simp
  show ?thesis using lpp_evaluation_branch_sound[OF lpp_finite_evaluation_integer_contract
    lpp_finite_evaluation_ground program check known free observed step] by auto
next
  case (LPPEChoice a b left right gs active saved e fs)
  have check: "lpp_check_evaluation_choice T fs fuel Q nds states contexts Fs nd F ss source_context a b left right gs active saved e"
    using checked LPPEChoice by simp
  show ?thesis using lpp_evaluation_choice_sound[OF lpp_finite_evaluation_integer_contract
    lpp_finite_evaluation_ground program check known free observed step] by auto
next
  case (LPPEIdentity f a b gs active saved yes no yes_facts no_facts)
  have check: "lpp_check_evaluation_identity T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context f a b gs active saved yes no"
    using checked LPPEIdentity by simp
  show ?thesis using lpp_evaluation_identity_sound[OF lpp_finite_evaluation_integer_contract
    lpp_finite_evaluation_ground program check known free observed step] by auto
next
  case (LPPEComparison evidence yes_facts no_facts error_facts)
  have check: "lpp_check_evaluation_comparison T yes_facts no_facts error_facts fuel Q nds states contexts Fs nd F ss source_context
    (lppfc_predicate evidence) (lppfc_comparison evidence) (lppfc_reversed evidence)
    (lppfc_left evidence) (lppfc_right evidence) (lppfc_goals evidence) (lppfc_active evidence)
    (lppfc_saved evidence) (lppfc_yes evidence) (lppfc_no evidence) (lppfc_error evidence)"
    using checked LPPEComparison by simp
  show ?thesis using lpp_evaluation_comparison_sound[OF lpp_finite_evaluation_integer_contract
    lpp_finite_evaluation_ground program check known free observed step] by auto
qed

lemma lpp_evaluation_primitive_domain:
  fixes SP :: "string lpp_success_clause list"
  assumes program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_primitive T fuel P Q nds states contexts Fs nd F ss source_context returned arity action"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and observed: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP source_context eta"
  shows "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_finite_source_domain (map fst (lpc_return_eval eta ss))"
proof (cases action)
  case (LPPEOrdinary primitive yes_facts no_facts)
  show ?thesis
  proof (cases "primitive=LPCRInconsistent")
    case True
    have "lp_cut_check_inconsistent (lpcn_guards nd)" using checked LPPEOrdinary True by simp
    then show ?thesis using lp_cut_checked_inconsistent known by blast
  next
    case False
    show ?thesis using checked LPPEOrdinary False
      by (auto dest: lpp_no_builtin_frame_sound lpp_no_builtin_domain_bad)
  qed
next
  case (LPPEIntegerTest a gs active saved yes no yes_facts no_facts)
  then show ?thesis using checked by (simp add: lpp_check_evaluation_integer_test_def lpc_return_eval_def lpp_finite_source_domain_def)
next
  case (LPPETermTest f a gs active saved yes no yes_facts no_facts)
  have check: "lpp_check_evaluation_term_test T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context f a gs active saved yes no"
    using checked LPPETermTest by simp
  show ?thesis by (rule lpp_evaluation_term_test_domain[OF check])
next
  case (LPPEGroundDisequality a b gs active saved yes no yes_facts no_facts)
  have check: "lpp_check_evaluation_ground_disequality T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context a b gs active saved yes no"
    using checked LPPEGroundDisequality by simp
  show ?thesis by (rule lpp_evaluation_ground_disequality_domain[OF lpp_finite_evaluation_ground check known observed])
next
  case (LPPERationalDisequality a b gs active saved yes no yes_facts no_facts)
  have check: "lpp_check_evaluation_rational_disequality T yes_facts no_facts fuel Q nds states contexts Fs nd F ss source_context a b gs active saved yes no"
    using checked LPPERationalDisequality by simp
  show ?thesis by (rule lpp_evaluation_rational_disequality_domain[OF check])
next
  case (LPPEProbe f g argv m n gs active saved e fs)
  have check: "lpp_check_evaluation_probe T fs fuel Q nds states contexts Fs nd F ss source_context f g argv m n gs active saved e"
    using checked LPPEProbe by simp
  show ?thesis by (rule lpp_evaluation_probe_domain[OF check])next
  case (LPPEBranch c y z cs ys zs m n gs active saved e fs)
  have check: "lpp_check_evaluation_branch T fs fuel Q nds states contexts Fs nd F ss source_context c y z cs ys zs m n gs active saved e"
    using checked LPPEBranch by simp
  show ?thesis by (rule lpp_evaluation_branch_domain[OF check])
next
  case (LPPEChoice a b left right gs active saved e fs)
  have check: "lpp_check_evaluation_choice T fs fuel Q nds states contexts Fs nd F ss source_context a b left right gs active saved e"
    using checked LPPEChoice by simp
  show ?thesis by (rule lpp_evaluation_choice_domain[OF check])
next
  case (LPPEIdentity f a b gs active saved yes no yes_facts no_facts)
  have name: "lpp_identity_name f" and shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs),active)#saved"
    using checked LPPEIdentity by (auto simp: lpp_check_evaluation_identity_def)
  have domain: "lpp_finite_source_domain f [lp_ieval a eta,lp_ieval b eta]"
    using lpp_identity_source_domain[OF name] by (rule lpp_finite_source_domain_extends)
  show ?thesis using domain by (simp add: shape lpc_return_eval_def)
next
  case (LPPEComparison evidence yes_facts no_facts error_facts)
  have check: "lpp_check_evaluation_comparison T yes_facts no_facts error_facts fuel Q nds states contexts Fs nd F ss source_context
    (lppfc_predicate evidence) (lppfc_comparison evidence) (lppfc_reversed evidence)
    (lppfc_left evidence) (lppfc_right evidence) (lppfc_goals evidence) (lppfc_active evidence)
    (lppfc_saved evidence) (lppfc_yes evidence) (lppfc_no evidence) (lppfc_error evidence)"
    using checked LPPEComparison by simp
  show ?thesis by (rule lpp_evaluation_comparison_domain[OF lpp_finite_evaluation_integer_contract
    lpp_finite_evaluation_ground program check known observed])
qed

end
