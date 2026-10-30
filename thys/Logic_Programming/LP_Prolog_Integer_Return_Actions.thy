theory LP_Prolog_Integer_Return_Actions
  imports LP_Prolog_Operation_Context
begin

text \<open>The arithmetic source extension uses the existing return table,
links, unification receipts and cut actions. Numeric operations add only their
typed primitive checks. No alternative stack or return semantics is defined.\<close>

datatype lpp_integer_return_action = LPPIRCut "string lpc_return_action"
  | LPPIRTest "string lpc_term" "string lpc_term lp_cut_goal list"
      "string lpc_term list" "string lpc_return_state" "string lpc_link" "string lpc_link"
  | LPPIRCompare "string list" string lpp_integer_comparison bool
      "string lpc_term" "string lpc_term" "string lpp_integer_expression" "string lpp_integer_expression"
      "string lpc_term lp_cut_goal list" "string lpc_term list" "string lpc_return_state"
      "string lpc_link" "string lpc_link"
  | LPPIRIs "string list" "string lpp_integer_expression" "string lpc_term" "string lpc_term"
      "string lpc_term lp_cut_goal list" "string lpc_term list" "string lpc_return_state"
      string nat nat "string lpc_term lp_cut_goal list" lp_cut_coverage
      "string lpc_term list" "string lpc_link" "string lpc_link"

fun lpp_integer_action_types where
  "lpp_integer_action_types (LPPIRCut action) = []"
| "lpp_integer_action_types (LPPIRTest a gs active saved yes no) = []"
| "lpp_integer_action_types (LPPIRCompare K f comparison reversed a b ea eb gs active saved yes no) = K"
| "lpp_integer_action_types (LPPIRIs K evidence a e gs active saved result_var k l continuation mode outputs yes no) = K"

fun lpp_check_integer_return_action where
  "lpp_check_integer_return_action fuel P Q nds states nd ss returned arity (LPPIRCut action) =
    (lpp_no_builtin_frame ss \<and> lpc_check_return_action fuel P Q nds states nd ss returned arity action)"
| "lpp_check_integer_return_action fuel P Q nds states nd ss returned arity (LPPIRTest a gs active saved yes no) =
    lpp_check_integer_test_node fuel Q nds states nd ss a gs active saved yes no"
| "lpp_check_integer_return_action fuel P Q nds states nd ss returned arity
    (LPPIRCompare K f comparison reversed a b ea eb gs active saved yes no) =
    lpp_check_integer_comparison_node fuel Q nds states nd ss K f comparison reversed a b ea eb gs active saved yes no"
| "lpp_check_integer_return_action fuel P Q nds states nd ss returned arity
    (LPPIRIs K evidence a e gs active saved result_var k l continuation mode outputs yes no) =
    lpp_check_integer_is_node fuel P Q nds states nd ss K evidence a e gs active saved result_var k l continuation mode outputs yes no"

theorem lpp_integer_return_action_sound:
  assumes checked: "lpp_check_integer_return_action fuel P Q nds states nd ss returned arity action"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and integers: "lpp_integer_known (lpp_integer_action_types action) eta"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin
      (lpc_return_eval eta ss) event tt"
  shows "(\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
      lpc_return_rep nds states (lpc_return_scope_word swaps tt) u) \<and>
    (\<forall>rho. event=Some rho \<longrightarrow>
      ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*)"
proof (cases action)
  case (LPPIRCut primitive)
  have clear: "lpp_no_builtin_frame ss" and check: "lpc_check_return_action fuel P Q nds states nd ss returned arity primitive"
    using checked LPPIRCut by auto
  show ?thesis by (rule lpc_return_action_sound[OF check known lpp_integer_source_nonbuiltin_base[OF clear step]])
next
  case (LPPIRTest a gs active saved yes no)
  have check: "lpp_check_integer_test_node fuel Q nds states nd ss a gs active saved yes no"
    using checked LPPIRTest by simp
  have exact: "\<And>outcome. lpp_integer_source_builtin ''1:integer'' [lp_ieval a eta] outcome =
    lpp_integer_test_outcome (lp_ieval a eta) outcome" by simp
  show ?thesis using lpp_integer_test_node_sound[OF check known exact step] by auto
next
  case (LPPIRCompare K f comparison reversed a b ea eb gs active saved yes no)
  have check: "lpp_check_integer_comparison_node fuel Q nds states nd ss K f comparison reversed a b ea eb gs active saved yes no"
    using checked LPPIRCompare by simp
  have typed: "lpp_integer_known K eta" using integers LPPIRCompare by simp
  have descriptor: "lpp_comparison_descriptor f comparison reversed"
    using check by (simp add: lpp_check_integer_comparison_node_def)
  have exact: "\<And>outcome. lpp_integer_source_builtin f [lp_ieval a eta,lp_ieval b eta] outcome =
    lpp_integer_compare_outcome comparison
      (if reversed then lp_ieval b eta else lp_ieval a eta)
      (if reversed then lp_ieval a eta else lp_ieval b eta) outcome"
    by (rule lpp_integer_source_comparison[OF descriptor])
  show ?thesis using lpp_integer_comparison_node_sound[OF check known typed exact step] by auto
next
  case (LPPIRIs K evidence a e gs active saved result_var k l continuation mode outputs yes no)
  have check: "lpp_check_integer_is_node fuel P Q nds states nd ss K evidence a e gs active saved result_var k l continuation mode outputs yes no"
    using checked LPPIRIs by simp
  have typed: "lpp_integer_known K eta" using integers LPPIRIs by simp
  have exact: "\<And>outcome. lpp_integer_source_builtin ''2:is'' [lp_ieval a eta,lp_ieval e eta] outcome =
    lpp_integer_is_outcome (lp_ieval a eta) (lp_ieval e eta) outcome" by simp
  show ?thesis using lpp_integer_is_node_sound[OF check known typed exact step] by auto
qed

lemma lpp_no_builtin_domain_bad:
  "\<not>lpp_builtin_active B s \<Longrightarrow> \<not>lpp_builtin_domain_bad B D s"
  by (cases "(B,D,s)" rule: lpp_builtin_domain_bad.cases) (auto simp: lpp_builtin_active_def)

theorem lpp_integer_return_action_domain:
  assumes checked: "lpp_check_integer_return_action fuel P Q nds states nd ss returned arity action"
    and integers: "lpp_integer_known (lpp_integer_action_types action) eta"
  shows "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_integer_source_domain
    (map fst (lpc_return_eval eta ss))"
  using checked integers
  by (cases action)
    (auto dest: lpp_no_builtin_domain_bad lpp_no_builtin_frame_sound
      lpp_integer_test_node_domain lpp_integer_comparison_node_domain lpp_integer_is_node_domain)

ML \<open>
val checked = [@{thm lpp_integer_return_action_sound}, @{thm lpp_integer_return_action_domain}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted integer return-action dependency" else ();
\<close>
end
