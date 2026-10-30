theory LP_Prolog_Context_Actions
 imports LP_Prolog_Context_Cut_Actions
begin
fun lpp_check_context_action where
  "lpp_check_context_action fuel P Q nds states contexts nd ss source_context returned arity (LPPIRCut action) =
    (lpp_no_builtin_frame ss \<and> lpp_check_context_cut_action fuel P Q nds states contexts nd ss source_context returned arity action)"
| "lpp_check_context_action fuel P Q nds states contexts nd ss source_context returned arity (LPPIRTest a gs active saved yes no) =
    lpp_check_context_integer_test fuel Q nds states contexts nd ss source_context a gs active saved yes no"
| "lpp_check_context_action fuel P Q nds states contexts nd ss source_context returned arity
    (LPPIRCompare K f comparison reversed a b ea eb gs active saved yes no) =
    lpp_check_context_comparison fuel Q nds states contexts nd ss source_context K f comparison reversed a b ea eb gs active saved yes no"
| "lpp_check_context_action fuel P Q nds states contexts nd ss source_context returned arity
    (LPPIRIs K evidence a e gs active saved result_var k l continuation mode outputs yes no) =
    lpp_check_context_is_node fuel P Q nds states contexts nd ss source_context K evidence a e gs active saved result_var k l continuation mode outputs yes no"

theorem lpp_context_action_sound:
  assumes checked: "lpp_check_context_action fuel P Q nds states contexts nd ss source_context returned arity action"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and observed: "lpp_source_context_holds SP source_context eta"
    and integers: "lpp_integer_known (lpp_integer_action_types action) eta"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin
      (lpc_return_eval eta ss) event tt"
  shows "(\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
      lpp_context_return_rep SP nds states contexts (lpc_return_scope_word swaps tt) u) \<and>
    (\<forall>rho. event=Some rho \<longrightarrow>
      ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*)"
proof (cases action)
  case (LPPIRCut primitive)
  have clear: "lpp_no_builtin_frame ss" and check: "lpp_check_context_cut_action fuel P Q nds states contexts nd ss source_context returned arity primitive"
    using checked LPPIRCut by auto
  show ?thesis by (rule lpp_context_cut_action_sound[OF check known observed lpp_integer_source_nonbuiltin_base[OF clear step]])
next
  case (LPPIRTest a gs active saved yes no)
  have check: "lpp_check_context_integer_test fuel Q nds states contexts nd ss source_context a gs active saved yes no"
    using checked LPPIRTest by simp
  have exact: "\<And>outcome. lpp_integer_source_builtin ''1:integer'' [lp_ieval a eta] outcome =
    lpp_integer_test_outcome (lp_ieval a eta) outcome" by simp
  show ?thesis using lpp_context_integer_test_sound[OF check known observed step] by auto
next
  case (LPPIRCompare K f comparison reversed a b ea eb gs active saved yes no)
  have check: "lpp_check_context_comparison fuel Q nds states contexts nd ss source_context K f comparison reversed a b ea eb gs active saved yes no"
    using checked LPPIRCompare by simp
  have typed: "lpp_integer_known K eta" using integers LPPIRCompare by simp
  have descriptor: "lpp_comparison_descriptor f comparison reversed"
    using check by (simp add: lpp_check_context_comparison_def lpp_check_integer_comparison_node_def)
  show ?thesis using lpp_context_comparison_sound[OF check known typed observed step] by auto
next
  case (LPPIRIs K evidence a e gs active saved result_var k l continuation mode outputs yes no)
  have check: "lpp_check_context_is_node fuel P Q nds states contexts nd ss source_context K evidence a e gs active saved result_var k l continuation mode outputs yes no"
    using checked LPPIRIs by simp
  have typed: "lpp_integer_known K eta" using integers LPPIRIs by simp
  have exact: "\<And>outcome. lpp_integer_source_builtin ''2:is'' [lp_ieval a eta,lp_ieval e eta] outcome =
    lpp_integer_is_outcome (lp_ieval a eta) (lp_ieval e eta) outcome" by simp
  show ?thesis using lpp_context_is_node_sound[OF check known observed typed exact step] by auto
qed


lemma lpp_context_is_erases:
  "lpp_check_context_is_node fuel P Q nds states contexts nd ss source_context K evidence a e gs active saved result_var k l continuation mode outputs yes no \<Longrightarrow>
   lpp_check_integer_is_node fuel P Q nds states nd ss K evidence a e gs active saved result_var k l continuation mode outputs yes no"
  by (auto simp: lpp_check_context_is_node_def lpp_check_integer_is_node_def
    lpp_check_context_equality_node_def lpc_check_return_equality_node_def lpp_check_context_table_link_def)

lemma lpp_context_action_domain:
  assumes checked: "lpp_check_context_action fuel P Q nds states contexts nd ss source_context returned arity action"
    and integers: "lpp_integer_known (lpp_integer_action_types action) eta"
  shows "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_integer_source_domain (map fst (lpc_return_eval eta ss))"
proof (cases action)
  case (LPPIRCut primitive)
  show ?thesis using checked LPPIRCut by (auto dest: lpp_no_builtin_frame_sound lpp_no_builtin_domain_bad)
next
  case (LPPIRTest a gs active saved yes no)
  show ?thesis using checked LPPIRTest by (simp add: lpp_check_context_integer_test_def lpc_return_eval_def)
next
  case (LPPIRCompare K f comparison reversed a b ea eb gs active saved yes no)
  show ?thesis using checked integers LPPIRCompare
    by (auto simp: lpp_check_context_comparison_def dest: lpp_integer_comparison_node_domain)
next
  case (LPPIRIs K evidence a e gs active saved result_var k l continuation mode outputs yes no)
  show ?thesis using checked integers LPPIRIs
    by (auto dest: lpp_context_is_erases lpp_integer_is_node_domain)
qed

fun lpp_check_context_typing where
  "lpp_check_context_typing T (facts,guards,observations) fs K = lpp_check_operation_context T facts guards fs K"

lemma lpp_context_typing_sound:
  fixes SP :: "string lpp_success_clause list"
    and source_context :: "string lpp_source_context"
  assumes program: "lpp_check_transfer_program T SP receipts"
    and typing: "lpp_check_context_typing T source_context fs K"
    and observed: "lpp_source_context_holds SP source_context eta"
  shows "lpp_integer_known K eta"
proof -
  obtain facts guards observations where shape: "source_context=(facts,guards,observations)"
    by (cases source_context) auto
  have check: "lpp_check_operation_context T facts guards fs K" using typing by (simp add: shape)
  have gs: "list_all (lpp_success_guard_holds lpp_integer_result eta) guards"
    and ps: "list_all (lpp_guarded_success SP lpp_integer_result) (map (\<lambda>b. lpp_success_atom_eval b eta) facts)"
    using observed by (auto simp: shape lpp_path_context_holds_def list_all_iff)
  show ?thesis by (rule lpp_checked_operation_context[OF program check gs ps])
qed

ML \<open>
val checked = [@{thm lpp_context_action_sound}, @{thm lpp_context_action_domain}, @{thm lpp_context_typing_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted contextual source action dependency" else ();
\<close>
end
