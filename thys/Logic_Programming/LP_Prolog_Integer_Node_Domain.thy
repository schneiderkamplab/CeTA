theory LP_Prolog_Integer_Node_Domain
  imports LP_Prolog_Integer_Source
begin

lemma lpp_integer_test_node_domain:
  assumes checked: "lpp_check_integer_test_node fuel Q nds states nd ss a gs active saved yes no"
  shows "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_integer_source_domain
    (map fst (lpc_return_eval eta ss))"
  using checked by (simp add: lpp_check_integer_test_node_def lpc_return_eval_def)

lemma lpp_integer_is_node_domain:
  assumes checked: "lpp_check_integer_is_node fuel P Q nds states nd ss K evidence a e gs active saved result_var k l next mode outputs yes no"
    and integers: "lpp_integer_known K eta"
  shows "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_integer_source_domain
    (map fst (lpc_return_eval eta ss))"
proof -
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved"
    and expr: "e=lpp_expression_term evidence" and typed: "lpp_expression_check K evidence"
    using checked by (auto simp: lpp_check_integer_is_node_def)
  obtain n where "lpp_integer_evaluation (lp_ieval e eta) n"
    using lpp_checked_expression_finishes[OF typed integers] expr by blast
  then show ?thesis by (auto simp: shape lpc_return_eval_def)
qed

lemma lpp_integer_comparison_node_domain:
  assumes checked: "lpp_check_integer_comparison_node fuel Q nds states nd ss K f comparison reversed a b ea eb gs active saved yes no"
    and integers: "lpp_integer_known K eta"
  shows "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_integer_source_domain
    (map fst (lpc_return_eval eta ss))"
proof -
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs),active)#saved"
    and name: "lpp_comparison_descriptor f comparison reversed"
    and left: "a=lpp_expression_term ea" "lpp_expression_check K ea"
    and right: "b=lpp_expression_term eb" "lpp_expression_check K eb"
    using checked by (auto simp: lpp_check_integer_comparison_node_def)
  obtain n m where ev: "lpp_integer_evaluation (lp_ieval a eta) n" "lpp_integer_evaluation (lp_ieval b eta) m"
    using lpp_checked_expression_finishes[OF left(2) integers]
      lpp_checked_expression_finishes[OF right(2) integers] left(1) right(1) by blast
  have ni: "f\<noteq>''1:integer''" and ne: "f\<noteq>''2:is''"
    using name by (cases comparison; cases reversed; auto)+
  have descriptor: "lpp_source_comparison f=Some (comparison,reversed)"
    using name lpp_source_comparison_descriptor by blast
  have domain: "lpp_integer_source_domain f [lp_ieval a eta,lp_ieval b eta]"
    using ev by (simp only: lpp_integer_source_domain.simps ni ne if_False descriptor option.case; auto dest: lpp_integer_evaluation_ground)
  show ?thesis using domain
    by (simp add: shape lpc_return_eval_def del: lpp_integer_source_domain.simps)
qed

ML \<open>
val checked = [@{thm lpp_integer_test_node_domain}, @{thm lpp_integer_is_node_domain},
  @{thm lpp_integer_comparison_node_domain}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted source-node domain dependency" else ();
\<close>
end
