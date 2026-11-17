theory LP_Prolog_Finite_Comparison_Test
 imports LP_Prolog_Finite_Direct_Comparison
begin

definition lpp_test_open_expression :: "(string lp_cut_symbol,string) lp_iterm" where
 "lpp_test_open_expression = LPIFun (LPCUser ''2:prolog_data_2b'')
   [LPIVar ''argument'',lpp_integer_value 1]"

lemma finite_compound_error:
 "lpp_finite_compare_outcome comparison lpp_test_open_expression (lpp_integer_value 0) outcome =
  (outcome=LPPBuiltinError)"
 by (auto simp: lpp_test_open_expression_def lpp_integer_value_def
   lpp_finite_compare_outcome_def lpp_finite_compare_error_def lp_seg_ground.simps)

lemma finite_compound_domain:
 "lpp_finite_source_domain ''2:>'' [lpp_test_open_expression,lpp_integer_value 0]"
 by (rule lpp_finite_comparison_source_domain[where comparison=LPPIntLess and reversed=True])
   (auto simp: lpp_test_open_expression_def lpp_integer_value_def)

primcorec lpp_test_cyclic_operand :: "(string lp_cut_symbol,string) lp_iterm" where
 "lpp_test_cyclic_operand = LPIFun (LPCUser ''1:cycle'') [lpp_test_cyclic_operand]"

lemma finite_operand_not_cyclic:
 "lpp_finite_term t \<Longrightarrow> t\<noteq>lpp_test_cyclic_operand"
proof (induct rule: lpp_finite_term.induct)
 case (variable x)
 then show ?case by (subst lpp_test_cyclic_operand.code) simp
next
 case (node ts f)
 show ?case
 proof
  assume equal: "LPIFun f ts=lpp_test_cyclic_operand"
  have "ts=[lpp_test_cyclic_operand]"
   using equal by (subst (asm) lpp_test_cyclic_operand.code) simp
  then show False using node by simp
 qed
qed

lemma cyclic_operand_is_not_error_evidence:
 "\<not>lpp_finite_compare_error (LPIVar x) lpp_test_cyclic_operand"
 using finite_operand_not_cyclic by (auto simp: lpp_finite_compare_error_def)

ML \<open>
val checked = [@{thm finite_compound_error}, @{thm finite_compound_domain},
 @{thm finite_operand_not_cyclic}, @{thm cyclic_operand_is_not_error_evidence}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite comparison regression" else ();
\<close>
end
