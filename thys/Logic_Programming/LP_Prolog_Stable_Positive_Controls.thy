theory LP_Prolog_Stable_Positive_Controls
 imports LP_Prolog_Stable_Positive_Context
begin

definition lpp_positive_control_observations :: "string lpp_numeric_observation list" where
  "lpp_positive_control_observations = [
    LPPOComparison LPPIntLess (lpp_integer_term 0) (Var ''Input''),
    LPPOEvaluation (Fun (LPCUser ''2:prolog_data_2f2f'')
      [Var ''Input'', lpp_integer_term 2]) (Var ''Result''),
    LPPOComparison LPPIntEqual (Var ''Input'')
      (Fun (LPCUser ''2:prolog_data_2a'') [Var ''Result'',lpp_integer_term 2])]"

definition lpp_positive_control_receipt where
  "lpp_positive_control_receipt = LPPPositiveQuotient 1 0 3 2
    (Var ''Input'') (lpp_integer_term 2) (Var ''Result'')"

lemma lpp_positive_control_accepts:
  "lpp_check_positive_derivation lpp_positive_control_observations
    [LPPPositiveLiteral 2,lpp_positive_control_receipt]"
  by (simp add: lpp_positive_control_observations_def lpp_positive_control_receipt_def)

lemma lpp_positive_control_rejects_missing_numerator:
  "\<not>lpp_check_positive_derivation (tl lpp_positive_control_observations)
    [LPPPositiveLiteral 2,lpp_positive_control_receipt]"
  by (simp add: lpp_positive_control_observations_def lpp_positive_control_receipt_def)

lemma lpp_positive_control_rejects_missing_exactness:
  "\<not>lpp_check_positive_derivation (take 2 lpp_positive_control_observations)
    [LPPPositiveLiteral 2,lpp_positive_control_receipt]"
  by (simp add: lpp_positive_control_observations_def lpp_positive_control_receipt_def)

lemma lpp_positive_control_rejects_future_fact:
  "\<not>lpp_check_positive_derivation lpp_positive_control_observations
    [lpp_positive_control_receipt,LPPPositiveLiteral 2]"
  by (simp add: lpp_positive_control_observations_def lpp_positive_control_receipt_def)

lemma lpp_positive_control_rejects_wrong_result:
  "\<not>lpp_check_positive_derivation lpp_positive_control_observations
    [LPPPositiveLiteral 2,LPPPositiveQuotient 1 0 3 2
      (Var ''Input'') (lpp_integer_term 2) (Var ''RequestedOutput'')]"
  by (simp add: lpp_positive_control_observations_def)

lemma lpp_positive_control_rejects_wrong_divisor:
  "\<not>lpp_check_positive_derivation lpp_positive_control_observations
    [LPPPositiveLiteral 2,LPPPositiveQuotient 1 0 3 2
      (Var ''Input'') (lpp_integer_term 3) (Var ''Result'')]"
  by (simp add: lpp_positive_control_observations_def lpp_integer_term_def)

lemma lpp_positive_control_rejects_nonpositive:
  "\<not>lpp_check_positive_derivation observations [LPPPositiveLiteral 0]"
  "\<not>lpp_check_positive_derivation observations [LPPPositiveLiteral (-2)]"
  by simp_all

lemma lpp_positive_equation_accepts:
  "lpp_check_positive_derivation [LPPOEquation (Var ''D'') (lpp_integer_term 2)]
    [LPPPositiveLiteral 2,LPPPositiveEquation 0 1 True (Var ''D'') (lpp_integer_term 2)]"
  "lpp_check_positive_derivation [LPPOEquation (lpp_integer_term 2) (Var ''D'')]
    [LPPPositiveLiteral 2,LPPPositiveEquation 0 1 False (lpp_integer_term 2) (Var ''D'')]"
  by simp_all

lemma lpp_positive_equation_rejects:
  "\<not>lpp_check_positive_derivation [LPPOEquation (Var ''D'') (lpp_integer_term 2)]
    [LPPPositiveLiteral 2,LPPPositiveEquation 0 1 False (Var ''D'') (lpp_integer_term 2)]"
  "\<not>lpp_check_positive_derivation []
    [LPPPositiveLiteral 2,LPPPositiveEquation 0 1 True (Var ''D'') (lpp_integer_term 2)]"
  "\<not>lpp_check_positive_derivation [LPPOEquation (Var ''D'') (lpp_integer_term 2)]
    [LPPPositiveLiteral 2,LPPPositiveEquation 0 1 True (Var ''Different'') (lpp_integer_term 2)]"
  by (simp_all add: lpp_integer_term_def)

lemma lpp_positive_integer_lower_accepts:
  "lpp_check_positive_derivation
    [LPPOInteger (Var ''Q''),LPPOComparison LPPIntLess (lpp_integer_term 0) (Var ''Q'')]
    [LPPPositiveIntegerLower 0 1 (Var ''Q'')]"
  by simp

lemma lpp_positive_integer_lower_rejects:
  "\<not>lpp_check_positive_derivation
    [LPPOGround (Var ''Q''),LPPOComparison LPPIntLess (lpp_integer_term 0) (Var ''Q'')]
    [LPPPositiveIntegerLower 0 1 (Var ''Q'')]"
  "\<not>lpp_check_positive_derivation [LPPOInteger (Var ''Q'')]
    [LPPPositiveIntegerLower 0 1 (Var ''Q'')]"
  "\<not>lpp_check_positive_derivation
    [LPPOInteger (Var ''Q''),LPPOComparison LPPIntLess (lpp_integer_term 0) (Var ''Other'')]
    [LPPPositiveIntegerLower 0 1 (Var ''Q'')]"
  by simp_all

ML \<open>
val checked = @{thms lpp_positive_integer_lower_accepts lpp_positive_integer_lower_rejects lpp_positive_equation_accepts lpp_positive_equation_rejects lpp_positive_control_accepts
  lpp_positive_control_rejects_missing_numerator lpp_positive_control_rejects_missing_exactness
  lpp_positive_control_rejects_future_fact lpp_positive_control_rejects_wrong_result
  lpp_positive_control_rejects_wrong_divisor lpp_positive_control_rejects_nonpositive};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted positive context controls" else ();
\<close>
end
