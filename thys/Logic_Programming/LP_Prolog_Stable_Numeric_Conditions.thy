theory LP_Prolog_Stable_Numeric_Conditions
 imports LP_Prolog_Stable_Magnitude_Conditions
begin

datatype 'v lpp_stable_condition_receipt =
    LPPStableMagnitudeLiteralOrderCondition int bool "(string lp_cut_symbol,'v) term"
  |     LPPStableMagnitudeOrderCondition bool "(string lp_cut_symbol,'v) term" "(string lp_cut_symbol,'v) term"
  | LPPStableMagnitudeModuloCondition "(string lp_cut_symbol,'v) term" "(string lp_cut_symbol,'v) term" "(string lp_cut_symbol,'v) term"
  | LPPStableMagnitudeQuotientModuloCondition "(string lp_cut_symbol,'v) term" "(string lp_cut_symbol,'v) term" "(string lp_cut_symbol,'v) term" "(string lp_cut_symbol,'v) term"
  | LPPStableScaledQuotientModuloCondition "(string lp_cut_symbol,'v) term" "(string lp_cut_symbol,'v) term" "(string lp_cut_symbol,'v) term" "(string lp_cut_symbol,'v) term"
  | LPPStableScaledOrderCondition bool "(string lp_cut_symbol,'v) term" "(string lp_cut_symbol,'v) term"
  | LPPStableScaledModuloCondition "(string lp_cut_symbol,'v) term" "(string lp_cut_symbol,'v) term" "(string lp_cut_symbol,'v) term"
  | LPPStableIgnoredCondition
  | LPPStableIntegerCondition "'v lpp_numeric_condition"
  | LPPStableUpperCondition "'v lpp_integer_expression" "(string lp_cut_symbol,'v) term"

  | LPPStableQuotientCondition "(string lp_cut_symbol,'v) term" int "(string lp_cut_symbol,'v) term"

  | LPPStableQuotientMagnitudeUpperCondition "'v lpp_integer_expression" "(string lp_cut_symbol,'v) term" "(string lp_cut_symbol,'v) term"

  | LPPStableQuotientUpperCondition "'v lpp_integer_expression" "(string lp_cut_symbol,'v) term" int

  | LPPStableModuloDescentCondition "(string lp_cut_symbol,'v) term" "(string lp_cut_symbol,'v) term" "(string lp_cut_symbol,'v) term"

  | LPPStableQuotientDescentCondition "(string lp_cut_symbol,'v) term" "(string lp_cut_symbol,'v) term" "(string lp_cut_symbol,'v) term"

fun lpp_check_stable_numeric_observation where
  "lpp_check_stable_numeric_observation K observation (LPPStableMagnitudeLiteralOrderCondition n is_strict b) =
    (0\<le>n \<and> observation=LPPOComparison (if is_strict then LPPIntLess else LPPIntLessEqual) (lpp_integer_term n) b)"
|   "lpp_check_stable_numeric_observation K observation (LPPStableMagnitudeOrderCondition is_strict a b) = False"
|   "lpp_check_stable_numeric_observation K observation (LPPStableMagnitudeModuloCondition a b result) = False"
|   "lpp_check_stable_numeric_observation K observation (LPPStableMagnitudeQuotientModuloCondition a n d result) = False"
|   "lpp_check_stable_numeric_observation K observation (LPPStableScaledQuotientModuloCondition a n d result) = False"
|  "lpp_check_stable_numeric_observation K observation (LPPStableScaledOrderCondition is_strict a b) =
    (observation=LPPOComparison (if is_strict then LPPIntLess else LPPIntLessEqual) a b)"
| "lpp_check_stable_numeric_observation K observation (LPPStableScaledModuloCondition a b result) = False"
|  "lpp_check_stable_numeric_observation K observation (LPPStableIntegerCondition test) =
    lpp_check_numeric_observation K observation test"
| "lpp_check_stable_numeric_observation K observation (LPPStableUpperCondition expression bound_term) =
    lpp_check_stable_upper_observation K observation expression bound_term"
| "lpp_check_stable_numeric_observation K observation (LPPStableQuotientCondition a d result) =
    (0<d \<and> observation=LPPOEvaluation
      (Fun (LPCUser ''2:prolog_data_2f2f'') [a,lpp_integer_term d]) result)"
| "lpp_check_stable_numeric_observation K observation (LPPStableQuotientMagnitudeUpperCondition expression a b) =
    lpp_check_stable_upper_observation K observation expression (Fun (LPCUser ''2:prolog_data_2f2f'') [a,b])"
| "lpp_check_stable_numeric_observation K observation (LPPStableQuotientUpperCondition expression a d) =
    (0<d \<and> lpp_check_stable_upper_observation K observation expression
      (Fun (LPCUser ''2:prolog_data_2f2f'') [a,lpp_integer_term d]))"
| "lpp_check_stable_numeric_observation K observation (LPPStableModuloDescentCondition a b result) = False"
| "lpp_check_stable_numeric_observation K observation (LPPStableQuotientDescentCondition a b result) = False"
| "lpp_check_stable_numeric_observation K observation LPPStableIgnoredCondition = True"

fun lpp_stable_numeric_condition where
  "lpp_stable_numeric_condition (LPPStableMagnitudeLiteralOrderCondition n is_strict b) =
    ((if is_strict then LPPIntLess else LPPIntLessEqual),LPPEConstant (n*lpp_scalar_scale),lpp_magnitude_expression b)"
|   "lpp_stable_numeric_condition (LPPStableMagnitudeOrderCondition is_strict a b) = (LPPIntEqual,LPPEConstant 0,LPPEConstant 0)"
|   "lpp_stable_numeric_condition (LPPStableMagnitudeModuloCondition a b result) = (LPPIntEqual,LPPEConstant 0,LPPEConstant 0)"
|   "lpp_stable_numeric_condition (LPPStableMagnitudeQuotientModuloCondition a n d result) = (LPPIntEqual,LPPEConstant 0,LPPEConstant 0)"
|   "lpp_stable_numeric_condition (LPPStableScaledQuotientModuloCondition a n d result) = (LPPIntEqual,LPPEConstant 0,LPPEConstant 0)"
|  "lpp_stable_numeric_condition (LPPStableScaledOrderCondition is_strict a b) =
    ((if is_strict then LPPIntLess else LPPIntLessEqual),lpp_scaled_expression a,lpp_scaled_expression b)"
| "lpp_stable_numeric_condition (LPPStableScaledModuloCondition a b result) = (LPPIntEqual,LPPEConstant 0,LPPEConstant 0)"
|  "lpp_stable_numeric_condition (LPPStableIntegerCondition test) =
    lpp_rename_numeric_condition LPPIntegerKey test"
| "lpp_stable_numeric_condition (LPPStableUpperCondition expression bound_term) =
    lpp_stable_upper_condition expression bound_term"
| "lpp_stable_numeric_condition (LPPStableQuotientCondition a d result) = (LPPIntEqual,LPPEConstant 0,LPPEConstant 0)"
| "lpp_stable_numeric_condition (LPPStableQuotientMagnitudeUpperCondition expression a b) = (LPPIntEqual,LPPEConstant 0,LPPEConstant 0)"
| "lpp_stable_numeric_condition (LPPStableQuotientUpperCondition expression a d) =
    lpp_stable_upper_condition expression (Fun (LPCUser ''2:prolog_data_2f2f'') [a,lpp_integer_term d])"
| "lpp_stable_numeric_condition (LPPStableModuloDescentCondition a b result) = (LPPIntEqual,LPPEConstant 0,LPPEConstant 0)"
| "lpp_stable_numeric_condition (LPPStableQuotientDescentCondition a b result) = (LPPIntEqual,LPPEConstant 0,LPPEConstant 0)"
| "lpp_stable_numeric_condition LPPStableIgnoredCondition = (LPPIntEqual,LPPEConstant 0,LPPEConstant 0)"

lemma lpp_stable_observation_finite_envelope:
  assumes compatible: "lpp_stable_integer_operations operation"
    and observed: "lpp_stable_observation_holds operation eta observation"
  shows "lpp_evaluation_observation_holds lpp_finite_evaluation_result eta observation"
  using observed lpp_stable_evaluation_finite_envelope[OF compatible]
    by (cases observation) (auto dest: lpp_stable_compare_refines_finite)

theorem lpp_checked_stable_numeric_condition:
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_stable_numeric_observation K observation receipt"
    and observed: "lpp_stable_observation_holds operation eta observation"
    and typed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (source_values x)"
  shows "lpp_numeric_condition_holds (lpp_stable_key_value operation eta source_values)
    (lpp_stable_numeric_condition receipt)"
proof (cases receipt)
  case (LPPStableMagnitudeLiteralOrderCondition n is_strict b)
  have sign: "0\<le>n" and order: "lpp_stable_compare_outcome operation
    (if is_strict then LPPIntLess else LPPIntLessEqual) (lpp_integer_value n) (lp_ieval b eta) (LPPBuiltinSuccess LPIVar)"
    using checked observed by (auto simp: LPPStableMagnitudeLiteralOrderCondition)
  have nonnegative: "0\<le>lpp_stable_scaled_bound operation (lpp_integer_value n)"
    using sign lpp_scalar_scale_positive by (simp add: lpp_stable_scaled_integer[OF lpp_stable_integer_literal])
  have bound: "lpp_integer_compare (if is_strict then LPPIntLess else LPPIntLessEqual)
    (abs (lpp_stable_scaled_bound operation (lpp_integer_value n)))
    (abs (lpp_stable_scaled_bound operation (lp_ieval b eta)))"
    by (rule lpp_stable_magnitude_order[OF order nonnegative])
  show ?thesis using bound sign lpp_scalar_scale_positive
    by (simp add: LPPStableMagnitudeLiteralOrderCondition lpp_stable_scaled_integer[OF lpp_stable_integer_literal] lpp_magnitude_expression_value abs_mult)
next
  case (LPPStableMagnitudeOrderCondition is_strict a b)
  then show ?thesis by simp
next
  case (LPPStableMagnitudeModuloCondition a b result)
  then show ?thesis by simp
next
  case (LPPStableMagnitudeQuotientModuloCondition a n d result)
  then show ?thesis by simp
next
  case (LPPStableScaledQuotientModuloCondition a n d result)
  then show ?thesis by simp
next
  case (LPPStableScaledOrderCondition is_strict a b)
  have observed_order: "lpp_stable_compare_outcome operation (if is_strict then LPPIntLess else LPPIntLessEqual)
      (lp_ieval a eta) (lp_ieval b eta) (LPPBuiltinSuccess LPIVar)"
    using checked observed by (simp add: LPPStableScaledOrderCondition)
  show ?thesis using lpp_stable_scaled_comparison[OF observed_order]
    by (simp add: LPPStableScaledOrderCondition lpp_scaled_expression_value)
next
  case (LPPStableScaledModuloCondition a b result)
  then show ?thesis by simp
next
  case (LPPStableQuotientMagnitudeUpperCondition expression a b)
  then show ?thesis by simp
next
  case (LPPStableModuloDescentCondition a b result)
  then show ?thesis by simp
next
  case (LPPStableQuotientDescentCondition a b result)
  then show ?thesis by simp
next
  case (LPPStableQuotientCondition a d result)
  then show ?thesis by simp
next
  case LPPStableIgnoredCondition
  then show ?thesis by simp
next
  case (LPPStableIntegerCondition test)
  have check: "lpp_check_numeric_observation K observation test"
    using checked by (simp add: LPPStableIntegerCondition)
  have known: "lpp_integer_known K eta"
    using typed by (auto simp: lpp_integer_known_def)
  have finite: "lpp_evaluation_observation_holds lpp_finite_evaluation_result eta observation"
    by (rule lpp_stable_observation_finite_envelope[OF compatible observed])
  have numeric: "lpp_numeric_observation_holds eta observation"
    by (rule lpp_finite_numeric_observation_integer[OF check known finite])
  have result: "lpp_numeric_condition_holds source_values test"
    by (rule lpp_check_numeric_observation_sound[OF check numeric typed])
  show ?thesis using result by (simp add: LPPStableIntegerCondition lpp_rename_numeric_condition_holds o_def)
next
  case (LPPStableQuotientUpperCondition expression a d)
  have check: "lpp_check_stable_upper_observation K observation expression
      (Fun (LPCUser ''2:prolog_data_2f2f'') [a,lpp_integer_term d])"
    using checked by (simp add: LPPStableQuotientUpperCondition)
  show ?thesis unfolding LPPStableQuotientUpperCondition lpp_stable_numeric_condition.simps
    by (rule lpp_checked_stable_upper_condition[OF compatible check observed])
      (use typed in auto)
next
  case (LPPStableUpperCondition expression bound_term)
  have check: "lpp_check_stable_upper_observation K observation expression bound_term"
    using checked by (simp add: LPPStableUpperCondition)
  have result: "lpp_numeric_condition_holds (lpp_stable_key_value operation eta source_values)
      (lpp_stable_upper_condition expression bound_term)"
    by (rule lpp_checked_stable_upper_condition[OF compatible check observed])
      (use typed in auto)
  show ?thesis using result by (simp add: LPPStableUpperCondition)
qed

fun lpp_numeric_condition_keys where
  "lpp_numeric_condition_keys (comparison,a,b) = set_lpp_integer_expression a \<union> set_lpp_integer_expression b"

lemma lpp_numeric_condition_value_cong:
  assumes equal: "\<And>x. x\<in>lpp_numeric_condition_keys test \<Longrightarrow> f x=g x"
  shows "lpp_numeric_condition_holds f test = lpp_numeric_condition_holds g test"
proof -
  obtain c a b where test: "test=(c,a,b)" by (cases test) auto
  have left: "lpp_expression_value a f=lpp_expression_value a g"
    by (rule lpp_stable_expression_value_cong) (use equal in \<open>auto simp: test\<close>)
  have right: "lpp_expression_value b f=lpp_expression_value b g"
    by (rule lpp_stable_expression_value_cong) (use equal in \<open>auto simp: test\<close>)
  show ?thesis by (simp add: test left right)
qed

lemma lpp_stable_numeric_condition_formula_sound:
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_stable_numeric_observation K observation receipt"
    and observed: "lpp_stable_observation_holds operation eta observation"
    and typed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (source_values x)"
    and assigned: "\<And>key. key\<in>lpp_numeric_condition_keys (lpp_stable_numeric_condition receipt) \<Longrightarrow>
      rho (rename key)=lpp_stable_key_value operation eta source_values key"
  shows "IA4.satisfies (lpp_integer_assignment rho)
    (lpp_numeric_condition_formula (lpp_rename_numeric_condition rename (lpp_stable_numeric_condition receipt)))"
proof -
  have truth: "lpp_numeric_condition_holds (lpp_stable_key_value operation eta source_values)
    (lpp_stable_numeric_condition receipt)"
    by (rule lpp_checked_stable_numeric_condition[OF compatible checked observed typed])
  have renamed: "lpp_numeric_condition_holds rho
    (lpp_rename_numeric_condition rename (lpp_stable_numeric_condition receipt))"
    unfolding lpp_rename_numeric_condition_holds
    using truth lpp_numeric_condition_value_cong[of "lpp_stable_numeric_condition receipt"
      "rho o rename" "lpp_stable_key_value operation eta source_values"] assigned by auto
  show ?thesis using renamed by (cases "lpp_stable_numeric_condition receipt")
    (auto simp: lpp_comparison_typed_assignment split: prod.splits)
qed

fun lpp_stable_receipt_keys where
  "lpp_stable_receipt_keys (LPPStableMagnitudeOrderCondition is_strict a b) = set_lpp_integer_expression (lpp_magnitude_expression a) \<union> set_lpp_integer_expression (lpp_magnitude_expression b)"
|   "lpp_stable_receipt_keys (LPPStableMagnitudeModuloCondition a b result) = {LPPMagnitudeKey b,LPPMagnitudeKey result}"
|   "lpp_stable_receipt_keys (LPPStableMagnitudeQuotientModuloCondition a n d result) = {LPPMagnitudeKey n,LPPMagnitudeKey result,LPPMagnitudeKey (Fun (LPCUser ''2:prolog_data_2f2f'') [n,d])}"
|   "lpp_stable_receipt_keys (LPPStableScaledQuotientModuloCondition a n d result) = {LPPScaledKey n,LPPScaledKey result,LPPScaledKey (Fun (LPCUser ''2:prolog_data_2f2f'') [n,d])}"
|  "lpp_stable_receipt_keys (LPPStableScaledModuloCondition a b result) = {LPPScaledKey b,LPPScaledKey result}"
|  "lpp_stable_receipt_keys (LPPStableQuotientCondition a d result) = {LPPBoundKey a,LPPBoundKey result}"
| "lpp_stable_receipt_keys (LPPStableQuotientMagnitudeUpperCondition expression a b) =
    insert (LPPBoundKey a) (LPPIntegerKey ` set_lpp_integer_expression expression)"
| "lpp_stable_receipt_keys (LPPStableQuotientUpperCondition expression a d) =
    insert (LPPBoundKey a) (lpp_numeric_condition_keys (lpp_stable_numeric_condition
      (LPPStableQuotientUpperCondition expression a d)))"
| "lpp_stable_receipt_keys (LPPStableModuloDescentCondition a b result) = {LPPBoundKey b,LPPBoundKey result}"
| "lpp_stable_receipt_keys (LPPStableQuotientDescentCondition a b result) = {LPPBoundKey a,LPPBoundKey result}"
| "lpp_stable_receipt_keys receipt = lpp_numeric_condition_keys (lpp_stable_numeric_condition receipt)"

definition lpp_stable_quotient_formula where
  "lpp_stable_quotient_formula rename a d result =
    (let n=LPPEVariable (rename (LPPBoundKey a));
         q=LPPEVariable (rename (LPPBoundKey result)); z=LPPEConstant 0 in
      Disjunction [Conjunction [
        lpp_numeric_condition_formula (LPPIntLessEqual,z,n),
        lpp_numeric_condition_formula (LPPIntEqual,q,LPPEDivide n d)],
      Conjunction [lpp_numeric_condition_formula (LPPIntLess,n,z),
        lpp_numeric_condition_formula (LPPIntEqual,q,LPPENegate (LPPEDivide (LPPENegate n) d))]])"

definition lpp_stable_quotient_descent_formula where
  "lpp_stable_quotient_descent_formula rename a result =
    (let n=LPPEVariable (rename (LPPBoundKey a));
         q=LPPEVariable (rename (LPPBoundKey result)) in
      Conjunction [lpp_numeric_condition_formula (LPPIntLessEqual,LPPEConstant 0,q),
        lpp_numeric_condition_formula (LPPIntLess,q,n)])"

definition lpp_stable_quotient_magnitude_formula where
  "lpp_stable_quotient_magnitude_formula rename expression a =
    (let n=LPPEVariable (rename (LPPBoundKey a));
         c=map_lpp_integer_expression (rename o LPPIntegerKey) expression in
      Disjunction [lpp_numeric_condition_formula (LPPIntLessEqual,c,n),
        lpp_numeric_condition_formula (LPPIntLessEqual,c,LPPENegate n)])"

fun lpp_stable_receipt_formula where
  "lpp_stable_receipt_formula rename (LPPStableMagnitudeOrderCondition is_strict a b) = lpp_numeric_condition_formula (lpp_rename_numeric_condition rename ((if is_strict then LPPIntLess else LPPIntLessEqual),lpp_magnitude_expression a,lpp_magnitude_expression b))"
|   "lpp_stable_receipt_formula rename (LPPStableMagnitudeModuloCondition a b result) = lpp_stable_magnitude_progress_formula rename b result"
|   "lpp_stable_receipt_formula rename (LPPStableMagnitudeQuotientModuloCondition a n d result) = lpp_stable_magnitude_quotient_modulo_formula rename n d result"
|   "lpp_stable_receipt_formula rename (LPPStableScaledQuotientModuloCondition a n d result) = lpp_stable_scaled_quotient_modulo_formula rename n d result"
|  "lpp_stable_receipt_formula rename (LPPStableScaledModuloCondition a b result) = lpp_stable_scaled_modulo_formula rename b result"
|  "lpp_stable_receipt_formula rename (LPPStableQuotientCondition a d result) =
    lpp_stable_quotient_formula rename a d result"
| "lpp_stable_receipt_formula rename (LPPStableQuotientMagnitudeUpperCondition expression a b) =
    lpp_stable_quotient_magnitude_formula rename expression a"
| "lpp_stable_receipt_formula rename (LPPStableQuotientUpperCondition expression a d) =
    Conjunction [lpp_numeric_condition_formula (lpp_rename_numeric_condition rename
      (lpp_stable_numeric_condition (LPPStableQuotientUpperCondition expression a d))),
      lpp_stable_quotient_formula rename a d (Fun (LPCUser ''2:prolog_data_2f2f'') [a,lpp_integer_term d])]"
| "lpp_stable_receipt_formula rename (LPPStableModuloDescentCondition a b result) =
    lpp_stable_quotient_descent_formula rename b result"
| "lpp_stable_receipt_formula rename (LPPStableQuotientDescentCondition a b result) =
    lpp_stable_quotient_descent_formula rename a result"
| "lpp_stable_receipt_formula rename receipt =
    lpp_numeric_condition_formula (lpp_rename_numeric_condition rename (lpp_stable_numeric_condition receipt))"

lemma lpp_stable_numeric_test_formula_typed:
  "IA4.formula (lpp_numeric_condition_formula test)"
  by (cases test) (auto simp: lpp_comparison_its_type split: prod.splits)

lemma lpp_stable_receipt_formula_typed:
  "IA4.formula (lpp_stable_receipt_formula rename receipt)"
  by (cases receipt) (auto simp: lpp_stable_magnitude_quotient_modulo_formula_def lpp_stable_magnitude_progress_formula_def lpp_stable_scaled_quotient_modulo_formula_def lpp_stable_scaled_modulo_formula_def lpp_stable_quotient_formula_def lpp_stable_quotient_descent_formula_def lpp_stable_quotient_magnitude_formula_def Let_def
    lpp_stable_numeric_test_formula_typed lpp_expression_its_type IA4.is_bool_def less_Suc_eq split: prod.splits)

lemma lpp_trunc_div_magnitude_bound:
  "lpp_trunc_div n d \<le> abs n"
proof -
  have nonneg: "0\<le>abs n div abs d"
    by (cases "d=0") (auto simp: pos_imp_zdiv_nonneg_iff)
  have bound: "abs n div abs d \<le> abs n"
    by (cases "n=0") (auto intro: int_div_le_self)
  show ?thesis using nonneg bound by (auto simp: lpp_trunc_div_def sgn_if abs_if)
qed

lemma lpp_stable_receipt_formula_sound:
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_stable_numeric_observation K observation receipt"
    and observed: "lpp_stable_observation_holds operation eta observation"
    and typed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (source_values x)"
    and assigned: "\<And>key. key\<in>lpp_stable_receipt_keys receipt \<Longrightarrow>
      rho (rename key)=lpp_stable_key_value operation eta source_values key"
  shows "IA4.satisfies (lpp_integer_assignment rho) (lpp_stable_receipt_formula rename receipt)"
proof (cases receipt)
  case (LPPStableMagnitudeLiteralOrderCondition n is_strict b)
  have keys: "lpp_stable_receipt_keys receipt=lpp_numeric_condition_keys (lpp_stable_numeric_condition receipt)"
    by (simp only: LPPStableMagnitudeLiteralOrderCondition lpp_stable_receipt_keys.simps)
  have truth: "IA4.satisfies (lpp_integer_assignment rho)
    (lpp_numeric_condition_formula (lpp_rename_numeric_condition rename (lpp_stable_numeric_condition receipt)))"
    by (rule lpp_stable_numeric_condition_formula_sound[where operation=operation and eta=eta and source_values=source_values and rho=rho and rename=rename and receipt=receipt and K=K and observation=observation,
      OF compatible checked observed typed assigned[unfolded keys]])
  show ?thesis using truth by (simp only: LPPStableMagnitudeLiteralOrderCondition lpp_stable_receipt_formula.simps)
next
  case (LPPStableScaledOrderCondition is_strict a b)
  have keys: "lpp_stable_receipt_keys receipt=lpp_numeric_condition_keys (lpp_stable_numeric_condition receipt)"
    by (simp only: LPPStableScaledOrderCondition lpp_stable_receipt_keys.simps)
  have truth: "IA4.satisfies (lpp_integer_assignment rho)
    (lpp_numeric_condition_formula (lpp_rename_numeric_condition rename (lpp_stable_numeric_condition receipt)))"
    by (rule lpp_stable_numeric_condition_formula_sound[where operation=operation and eta=eta and source_values=source_values and rho=rho and rename=rename and receipt=receipt and K=K and observation=observation,
      OF compatible checked observed typed assigned[unfolded keys]])
  show ?thesis using truth by (simp only: LPPStableScaledOrderCondition lpp_stable_receipt_formula.simps)
next
  case (LPPStableQuotientMagnitudeUpperCondition expression a b)
  let ?q = "Fun (LPCUser ''2:prolog_data_2f2f'') [a,b]"
  have check: "lpp_check_stable_upper_observation K observation expression ?q"
    using checked by (simp add: LPPStableQuotientMagnitudeUpperCondition)
  obtain c t where observation: "observation=LPPOComparison c t ?q"
    using check by (cases observation) auto
  obtain v where evaluation: "lpp_stable_scalar_evaluation operation (lp_ieval ?q eta) v"
    using observed by (auto simp: observation lpp_stable_compare_outcome_def lpp_stable_compare_values_def split: if_splits)
  have expanded: "lpp_stable_scalar_evaluation operation
    (LPIFun (LPCUser ''2:prolog_data_2f2f'') [lp_ieval a eta,lp_ieval b eta]) v"
    using evaluation by simp
  obtain n d where left: "lpp_stable_scalar_evaluation operation (lp_ieval a eta) (lpp_integer_value n)"
    and scalar: "v=lpp_integer_value (lpp_trunc_div n d)"
    by (rule lpp_stable_quotient_operands[OF compatible expanded]) blast
  have bound_q: "lpp_stable_expression_bound operation (lp_ieval ?q eta)=lpp_trunc_div n d"
    by (rule lpp_stable_integer_bound) (use evaluation scalar in auto)
  have upper: "lpp_numeric_condition_holds (lpp_stable_key_value operation eta source_values)
    (lpp_stable_upper_condition expression ?q)"
    by (rule lpp_checked_stable_upper_condition[OF compatible check observed]) (use typed in auto)
  have c: "lpp_expression_value expression source_values \<le> lpp_trunc_div n d"
    using upper by (simp add: lpp_stable_upper_condition_def lpp_expression_rename_value o_def bound_q[simplified])
  have a: "rho (rename (LPPBoundKey a))=n"
    using assigned lpp_stable_integer_bound[OF left] by (auto simp: LPPStableQuotientMagnitudeUpperCondition)
  have environment: "lpp_expression_value expression (rho o rename o LPPIntegerKey)=lpp_expression_value expression source_values"
    by (rule lpp_stable_expression_value_cong) (use assigned in \<open>auto simp: LPPStableQuotientMagnitudeUpperCondition\<close>)
  have bound: "lpp_expression_value expression source_values \<le> abs n"
    using c lpp_trunc_div_magnitude_bound[of n d] by linarith
  show ?thesis using bound by (auto simp: LPPStableQuotientMagnitudeUpperCondition
    lpp_stable_quotient_magnitude_formula_def Let_def lpp_comparison_typed_assignment
    lpp_expression_typed_assignment lpp_expression_rename_value o_assoc environment a abs_if algebra.eval.simps split: if_splits)
next
  case (LPPStableQuotientUpperCondition expression a d)
  let ?b = "Fun (LPCUser ''2:prolog_data_2f2f'') [a,lpp_integer_term d]"
  have positive: "0<d" and check: "lpp_check_stable_upper_observation K observation expression ?b"
    using checked by (auto simp: LPPStableQuotientUpperCondition)
  obtain c t where observation: "observation=LPPOComparison c t ?b"
    using check by (cases observation) auto
  obtain v where evaluation: "lpp_stable_scalar_evaluation operation (lp_ieval ?b eta) v"
    using observed by (auto simp: observation lpp_stable_compare_outcome_def lpp_stable_compare_values_def split: if_splits)
  have evaluation_expanded: "lpp_stable_scalar_evaluation operation
    (LPIFun (LPCUser ''2:prolog_data_2f2f'') [lp_ieval a eta,lpp_integer_value d]) v"
    using evaluation by simp
  obtain n where left: "lpp_stable_scalar_evaluation operation (lp_ieval a eta) (lpp_integer_value n)"
    and scalar: "v=lpp_integer_value (lpp_trunc_div n d)"
    by (rule lpp_stable_quotient_result[OF compatible evaluation_expanded]) blast
  have a: "rho (rename (LPPBoundKey a))=n"
    using assigned lpp_stable_integer_bound[OF left] by (auto simp: LPPStableQuotientUpperCondition)
  have b: "rho (rename (LPPBoundKey ?b))=lpp_trunc_div n d"
    using assigned lpp_stable_integer_bound[of operation "lp_ieval ?b eta" "lpp_trunc_div n d"] evaluation scalar
    by (auto simp: LPPStableQuotientUpperCondition lpp_stable_upper_condition_def)
  have quotient: "IA4.satisfies (lpp_integer_assignment rho) (lpp_stable_quotient_formula rename a d ?b)"
    using positive by (auto simp: lpp_stable_quotient_formula_def Let_def
      lpp_comparison_typed_assignment euclid_quot_def a b lpp_trunc_div_def abs_if)
  have upper: "IA4.satisfies (lpp_integer_assignment rho)
    (lpp_numeric_condition_formula (lpp_rename_numeric_condition rename (lpp_stable_numeric_condition receipt)))"
    by (rule lpp_stable_numeric_condition_formula_sound[OF compatible checked observed typed])
      (use assigned in \<open>auto simp: LPPStableQuotientUpperCondition\<close>)
  show ?thesis using upper quotient by (simp add: LPPStableQuotientUpperCondition)
next
  case (LPPStableQuotientCondition a d result)
  have positive: "0<d" and evaluation: "lpp_stable_scalar_evaluation operation
      (LPIFun (LPCUser ''2:prolog_data_2f2f'') [lp_ieval a eta,lpp_integer_value d]) (lp_ieval result eta)"
    using checked observed by (auto simp: LPPStableQuotientCondition)
  have bound: "(0\<le>lpp_stable_expression_bound operation (lp_ieval a eta) \<and>
      lpp_stable_expression_bound operation (lp_ieval result eta)=lpp_stable_expression_bound operation (lp_ieval a eta) div d) \<or>
    (lpp_stable_expression_bound operation (lp_ieval a eta)<0 \<and>
      lpp_stable_expression_bound operation (lp_ieval result eta)= - ((- lpp_stable_expression_bound operation (lp_ieval a eta)) div d))"
    by (rule lpp_stable_quotient_bounds[OF compatible positive evaluation])
  have a: "rho (rename (LPPBoundKey a))=lpp_stable_expression_bound operation (lp_ieval a eta)"
    and result: "rho (rename (LPPBoundKey result))=lpp_stable_expression_bound operation (lp_ieval result eta)"
    using assigned by (auto simp: LPPStableQuotientCondition)
  show ?thesis using bound positive by (auto simp: LPPStableQuotientCondition
    lpp_stable_quotient_formula_def Let_def lpp_comparison_typed_assignment euclid_quot_def a result)
qed (use lpp_stable_numeric_condition_formula_sound[OF compatible checked observed typed]
    assigned checked in auto)

fun lpp_check_stable_path_observation where
  "lpp_check_stable_path_observation K ambient observation (LPPStableMagnitudeOrderCondition is_strict a b) = (observation=LPPOComparison (if is_strict then LPPIntLess else LPPIntLessEqual) a b \<and> (a=lpp_integer_term 0 \<or> LPPOComparison LPPIntLess (lpp_integer_term 0) a \<in>set ambient \<or> LPPOComparison LPPIntLessEqual (lpp_integer_term 0) a \<in>set ambient))"
|   "lpp_check_stable_path_observation K ambient observation (LPPStableMagnitudeModuloCondition a b result) = (observation=LPPOEvaluation (Fun (LPCUser ''2:prolog_data_6d6f64'') [a,b]) result \<and> LPPOComparison LPPIntLess (lpp_integer_term 0) b \<in>set ambient)"
|   "lpp_check_stable_path_observation K ambient observation (LPPStableMagnitudeQuotientModuloCondition a n d result) = (observation=LPPOEvaluation (Fun (LPCUser ''2:prolog_data_6d6f64'') [a,Fun (LPCUser ''2:prolog_data_2f2f'') [n,d]]) result \<and> LPPOComparison LPPIntLess (lpp_integer_term 0) (Fun (LPCUser ''2:prolog_data_2f2f'') [n,d]) \<in>set ambient)"
|   "lpp_check_stable_path_observation K ambient observation (LPPStableScaledQuotientModuloCondition a n d result) = (observation=LPPOEvaluation (Fun (LPCUser ''2:prolog_data_6d6f64'') [a,Fun (LPCUser ''2:prolog_data_2f2f'') [n,d]]) result \<and> LPPOComparison LPPIntLess (lpp_integer_term 0) (Fun (LPCUser ''2:prolog_data_2f2f'') [n,d]) \<in>set ambient)"
|  "lpp_check_stable_path_observation K ambient observation (LPPStableScaledModuloCondition a b result) =
    (observation=LPPOEvaluation (Fun (LPCUser ''2:prolog_data_6d6f64'') [a,b]) result \<and>
      LPPOComparison LPPIntLess (lpp_integer_term 0) b \<in>set ambient)"
|  "lpp_check_stable_path_observation K ambient observation (LPPStableModuloDescentCondition a b result) =
    (observation=LPPOEvaluation (Fun (LPCUser ''2:prolog_data_6d6f64'') [a,b]) result \<and>
      LPPOComparison LPPIntLess (lpp_integer_term 0) b \<in>set ambient)"
|  "lpp_check_stable_path_observation K ambient observation (LPPStableQuotientDescentCondition a b result) =
    (observation=LPPOEvaluation (Fun (LPCUser ''2:prolog_data_2f2f'') [a,b]) result \<and>
      LPPOComparison LPPIntLess (lpp_integer_term 1) b \<in>set ambient \<and>
      (LPPOComparison LPPIntLess (lpp_integer_term 0) a \<in>set ambient \<or>
       LPPOComparison LPPIntLessEqual b a \<in>set ambient \<or>
       LPPOComparison LPPIntLess b a \<in>set ambient))"
| "lpp_check_stable_path_observation K ambient observation receipt =
    lpp_check_stable_numeric_observation K observation receipt"

lemma lpp_stable_path_receipt_formula_sound:
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_stable_path_observation K ambient observation receipt"
    and observed: "lpp_stable_observation_holds operation eta observation"
    and ambient: "list_all (lpp_stable_observation_holds operation eta) ambient"
    and typed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (source_values x)"
    and assigned: "\<And>key. key\<in>lpp_stable_receipt_keys receipt \<Longrightarrow>
      rho (rename key)=lpp_stable_key_value operation eta source_values key"
  shows "IA4.satisfies (lpp_integer_assignment rho) (lpp_stable_receipt_formula rename receipt)"
proof (cases receipt)
  case (LPPStableMagnitudeOrderCondition is_strict a b)
  have order: "lpp_stable_compare_outcome operation (if is_strict then LPPIntLess else LPPIntLessEqual)
      (lp_ieval a eta) (lp_ieval b eta) (LPPBuiltinSuccess LPIVar)"
    using checked observed by (simp add: LPPStableMagnitudeOrderCondition)
  have sign: "lpp_stable_compare_outcome operation c (lpp_integer_value 0) (lp_ieval a eta)
      (LPPBuiltinSuccess LPIVar)" if "LPPOComparison c (lpp_integer_term 0) a\<in>set ambient" for c
  proof -
    have "lpp_stable_observation_holds operation eta (LPPOComparison c (lpp_integer_term 0) a)"
      using ambient that by (meson list_all_iff)
    then show ?thesis by simp
  qed
  have sign_bound: "lpp_integer_compare c 0 (lpp_stable_scaled_bound operation (lp_ieval a eta))"
      if "LPPOComparison c (lpp_integer_term 0) a\<in>set ambient" for c
    using lpp_stable_scaled_comparison[OF sign[OF that]]
    by (simp add: lpp_stable_scaled_integer[OF lpp_stable_integer_literal])
  have nonnegative: "0\<le>lpp_stable_scaled_bound operation (lp_ieval a eta)"
    using checked sign_bound[of LPPIntLess] sign_bound[of LPPIntLessEqual]
    by (auto simp: LPPStableMagnitudeOrderCondition lpp_stable_scaled_integer[OF lpp_stable_integer_literal])
  let ?values = "lpp_stable_key_value operation eta source_values"
  have valuation: "lpp_expression_value (lpp_magnitude_expression t) (rho o rename)=
      lpp_expression_value (lpp_magnitude_expression t) ?values" if "t=a \<or> t=b" for t
    by (rule lpp_stable_expression_value_cong)
      (use assigned that in \<open>auto simp: LPPStableMagnitudeOrderCondition\<close>)
  have truth: "lpp_integer_compare (if is_strict then LPPIntLess else LPPIntLessEqual)
      (abs (lpp_stable_scaled_bound operation (lp_ieval a eta)))
      (abs (lpp_stable_scaled_bound operation (lp_ieval b eta)))"
    by (rule lpp_stable_magnitude_order[OF order nonnegative])
  show ?thesis using truth valuation[of a] valuation[of b]
    by (cases is_strict) (auto simp: LPPStableMagnitudeOrderCondition lpp_comparison_typed_assignment
      lpp_expression_typed_assignment lpp_expression_rename_value lpp_magnitude_expression_value)
next
  case (LPPStableScaledOrderCondition is_strict a b)
  have check: "lpp_check_stable_numeric_observation K observation receipt"
    using checked by (simp only: LPPStableScaledOrderCondition lpp_check_stable_path_observation.simps)
  show ?thesis by (rule lpp_stable_receipt_formula_sound[where operation=operation and K=K and observation=observation and receipt=receipt and eta=eta and source_values=source_values and rho=rho and rename=rename, OF compatible check observed typed assigned])
next
  case (LPPStableMagnitudeModuloCondition a b result)
  have evaluation: "lpp_stable_scalar_evaluation operation
      (LPIFun (LPCUser ''2:prolog_data_6d6f64'') [lp_ieval a eta,lp_ieval b eta]) (lp_ieval result eta)"
    using checked observed by (auto simp: LPPStableMagnitudeModuloCondition)
  have denominator: "lpp_stable_compare_outcome operation LPPIntLess (lpp_integer_value 0) (lp_ieval b eta) (LPPBuiltinSuccess LPIVar)"
    using checked ambient by (auto simp: LPPStableMagnitudeModuloCondition list_all_iff)
  have progress: "0\<le>abs (lpp_stable_scaled_bound operation (lp_ieval result eta)) \<and>
    abs (lpp_stable_scaled_bound operation (lp_ieval result eta)) < abs (lpp_stable_scaled_bound operation (lp_ieval b eta))"
    by (rule lpp_stable_magnitude_modulo_progress[OF compatible evaluation denominator])
  have b: "rho (rename (LPPMagnitudeKey b))=abs (lpp_stable_scaled_bound operation (lp_ieval b eta))"
    and result: "rho (rename (LPPMagnitudeKey result))=abs (lpp_stable_scaled_bound operation (lp_ieval result eta))"
    using assigned by (auto simp: LPPStableMagnitudeModuloCondition)
  show ?thesis using progress by (auto simp: LPPStableMagnitudeModuloCondition
    lpp_stable_magnitude_progress_formula_def Let_def lpp_comparison_typed_assignment b result)
next
  case (LPPStableMagnitudeQuotientModuloCondition a n d result)
  have evaluation: "lpp_stable_scalar_evaluation operation
      (LPIFun (LPCUser ''2:prolog_data_6d6f64'') [lp_ieval a eta,LPIFun (LPCUser ''2:prolog_data_2f2f'') [lp_ieval n eta,lp_ieval d eta]]) (lp_ieval result eta)"
    using checked observed by (auto simp: LPPStableMagnitudeQuotientModuloCondition)
  have denominator: "lpp_stable_compare_outcome operation LPPIntLess (lpp_integer_value 0) (LPIFun (LPCUser ''2:prolog_data_2f2f'') [lp_ieval n eta,lp_ieval d eta]) (LPPBuiltinSuccess LPIVar)"
    using checked ambient by (auto simp: LPPStableMagnitudeQuotientModuloCondition list_all_iff)
  have progress: "0\<le>abs (lpp_stable_scaled_bound operation (lp_ieval result eta)) \<and>
    abs (lpp_stable_scaled_bound operation (lp_ieval result eta)) < abs (lpp_stable_scaled_bound operation (lp_ieval n eta))"
    by (rule lpp_stable_magnitude_quotient_modulo_progress[OF compatible evaluation denominator])
  have n: "rho (rename (LPPMagnitudeKey n))=abs (lpp_stable_scaled_bound operation (lp_ieval n eta))"
    and result: "rho (rename (LPPMagnitudeKey result))=abs (lpp_stable_scaled_bound operation (lp_ieval result eta))"
    using assigned by (auto simp: LPPStableMagnitudeQuotientModuloCondition)
  have direct: "0\<le>abs (lpp_stable_scaled_bound operation (lp_ieval result eta)) \<and> abs (lpp_stable_scaled_bound operation (lp_ieval result eta)) < abs (lpp_stable_scaled_bound operation (LPIFun (LPCUser ''2:prolog_data_2f2f'') [lp_ieval n eta,lp_ieval d eta]))"
    by (rule lpp_stable_magnitude_modulo_progress[OF compatible evaluation denominator])
  have quotient: "rho (rename (LPPMagnitudeKey (Fun (LPCUser ''2:prolog_data_2f2f'') [n,d])))=abs (lpp_stable_scaled_bound operation (LPIFun (LPCUser ''2:prolog_data_2f2f'') [lp_ieval n eta,lp_ieval d eta]))"
    using assigned by (auto simp: LPPStableMagnitudeQuotientModuloCondition)
  show ?thesis using progress direct by (auto simp: LPPStableMagnitudeQuotientModuloCondition
    lpp_stable_magnitude_quotient_modulo_formula_def lpp_stable_magnitude_progress_formula_def Let_def lpp_comparison_typed_assignment n result quotient)
next
  case (LPPStableScaledQuotientModuloCondition a n d result)
  have evaluation: "lpp_stable_scalar_evaluation operation
      (LPIFun (LPCUser ''2:prolog_data_6d6f64'') [lp_ieval a eta,LPIFun (LPCUser ''2:prolog_data_2f2f'') [lp_ieval n eta,lp_ieval d eta]]) (lp_ieval result eta)"
    using checked observed by (auto simp: LPPStableScaledQuotientModuloCondition)
  have denominator: "lpp_stable_compare_outcome operation LPPIntLess (lpp_integer_value 0) (LPIFun (LPCUser ''2:prolog_data_2f2f'') [lp_ieval n eta,lp_ieval d eta]) (LPPBuiltinSuccess LPIVar)"
    using checked ambient by (auto simp: LPPStableScaledQuotientModuloCondition list_all_iff)
  have progress: "0\<le>lpp_stable_scaled_bound operation (lp_ieval result eta) \<and>
    lpp_stable_scaled_bound operation (lp_ieval result eta) < abs (lpp_stable_scaled_bound operation (lp_ieval n eta))"
    by (rule lpp_stable_scaled_quotient_modulo_progress[OF compatible evaluation denominator])
  have n: "rho (rename (LPPScaledKey n))=lpp_stable_scaled_bound operation (lp_ieval n eta)"
    and result: "rho (rename (LPPScaledKey result))=lpp_stable_scaled_bound operation (lp_ieval result eta)"
    using assigned by (auto simp: LPPStableScaledQuotientModuloCondition)
  have direct: "0\<le>lpp_stable_scaled_bound operation (lp_ieval result eta) \<and> lpp_stable_scaled_bound operation (lp_ieval result eta) < lpp_stable_scaled_bound operation (LPIFun (LPCUser ''2:prolog_data_2f2f'') [lp_ieval n eta,lp_ieval d eta])"
    by (rule lpp_stable_scaled_modulo_progress[OF compatible evaluation denominator])
  have quotient: "rho (rename (LPPScaledKey (Fun (LPCUser ''2:prolog_data_2f2f'') [n,d])))=lpp_stable_scaled_bound operation (LPIFun (LPCUser ''2:prolog_data_2f2f'') [lp_ieval n eta,lp_ieval d eta])"
    using assigned by (auto simp: LPPStableScaledQuotientModuloCondition)
  show ?thesis using progress direct by (auto simp: LPPStableScaledQuotientModuloCondition
    lpp_stable_scaled_quotient_modulo_formula_def lpp_stable_scaled_modulo_formula_def Let_def lpp_comparison_typed_assignment n result quotient abs_if split: if_splits)
next
  case (LPPStableScaledModuloCondition a b result)
  have evaluation: "lpp_stable_scalar_evaluation operation
      (LPIFun (LPCUser ''2:prolog_data_6d6f64'') [lp_ieval a eta,lp_ieval b eta]) (lp_ieval result eta)"
    using checked observed by (auto simp: LPPStableScaledModuloCondition)
  have denominator: "lpp_stable_compare_outcome operation LPPIntLess (lpp_integer_value 0) (lp_ieval b eta) (LPPBuiltinSuccess LPIVar)"
    using checked ambient by (auto simp: LPPStableScaledModuloCondition list_all_iff)
  have progress: "0\<le>lpp_stable_scaled_bound operation (lp_ieval result eta) \<and>
    lpp_stable_scaled_bound operation (lp_ieval result eta) < lpp_stable_scaled_bound operation (lp_ieval b eta)"
    by (rule lpp_stable_scaled_modulo_progress[OF compatible evaluation denominator])
  have b: "rho (rename (LPPScaledKey b))=lpp_stable_scaled_bound operation (lp_ieval b eta)"
    and result: "rho (rename (LPPScaledKey result))=lpp_stable_scaled_bound operation (lp_ieval result eta)"
    using assigned by (auto simp: LPPStableScaledModuloCondition)
  show ?thesis using progress by (auto simp: LPPStableScaledModuloCondition
    lpp_stable_scaled_modulo_formula_def Let_def lpp_comparison_typed_assignment b result)
next
  case (LPPStableModuloDescentCondition a b result)
  have evaluation: "lpp_stable_scalar_evaluation operation
      (LPIFun (LPCUser ''2:prolog_data_6d6f64'') [lp_ieval a eta,lp_ieval b eta]) (lp_ieval result eta)"
    using checked observed by (auto simp: LPPStableModuloDescentCondition)
  have denominator: "lpp_stable_compare_outcome operation LPPIntLess (lpp_integer_value 0) (lp_ieval b eta) (LPPBuiltinSuccess LPIVar)"
    using checked ambient by (auto simp: LPPStableModuloDescentCondition list_all_iff)
  have progress: "0\<le>lpp_stable_expression_bound operation (lp_ieval result eta) \<and>
    lpp_stable_expression_bound operation (lp_ieval result eta) < lpp_stable_expression_bound operation (lp_ieval b eta)"
    by (rule lpp_stable_modulo_progress[OF compatible evaluation denominator])
  have b: "rho (rename (LPPBoundKey b))=lpp_stable_expression_bound operation (lp_ieval b eta)"
    and result: "rho (rename (LPPBoundKey result))=lpp_stable_expression_bound operation (lp_ieval result eta)"
    using assigned by (auto simp: LPPStableModuloDescentCondition)
  show ?thesis using progress by (auto simp: LPPStableModuloDescentCondition
    lpp_stable_quotient_descent_formula_def Let_def lpp_comparison_typed_assignment b result)
next
  case (LPPStableQuotientDescentCondition a b result)
  have evaluation: "lpp_stable_scalar_evaluation operation
      (LPIFun (LPCUser ''2:prolog_data_2f2f'') [lp_ieval a eta,lp_ieval b eta]) (lp_ieval result eta)"
    using checked observed by (auto simp: LPPStableQuotientDescentCondition)
  have denominator: "lpp_stable_compare_outcome operation LPPIntLess (lpp_integer_value 1) (lp_ieval b eta) (LPPBuiltinSuccess LPIVar)"
    and numerator: "lpp_stable_compare_outcome operation LPPIntLess (lpp_integer_value 0) (lp_ieval a eta) (LPPBuiltinSuccess LPIVar) \<or>
      lpp_stable_compare_outcome operation LPPIntLessEqual (lp_ieval b eta) (lp_ieval a eta) (LPPBuiltinSuccess LPIVar) \<or>
      lpp_stable_compare_outcome operation LPPIntLess (lp_ieval b eta) (lp_ieval a eta) (LPPBuiltinSuccess LPIVar)"
    using checked ambient by (auto simp: LPPStableQuotientDescentCondition list_all_iff)
  have progress: "0\<le>lpp_stable_expression_bound operation (lp_ieval result eta) \<and>
    lpp_stable_expression_bound operation (lp_ieval result eta) < lpp_stable_expression_bound operation (lp_ieval a eta)"
    by (rule lpp_stable_quotient_progress[OF compatible evaluation denominator numerator])
  have a: "rho (rename (LPPBoundKey a))=lpp_stable_expression_bound operation (lp_ieval a eta)"
    and result: "rho (rename (LPPBoundKey result))=lpp_stable_expression_bound operation (lp_ieval result eta)"
    using assigned by (auto simp: LPPStableQuotientDescentCondition)
  show ?thesis using progress by (auto simp: LPPStableQuotientDescentCondition
    lpp_stable_quotient_descent_formula_def Let_def lpp_comparison_typed_assignment a result)
qed (use lpp_stable_receipt_formula_sound[where operation=operation and K=K and observation=observation and receipt=receipt and eta=eta and source_values=source_values and rho=rho and rename=rename, OF compatible _ observed typed assigned]
    checked in auto)

ML \<open>
val checked = [@{thm lpp_stable_path_receipt_formula_sound}, @{thm lpp_stable_receipt_formula_sound}, @{thm lpp_stable_receipt_formula_typed}, @{thm lpp_checked_stable_numeric_condition}, @{thm lpp_stable_numeric_condition_formula_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable numeric condition dependency" else ();
\<close>
end
