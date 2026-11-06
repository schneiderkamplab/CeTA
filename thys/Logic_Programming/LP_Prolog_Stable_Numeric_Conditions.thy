theory LP_Prolog_Stable_Numeric_Conditions
 imports LP_Prolog_Stable_Endpoints
begin

datatype 'v lpp_stable_condition_receipt =
    LPPStableIgnoredCondition
  | LPPStableIntegerCondition "'v lpp_numeric_condition"
  | LPPStableUpperCondition "'v lpp_integer_expression" "(string lp_cut_symbol,'v) term"

fun lpp_check_stable_numeric_observation where
  "lpp_check_stable_numeric_observation K observation (LPPStableIntegerCondition test) =
    lpp_check_numeric_observation K observation test"
| "lpp_check_stable_numeric_observation K observation (LPPStableUpperCondition expression bound_term) =
    lpp_check_stable_upper_observation K observation expression bound_term"
| "lpp_check_stable_numeric_observation K observation LPPStableIgnoredCondition = True"

fun lpp_stable_numeric_condition where
  "lpp_stable_numeric_condition (LPPStableIntegerCondition test) =
    lpp_rename_numeric_condition LPPIntegerKey test"
| "lpp_stable_numeric_condition (LPPStableUpperCondition expression bound_term) =
    lpp_stable_upper_condition expression bound_term"
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

ML \<open>
val checked = [@{thm lpp_checked_stable_numeric_condition}, @{thm lpp_stable_numeric_condition_formula_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable numeric condition dependency" else ();
\<close>
end
