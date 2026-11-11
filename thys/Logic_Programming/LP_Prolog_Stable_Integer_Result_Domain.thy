theory LP_Prolog_Stable_Integer_Result_Domain
 imports LP_Prolog_Stable_Modulo
begin

text \<open>This property describes actual successful evaluations. It neither
asserts evaluability nor says that an unevaluated input is an integer literal.
Source termination, failure alternatives and return coverage remain separate.\<close>

definition lpp_stable_integer_result_domain where
  "lpp_stable_integer_result_domain operation expression =
    (\<forall>result. lpp_stable_scalar_evaluation operation expression result \<longrightarrow>
      lpp_is_integer result)"

lemma lpp_stable_integer_result_domain_literal:
  "lpp_stable_integer_result_domain operation (lpp_integer_value n)"
  using lpp_stable_scalar_evaluation_unique[OF _ lpp_stable_integer_literal]
  by (auto simp: lpp_stable_integer_result_domain_def lpp_is_integer_def)

lemma lpp_stable_integer_result_domain_quotient:
  assumes "lpp_stable_integer_operations operation"
  shows "lpp_stable_integer_result_domain operation
    (LPIFun (LPCUser ''2:prolog_data_2f2f'') [a,b])"
proof (unfold lpp_stable_integer_result_domain_def, intro allI impI)
  fix result
  assume evaluated: "lpp_stable_scalar_evaluation operation
    (LPIFun (LPCUser ''2:prolog_data_2f2f'') [a,b]) result"
  obtain n d where "result=lpp_integer_value (lpp_trunc_div n d)"
    by (rule lpp_stable_quotient_operands[OF assms evaluated]) blast
  then show "lpp_is_integer result" by (auto simp: lpp_is_integer_def)
qed

lemma lpp_stable_integer_result_domain_modulo:
  assumes "lpp_stable_integer_operations operation"
  shows "lpp_stable_integer_result_domain operation
    (LPIFun (LPCUser ''2:prolog_data_6d6f64'') [a,b])"
proof (unfold lpp_stable_integer_result_domain_def, intro allI impI)
  fix result
  assume evaluated: "lpp_stable_scalar_evaluation operation
    (LPIFun (LPCUser ''2:prolog_data_6d6f64'') [a,b]) result"
  obtain n d where "result=lpp_integer_value (n mod d)"
    by (rule lpp_stable_modulo_operands[OF assms evaluated]) blast
  then show "lpp_is_integer result" by (auto simp: lpp_is_integer_def)
qed

lemma lpp_stable_integer_result_domain_binary:
  assumes left: "lpp_stable_integer_result_domain operation a"
    and right: "lpp_stable_integer_result_domain operation b"
    and closed: "\<And>n m v. operation f [lpp_integer_value n,lpp_integer_value m]=Some v
      \<Longrightarrow> lpp_is_integer v"
  shows "lpp_stable_integer_result_domain operation (LPIFun f [a,b])"
proof (unfold lpp_stable_integer_result_domain_def, intro allI impI)
  fix result
  assume evaluated: "lpp_stable_scalar_evaluation operation (LPIFun f [a,b]) result"
  obtain x y where a: "lpp_stable_scalar_evaluation operation a x"
    and b: "lpp_stable_scalar_evaluation operation b y"
    and step: "operation f [x,y]=Some result"
    using evaluated by (cases rule: lpp_stable_scalar_evaluation.cases)
      (auto dest: lpp_scalar_fraction_nullary)
  have xi: "lpp_is_integer x" using left a
    by (auto simp: lpp_stable_integer_result_domain_def)
  have yi: "lpp_is_integer y" using right b
    by (auto simp: lpp_stable_integer_result_domain_def)
  obtain n m where "x=lpp_integer_value n" "y=lpp_integer_value m"
    using xi yi by (auto simp: lpp_is_integer_def)
  then show "lpp_is_integer result" using closed step by blast
qed

lemma lpp_stable_integer_result_domain_add:
  assumes compatible: "lpp_stable_integer_operations operation"
    and left: "lpp_stable_integer_result_domain operation a"
    and right: "lpp_stable_integer_result_domain operation b"
  shows "lpp_stable_integer_result_domain operation (LPIFun (LPCUser ''2:prolog_data_2b'') [a,b])"
  by (rule lpp_stable_integer_result_domain_binary[OF left right])
    (use compatible in \<open>auto simp: lpp_stable_integer_operations_def lpp_is_integer_def\<close>)

lemma lpp_stable_integer_result_domain_subtract:
  assumes compatible: "lpp_stable_integer_operations operation"
    and left: "lpp_stable_integer_result_domain operation a"
    and right: "lpp_stable_integer_result_domain operation b"
  shows "lpp_stable_integer_result_domain operation (LPIFun (LPCUser ''2:prolog_data_2d'') [a,b])"
  by (rule lpp_stable_integer_result_domain_binary[OF left right])
    (use compatible in \<open>auto simp: lpp_stable_integer_operations_def lpp_is_integer_def\<close>)

lemma lpp_stable_integer_result_domain_multiply:
  assumes compatible: "lpp_stable_integer_operations operation"
    and left: "lpp_stable_integer_result_domain operation a"
    and right: "lpp_stable_integer_result_domain operation b"
  shows "lpp_stable_integer_result_domain operation (LPIFun (LPCUser ''2:prolog_data_2a'') [a,b])"
  by (rule lpp_stable_integer_result_domain_binary[OF left right])
    (use compatible in \<open>auto simp: lpp_stable_integer_operations_def lpp_is_integer_def\<close>)

datatype 'v lpp_integer_result_receipt =
    LPPRILiteral int
  | LPPRIKnown 'v
  | LPPRIQuotient "(string lp_cut_symbol,'v) term" "(string lp_cut_symbol,'v) term"
  | LPPRIModulo "(string lp_cut_symbol,'v) term" "(string lp_cut_symbol,'v) term"
  | LPPRIAdd "'v lpp_integer_result_receipt" "'v lpp_integer_result_receipt"
  | LPPRISubtract "'v lpp_integer_result_receipt" "'v lpp_integer_result_receipt"
  | LPPRIMultiply "'v lpp_integer_result_receipt" "'v lpp_integer_result_receipt"

fun lpp_integer_result_term where
  "lpp_integer_result_term (LPPRILiteral n) = lpp_integer_term n"
| "lpp_integer_result_term (LPPRIKnown x) = Var x"
| "lpp_integer_result_term (LPPRIQuotient a b) = Fun (LPCUser ''2:prolog_data_2f2f'') [a,b]"
| "lpp_integer_result_term (LPPRIModulo a b) = Fun (LPCUser ''2:prolog_data_6d6f64'') [a,b]"
| "lpp_integer_result_term (LPPRIAdd a b) = Fun (LPCUser ''2:prolog_data_2b'') [lpp_integer_result_term a,lpp_integer_result_term b]"
| "lpp_integer_result_term (LPPRISubtract a b) = Fun (LPCUser ''2:prolog_data_2d'') [lpp_integer_result_term a,lpp_integer_result_term b]"
| "lpp_integer_result_term (LPPRIMultiply a b) = Fun (LPCUser ''2:prolog_data_2a'') [lpp_integer_result_term a,lpp_integer_result_term b]"

fun lpp_check_integer_result_receipt where
  "lpp_check_integer_result_receipt K (LPPRILiteral n) = True"
| "lpp_check_integer_result_receipt K (LPPRIKnown x) = (x\<in>set K)"
| "lpp_check_integer_result_receipt K (LPPRIQuotient a b) = True"
| "lpp_check_integer_result_receipt K (LPPRIModulo a b) = True"
| "lpp_check_integer_result_receipt K (LPPRIAdd a b) = (lpp_check_integer_result_receipt K a \<and> lpp_check_integer_result_receipt K b)"
| "lpp_check_integer_result_receipt K (LPPRISubtract a b) = (lpp_check_integer_result_receipt K a \<and> lpp_check_integer_result_receipt K b)"
| "lpp_check_integer_result_receipt K (LPPRIMultiply a b) = (lpp_check_integer_result_receipt K a \<and> lpp_check_integer_result_receipt K b)"

lemma lpp_check_integer_result_receipt_sound:
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_integer_result_receipt K receipt"
    and known: "lpp_integer_known K eta"
  shows "lpp_stable_integer_result_domain operation (lp_ieval (lpp_integer_result_term receipt) eta)"
  using checked
proof (induction receipt)
  case (LPPRILiteral n)
  show ?case by (simp add: lpp_stable_integer_result_domain_literal)
next
  case (LPPRIKnown x)
  obtain n where "eta x=lpp_integer_value n"
    using known LPPRIKnown by (auto simp: lpp_integer_known_def)
  then show ?case by (simp add: lpp_stable_integer_result_domain_literal)
next
  case (LPPRIQuotient a b)
  show ?case by (simp add: lpp_stable_integer_result_domain_quotient[OF compatible])
next
  case (LPPRIModulo a b)
  show ?case by (simp add: lpp_stable_integer_result_domain_modulo[OF compatible])
next
  case (LPPRIAdd a b)
  then show ?case by (auto intro: lpp_stable_integer_result_domain_add[OF compatible])
next
  case (LPPRISubtract a b)
  then show ?case by (auto intro: lpp_stable_integer_result_domain_subtract[OF compatible])
next
  case (LPPRIMultiply a b)
  then show ?case by (auto intro: lpp_stable_integer_result_domain_multiply[OF compatible])
qed

lemma lpp_checked_actual_integer_result:
  assumes "lpp_stable_integer_operations operation"
    "lpp_check_integer_result_receipt K receipt" "lpp_integer_known K eta"
    "lpp_stable_scalar_evaluation operation (lp_ieval (lpp_integer_result_term receipt) eta) result"
  shows "lpp_is_integer result"
  using lpp_check_integer_result_receipt_sound[OF assms(1-3)] assms(4)
  by (auto simp: lpp_stable_integer_result_domain_def)

ML \<open>
val checked = @{thms lpp_check_integer_result_receipt_sound lpp_checked_actual_integer_result lpp_stable_integer_result_domain_literal
  lpp_stable_integer_result_domain_quotient lpp_stable_integer_result_domain_modulo
  lpp_stable_integer_result_domain_binary lpp_stable_integer_result_domain_add
  lpp_stable_integer_result_domain_subtract lpp_stable_integer_result_domain_multiply};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted integer-result domain dependency" else ();
\<close>
end
