theory LP_Prolog_Integer_Call_Formula
  imports LP_Prolog_Integer_Call_Relation LP_Prolog_Integer_Recurrence_Valuation
begin

definition lpp_argument_expressions where
  "lpp_argument_expressions xs coordinates x =
    (case map_of (zip xs coordinates) x of None \<Rightarrow> LPPEConstant 0 | Some y \<Rightarrow> LPPEVariable y)"

lemma lpp_argument_expressions_value:
  "lpp_expression_value (lpp_argument_expressions xs coordinates x) rho =
    lpp_recurrence_arguments xs (map rho coordinates) x"
proof (induct xs arbitrary: coordinates)
  case Nil show ?case by (simp add: lpp_argument_expressions_def lpp_recurrence_arguments_def)
next
  case (Cons y ys)
  show ?case by (cases coordinates)
    (auto simp: lpp_argument_expressions_def lpp_recurrence_arguments_def
      Cons.hyps[unfolded lpp_argument_expressions_def lpp_recurrence_arguments_def])
qed

lemma lpp_argument_expressions_values:
  "(\<lambda>x. lpp_expression_value (lpp_argument_expressions xs coordinates x) rho) =
    lpp_recurrence_arguments xs (map rho coordinates)"
  by (rule ext) (rule lpp_argument_expressions_value)

definition lpp_preconditions_formula where
  "lpp_preconditions_formula numeric_tests = Conjunction
    (map (lpp_numeric_condition_formula o lpp_rename_numeric_condition Pre) numeric_tests)"

lemma lpp_preconditions_formula_exact:
  "IA4.satisfies (lpp_integer_assignment (lpp_trans_integer before after middle))
      (lpp_preconditions_formula numeric_tests) = list_all (lpp_numeric_condition_holds before) numeric_tests"
  by (auto simp: lpp_preconditions_formula_def lpp_comparison_typed_assignment
    lpp_rename_numeric_condition_holds lpp_expression_typed_assignment algebra.eval.simps
    lpp_expression_rename_value o_def list_all_iff split: prod.splits)

definition lpp_failure_condition where
  "lpp_failure_condition r coordinates =
    (let env=lpp_recurrence_symbolic_values (lpp_failure_prefix r)
       (lpp_argument_expressions (lpp_failure_variables r) coordinates)
     in (lpp_failure_comparison r,
       lpp_recurrence_substitute env (if lpp_failure_reversed r then lpp_failure_right r else lpp_failure_left r),
       lpp_recurrence_substitute env (if lpp_failure_reversed r then lpp_failure_left r else lpp_failure_right r)))"

fun lpp_complement_condition where
  "lpp_complement_condition (LPPIntLess,a,b) = (LPPIntLessEqual,b,a)"
| "lpp_complement_condition (LPPIntLessEqual,a,b) = (LPPIntLess,b,a)"
| "lpp_complement_condition (LPPIntEqual,a,b) = (LPPIntNotEqual,a,b)"
| "lpp_complement_condition (LPPIntNotEqual,a,b) = (LPPIntEqual,a,b)"

lemma lpp_complement_condition_holds:
  "lpp_numeric_condition_holds rho (lpp_complement_condition test) =
    (\<not>lpp_numeric_condition_holds rho test)"
proof -
  obtain comparison a b where parts: "test=(comparison,a,b)"
    by (cases test; case_tac b) auto
  show ?thesis by (cases comparison) (simp_all add: parts not_less not_le)
qed

definition lpp_failure_formula where
  "lpp_failure_formula r coordinates = Conjunction [
    lpp_preconditions_formula (lpp_recurrence_symbolic_guards (lpp_failure_prefix r)
      (lpp_argument_expressions (lpp_failure_variables r) coordinates)),
    lpp_numeric_condition_formula (lpp_rename_numeric_condition Pre
      (lpp_complement_condition (lpp_failure_condition r coordinates)))]"

lemma lpp_failure_formula_exact:
  "IA4.satisfies (lpp_integer_assignment (lpp_trans_integer before after middle))
      (lpp_failure_formula r coordinates) = lpp_arithmetic_failure_holds r (map before coordinates)"
proof -
  let ?env = "lpp_argument_expressions (lpp_failure_variables r) coordinates"
  have symbolic: "(\<lambda>x. lpp_expression_value
      (lpp_recurrence_symbolic_values (lpp_failure_prefix r) ?env x) before) =
      lpp_recurrence_values (lpp_failure_prefix r)
        (lpp_recurrence_arguments (lpp_failure_variables r) (map before coordinates))"
    using lpp_recurrence_symbolic_values_exact[of "lpp_failure_prefix r" ?env before]
    by (simp only: lpp_argument_expressions_values)
  have guards: "list_all (lpp_numeric_condition_holds before)
      (lpp_recurrence_symbolic_guards (lpp_failure_prefix r) ?env) =
      lpp_recurrence_guards (lpp_failure_prefix r)
        (lpp_recurrence_arguments (lpp_failure_variables r) (map before coordinates))"
    using lpp_recurrence_symbolic_guards_exact[of before "lpp_failure_prefix r" ?env]
    by (simp only: lpp_argument_expressions_values)
  show ?thesis
    by (simp add: lpp_failure_formula_def lpp_failure_condition_def lpp_arithmetic_failure_holds_def
      lpp_preconditions_formula_exact lpp_comparison_typed_assignment lpp_expression_typed_assignment
      lpp_rename_numeric_condition_holds lpp_expression_rename_value lpp_recurrence_substitute_value
      symbolic guards o_def Let_def lpp_complement_condition_holds)
qed


definition lpp_call_formula where
  "lpp_call_formula r input_coordinates output_coordinates =
    (let env=lpp_argument_expressions (lpp_call_variables r) input_coordinates;
         final=lpp_recurrence_symbolic_values (lpp_call_prefix r) env
     in Conjunction [
       lpp_preconditions_formula (lpp_recurrence_symbolic_guards (lpp_call_prefix r) env),
       Conjunction (map (\<lambda>failed. lpp_failure_formula failed input_coordinates) (lpp_call_failures r)),
       Conjunction (map (\<lambda>(x,e). lpp_numeric_condition_formula
         (LPPIntEqual, LPPEVariable (Post x),
          map_lpp_integer_expression Pre (lpp_recurrence_substitute final e)))
         (zip output_coordinates (lpp_call_outputs r)))])"

lemma lpp_call_formula_exact:
  assumes lengths: "length output_coordinates=length (lpp_call_outputs r)"
  shows "IA4.satisfies (lpp_integer_assignment (lpp_trans_integer before after middle))
      (lpp_call_formula r input_coordinates output_coordinates) =
    (lpp_arithmetic_call_holds r (map before input_coordinates) \<and>
      map after output_coordinates=lpp_arithmetic_call_outputs r (map before input_coordinates))"
proof -
  let ?env = "lpp_argument_expressions (lpp_call_variables r) input_coordinates"
  let ?rho = "lpp_recurrence_arguments (lpp_call_variables r) (map before input_coordinates)"
  let ?final = "lpp_recurrence_values (lpp_call_prefix r) ?rho"
  have symbolic: "(\<lambda>x. lpp_expression_value
      (lpp_recurrence_symbolic_values (lpp_call_prefix r) ?env x) before) = ?final"
    using lpp_recurrence_symbolic_values_exact[of "lpp_call_prefix r" ?env before]
    by (simp only: lpp_argument_expressions_values)
  have guards: "list_all (lpp_numeric_condition_holds before)
      (lpp_recurrence_symbolic_guards (lpp_call_prefix r) ?env) =
      lpp_recurrence_guards (lpp_call_prefix r) ?rho"
    using lpp_recurrence_symbolic_guards_exact[of before "lpp_call_prefix r" ?env]
    by (simp only: lpp_argument_expressions_values)
  have outputs: "(\<forall>(x,e)\<in>set (zip output_coordinates (lpp_call_outputs r)).
      after x=lpp_expression_value e ?final) =
      (map after output_coordinates=lpp_arithmetic_call_outputs r (map before input_coordinates))"
    using lengths by (auto simp: lpp_arithmetic_call_outputs_def
      list_eq_iff_zip_eq zip_map1 zip_map2 split: prod.splits)
  let ?alpha = "lpp_integer_assignment (lpp_trans_integer before after middle)"
  have source_guard: "IA4.satisfies ?alpha
      (lpp_preconditions_formula (lpp_recurrence_symbolic_guards (lpp_call_prefix r) ?env)) =
      lpp_recurrence_guards (lpp_call_prefix r) ?rho"
    by (simp only: lpp_preconditions_formula_exact guards)
  have failures: "IA4.satisfies ?alpha
      (Conjunction (map (\<lambda>failed. lpp_failure_formula failed input_coordinates) (lpp_call_failures r))) =
      list_all (\<lambda>failed. lpp_arithmetic_failure_holds failed (map before input_coordinates)) (lpp_call_failures r)"
    by (simp add: lpp_failure_formula_exact list_all_iff)
  have updates: "IA4.satisfies ?alpha
      (Conjunction (map (\<lambda>(x,e). lpp_numeric_condition_formula
         (LPPIntEqual, LPPEVariable (Post x),
          map_lpp_integer_expression Pre (lpp_recurrence_substitute
            (lpp_recurrence_symbolic_values (lpp_call_prefix r) ?env) e)))
         (zip output_coordinates (lpp_call_outputs r)))) =
      (\<forall>(x,e)\<in>set (zip output_coordinates (lpp_call_outputs r)).
        after x=lpp_expression_value e ?final)"
    by (auto simp: lpp_comparison_typed_assignment lpp_expression_typed_assignment
      lpp_expression_rename_value lpp_recurrence_substitute_value symbolic o_def split: prod.splits)
  have triple: "IA4.satisfies ?alpha (Conjunction [fa,fb,fc]) =
      (IA4.satisfies ?alpha fa \<and> IA4.satisfies ?alpha fb \<and> IA4.satisfies ?alpha fc)"
    for fa fb fc by simp
  have expanded: "IA4.satisfies ?alpha
      (lpp_call_formula r input_coordinates output_coordinates) =
    (lpp_arithmetic_call_holds r (map before input_coordinates) \<and>
      (\<forall>(x,e)\<in>set (zip output_coordinates (lpp_call_outputs r)).
        after x=lpp_expression_value e ?final))"
    by (simp only: lpp_call_formula_def Let_def triple source_guard failures updates
      lpp_arithmetic_call_holds_def; blast)
  show ?thesis using expanded by (simp only: outputs)
qed

lemma lpp_call_formula_valuation_cong:
  assumes same: "\<And>x. alpha (x,IA.IntT)=beta (x,IA.IntT)"
  shows "IA4.satisfies alpha (lpp_call_formula r input_coordinates output_coordinates) =
    IA4.satisfies beta (lpp_call_formula r input_coordinates output_coordinates)"
proof -
  have condition: "IA4.satisfies alpha (lpp_numeric_condition_formula test) =
      IA4.satisfies beta (lpp_numeric_condition_formula test)" for test
    by (rule lpp_recurrence_condition_valuation_cong[where alpha=alpha and beta=beta, OF same])
  show ?thesis
    by (auto simp: lpp_call_formula_def lpp_failure_formula_def lpp_preconditions_formula_def
      condition o_def Let_def algebra.eval.simps same
      lpp_recurrence_expression_valuation_cong[where alpha=alpha and beta=beta, OF same])
qed

lemma lpp_call_formula_arbitrary_valuation:
  assumes typed: "IA4.assignment alpha"
  shows "IA4.satisfies alpha (lpp_call_formula r input_coordinates output_coordinates) =
    IA4.satisfies (lpp_integer_assignment (\<lambda>x. IA.to_int (alpha (x,IA.IntT))))
      (lpp_call_formula r input_coordinates output_coordinates)"
  by (rule lpp_call_formula_valuation_cong)
    (simp only: lpp_integer_assignment.simps; rule lpp_recurrence_assignment_integer[OF typed])

ML \<open>
val checked = [@{thm lpp_argument_expressions_value}, @{thm lpp_failure_formula_exact},
  @{thm lpp_call_formula_exact}, @{thm lpp_call_formula_arbitrary_valuation}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted arithmetic failure formula dependency" else ();
\<close>
end
