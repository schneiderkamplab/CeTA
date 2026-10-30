theory LP_Prolog_Numeric_Row_Check
  imports LP_Prolog_Numeric_Observations LP_Prolog_ITS_Transitions
begin

text \<open>Bind the arithmetic condition to the observed source syntax.
Evaluation and comparison are different source operations, even when both
produce an equality in the numeric child. Integer type tests supply type
facts separately and cannot be substituted for an arbitrary numeric guard.\<close>

fun lpp_check_numeric_observation where
  "lpp_check_numeric_observation K (LPPOGround t) numeric_test = False"
| "lpp_check_numeric_observation K (LPPOInteger t) numeric_test = False"
| "lpp_check_numeric_observation K (LPPOEvaluation e t) (comparison,a,b) =
    (comparison=LPPIntEqual \<and> t=lpp_expression_term a \<and> e=lpp_expression_term b \<and>
      lpp_expression_check K a \<and> lpp_expression_check K b)"
| "lpp_check_numeric_observation K (LPPOComparison c l r) (comparison,a,b) =
    (comparison=c \<and> l=lpp_expression_term a \<and> r=lpp_expression_term b \<and>
      lpp_expression_check K a \<and> lpp_expression_check K b)"

lemma lpp_check_numeric_observation_sound:
  assumes checked: "lpp_check_numeric_observation K observation numeric_test"
    and observed: "lpp_numeric_observation_holds eta observation"
    and typed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (rho x)"
  shows "lpp_numeric_condition_holds rho numeric_test"
proof -
  obtain comparison a b where numeric_test: "numeric_test=(comparison,a,b)"
    by (cases numeric_test; auto)
  show ?thesis
  proof (cases observation)
    case (LPPOGround t)
    then show ?thesis using checked by simp
  next
    case (LPPOInteger t)
    then show ?thesis using checked by simp
  next
    case (LPPOEvaluation e t)
    have left: "lpp_integer_evaluation (lp_ieval t eta) (lpp_expression_value a rho)"
      and right: "lpp_integer_evaluation (lp_ieval e eta) (lpp_expression_value b rho)"
      using checked lpp_expression_evaluation[of K a eta rho, OF _ typed]
        lpp_expression_evaluation[of K b eta rho, OF _ typed]
      by (auto simp: LPPOEvaluation numeric_test)
    obtain n where ev: "lpp_integer_evaluation (lp_ieval e eta) n"
      and result: "lp_ieval t eta=lpp_integer_value n"
      using observed by (auto simp: LPPOEvaluation lpp_integer_result_def)
    have left_n: "lpp_integer_evaluation (lp_ieval t eta) n"
      by (simp add: result lpp_integer_evaluation.literal)
    have equal: "lpp_expression_value a rho=lpp_expression_value b rho"
      using lpp_integer_evaluation_unique[OF right ev]
        lpp_integer_evaluation_unique[OF left left_n] by simp
    show ?thesis using checked equal by (auto simp: numeric_test LPPOEvaluation)
  next
    case (LPPOComparison c l r)
    have left: "lpp_integer_evaluation (lp_ieval l eta) (lpp_expression_value a rho)"
      and right: "lpp_integer_evaluation (lp_ieval r eta) (lpp_expression_value b rho)"
      using checked lpp_expression_evaluation[of K a eta rho, OF _ typed]
        lpp_expression_evaluation[of K b eta rho, OF _ typed]
      by (auto simp: LPPOComparison numeric_test)
    have integer_observation: "lpp_integer_compare_outcome c (lp_ieval l eta) (lp_ieval r eta) (LPPBuiltinSuccess LPIVar)"
      using observed by (simp only: LPPOComparison lpp_numeric_observation_holds.simps lpp_finite_comparison_integer[OF left right])
    show ?thesis using checked integer_observation lpp_integer_compare_outcome_exact[OF left right,
      where comparison=c and outcome="LPPBuiltinSuccess LPIVar"]
      by (auto simp: numeric_test LPPOComparison split: if_splits)
  qed
qed

lemma lpp_expression_rename_value:
  "lpp_expression_value (map_lpp_integer_expression rename e) rho =
    lpp_expression_value e (rho o rename)"
  by (induct e) (auto simp: o_def)

fun lpp_rename_numeric_condition where
  "lpp_rename_numeric_condition rename (comparison,a,b) =
    (comparison,map_lpp_integer_expression rename a,map_lpp_integer_expression rename b)"

lemma lpp_rename_numeric_condition_holds:
  "lpp_numeric_condition_holds rho (lpp_rename_numeric_condition rename numeric_test) =
    lpp_numeric_condition_holds (rho o rename) numeric_test"
  by (cases numeric_test) (simp add: lpp_expression_rename_value split: prod.splits)

definition lpp_numeric_rename where
  "lpp_numeric_rename bindings x = (case map_of bindings x of None \<Rightarrow> Intermediate ([]::string) | Some v \<Rightarrow> v)"

definition lpp_check_numeric_row_guard where
  "lpp_check_numeric_row_guard K observation numeric_test bindings formula =
    (distinct (map fst bindings) \<and> list_all (\<lambda>x. map_of bindings x\<noteq>None) K \<and>
     lpp_check_numeric_observation K observation numeric_test \<and>
     formula=lpp_numeric_condition_formula (lpp_rename_numeric_condition (lpp_numeric_rename bindings) numeric_test))"

theorem lpp_check_numeric_row_guard_sound:
  assumes checked: "lpp_check_numeric_row_guard K observation numeric_test bindings formula"
    and observed: "lpp_numeric_observation_holds eta observation"
    and typed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (rho (lpp_numeric_rename bindings x))"
  shows "IA4.satisfies (lpp_integer_assignment rho) formula"
    "IA4.formula formula"
proof -
  have check: "lpp_check_numeric_observation K observation numeric_test"
    and formula: "formula=lpp_numeric_condition_formula (lpp_rename_numeric_condition (lpp_numeric_rename bindings) numeric_test)"
    using checked by (auto simp: lpp_check_numeric_row_guard_def)
  have truth: "lpp_numeric_condition_holds (rho o lpp_numeric_rename bindings) numeric_test"
    by (rule lpp_check_numeric_observation_sound[OF check observed]) (use typed in auto)
  have renamed: "lpp_numeric_condition_holds rho (lpp_rename_numeric_condition (lpp_numeric_rename bindings) numeric_test)"
    using truth by (simp only: lpp_rename_numeric_condition_holds)
  show "IA4.satisfies (lpp_integer_assignment rho) formula"
    using renamed by (cases numeric_test) (auto simp: formula lpp_comparison_typed_assignment split: prod.splits)
  show "IA4.formula formula"
    by (cases numeric_test) (auto simp: formula lpp_comparison_its_type split: prod.splits)
qed

ML \<open>
val checked = [@{thm lpp_check_numeric_observation_sound}] @ @{thms lpp_check_numeric_row_guard_sound};
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted numeric source-row dependency" else ();
\<close>
end
