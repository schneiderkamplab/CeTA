theory LP_Prolog_Numeric_Guards
  imports LP_Prolog_Integer_Builtins LP_Prolog_Arithmetic_ITS
begin

text \<open>Arithmetic path guards retain their source expressions. The ITS
formula is reconstructed rather than supplied as an unrelated terminating
subject. Greater comparisons are represented by exchanging operands.\<close>

fun lpp_comparison_its where
  "lpp_comparison_its LPPIntLess a b = Atom (Fun (IA4_Base IA.LessF) [a,b])"
| "lpp_comparison_its LPPIntLessEqual a b = Atom (Fun (IA4_Base IA.LeF) [a,b])"
| "lpp_comparison_its LPPIntEqual a b = Atom (Fun (IA4_Base IA.EqF) [a,b])"
| "lpp_comparison_its LPPIntNotEqual a b = Disjunction
    [Atom (Fun (IA4_Base IA.LessF) [a,b]),Atom (Fun (IA4_Base IA.LessF) [b,a])]"

lemma lpp_comparison_its_value:
  "IA4.satisfies (\<lambda>(x,ty). IA.Int (rho x))
    (lpp_comparison_its comparison (lpp_expression_its a) (lpp_expression_its b)) =
   lpp_integer_compare comparison (lpp_expression_value a rho) (lpp_expression_value b rho)"
  by (cases comparison) (auto simp: lpp_expression_its_value algebra.eval.simps)

lemma lpp_comparison_its_type:
  "IA4.formula (lpp_comparison_its comparison (lpp_expression_its a) (lpp_expression_its b))"
  by (cases comparison) (auto simp: IA4.is_bool_def less_Suc_eq lpp_expression_its_type)

definition lpp_check_numeric_guard where
  "lpp_check_numeric_guard K comparison left right a b formula =
    (left=lpp_expression_term a \<and> right=lpp_expression_term b \<and>
     lpp_expression_check K a \<and> lpp_expression_check K b \<and>
     formula=lpp_comparison_its comparison (lpp_expression_its a) (lpp_expression_its b))"

theorem lpp_check_numeric_guard_sound:
  assumes checked: "lpp_check_numeric_guard K comparison left right a b formula"
    and typed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (rho x)"
  shows "lpp_integer_compare_outcome comparison (lp_ieval left eta) (lp_ieval right eta)
      (LPPBuiltinSuccess LPIVar) = IA4.satisfies (\<lambda>(x,ty). IA.Int (rho x)) formula"
    "IA4.formula formula"
proof -
  have left: "lpp_integer_evaluation (lp_ieval left eta) (lpp_expression_value a rho)"
    and right: "lpp_integer_evaluation (lp_ieval right eta) (lpp_expression_value b rho)"
    using lpp_expression_evaluation[of K a eta rho] lpp_expression_evaluation[of K b eta rho]
      checked typed by (auto simp: lpp_check_numeric_guard_def)
  show "lpp_integer_compare_outcome comparison (lp_ieval left eta) (lp_ieval right eta)
      (LPPBuiltinSuccess LPIVar) = IA4.satisfies (\<lambda>(x,ty). IA.Int (rho x)) formula"
    using lpp_integer_compare_outcome_exact[OF left right, where comparison=comparison and outcome="LPPBuiltinSuccess LPIVar"] checked
    by (auto simp: lpp_check_numeric_guard_def lpp_comparison_its_value split: if_splits)
  show "IA4.formula formula" using checked lpp_comparison_its_type
    by (simp add: lpp_check_numeric_guard_def)
qed

lemma lpp_is_guard_as_equality:
  assumes success: "lpp_integer_is_outcome a e (LPPBuiltinSuccess mu)"
  shows "lpp_integer_compare_outcome LPPIntEqual (lp_isubst a mu) (lp_isubst e mu)
    (LPPBuiltinSuccess LPIVar)"
proof -
  obtain n where evaluated: "lpp_integer_evaluation e n"
    and chosen: "lpp_integer_unifier a n=Some mu"
    using success by (auto simp: lpp_integer_is_outcome_def split: option.splits)
  have lhs: "lp_isubst a mu=lpp_integer_value n" by (rule lpp_integer_unifier_sound[OF chosen])
  have rhs: "lp_isubst e mu=e" by (rule lpp_integer_evaluation_subst[OF evaluated])
  show ?thesis unfolding lhs rhs lpp_integer_compare_outcome_def
    by (rule exI[of _ n], rule exI[of _ n])
      (use evaluated lpp_integer_evaluation.literal[of n] in simp)
qed

ML \<open>
val checked = @{thms lpp_check_numeric_guard_sound} @
  [@{thm lpp_is_guard_as_equality}, @{thm lpp_comparison_its_type}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted numeric guard dependency" else ();
\<close>
end
