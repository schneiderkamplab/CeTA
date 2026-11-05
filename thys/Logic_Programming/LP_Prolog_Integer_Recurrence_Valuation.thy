theory LP_Prolog_Integer_Recurrence_Valuation
  imports LP_Prolog_Integer_Recurrence_Inverse
begin

text \<open>Integer-child transitions use arbitrary well-typed ITS valuations.
Boolean coordinates need not equal the canonical false assignment used in
arithmetic lemmas. The bridge observes only integer coordinates and proves
that changing the unobserved Boolean values cannot change its relation.\<close>

lemma lpp_recurrence_assignment_integer:
  assumes typed: "IA4.assignment alpha"
  shows "alpha (x,IA.IntT)=IA.Int (IA.to_int (alpha (x,IA.IntT)))"
  using IA4.assignmentD[OF typed, of "(x,IA.IntT)"] by auto

lemma lpp_recurrence_expression_valuation_cong:
  assumes same: "\<And>x. alpha (x,IA.IntT)=beta (x,IA.IntT)"
  shows "IA4.eval (lpp_expression_its e) alpha=IA4.eval (lpp_expression_its e) beta"
  by (induct e) (simp_all add: algebra.eval.simps same Let_def)

lemma lpp_recurrence_comparison_valuation_cong:
  assumes same: "\<And>x. alpha (x,IA.IntT)=beta (x,IA.IntT)"
  shows "IA4.satisfies alpha (lpp_comparison_its c (lpp_expression_its a) (lpp_expression_its b)) =
    IA4.satisfies beta (lpp_comparison_its c (lpp_expression_its a) (lpp_expression_its b))"
  by (cases c) (simp_all add: algebra.eval.simps lpp_recurrence_expression_valuation_cong[where alpha=alpha and beta=beta, OF same])

lemma lpp_recurrence_condition_valuation_cong:
  assumes same: "\<And>x. alpha (x,IA.IntT)=beta (x,IA.IntT)"
  shows "IA4.satisfies alpha (lpp_numeric_condition_formula condition) =
    IA4.satisfies beta (lpp_numeric_condition_formula condition)"
  by (cases condition) (simp add: lpp_recurrence_comparison_valuation_cong[where alpha=alpha and beta=beta, OF same] split: prod.splits)

lemma lpp_recurrence_relation_valuation_cong:
  assumes same: "\<And>x. alpha (x,IA.IntT)=beta (x,IA.IntT)"
  shows "IA4.satisfies alpha (lpp_recurrence_relation_formula xs ops outputs) =
    IA4.satisfies beta (lpp_recurrence_relation_formula xs ops outputs)"
proof -
  have condition: "IA4.satisfies alpha (lpp_numeric_condition_formula test) =
      IA4.satisfies beta (lpp_numeric_condition_formula test)" for test
    by (rule lpp_recurrence_condition_valuation_cong[where alpha=alpha and beta=beta, OF same])
  have image: "(\<forall>x\<in>f ` A. Q x) = (\<forall>x\<in>A. Q (f x))" for f A Q by auto
  show ?thesis
    unfolding lpp_recurrence_relation_formula_def
    by (simp only: formula.satisfies.simps set_map image condition)
qed

lemma lpp_recurrence_relation_arbitrary_valuation:
  assumes typed: "IA4.assignment alpha"
  shows "IA4.satisfies alpha (lpp_recurrence_relation_formula xs ops outputs) =
    IA4.satisfies (lpp_integer_assignment (\<lambda>x. IA.to_int (alpha (x,IA.IntT))))
      (lpp_recurrence_relation_formula xs ops outputs)"
  by (rule lpp_recurrence_relation_valuation_cong)
    (simp only: lpp_integer_assignment.simps; rule lpp_recurrence_assignment_integer[OF typed])

ML \<open>
val checked = [@{thm lpp_recurrence_relation_arbitrary_valuation}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted recurrence valuation dependency" else ();
\<close>
end
