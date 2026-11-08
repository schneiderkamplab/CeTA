theory TRS_Standard_Examples
  imports TRS_Standard_Spec
begin
lemma empty_terminates: "trs_standard_terminates A {}"
  by (simp add: trs_standard_terminates_def standard_step_def)

lemma self_loop:
  assumes "arity_correct A t"
  shows "\<not> trs_standard_terminates A {(t,t)}"
proof -
  have "standard_subst SVar t = t"
    by (induct t) (auto simp: map_idI)
  then have "standard_step A {(t,t)} t t"
    using assms unfolding standard_step_def correct_substitution_def
    by (intro conjI; (assumption | metis standard_plug.simps(1) correct_context.simps(1) arity_correct.simps(1) singletonI))
  then show ?thesis unfolding trs_standard_nontermination_iff by (intro exI[of _ "\<lambda>_. t"]) simp
qed

text \<open>The unary signature has no constants, yet has variables and compound
nonground terms. Arity errors are rejected.\<close>
definition unary :: "unit ranked_signature" where "unary f = Some 1"
lemma no_constants: "\<not> arity_correct unary (SFun f [])"
  by (simp add: unary_def)
lemma wrong_arity: "\<not> arity_correct unary (SFun () [SVar (0::nat), SVar (1::nat)])"
  by (simp add: unary_def)
lemma nonground_term: "arity_correct unary (SFun () [SVar (7::nat)])"
  by (simp add: unary_def)
lemma no_constants_nontermination:
  "\<not> trs_standard_terminates unary {(SFun () [SVar (0::nat)], SFun () [SVar (0::nat)])}"
  by (rule self_loop) (simp add: unary_def)

text \<open>The rule f(x) to x decreases the number of function occurrences,
including when applied below the root or with a nonground substitution.\<close>
fun function_count where
  "function_count (SVar x) = (0::nat)"
| "function_count (SFun f ts) = Suc (sum_list (map function_count ts))"
lemma plug_decreases:
  "function_count s < function_count t \<Longrightarrow>
   function_count (standard_plug C s) < function_count (standard_plug C t)"
  by (induct C) auto
lemma reduction_decreases:
  "standard_step A {(SFun f [SVar (0::nat)], SVar (0::nat))} s t \<Longrightarrow>
   function_count t < function_count s"
  by (auto simp: standard_step_def intro: plug_decreases)
lemma reduction_terminates:
  "trs_standard_terminates A {(SFun f [SVar (0::nat)], SVar (0::nat))}"
proof (unfold trs_standard_terminates_def, clarify)
  fix ts
  assume steps: "\<forall>i. standard_step A {(SFun f [SVar (0::nat)], SVar (0::nat))} (ts i) (ts (Suc i))"
  have bound: "\<And>n. function_count (ts n) + n \<le> function_count (ts 0)"
  proof -
    fix n
    show "function_count (ts n) + n \<le> function_count (ts 0)"
    proof (induct n)
      case 0
      show ?case by simp
    next
      case (Suc n)
      have "function_count (ts (Suc n)) < function_count (ts n)"
        by (rule reduction_decreases[of A f], rule steps[rule_format])
      then show ?case using Suc by arith
    qed
  qed
  from bound[of "Suc (function_count (ts 0))"] show False by simp
qed

lemma below_root_nonground:
  "standard_step unary {(SFun () [SVar (0::nat)], SVar (0::nat))}
    (SFun () [SFun () [SVar (7::nat)]]) (SFun () [SVar (7::nat)])"
  unfolding standard_step_def
  apply (intro conjI)
    apply (simp add: unary_def)
   apply (simp add: unary_def)
  apply (rule exI[of _ "SFun () [SVar (0::nat)]"])
  apply (rule exI[of _ "SVar (0::nat)"])
  apply (rule exI[of _ "SMore () [] SHole []"])
  apply (rule exI[of _ "\<lambda>_. SVar (7::nat)"])
  by (simp add: unary_def correct_substitution_def)
lemma reduction_is_problem:
  "standard_problem unary {(SFun () [SVar (0::nat)], SVar (0::nat))}"
  by (simp add: standard_problem_def unary_def)

lemma malformed_source_cannot_step:
  "\<not> standard_step unary R (SFun () []) t"
  by (simp add: standard_step_def unary_def)
lemma variable_left_and_extra_right_allowed:
  "standard_problem unary {(SVar (0::nat), SVar 1)}"
  by (simp add: standard_problem_def)
end
