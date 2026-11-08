theory TRS_Outermost_Examples
  imports TRS_Outermost_Spec TRS_Standard_Examples
begin
lemma outermost_implies_standard_step:
  "outermost_step A R s t \<Longrightarrow> standard_step A R s t"
  by (auto simp: outermost_step_def standard_step_def)
lemma outermost_empty_terminates: "trs_outermost_terminates A {}"
  by (simp add: trs_outermost_terminates_def no_infinite_steps_def outermost_step_def)
lemma outermost_reduction_terminates:
  "trs_outermost_terminates A {(SFun f [SVar (0::nat)], SVar 0)}"
  using reduction_terminates[of A f] outermost_implies_standard_step
  unfolding trs_outermost_terminates_def no_infinite_steps_def trs_standard_terminates_def by blast
lemma outermost_self_loop:
  assumes "arity_correct A t"
  shows "\<not> trs_outermost_terminates A {(t,t)}"
proof -
  have sub: "standard_subst SVar t = t"
    by (induct t) (auto simp: map_idI)
  have step: "outermost_step A {(t,t)} t t"
    unfolding outermost_step_def
    apply (intro conjI)
      apply (rule assms)
     apply (rule assms)
    apply (rule exI[of _ t], rule exI[of _ t], rule exI[of _ SHole], rule exI[of _ SVar])
    by (simp add: sub correct_substitution_def)
  show ?thesis unfolding trs_outermost_nontermination_iff
    by (intro exI[of _ "\<lambda>_. t"]) (simp add: step)
qed
lemma outermost_without_constants:
  "\<not> trs_outermost_terminates unary {(SFun () [SVar (7::nat)], SFun () [SVar 7])}"
  by (rule outermost_self_loop) (simp add: unary_def)
lemma outermost_variable_rule_without_symbols:
  "\<not> trs_outermost_terminates (\<lambda>_. None) {(SVar (0::nat), SVar 0)}"
  by (rule outermost_self_loop) simp
lemma outermost_arity_mismatch:
  "\<not> outermost_step unary R (SFun () []) t"
  by (simp add: outermost_step_def unary_def)
text \<open>With f(x) to x, the redex f(f(y)) at the root blocks selecting
its inner f(y). Outermost does not mean an arbitrary rewrite step.\<close>
lemma outermost_root_blocks_inner:
  "\<not> outermost_above unary {(SFun () [SVar (0::nat)], SVar 0)}
    (SMore () [] SHole []) (SFun () [SVar 7])"
proof -
  have "outermost_root_redex unary {(SFun () [SVar (0::nat)], SVar 0)}
      (SFun () [SFun () [SVar 7]])"
    unfolding outermost_root_redex_def
    apply (rule exI[of _ "SFun () [SVar (0::nat)]"])
    apply (rule exI[of _ "SVar (0::nat)"])
    apply (rule exI[of _ "\<lambda>_::nat. SFun () [SVar (7::nat)]"])
    by (simp add: correct_substitution_def unary_def)
  then show ?thesis by simp
qed
text \<open>A different head above a self-loop does not block its contraction.
The context and substitution may be nonground.\<close>
lemma outermost_below_root:
  "outermost_step (\<lambda>_::bool. Some 1)
    {(SFun False [SVar (0::nat)], SFun False [SVar 0])}
    (SFun True [SFun False [SVar 7]]) (SFun True [SFun False [SVar 7]])"
  unfolding outermost_step_def
  apply (intro conjI)
    apply simp
   apply simp
  apply (rule exI[of _ "SFun False [SVar (0::nat)]"])
  apply (rule exI[of _ "SFun False [SVar (0::nat)]"])
  apply (rule exI[of _ "SMore True [] SHole []"])
  apply (rule exI[of _ "\<lambda>_. SVar (7::nat)"])
  by (simp add: correct_substitution_def outermost_root_redex_def)
end
