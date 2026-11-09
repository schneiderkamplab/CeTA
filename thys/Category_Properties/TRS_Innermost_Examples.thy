theory TRS_Innermost_Examples
  imports TRS_Innermost_Properties TRS_Standard_Examples
begin
lemma innermost_is_standard:
  "innermost_step A R s t \<Longrightarrow> fo_step A R s t"
  unfolding innermost_step_def fo_step_def by blast
lemma standard_termination_implies_innermost:
  "trs_standard_terminates A R \<Longrightarrow> trs_innermost_terminates A R"
  unfolding trs_standard_terminates_def no_infinite_steps_def trs_innermost_terminates_def no_infinite_steps_def
  using innermost_is_standard by blast
lemma empty_innermost: "trs_innermost_terminates A {}"
  by (rule standard_termination_implies_innermost, rule empty_terminates)
lemma reduction_innermost:
  "trs_innermost_terminates A {(SFun f [SVar (0::nat)], SVar 0)}"
  by (rule standard_termination_implies_innermost, rule reduction_terminates)

lemma plug_function_not_variable:
  "fo_plug C (SFun f ts) \<noteq> SVar x"
  by (cases C) auto
lemma variable_normal:
  "innermost_normal A {(SFun f ts,r)} (SVar x)"
  by (auto simp: innermost_normal_def dest: sym) (metis plug_function_not_variable)

text \<open>A nonground instance is contracted below the root in a signature
without constants. The reducible outer function does not block an inner step.\<close>
lemma innermost_below_root_nonground:
  "innermost_step unary {(SFun () [SVar (0::nat)], SVar 0)}
    (SFun () [SFun () [SVar 7]]) (SFun () [SVar 7])"
  unfolding innermost_step_def
  apply (intro conjI)
    apply (simp add: unary_def)
   apply (simp add: unary_def)
  apply (rule exI[of _ "SFun () [SVar (0::nat)]"])
  apply (rule exI[of _ "SVar (0::nat)"])
  apply (rule exI[of _ "SMore () [] SHole []"])
  apply (rule exI[of _ "\<lambda>_. SVar (7::nat)"])
  by (simp add: unary_def correct_substitution_def variable_normal)

lemma unary_redex_not_normal:
  "\<not> innermost_normal unary {(SFun () [SVar (0::nat)],r)} (SFun () [SVar 7])"
  unfolding innermost_normal_def
  apply simp
  apply (rule exI[of _ SHole])
  apply (simp only: correct_context.simps fo_plug.simps simp_thms)
  apply (rule exI[of _ "\<lambda>_. SVar (7::nat)"])
  by (simp add: correct_substitution_def)

text \<open>The root instance f(f(x)) fails the proper-subterm test.\<close>
lemma nested_root_blocked:
  "\<not> (\<forall>u\<in>proper_subterms (SFun () [SFun () [SVar (7::nat)]]).
    innermost_normal unary {(SFun () [SVar (0::nat)], SVar 0)} u)"
  using unary_redex_not_normal[of "SVar (0::nat)"] by auto

lemma innermost_self_loop_no_constants:
  "\<not> trs_innermost_terminates unary
    {(SFun () [SVar (0::nat)], SFun () [SVar 0])}"
proof -
  let ?t = "SFun () [SVar (0::nat)]"
  have "innermost_step unary {(?t,?t)} ?t ?t"
    unfolding innermost_step_def
    apply (intro conjI)
      apply (simp add: unary_def)
     apply (simp add: unary_def)
    apply (rule exI[of _ ?t], rule exI[of _ ?t])
    apply (rule exI[of _ SHole], rule exI[of _ SVar])
    by (simp add: unary_def correct_substitution_def variable_normal)
  then show ?thesis unfolding trs_innermost_nontermination_iff
    by (intro exI[of _ "\<lambda>_. ?t"]) simp
qed
lemma innermost_arity_mismatch:
  "\<not> innermost_step unary R (SFun () []) t"
  by (simp add: innermost_step_def unary_def)
end
