theory TRS_Relative_Examples
  imports TRS_Relative_Properties TRS_Standard_Examples
begin
lemma no_strict_rules:
  "trs_relative_terminates A {} S"
  by (simp add: trs_relative_terminates_def no_infinite_steps_def relative_step_def fo_step_def)

text \<open>A weak self-loop alone is harmless for relative termination.\<close>
lemma weak_loop_allowed:
  "trs_relative_terminates unary {} {(SFun () [SVar (0::nat)], SFun () [SVar 0])}"
  by (rule no_strict_rules)

lemma finite_empty_steps:
  "finite_steps (fo_step A {}) s t \<longleftrightarrow> s = t"
  by (auto elim: finite_steps.cases simp: fo_step_def intro: finite_steps.zero)
lemma no_weak_rules:
  "trs_relative_terminates A R {} \<longleftrightarrow> trs_standard_terminates A R"
  by (simp add: trs_relative_terminates_def no_infinite_steps_def relative_step_def
      finite_empty_steps trs_standard_terminates_def no_infinite_steps_def)
lemma strict_loop_rejected:
  "\<not> trs_relative_terminates unary {(SFun () [SVar (0::nat)], SFun () [SVar 0])} {}"
  by (simp add: no_weak_rules no_constants_nontermination)
lemma relative_reduction:
  "trs_relative_terminates unary {(SFun () [SVar (0::nat)], SVar 0)} {}"
  by (simp add: no_weak_rules reduction_terminates)
end
