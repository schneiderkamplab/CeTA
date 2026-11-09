theory Higher_Order_Examples
  imports Higher_Order_Sorts_Properties
begin
text \<open>Beta reduction preserves binding: the argument's free bound index
is lifted when it crosses a remaining abstraction.\<close>
lemma higher_capture_avoiding_example:
  "higher_beta_subst (SpecHBound 0) 0 (SpecHAbs (SpecHBase 0) (SpecHBound 1)) =
    SpecHAbs (SpecHBase 0) (SpecHBound 1)"
  by simp
lemma higher_beta_identity_example:
  "higher_order_step [SpecHBase 0] [] [] (SpecHBase 0)
    (SpecHApp (SpecHAbs (SpecHBase 0) (SpecHBound 0)) (SpecHConst 0)) (SpecHConst 0)"
  using higher_step.beta[where S="[SpecHBase 0]" and V="[]" and R="[]" and B="[]"
    and A="SpecHBase 0" and t="SpecHBound 0" and u="SpecHConst 0"]
  by (simp add: higher_order_step_def)
text \<open>Ordinary application is retained; only designated meta arguments
are contracted while instantiating a rule.\<close>
lemma higher_ordinary_application_example:
  "higher_instantiate (\<lambda>_. SpecHAbs (SpecHBase 0) (SpecHBound 0)) 0
    (SpecPApp (SpecPMeta 0 []) (SpecPConst 0)) =
    Some (SpecHApp (SpecHAbs (SpecHBase 0) (SpecHBound 0)) (SpecHConst 0))"
  by simp
lemma higher_meta_under_binder_example:
  "higher_instantiate (\<lambda>_. SpecHAbs (SpecHBase 0) (SpecHBound 0)) 0
    (SpecPAbs (SpecHBase 0) (SpecPMeta 0 [SpecPBound 0])) =
    Some (SpecHAbs (SpecHBase 0) (SpecHBound 0))"
  by simp
lemma higher_type_mismatch_example:
  "higher_typeof [SpecHBase 0] [] [] (SpecHApp (SpecHConst 0) (SpecHConst 0)) = None"
  by simp
lemma higher_constant_loop_example:
  "higher_order_step [SpecHBase 0] [] [([],SpecPConst 0,SpecPConst 0)] (SpecHBase 0)
    (SpecHConst 0) (SpecHConst 0)"
proof -
  have "higher_step [SpecHBase 0] [] [([],SpecPConst 0,SpecPConst 0)] [] (SpecHConst 0) (SpecHConst 0)"
    by (rule higher_step.rule[where G="[]" and l="SpecPConst 0" and r="SpecPConst 0" and s="\<lambda>_. SpecHConst 0"])
      (simp_all add: higher_rule_welltyped_def higher_typed_subst_def)
  then show ?thesis by (simp add: higher_order_step_def)
qed
lemma higher_constant_nontermination_example:
  "\<not> higher_order_terminates [SpecHBase 0] [([],SpecPConst 0,SpecPConst 0)]"
  unfolding higher_order_nontermination_iff
  by (intro exI[of _ "[]"] exI[of _ "SpecHBase 0"] exI[of _ "\<lambda>_. SpecHConst 0"])
    (simp add: higher_constant_loop_example)
text \<open>Validity is separate from termination: a well-formed constant loop
is a category input, while repeated left meta-arguments are not.\<close>
lemma higher_valid_loop_example:
  "higher_order_problem [SpecHBase 0] [([],SpecPConst 0,SpecPConst 0)]"
  by (simp add: higher_order_problem_def higher_category_rule_def higher_rule_welltyped_def)
lemma higher_repeated_meta_argument_rejected:
  "\<not> higher_left_pattern ar (SpecPMeta 0 [SpecPBound 0, SpecPBound 0])"
  by simp
lemma higher_beta_pattern_rejected:
  "\<not> higher_right_pattern ar
    (SpecPApp (SpecPAbs (SpecHBase 0) (SpecPBound 0)) (SpecPConst 0))"
  by simp

text \<open>The canonical property uses precisely the declared sorts. A valid
constant loop remains nonterminating there, while an undeclared sort is rejected.
Open typed terms are available even when there are no constants.\<close>
lemma higher_declared_loop_valid:
  "higher_order_declared_problem 1 [SpecHBase 0] [([],SpecPConst 0,SpecPConst 0)]"
  by (simp add: higher_order_declared_problem_def higher_valid_loop_example higher_sort_rule_def)
lemma higher_declared_loop_nontermination:
  "\<not> higher_order_terminates_over_sorts 1 [SpecHBase 0] [([],SpecPConst 0,SpecPConst 0)]"
  unfolding higher_order_declared_nontermination_iff
  by (intro exI[of _ "[]"] exI[of _ "SpecHBase 0"] exI[of _ "\<lambda>_. SpecHConst 0"])
    (simp add: higher_constant_loop_example)
lemma higher_undeclared_sort_rejected:
  "\<not> higher_order_declared_problem 1 [SpecHBase 1] []"
  by (simp add: higher_order_declared_problem_def)
lemma higher_open_term_without_constants:
  "higher_typeof [] [SpecHBase 0] [] (SpecHFree 0) = Some (SpecHBase 0)"
  by simp
end
