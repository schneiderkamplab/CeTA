theory LP_Prolog_Probe_Return_Domain
  imports LP_Prolog_Finite_Source
begin

lemma lpp_integer_source_no_probe:
  "\<not>lpp_integer_source_builtin f ts (LPPBuiltinProbe a keep)"
  by (auto simp del: lpp_source_comparison.simps simp: lpp_integer_test_outcome_def lpp_integer_is_outcome_def
    lpp_finite_compare_outcome_def lpp_integer_compare_outcome_def
    lpp_test_builtin_def lpp_var_builtin_def split: if_splits option.splits prod.splits)

lemma lpp_integer_source_no_call:
  "\<not>lpp_integer_source_builtin f ts (LPPBuiltinCall a)"
  by (auto simp del: lpp_source_comparison.simps simp: lpp_integer_test_outcome_def lpp_integer_is_outcome_def
    lpp_finite_compare_outcome_def lpp_integer_compare_outcome_def
    lpp_test_builtin_def lpp_var_builtin_def split: if_splits option.splits prod.splits)

lemma lpp_integer_source_no_branch:
  "\<not>lpp_integer_source_builtin f ts (LPPBuiltinBranch cs ys ns)"
  by (auto simp del: lpp_source_comparison.simps simp: lpp_integer_test_outcome_def lpp_integer_is_outcome_def
    lpp_finite_compare_outcome_def lpp_integer_compare_outcome_def
    lpp_test_builtin_def lpp_var_builtin_def split: if_splits option.splits prod.splits)

lemma lpp_integer_source_no_choice:
  "\<not>lpp_integer_source_builtin f ts (LPPBuiltinChoice left right)"
  by (auto simp del: lpp_source_comparison.simps simp: lpp_integer_test_outcome_def lpp_integer_is_outcome_def
    lpp_finite_compare_outcome_def lpp_integer_compare_outcome_def
    lpp_test_builtin_def lpp_var_builtin_def split: if_splits option.splits prod.splits)

lemma lpp_finite_source_probe_name:
  "lpp_finite_source_builtin f ts (LPPBuiltinProbe a keep) \<Longrightarrow> lpp_probe_name f"
  using lpp_integer_source_no_probe[of f ts a keep]
  by (auto simp: lpp_finite_source_builtin_def lpp_finite_is_outcome_def
    lpp_integer_is_outcome_def lpp_finite_length_outcome_def
    lpp_rational_disequality_outcome_def lpp_branch_outcome_def split: if_splits option.splits)

end
