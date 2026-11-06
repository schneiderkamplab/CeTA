theory LP_Prolog_Stable_Source_Arithmetic
 imports LP_Prolog_Stable_Split_Contract
begin

lemma lpp_stable_source_is:
  "lpp_stable_source_builtin operation ''2:is'' [a,e] outcome =
    lpp_stable_is_outcome operation a e outcome"
  by (auto simp: lpp_stable_source_builtin_def lpp_finite_source_builtin_def
    lpp_stable_is_outcome_def)

lemma lpp_stable_source_comparison:
  assumes name: "lpp_comparison_descriptor f comparison reversed"
  shows "lpp_stable_source_builtin operation f [a,b] outcome =
    lpp_stable_compare_outcome operation comparison
      (if reversed then b else a) (if reversed then a else b) outcome"
proof -
  have ne: "f\<noteq>''2:is''" and nl: "f\<noteq>''2:length''"
    using name by (cases comparison; cases reversed; auto)+
  have descriptor: "lpp_source_comparison f=Some (comparison,reversed)"
    using name by (simp only: lpp_source_comparison_descriptor)
  have nd: "f\<noteq>lpp_disequality_predicate"
    using descriptor by (auto simp only: lpp_disequality_names)
  have np: "\<not>lpp_probe_name f"
  proof
    assume probe: "lpp_probe_name f"
    have "lpp_source_comparison f=None"
      using probe by (auto simp only: lpp_probe_name_def lpp_probe_legacy_flags(3,8,13))
    with descriptor show False by simp
  qed
  show ?thesis
    by (simp only: lpp_stable_source_builtin_def ne if_False descriptor option.case prod.case
      lpp_finite_source_legacy[OF ne nd nl np] lpp_integer_source_finite_comparison[OF name];
      auto simp: lpp_stable_compare_outcome_def)
qed

lemma lpp_stable_source_is_errors:
  "lpp_stable_source_builtin operation ''2:is'' [a,e] LPPBuiltinError =
    lpp_finite_source_builtin ''2:is'' [a,e] LPPBuiltinError"
  by (simp add: lpp_stable_source_is lpp_stable_is_preserves_errors lpp_finite_source_builtin_def)

lemma lpp_stable_source_comparison_errors:
  assumes name: "lpp_comparison_descriptor f comparison reversed"
  shows "lpp_stable_source_builtin operation f [a,b] LPPBuiltinError =
    lpp_finite_compare_outcome comparison (if reversed then b else a)
      (if reversed then a else b) LPPBuiltinError"
  by (simp only: lpp_stable_source_comparison[OF name] lpp_stable_compare_preserves_errors)

lemma lpp_stable_source_integer_is:
  assumes compatible: "lpp_stable_integer_operations operation"
    and evaluated: "lpp_integer_evaluation e n"
  shows "lpp_stable_source_builtin operation ''2:is'' [a,e] outcome =
    lpp_integer_is_outcome a e outcome"
  by (simp only: lpp_stable_source_is lpp_stable_is_integer_exact[OF compatible evaluated])

ML \<open>
val checked = [@{thm lpp_stable_source_is}, @{thm lpp_stable_source_comparison},
  @{thm lpp_stable_source_is_errors}, @{thm lpp_stable_source_comparison_errors},
  @{thm lpp_stable_source_integer_is}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable source arithmetic dependency" else ();
\<close>
end
