theory LP_Prolog_Ground_Integer_NO_Profile
 imports LP_Prolog_Ground_Integer_NO LP_Prolog_Stable_Source
begin

lemma lpp_test_builtin_stable:
 assumes outcome: "lpp_test_builtin f ts result"
 shows "lpp_stable_source_builtin operation f ts result"
proof -
 have names: "lpp_var_name f \<or> lpp_identity_name f"
   using outcome by (auto simp: lpp_test_builtin_def lpp_var_builtin_def)
 have ni: "f\<noteq>''2:is''" and nt: "f\<noteq>''1:integer''"
   using names by (auto simp: lpp_var_name_def lpp_identity_name_def)+
 have nc: "lpp_source_comparison f=None"
   using names by (auto simp only: lpp_var_name_def lpp_identity_name_def lpp_source_comparison_legacy_names)
 have lengths: "(lpp_var_name f \<and> length ts=1) \<or> (lpp_identity_name f \<and> length ts=2)"
   using outcome by (auto simp: lpp_test_builtin_def lpp_var_builtin_def)
 have domain: "lpp_integer_source_domain f ts"
   using lengths by (simp only: lpp_integer_source_domain.simps ni nt if_False nc option.case)
 show ?thesis using outcome
   by (simp only: lpp_stable_source_other[OF ni nc]
     lpp_finite_source_integer_domain[OF domain] lpp_integer_source_legacy[OF names])
qed

lemma lpp_integer_identity_stable:
 assumes compatible: "lpp_stable_integer_operations operation"
 shows "lpp_stable_source_builtin operation ''2:is''
   [lpp_integer_value n,lpp_integer_value n] (LPPBuiltinSuccess LPIVar)"
proof -
 have ev: "lpp_integer_evaluation (lpp_integer_value n) n"
   by (rule lpp_integer_evaluation.literal)
 have domain: "lpp_integer_source_domain ''2:is'' [lpp_integer_value n,lpp_integer_value n]"
   using ev by auto
 have identity: "lpp_integer_is_outcome (lpp_integer_value n) (lpp_integer_value n) (LPPBuiltinSuccess LPIVar)"
   by (simp only: lpp_integer_is_outcome_exact[OF ev]; simp add: lpp_integer_value_def)
 have finite: "lpp_finite_source_builtin ''2:is'' [lpp_integer_value n,lpp_integer_value n] (LPPBuiltinSuccess LPIVar)"
   by (simp only: lpp_finite_source_integer_domain[OF domain] lpp_integer_source_is identity)
 have stable: "lpp_stable_is_outcome operation (lpp_integer_value n) (lpp_integer_value n) (LPPBuiltinSuccess LPIVar)"
   by (simp only: lpp_stable_is_integer_exact[OF compatible ev] identity)
 show ?thesis using finite stable by (simp add: lpp_stable_source_builtin_def)
qed

lemma lpp_integer_comparison_stable:
 assumes compatible: "lpp_stable_integer_operations operation"
   and name: "lpp_comparison_descriptor f comparison reversed"
   and outcome: "lpp_integer_compare_outcome comparison
     (if reversed then b else a) (if reversed then a else b) result"
 shows "lpp_stable_source_builtin operation f [a,b] result"
proof -
 obtain n m where left: "lpp_integer_evaluation a n" and right: "lpp_integer_evaluation b m"
   using outcome by (cases reversed) (auto simp: lpp_integer_compare_outcome_def)
 have nc: "lpp_source_comparison f=Some (comparison,reversed)"
   using name lpp_source_comparison_descriptor by blast
 have ni: "f\<noteq>''2:is''" and nt: "f\<noteq>''1:integer''"
   using name by (cases comparison; cases reversed; auto)+
 have domain: "lpp_integer_source_domain f [a,b]"
   using lpp_integer_evaluation_ground[OF left] lpp_integer_evaluation_ground[OF right]
   by (simp only: lpp_integer_source_domain.simps ni nt if_False nc option.case; simp)
 have finite: "lpp_finite_source_builtin f [a,b] result"
   using outcome by (simp only: lpp_finite_source_integer_domain[OF domain]
     lpp_integer_source_comparison[OF name left right])
 have stable: "lpp_stable_compare_outcome operation comparison
   (if reversed then b else a) (if reversed then a else b) result"
   using outcome by (cases reversed)
     (simp_all only: if_True if_False lpp_stable_compare_integer_exact[OF compatible left right]
       lpp_stable_compare_integer_exact[OF compatible right left])
 show ?thesis using finite stable
   by (simp only: lpp_stable_source_builtin_def ni if_False nc option.case prod.case; auto split: if_splits)

qed

lemma lpp_ground_integer_no_stable:
 assumes compatible: "lpp_stable_integer_operations operation"
   and outcome: "lpp_ground_integer_no_builtin f ts result"
 shows "lpp_stable_source_builtin operation f ts result"
 using outcome lpp_test_builtin_stable lpp_integer_identity_stable[OF compatible]
   lpp_integer_comparison_stable[OF compatible]
 by (auto simp: lpp_ground_integer_no_builtin_def lpp_integer_no_builtin_def)

corollary lpp_ground_integer_no_profile_sound:
 assumes checked: "lpp_ground_integer_no_check_source fuel P q modes argv a before after initial_steps steps"
   and compatible: "lpp_stable_integer_operations operation"
 shows "\<not> SN_on (lpp_builtin_source P (lpp_stable_source_builtin operation))
   {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
proof
 let ?initial = "[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]"
 assume sn: "SN_on (lpp_builtin_source P (lpp_stable_source_builtin operation)) {?initial}"
 have included: "lpp_builtin_source P lpp_ground_integer_no_builtin \<subseteq>
   lpp_builtin_source P (lpp_stable_source_builtin operation)"
   by (rule lpp_builtin_source_mono) (rule lpp_ground_integer_no_stable[OF compatible])
 have smaller: "SN_on (lpp_builtin_source P lpp_ground_integer_no_builtin) {?initial}"
   by (rule SN_on_subset1[OF sn included])
 show False using smaller lpp_ground_integer_no_check_source_sound[OF checked] by blast
qed

ML \<open>
val checked = [@{thm lpp_ground_integer_no_profile_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted ground integer profile dependency" else ();
\<close>
end
