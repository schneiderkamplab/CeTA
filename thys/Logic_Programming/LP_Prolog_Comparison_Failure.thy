theory LP_Prolog_Comparison_Failure
 imports LP_Prolog_Finite_Source_Bridges
begin

text \<open>The complement reverses operands as well as the comparison. This
covers failed comparisons without treating arbitrary ground values as integers.\<close>
fun lpp_comparison_complement where
  "lpp_comparison_complement LPPIntLess = LPPIntLessEqual"
| "lpp_comparison_complement LPPIntLessEqual = LPPIntLess"
| "lpp_comparison_complement LPPIntEqual = LPPIntNotEqual"
| "lpp_comparison_complement LPPIntNotEqual = LPPIntEqual"

lemma lpp_comparison_complement_truth:
  fixes n m :: int
  shows "lpp_integer_compare (lpp_comparison_complement c) m n = (\<not>lpp_integer_compare c n m)"
  by (cases c) auto

lemma lpp_finite_comparison_failure_complement:
  assumes failed: "lpp_finite_compare_outcome c a b LPPBuiltinFailure"
  shows "lpp_finite_compare_outcome (lpp_comparison_complement c) b a (LPPBuiltinSuccess LPIVar)"
proof (cases "(\<exists>n. lpp_integer_evaluation a n) \<and> (\<exists>m. lpp_integer_evaluation b m)")
  case True
  then obtain n m where left: "lpp_integer_evaluation a n" and right: "lpp_integer_evaluation b m" by blast
  show ?thesis using failed
    by (simp only: lpp_finite_comparison_integer[OF left right]
      lpp_finite_comparison_integer[OF right left]
      lpp_integer_compare_outcome_exact[OF left right]
      lpp_integer_compare_outcome_exact[OF right left] lpp_comparison_complement_truth;
      auto split: if_splits)
next
  case False
  then show ?thesis using failed by (auto simp: lpp_finite_compare_outcome_def)
qed

lemma lpp_finite_comparison_precise_step:
  assumes descriptor: "lpp_comparison_descriptor f comparison reversed"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin
      ((LPCGoals (LPCAtom (LPIFun (LPCUser f) [a,b])#gs),eta)#saved) event tt"
  shows "event=None \<and>
    ((tt=(LPCGoals gs,eta)#saved \<and>
      lpp_finite_compare_outcome comparison (if reversed then b else a) (if reversed then a else b) (LPPBuiltinSuccess LPIVar))
     \<or> (tt=saved \<and> lpp_finite_compare_outcome comparison (if reversed then b else a) (if reversed then a else b) LPPBuiltinFailure) \<or> tt=[])"
proof -
  have selected: "(f,length [a,b])\<in>lpp_builtin_signature"
    using lpp_comparison_selected[OF descriptor] by (simp add: numeral_2_eq_2)
  have outcomes: "\<And>outcome. lpp_integer_source_builtin f [a,b] outcome =
      lpp_finite_compare_outcome comparison (if reversed then b else a) (if reversed then a else b) outcome"
    by (rule lpp_integer_source_finite_comparison[OF descriptor])
  have identity: "\<And>sigma. lpp_integer_source_builtin f [a,b] (LPPBuiltinSuccess sigma) \<Longrightarrow> sigma=LPIVar"
    unfolding outcomes by (rule lpp_finite_comparison_success_identity)
  have success: "\<And>sigma. lpp_integer_source_builtin f [a,b] (LPPBuiltinSuccess sigma) \<Longrightarrow>
    sigma=LPIVar \<and> lpp_finite_compare_outcome comparison (if reversed then b else a) (if reversed then a else b) (LPPBuiltinSuccess LPIVar)"
    using identity outcomes by metis
  have failure: "lpp_integer_source_builtin f [a,b] LPPBuiltinFailure \<Longrightarrow>
    lpp_finite_compare_outcome comparison (if reversed then b else a) (if reversed then a else b) LPPBuiltinFailure"
    by (simp only: outcomes)
  show ?thesis using step selected
    by (cases rule: lpp_answer_transition.cases)
      (auto simp: lpp_builtin_active_def lpp_integer_source_no_probe simp del: lpp_integer_source_builtin.simps
        dest: failure dest!: success)
qed


lemma lpp_finite_source_comparison_precise_step:
  assumes descriptor: "lpp_comparison_descriptor f comparison reversed"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin
      ((LPCGoals (LPCAtom (LPIFun (LPCUser f) [a,b])#gs),eta)#saved) event tt"
  shows "event=None \<and>
    ((tt=(LPCGoals gs,eta)#saved \<and>
      lpp_finite_compare_outcome comparison (if reversed then b else a) (if reversed then a else b) (LPPBuiltinSuccess LPIVar))
     \<or> (tt=saved \<and> lpp_finite_compare_outcome comparison (if reversed then b else a) (if reversed then a else b) LPPBuiltinFailure) \<or> tt=[])"
proof -
  have ne: "f\<noteq>''2:is''" using descriptor by (cases comparison; cases reversed; auto)
  have comparison: "lpp_source_comparison f=Some (comparison,reversed)"
    using descriptor by (simp only: lpp_source_comparison_descriptor)
  have nd: "f\<noteq>lpp_disequality_predicate"
  proof
    assume "f=lpp_disequality_predicate"
    with comparison show False by (simp only: lpp_disequality_names option.distinct)
  qed
  have nl: "f\<noteq>''2:length''" using comparison by auto
  have np: "\<not>lpp_probe_name f"
  proof
    assume name: "lpp_probe_name f"
    have none: "lpp_source_comparison f=None"
      using name by (auto simp only: lpp_probe_name_def lpp_probe_legacy_flags(3,8,13))
    with comparison show False by simp
  qed
  have selected: "(f,length [a,b])\<in>lpp_builtin_signature"
    using lpp_comparison_selected[OF descriptor] by (simp add: numeral_2_eq_2)
  have old: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin
      ((LPCGoals (LPCAtom (LPIFun (LPCUser f) [a,b])#gs),eta)#saved) event tt"
    using step by (simp only: lpp_finite_source_nonis_step[OF ne nd nl np selected])
  show ?thesis by (rule lpp_finite_comparison_precise_step[OF descriptor old])
qed

end
