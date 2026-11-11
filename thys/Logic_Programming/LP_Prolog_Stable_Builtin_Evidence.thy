theory LP_Prolog_Stable_Builtin_Evidence
 imports LP_Prolog_Stable_Source
begin

lemma lpp_stable_is_evaluated:
 assumes compatible: "lpp_stable_integer_operations operation"
   and evaluated: "lpp_stable_scalar_evaluation operation e (LPIFun (LPCUser f) [])"
 shows "lpp_stable_is_outcome operation a e
   (case lpp_scalar_unifier a f of None \<Rightarrow> LPPBuiltinFailure | Some mu \<Rightarrow> LPPBuiltinSuccess mu)"
proof -
 let ?out="case lpp_scalar_unifier a f of None \<Rightarrow> LPPBuiltinFailure | Some mu \<Rightarrow> LPPBuiltinSuccess mu"
 have ground: "lp_seg_ground e" using lpp_stable_scalar_evaluation_ground[OF evaluated] by blast
 have finite: "lpp_finite_is_outcome a e ?out"
 proof (cases "\<exists>n. lpp_integer_evaluation e n")
  case True
  then obtain n where integer: "lpp_integer_evaluation e n" by blast
  have name: "f=lpp_integer_name n"
    using lpp_stable_evaluation_integer_exact[OF compatible integer, THEN iffD1, OF evaluated]
    by (simp add: lpp_integer_value_def)
  show ?thesis
    by (simp only: lpp_finite_is_integer[OF integer] lpp_integer_is_outcome_exact[OF integer] name
       lpp_scalar_integer_unifier)
 next
  case False
  show ?thesis using ground False
    by (auto simp: lpp_finite_is_outcome_def lpp_finite_instantiation_error_def split: option.splits)
 qed
 show ?thesis using finite evaluated
   by (auto simp: lpp_stable_is_outcome_def split: option.splits)
qed

lemma lpp_stable_comparison_evaluated:
 assumes compatible: "lpp_stable_integer_operations operation"
   and compared: "lpp_stable_compare_values operation comparison a b truth"
 shows "lpp_stable_compare_outcome operation comparison a b
   (if truth then LPPBuiltinSuccess LPIVar else LPPBuiltinFailure)"
proof -
 let ?out="if truth then LPPBuiltinSuccess LPIVar else LPPBuiltinFailure"
 have ground: "lp_seg_ground a" "lp_seg_ground b"
   using compared lpp_stable_scalar_evaluation_ground
   by (auto simp: lpp_stable_compare_values_def)
 have finite: "lpp_finite_compare_outcome comparison a b ?out"
 proof (cases "(\<exists>n. lpp_integer_evaluation a n) \<and> (\<exists>m. lpp_integer_evaluation b m)")
  case True
  then obtain n m where left: "lpp_integer_evaluation a n" and right: "lpp_integer_evaluation b m" by blast
  have exact: "truth=lpp_integer_compare comparison n m"
    using compared lpp_stable_compare_values_exact[OF lpp_integer_evaluation_stable[OF compatible left]
      lpp_integer_evaluation_stable[OF compatible right]
      lpp_integer_scalar_observation lpp_integer_scalar_observation] by simp
  show ?thesis by (simp only: lpp_finite_comparison_integer[OF left right]
    lpp_integer_compare_outcome_exact[OF left right] exact)
 next
  case False
  show ?thesis using False ground by (auto simp: lpp_finite_compare_outcome_def)
 qed
 show ?thesis using finite compared by (auto simp: lpp_stable_compare_outcome_def)
qed

ML \<open>
val checked = [@{thm lpp_stable_is_evaluated}, @{thm lpp_stable_comparison_evaluated}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted evaluated builtin evidence dependency" else ();
\<close>
end
