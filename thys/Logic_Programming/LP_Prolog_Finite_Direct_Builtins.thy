theory LP_Prolog_Finite_Direct_Builtins
 imports LP_Prolog_Finite_Direct_State
begin

fun lpp_finite_direct_outcome where
 "lpp_finite_direct_outcome (LPPBuiltinSuccess sigma) =
   (\<forall>t. lpp_finite_term t \<longrightarrow> lpp_finite_term (lp_isubst t sigma))"
| "lpp_finite_direct_outcome LPPBuiltinFailure = True"
| "lpp_finite_direct_outcome LPPBuiltinError = True"
| "lpp_finite_direct_outcome outcome = False"

definition lpp_direct_arithmetic_name where
 "lpp_direct_arithmetic_name f = (f=''2:is'' \<or> lpp_source_comparison f\<noteq>None)"

lemma lpp_direct_arithmetic_outcome:
 assumes name: "lpp_direct_arithmetic_name f"
   and outcome: "lpp_stable_source_builtin operation f ts result"
 shows "lpp_finite_direct_outcome result"
proof (cases "f=''2:is''")
 case True
 have stable: "lpp_stable_is_outcome operation (ts!0) (ts!1) result"
   using outcome True by (simp add: lpp_stable_source_builtin_def)
 show ?thesis using stable
   by (auto simp: lpp_stable_is_outcome_def split: option.splits
     intro: lpp_scalar_unifier_preserves_finite)
next
 case False
 obtain comparison reversed where descriptor: "lpp_source_comparison f=Some (comparison,reversed)"
   using name False by (auto simp: lpp_direct_arithmetic_name_def)
 have stable: "lpp_stable_compare_outcome operation comparison
     (if reversed then ts!1 else ts!0) (if reversed then ts!0 else ts!1) result"
   using outcome False descriptor by (simp add: lpp_stable_source_builtin_def)
 show ?thesis using stable by (auto simp: lpp_stable_compare_outcome_def split: if_splits)
qed

lemma lpp_finite_direct_substitute:
 assumes safe: "lpp_finite_direct_outcome (LPPBuiltinSuccess sigma)"
   and goal: "lpp_finite_direct_goal g"
 shows "lpp_finite_direct_goal (lp_cut_map (\<lambda>t. lp_isubst t sigma) g)"
 using safe goal by (cases g) auto

ML \<open>
val checked = [@{thm lpp_direct_arithmetic_outcome}, @{thm lpp_finite_direct_substitute}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite builtin transport" else ();
\<close>
end
