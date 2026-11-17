theory LP_Prolog_Finite_Operation_Outcome
 imports LP_Prolog_Finite_Execution_Builtin LP_Prolog_Finite_Direct_Builtins LP_Prolog_Finite_Fresh_Body
begin

lemma lpp_direct_outcome_finite_execution:
 assumes safe: "lpp_finite_direct_outcome outcome"
 and finite: "lpp_finite_goals gs"
 shows "lpp_finite_execution_outcome gs outcome"
 using safe finite
 by (cases outcome) (auto simp: lpp_finite_goals_def lpp_finite_goal_map list_all_iff)

lemma lpp_arithmetic_finite_execution_outcome:
 assumes name: "lpp_direct_arithmetic_name f"
 and outcome: "lpp_stable_source_builtin operation f ts result"
 and finite: "lpp_finite_goals gs"
 shows "lpp_finite_execution_outcome gs result"
 by (rule lpp_direct_outcome_finite_execution[OF lpp_direct_arithmetic_outcome[OF name outcome] finite])

lemma lpp_term_test_finite_execution_outcome:
 assumes outcome: "lpp_test_builtin f ts result"
 and finite: "lpp_finite_goals gs"
 shows "lpp_finite_execution_outcome gs result"
 using outcome finite
 by (auto simp: lpp_test_builtin_def lpp_var_builtin_def split: if_splits)

lemma lpp_fresh_univ_finite_execution_outcome:
 assumes outcome: "lpp_univ_view_outcome names (LPIFun f ts)
   (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y]) result"
 and finite: "list_all lpp_finite_term ts"
 and distinct: "x\<noteq>y"
 and fresh: "x\<notin>set2_lp_iterm (LPIFun f ts)" "y\<notin>set2_lp_iterm (LPIFun f ts)"
 and goals: "lpp_finite_goals gs"
 shows "lpp_finite_execution_outcome gs result"
proof (cases result)
 case (LPPBuiltinSuccess mu)
 have decomposition: "lpp_univ_decompose_outcome names (LPIFun f ts)
   (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y]) (LPPBuiltinSuccess mu)"
   using outcome LPPBuiltinSuccess by simp
 show ?thesis using lpp_fresh_univ_finite_goals[OF decomposition finite distinct fresh goals]
   by (simp add: LPPBuiltinSuccess)
qed (use outcome in \<open>auto simp: lpp_univ_decompose_outcome_def\<close>)

lemma lpp_variable_univ_finite_execution_outcome:
 "lpp_univ_view_outcome names (LPIVar x) requested result \<Longrightarrow>
  lpp_finite_execution_outcome gs result"
 by simp


lemma lpp_fresh_clause_finite_execution_outcome:
 assumes checked: "lpp_check_fresh_univ_clause h bs x y z"
 and resolved: "lpc_mgu_resolve a gs h bs sigma rho"
 and finite: "lpp_finite_term (lp_isubst a sigma)"
 and outcome: "lpp_univ_view_outcome names (rho x)
   (LPIFun (LPCUser ''2:prolog_data_2e'') [rho y,rho z]) result"
 and goals: "lpp_finite_goals rest"
 shows "lpp_finite_execution_outcome rest result"
proof (cases "rho x")
 case (LPIVar v)
 then show ?thesis using outcome by simp
next
 case (LPIFun f ts)
 show ?thesis
 proof (cases result)
  case (LPPBuiltinSuccess mu)
  have decomposition: "lpp_univ_decompose_outcome names (rho x)
    (LPIFun (LPCUser ''2:prolog_data_2e'') [rho y,rho z]) (LPPBuiltinSuccess mu)"
    using outcome by (simp add: LPIFun LPPBuiltinSuccess)
  show ?thesis using lpp_fresh_univ_clause_finite_continuation[OF checked resolved finite LPIFun decomposition goals]
    by (simp add: LPPBuiltinSuccess)
 qed (use outcome LPIFun in \<open>auto simp: lpp_univ_decompose_outcome_def\<close>)
qed

ML \<open>
val checked = @{thms lpp_arithmetic_finite_execution_outcome lpp_term_test_finite_execution_outcome
 lpp_fresh_univ_finite_execution_outcome lpp_variable_univ_finite_execution_outcome
 lpp_fresh_clause_finite_execution_outcome};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite operation outcome" else ();
\<close>
end
