theory LP_Prolog_Finite_Execution_Builtin
 imports LP_Prolog_Finite_Execution_Step
begin

fun lpp_finite_execution_outcome where
 "lpp_finite_execution_outcome gs (LPPBuiltinSuccess sigma) =
   lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)"
| "lpp_finite_execution_outcome gs LPPBuiltinFailure = True"
| "lpp_finite_execution_outcome gs LPPBuiltinError = True"
| "lpp_finite_execution_outcome gs (LPPBuiltinProbe a keep) = lpp_finite_term a"
| "lpp_finite_execution_outcome gs (LPPBuiltinCall a) = lpp_finite_term a"
| "lpp_finite_execution_outcome gs (LPPBuiltinBranch cs ys ns) =
   (lpp_finite_goals cs \<and> lpp_finite_goals ys \<and> lpp_finite_goals ns)"
| "lpp_finite_execution_outcome gs (LPPBuiltinChoice left right) =
   (lpp_finite_goals left \<and> lpp_finite_goals right)"

lemma lpp_finite_extended_answer_step:
 assumes step: "lpp_answer_transition P B U ss event tt"
 and finite: "lpp_finite_execution ss"
 and base: "\<And>ev us. lpc_answer_transition P ss ev us \<Longrightarrow> lpp_finite_execution us"
 and builtins: "\<And>f ts gs eta es outcome.
   ss=(LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs),eta)#es \<Longrightarrow>
   U f ts outcome \<Longrightarrow> lpp_finite_execution_outcome gs outcome"
 shows "lpp_finite_execution tt"
 using step
proof (cases rule: lpp_answer_transition.cases)
 case base
 then show ?thesis using base assms(3) by blast
next
 case (success f ts sigma gs eta es)
 have local: "lpp_finite_execution_outcome gs (LPPBuiltinSuccess sigma)"
   by (rule builtins) (use success in auto)
 show ?thesis using finite local success
   by (auto simp: lpp_finite_execution_def lpp_finite_goals_def
     lp_cut_terms.simps list_all_iff lpp_probe_goals_def lpp_probe_else_def)
next
 case (probe f ts a keep m gs es n eta)
 have local: "lpp_finite_execution_outcome gs (LPPBuiltinProbe a keep)"
   by (rule builtins) (use probe in auto)
 show ?thesis using finite local probe
   by (auto simp: lpp_finite_execution_def lpp_finite_goals_def
     lp_cut_terms.simps list_all_iff lpp_probe_goals_def lpp_probe_else_def)
next
 case (call f ts a gs eta es)
 have local: "lpp_finite_execution_outcome gs (LPPBuiltinCall a)"
   by (rule builtins) (use call in auto)
 show ?thesis using finite local call
   by (auto simp: lpp_finite_execution_def lpp_finite_goals_def
     lp_cut_terms.simps list_all_iff lpp_probe_goals_def lpp_probe_else_def)
next
 case (branch f ts cs ys ns m gs es n eta)
 have local: "lpp_finite_execution_outcome gs (LPPBuiltinBranch cs ys ns)"
   by (rule builtins) (use branch in auto)
 show ?thesis using finite local branch
   by (auto simp: lpp_finite_execution_def lpp_finite_goals_def
     lp_cut_terms.simps list_all_iff lpp_probe_goals_def lpp_probe_else_def)
next
 case (choice f ts left right gs eta es)
 have local: "lpp_finite_execution_outcome gs (LPPBuiltinChoice left right)"
   by (rule builtins) (use choice in auto)
 show ?thesis using finite local choice
   by (auto simp: lpp_finite_execution_def lpp_finite_goals_def
     lp_cut_terms.simps list_all_iff lpp_probe_goals_def lpp_probe_else_def)
qed (use finite in \<open>auto simp: lpp_finite_execution_def\<close>)

lemma lpp_finite_domain_answer_step:
 assumes step: "lpp_domain_answers P B U D ss event tt"
 and finite: "lpp_finite_execution ss"
 and base: "\<And>ev us. lpc_answer_transition P ss ev us \<Longrightarrow> lpp_finite_execution us"
 and builtins: "\<And>f ts gs eta es outcome.
   ss=(LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs),eta)#es \<Longrightarrow>
   U f ts outcome \<Longrightarrow> lpp_finite_execution_outcome gs outcome"
 shows "lpp_finite_execution tt"
 using lpp_finite_extended_answer_step[OF _ finite base builtins] step finite
 by (auto simp: lpp_domain_answers_def)

ML \<open>
val checked = @{thms lpp_finite_extended_answer_step lpp_finite_domain_answer_step};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite builtin execution step" else ();
\<close>
end
