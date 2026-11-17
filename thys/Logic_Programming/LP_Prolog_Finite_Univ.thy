theory LP_Prolog_Finite_Univ
 imports LP_Prolog_Univ_Decomposition LP_Prolog_Finite_Scalar_Unify
begin

text \<open>Decomposition into fresh outputs has a finite comparison unifier.
The runtime support condition is essential: free output variables alone do not
exclude their occurrence inside the input. Most-generality then preserves the
whole active continuation, including variables not present in the equation.\<close>

lemma lpp_finite_term_subst_untouched:
 assumes finite: "lpp_finite_term t"
 and untouched: "\<And>x. x\<in>set2_lp_iterm t \<Longrightarrow> sigma x=LPIVar x"
 shows "lp_isubst t sigma=t"
 using finite untouched
 by (induction rule: lpp_finite_term.induct) (auto simp: list_all_iff intro!: map_idI)

lemma lpp_fresh_univ_finite_comparison:
 fixes names :: "string lp_cut_symbol \<Rightarrow> string lp_cut_symbol"
 assumes finite: "list_all lpp_finite_term ts"
 and distinct: "x\<noteq>y"
 and fresh: "x\<notin>set2_lp_iterm (LPIFun f ts)" "y\<notin>set2_lp_iterm (LPIFun f ts)"
 defines "comparison_substitution \<equiv> LPIVar(x := LPIFun (names f) [], y := lpp_argument_list ts)"
 shows "lp_isubst (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y]) comparison_substitution =
   lp_isubst (lpp_argument_list (LPIFun (names f) [] # ts)) comparison_substitution"
 and "\<And>z. lpp_finite_term (comparison_substitution z)"
proof -
 have children: "map (\<lambda>t. lp_isubst t comparison_substitution) ts=ts"
 proof (rule map_idI)
  fix t assume member: "t\<in>set ts"
  have fin: "lpp_finite_term t" using finite member by (simp add: list_all_iff)
  show "lp_isubst t comparison_substitution=t"
   by (rule lpp_finite_term_subst_untouched[OF fin])
    (use fresh member in \<open>auto simp: comparison_substitution_def\<close>)
 qed
 show "lp_isubst (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y]) comparison_substitution =
   lp_isubst (lpp_argument_list (LPIFun (names f) [] # ts)) comparison_substitution"
  using distinct children by (simp add: comparison_substitution_def lpp_argument_list_subst)
 show "lpp_finite_term (comparison_substitution z)" for z
  using finite by (simp add: comparison_substitution_def lpp_argument_list_finite)
qed

lemma lpp_fresh_univ_finite_goals:
 assumes outcome: "lpp_univ_decompose_outcome names (LPIFun f ts)
   (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y]) (LPPBuiltinSuccess mu)"
 and finite: "list_all lpp_finite_term ts"
 and distinct: "x\<noteq>y"
 and fresh: "x\<notin>set2_lp_iterm (LPIFun f ts)" "y\<notin>set2_lp_iterm (LPIFun f ts)"
 and goals: "lpp_finite_goals gs"
 shows "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_isubst t mu)) gs)"
proof -
 let ?comparison_substitution = "LPIVar(x := LPIFun (names f) [], y := lpp_argument_list ts)"
 have mgu: "lpc_mgu_unify
   (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y])
   (lpp_argument_list (LPIFun (names f) [] # ts)) gs mu"
  using outcome by (simp add: lpp_univ_decompose_outcome_def)
 have comparison: "lp_isubst (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y]) ?comparison_substitution =
   lp_isubst (lpp_argument_list (LPIFun (names f) [] # ts)) ?comparison_substitution"
  by (rule lpp_fresh_univ_finite_comparison(1)[OF finite distinct fresh])
 have images: "lpp_finite_term (?comparison_substitution z)" for z
  by (rule lpp_fresh_univ_finite_comparison(2)[OF finite distinct fresh])
 have old: "lpp_finite_term t" if "g\<in>set gs" "t\<in>set (lp_cut_terms g)" for g t
  using goals that by (auto simp: lpp_finite_goals_def list_all_iff)
 have after: "lpp_finite_term (lp_isubst t mu)"
  if "g\<in>set gs" "t\<in>set (lp_cut_terms g)" for g t
  by (rule lpp_mgu_unify_continuation_finite[OF mgu comparison _ that])
   (auto intro: lpp_finite_term_substitute[OF old images])
 show ?thesis using after
  by (auto simp: lpp_finite_goals_def lpp_finite_goal_map list_all_iff)
qed

lemma lpp_aliased_univ_freshness_rejected:
 "x\<in>set2_lp_iterm (LPIFun f [LPIVar x])"
 by simp

ML \<open>
val checked = [@{thm lpp_fresh_univ_finite_comparison(1)}, @{thm lpp_fresh_univ_finite_comparison(2)}, @{thm lpp_fresh_univ_finite_goals}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite univ dependency" else ();
\<close>
end
