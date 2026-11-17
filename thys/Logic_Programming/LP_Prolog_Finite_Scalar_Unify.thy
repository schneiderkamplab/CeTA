theory LP_Prolog_Finite_Scalar_Unify
 imports LP_Prolog_Finite_Goal_Transport
begin

lemma lpp_mgu_unify_continuation_finite:
 fixes tau :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_unify a b gs sigma"
   and comparison: "lp_isubst a tau=lp_isubst b tau"
   and finite: "\<And>g t. g\<in>set gs \<Longrightarrow> t\<in>set (lp_cut_terms g) \<Longrightarrow>
      lpp_finite_term (lp_isubst t tau)"
 shows "\<And>g t. g\<in>set gs \<Longrightarrow> t\<in>set (lp_cut_terms g) \<Longrightarrow>
      lpp_finite_term (lp_isubst t sigma)"
proof -
 fix g t assume member: "g\<in>set gs" "t\<in>set (lp_cut_terms g)"
 obtain delta where factor: "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta)) gs =
     map (lp_cut_map (\<lambda>t. lp_isubst t tau)) gs"
   using mgu comparison unfolding lpc_mgu_unify_def by blast
 have goal_equal: "lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta) g =
     lp_cut_map (\<lambda>t. lp_isubst t tau) g"
   using factor member(1) by (simp add: map_eq_conv)
 have equal: "lp_isubst (lp_isubst t sigma) delta=lp_isubst t tau"
   using goal_equal member(2) by (cases g) auto
 show "lpp_finite_term (lp_isubst t sigma)"
   by (rule lpp_finite_term_substitution_reflects[OF finite[OF member] equal[symmetric]])
qed

lemma lpp_scalar_mgu_finite_goals:
 assumes mgu: "lpc_mgu_unify a (LPIFun (LPCUser f) []) gs sigma"
   and finite: "lpp_finite_goals gs"
 shows "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)"
proof -
 have unifies: "lp_isubst a sigma=LPIFun (LPCUser f) []"
   using mgu by (simp add: lpc_mgu_unify_def)
 obtain mu where chosen: "lpp_scalar_unifier a f=Some mu"
   using unifies lpp_scalar_unifier_complete[of a f] by (cases "lpp_scalar_unifier a f") auto
 have comparison: "lp_isubst a mu=lp_isubst (LPIFun (LPCUser f) []) mu"
   using lpp_scalar_unifier_sound[OF chosen] by simp
 have old: "lpp_finite_term t" if "g\<in>set gs" "t\<in>set (lp_cut_terms g)" for g t
   using finite that by (auto simp: lpp_finite_goals_def list_all_iff)
 have mapped: "lpp_finite_term (lp_isubst t sigma)"
   if "g\<in>set gs" "t\<in>set (lp_cut_terms g)" for g t
   by (rule lpp_mgu_unify_continuation_finite[OF mgu comparison _ that])
      (auto intro: lpp_scalar_unifier_preserves_finite[OF chosen] old)
 show ?thesis using mapped
   by (auto simp: lpp_finite_goals_def lpp_finite_goal_map list_all_iff)
qed

ML \<open>
val checked = [@{thm lpp_scalar_mgu_finite_goals}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite scalar equality" else ();
\<close>
end
