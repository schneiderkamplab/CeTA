theory LP_Prolog_Finite_Term_Transport
 imports LP_Prolog_Finite_Is LP_Cut_Factored_Head_Resolution
begin

text \<open>Finiteness is weaker than groundness and is not preserved by an
arbitrary rational substitution. These lemmas require explicit finite images;
none turns an unconstrained query mode into freeness or groundness.\<close>

lemma lpp_finite_term_substitute:
 assumes finite: "lpp_finite_term t"
   and images: "\<And>x. lpp_finite_term (sigma x)"
 shows "lpp_finite_term (lp_isubst t sigma)"
 using finite by (induct rule: lpp_finite_term.induct)
   (auto simp: list_all_iff images intro: lpp_finite_term.intros)

lemma lpp_finite_term_substitution_reflects:
 assumes finite: "lpp_finite_term u"
 shows "\<And>t sigma. u=lp_isubst t sigma \<Longrightarrow> lpp_finite_term t"
 using finite
proof (induct rule: lpp_finite_term.induct)
 case (variable x)
 then show ?case by (cases t) auto
next
 case (node ts f)
 show ?case
 proof (cases t)
  case (LPIVar x)
  then show ?thesis by simp
 next
  case (LPIFun g args)
  have shape: "f=g" "ts=map (\<lambda>t. lp_isubst t sigma) args"
   using node.prems LPIFun by simp_all
  have "list_all lpp_finite_term args"
   using node.hyps shape by (auto simp: list_all_iff)
  then show ?thesis using LPIFun by simp
 qed
qed

lemma lpp_finite_term_initial:
 "lpp_finite_term (lp_ieval t LPIVar)"
 by (rule lpp_finite_term_eval) simp

lemma lpp_scalar_unifier_preserves_finite:
 assumes chosen: "lpp_scalar_unifier a f=Some mu"
 shows "lpp_finite_term t \<Longrightarrow> lpp_finite_term (lp_isubst t mu)"
proof -
 assume finite: "lpp_finite_term t"
 have images: "lpp_finite_term (mu x)" for x
   using chosen by (cases a) (auto split: if_splits)
 show ?thesis by (rule lpp_finite_term_substitute[OF finite images])
qed

lemma lpp_mgu_body_variable_finite:
 fixes a :: "('f,string) lp_iterm"
   and tau nu :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_resolve a gs h bs sigma rho"
   and comparison: "lp_isubst a tau=lp_ieval h nu"
   and member: "g\<in>set bs" "t\<in>set (lp_cut_terms g)" "x\<in>vars_term t"
   and finite: "lpp_finite_term (nu x)"
 shows "lpp_finite_term (rho x)"
proof -
 obtain delta where factor: "lp_isubst (rho x) delta=nu x"
   using lpc_mgu_body_factor[OF mgu comparison] member by blast
 show ?thesis by (rule lpp_finite_term_substitution_reflects[OF finite factor[symmetric]])
qed

lemma lpp_finite_goal_map:
 "lp_cut_terms (lp_cut_map f g)=map f (lp_cut_terms g)"
 by (cases g) auto

lemma lpp_mgu_continuation_finite:
 fixes a :: "('f,string) lp_iterm"
   and tau nu :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_resolve a gs h bs sigma rho"
   and comparison: "lp_isubst a tau=lp_ieval h nu"
   and finite: "\<And>g t. g\<in>set gs \<Longrightarrow> t\<in>set (lp_cut_terms g) \<Longrightarrow>
      lpp_finite_term (lp_isubst t tau)"
 shows "\<And>g t. g\<in>set gs \<Longrightarrow> t\<in>set (lp_cut_terms g) \<Longrightarrow>
      lpp_finite_term (lp_isubst t sigma)"
proof -
 fix g t assume member: "g\<in>set gs" "t\<in>set (lp_cut_terms g)"
 obtain delta where factor: "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta)) gs =
     map (lp_cut_map (\<lambda>t. lp_isubst t tau)) gs"
   using mgu comparison unfolding lpc_mgu_resolve_def by blast
 have goal_equal: "lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta) g =
     lp_cut_map (\<lambda>t. lp_isubst t tau) g"
   using factor member(1) by (simp add: map_eq_conv)
 have equal: "lp_isubst (lp_isubst t sigma) delta=lp_isubst t tau"
   using goal_equal member(2) by (cases g) auto
 show "lpp_finite_term (lp_isubst t sigma)"
   by (rule lpp_finite_term_substitution_reflects[OF finite[OF member] equal[symmetric]])
qed

ML \<open>
val checked = [@{thm lpp_finite_term_substitute},
 @{thm lpp_finite_term_substitution_reflects}, @{thm lpp_finite_term_initial},
 @{thm lpp_scalar_unifier_preserves_finite}, @{thm lpp_mgu_body_variable_finite},
 @{thm lpp_mgu_continuation_finite}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite-term transport" else ();
\<close>
end
