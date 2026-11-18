theory LP_Prolog_Pair_Leaf_Images
 imports LP_Prolog_Relational_Reflexive_Leaf
begin

lemma lpp_finite_substitution_factor_variable:
 fixes sigma delta comparison :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes finite: "lpp_finite_term t"
 and factor: "lp_isubst (lp_isubst t sigma) delta=lp_isubst t comparison"
 and member: "z\<in>set2_lp_iterm t"
 shows "lp_isubst (sigma z) delta=comparison z"
proof -
 obtain u where represented: "t=lp_ieval u LPIVar"
  using lpp_finite_runtime_template[OF finite] by blast
 have equation: "lp_ieval u (\<lambda>x. lp_isubst (sigma x) delta)=lp_ieval u comparison"
  using factor by (simp add: represented lp_ieval_subst)
 have occurs: "z\<in>vars_term u" using member by (simp add: represented lpp_template_runtime_support)
 show ?thesis by (rule lpc_ieval_variables_eq[OF equation occurs])
qed

lemma lpp_pair_protected_leaf_images:
 assumes mgu: "lpc_mgu_unify (LPIFun f [LPIVar x,LPIVar y]) (LPIFun f [a,b]) gs sigma"
 and finite: "lpp_finite_term a" "lpp_finite_term b"
 and finite_rest: "lpp_finite_goals gs"
 and distinct: "x\<noteq>y"
 and fresh: "{x,y}\<inter>(set2_lp_iterm a\<union>set2_lp_iterm b)={}"
 and protected: "V\<inter>{x,y}={}"
 and covered: "V \<subseteq> set2_lp_iterm (LPIFun f [a,b]) \<union>
   (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
 shows "lpp_bounded_images A sigma V"
proof -
 let ?comparison = "LPIVar(x := a,y := b)"
 have unchanged: "lp_isubst a ?comparison=a" "lp_isubst b ?comparison=b"
  by (rule lpp_finite_term_subst_untouched[OF finite(1)], use fresh in auto,
      rule lpp_finite_term_subst_untouched[OF finite(2)], use fresh in auto)
 have comparison: "lp_isubst (LPIFun f [LPIVar x,LPIVar y]) ?comparison =
   lp_isubst (LPIFun f [a,b]) ?comparison"
  using unchanged distinct by simp
 obtain delta where one: "lp_isubst (lp_isubst (LPIFun f [LPIVar x,LPIVar y]) sigma) delta =
   lp_isubst (LPIFun f [LPIVar x,LPIVar y]) ?comparison"
 and rest: "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta)) gs =
   map (lp_cut_map (\<lambda>t. lp_isubst t ?comparison)) gs"
  using mgu comparison unfolding lpc_mgu_unify_def by blast
 have unifies: "lp_isubst (LPIFun f [LPIVar x,LPIVar y]) sigma=lp_isubst (LPIFun f [a,b]) sigma"
  using mgu by (simp add: lpc_mgu_unify_def)
 have rhs_factor: "lp_isubst (lp_isubst (LPIFun f [a,b]) sigma) delta =
   lp_isubst (LPIFun f [a,b]) ?comparison"
  using one unifies comparison by metis
 have inverse: "lp_isubst (sigma z) delta=LPIVar z" if member: "z\<in>V" for z
 proof -
  have outside: "z\<noteq>x" "z\<noteq>y" using protected member by auto
  have factor_z: "lp_isubst (sigma z) delta=?comparison z"
  proof (cases "z\<in>set2_lp_iterm (LPIFun f [a,b])")
   case True
   have finite_pair: "lpp_finite_term (LPIFun f [a,b])" using finite by simp
   show ?thesis by (rule lpp_finite_substitution_factor_variable[OF finite_pair rhs_factor True])
  next
   case False
   obtain g t where occurs: "g\<in>set gs" "t\<in>set (lp_cut_terms g)" "z\<in>set2_lp_iterm t"
    using member covered False by blast
   have goal: "lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta) g =
     lp_cut_map (\<lambda>t. lp_isubst t ?comparison) g"
    using rest occurs(1) by (simp add: map_eq_conv)
   have term_factor: "lp_isubst (lp_isubst t sigma) delta=lp_isubst t ?comparison"
    using goal occurs(2) by (cases g) auto
   have finite_t: "lpp_finite_term t"
    using finite_rest occurs(1,2) by (auto simp: lpp_finite_goals_def list_all_iff)
   show ?thesis by (rule lpp_finite_substitution_factor_variable[OF finite_t term_factor occurs(3)])
  qed
  show ?thesis using factor_z outside by simp
 qed
 show ?thesis unfolding lpp_bounded_images_def
  using lpc_isubst_variable_reflect[OF inverse] by blast
qed

ML \<open>
val checked = @{thms lpp_finite_substitution_factor_variable lpp_pair_protected_leaf_images};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted pair leaf images" else ();
\<close>
end
