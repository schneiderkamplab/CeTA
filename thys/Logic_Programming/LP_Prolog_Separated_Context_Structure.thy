theory LP_Prolog_Separated_Context_Structure
 imports LP_Prolog_Separated_Pair_Structure LP_Prolog_Runtime_Leaf_Invariant
begin

text \<open>A fresh output binding may change the output's own observation,
while preserving an unrelated live continuation value. Separation is a fact
about runtime support. Answer-only coordinates outside the actual continuation
are not covered by most-generality and are deliberately excluded.\<close>

lemma lpp_unify_untouched_continuation_observation:
 fixes comparison :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_unify a b gs sigma"
 and unifies: "lp_isubst a comparison = lp_isubst b comparison"
 and member: "g\<in>set gs" "t\<in>set (lp_cut_terms g)"
 and untouched: "lp_isubst t comparison = t"
 and finite: "lpp_finite_term t"
 shows "\<exists>observed. lpp_runtime_structure t observed \<and>
   lpp_runtime_structure (lp_isubst t sigma) observed"
proof -
 obtain delta where factor:
   "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta)) gs =
    map (lp_cut_map (\<lambda>t. lp_isubst t comparison)) gs"
  using mgu unifies unfolding lpc_mgu_unify_def by blast
 have goal_equal: "lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta) g =
     lp_cut_map (\<lambda>t. lp_isubst t comparison) g"
  using factor member(1) by (simp add: map_eq_conv)
 have inverse: "lp_isubst (lp_isubst t sigma) delta = t"
  using goal_equal member(2) untouched by (cases g) auto
 show ?thesis by (rule lpp_finite_inverse_structural_observation[OF finite inverse])
qed

lemma lpp_separated_pair_continuation_observation:
 assumes mgu: "lpc_mgu_unify (LPIFun f [LPIVar x,LPIVar y]) (LPIFun f [a,b]) gs sigma"
 and finite: "lpp_finite_term a" "lpp_finite_term b" "lpp_finite_term t"
 and distinct: "x\<noteq>y"
 and fresh: "{x,y}\<inter>(set2_lp_iterm a\<union>set2_lp_iterm b)={}"
 and protected: "{x,y}\<inter>set2_lp_iterm t={}"
 and member: "g\<in>set gs" "t\<in>set (lp_cut_terms g)"
 shows "\<exists>observed. lpp_runtime_structure t observed \<and>
   lpp_runtime_structure (lp_isubst t sigma) observed"
proof -
 let ?comparison = "LPIVar(x := a,y := b)"
 have unchanged: "lp_isubst a ?comparison=a" "lp_isubst b ?comparison=b"
  by (rule lpp_finite_term_subst_untouched[OF finite(1)], use fresh in auto,
      rule lpp_finite_term_subst_untouched[OF finite(2)], use fresh in auto)
 have unifies: "lp_isubst (LPIFun f [LPIVar x,LPIVar y]) ?comparison =
   lp_isubst (LPIFun f [a,b]) ?comparison"
  using unchanged distinct by simp
 have untouched: "lp_isubst t ?comparison=t"
  by (rule lpp_finite_term_subst_untouched[OF finite(3)]) (use protected in auto)
 show ?thesis by (rule lpp_unify_untouched_continuation_observation[OF mgu unifies member untouched finite(3)])
qed

lemma lpp_runtime_leaf_effect_separated_pair:
 assumes known: "lpp_runtime_leaf_effect A initial_structure t"
 and mgu: "lpc_mgu_unify (LPIFun f [LPIVar x,LPIVar y]) (LPIFun f [a,b]) gs sigma"
 and finite: "lpp_finite_term a" "lpp_finite_term b"
 and distinct: "x\<noteq>y"
 and fresh: "{x,y}\<inter>(set2_lp_iterm a\<union>set2_lp_iterm b)={}"
 and protected: "{x,y}\<inter>set2_lp_iterm t={}"
 and member: "g\<in>set gs" "t\<in>set (lp_cut_terms g)"
 shows "lpp_runtime_leaf_effect A initial_structure (lp_isubst t sigma)"
proof -
 have finite_t: "lpp_finite_term t" by (rule lpp_runtime_leaf_effect_finite[OF known])
 obtain observed where before: "lpp_runtime_structure t observed"
 and after: "lpp_runtime_structure (lp_isubst t sigma) observed"
  using lpp_separated_pair_continuation_observation[OF mgu finite finite_t distinct fresh protected member] by blast
 show ?thesis by (rule lpp_runtime_leaf_effect_preserved_observation[OF known before after])
qed


lemma lpp_unify_untouched_context_variable:
 fixes eta comparison :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_unify a b (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma"
 and unifies: "lp_isubst a comparison = lp_isubst b comparison"
 and covered: "v\<in>(\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 and untouched: "lp_isubst (eta v) comparison = eta v"
 and finite: "lpp_finite_term (eta v)"
 shows "\<exists>observed. lpp_runtime_structure (eta v) observed \<and>
   lpp_runtime_structure (lp_isubst (eta v) sigma) observed"
proof -
 obtain g t where member: "g\<in>set gs" "t\<in>set (lp_cut_terms g)" "v\<in>vars_term t"
  using covered by blast
 obtain delta where factor:
   "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta))
      (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) =
    map (lp_cut_map (\<lambda>t. lp_isubst t comparison))
      (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
  using mgu unifies unfolding lpc_mgu_unify_def by blast
 have goal_equal: "lp_cut_map (\<lambda>t. lp_isubst (lp_isubst (lp_ieval t eta) sigma) delta) g =
     lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t eta) comparison) g"
  using factor member(1) by (simp add: map_map o_def lp_cut_map_comp map_eq_conv)
 have term_equal: "lp_isubst (lp_isubst (lp_ieval t eta) sigma) delta = lp_isubst (lp_ieval t eta) comparison"
  using goal_equal member(2) by (cases g) auto
 have variable_equal: "lp_isubst (lp_isubst (eta v) sigma) delta = lp_isubst (eta v) comparison"
  using lpc_ieval_variables_eq[OF _ member(3)] term_equal by (simp add: lp_ieval_subst)
 have inverse: "lp_isubst (lp_isubst (eta v) sigma) delta = eta v"
  using variable_equal untouched by simp
 show ?thesis by (rule lpp_finite_inverse_structural_observation[OF finite inverse])
qed

lemma lpp_runtime_leaf_effect_separated_pair_context:
 fixes eta :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes known: "lpp_runtime_leaf_effect A initial_structure (eta v)"
 and mgu: "lpc_mgu_unify (LPIFun f [LPIVar x,LPIVar y]) (LPIFun f [a,b])
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma"
 and finite: "lpp_finite_term a" "lpp_finite_term b"
 and distinct: "x\<noteq>y"
 and fresh: "{x,y}\<inter>(set2_lp_iterm a\<union>set2_lp_iterm b)={}"
 and protected: "{x,y}\<inter>set2_lp_iterm (eta v)={}"
 and covered: "v\<in>(\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 shows "lpp_runtime_leaf_effect A initial_structure (lp_isubst (eta v) sigma)"
proof -
 let ?comparison = "LPIVar(x := a,y := b)"
 have unchanged: "lp_isubst a ?comparison=a" "lp_isubst b ?comparison=b"
  by (rule lpp_finite_term_subst_untouched[OF finite(1)], use fresh in auto,
      rule lpp_finite_term_subst_untouched[OF finite(2)], use fresh in auto)
 have unifies: "lp_isubst (LPIFun f [LPIVar x,LPIVar y]) ?comparison =
   lp_isubst (LPIFun f [a,b]) ?comparison"
  using unchanged distinct by simp
 have finite_v: "lpp_finite_term (eta v)" by (rule lpp_runtime_leaf_effect_finite[OF known])
 have untouched: "lp_isubst (eta v) ?comparison=eta v"
  by (rule lpp_finite_term_subst_untouched[OF finite_v]) (use protected in auto)
 obtain observed where before: "lpp_runtime_structure (eta v) observed"
 and after: "lpp_runtime_structure (lp_isubst (eta v) sigma) observed"
  using lpp_unify_untouched_context_variable[OF mgu unifies covered untouched finite_v] by blast
 show ?thesis by (rule lpp_runtime_leaf_effect_preserved_observation[OF known before after])
qed


lemma lpp_pair_output_observation_changes:
 fixes x y :: string and a b f :: "'f"
 assumes distinct: "x\<noteq>y"
 defines "sigma \<equiv> LPIVar(x := LPIFun a [], y := LPIFun b [])"
 shows "lpc_mgu_unify (LPIFun f [LPIVar x,LPIVar y])
    (LPIFun f [LPIFun a [],LPIFun b []]) [LPCAtom (LPIVar x)] sigma \<and>
   \<not>(\<exists>observed. lpp_runtime_structure (LPIVar x) observed \<and>
    lpp_runtime_structure (lp_isubst (LPIVar x) sigma) observed)"
proof -
 have mgu: "lpc_mgu_unify (LPIFun f [LPIVar x,LPIVar y])
    (LPIFun f [LPIFun a [],LPIFun b []]) [LPCAtom (LPIVar x)] sigma"
  using distinct unfolding sigma_def lpc_mgu_unify_def by auto
 have before: "lpp_runtime_structure (LPIVar x) (Fun (Inr ()) [])"
  unfolding lpp_runtime_structure_def by (rule exI[of _ "Var x"]) simp
 have after: "lpp_runtime_structure (lp_isubst (LPIVar x) sigma) (Fun (Inl a) [])"
  unfolding lpp_runtime_structure_def by (rule exI[of _ "Fun a []"]) (use distinct in \<open>simp add: sigma_def\<close>)
 have different: "\<not>(\<exists>observed. lpp_runtime_structure (LPIVar x) observed \<and>
    lpp_runtime_structure (lp_isubst (LPIVar x) sigma) observed)"
  using lpp_runtime_structure_unique[OF before] lpp_runtime_structure_unique[OF after] by fastforce
 show ?thesis using mgu different by blast
qed

ML \<open>
val checked = @{thms lpp_unify_untouched_continuation_observation
 lpp_separated_pair_continuation_observation lpp_runtime_leaf_effect_separated_pair
 lpp_unify_untouched_context_variable lpp_runtime_leaf_effect_separated_pair_context lpp_pair_output_observation_changes};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted separated continuation observation" else ();
\<close>
end
