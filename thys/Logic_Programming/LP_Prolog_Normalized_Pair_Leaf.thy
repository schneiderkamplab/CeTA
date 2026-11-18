theory LP_Prolog_Normalized_Pair_Leaf
 imports LP_Prolog_Fresh_Continuation_Separation
begin

lemma lpp_reflexive_pair_context_inverses:
 fixes eta :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes first: "lpc_mgu_unify input_term input_term
   (LPCUnify left right#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma"
 shows "\<exists>delta. lp_isubst (lp_isubst left sigma) delta=left \<and>
   lp_isubst (lp_isubst right sigma) delta=right \<and>
   (\<forall>v\<in>(\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t).
    lp_isubst (lp_isubst (eta v) sigma) delta=eta v)"
proof -
 obtain delta where factor:
   "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta))
     (LPCUnify left right#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) =
    map (lp_cut_map (\<lambda>t. lp_isubst t LPIVar))
     (LPCUnify left right#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
  using first unfolding lpc_mgu_unify_def by blast
 have pair: "lp_isubst (lp_isubst left sigma) delta=left"
   "lp_isubst (lp_isubst right sigma) delta=right"
  using factor by auto
 have caller: "lp_isubst (lp_isubst (eta v) sigma) delta=eta v"
  if covered: "v\<in>(\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)" for v
 proof -
  obtain g t where member: "g\<in>set gs" "t\<in>set (lp_cut_terms g)" "v\<in>vars_term t"
   using covered by blast
  have goal_equal: "lp_cut_map (\<lambda>t. lp_isubst (lp_isubst (lp_ieval t eta) sigma) delta) g =
     lp_cut_map (\<lambda>t. lp_ieval t eta) g"
   using factor member(1) by (simp add: map_map o_def lp_cut_map_comp map_eq_conv)
  have term_equal: "lp_isubst (lp_isubst (lp_ieval t eta) sigma) delta=lp_ieval t eta"
   using goal_equal member(2) by (cases g) auto
  show ?thesis using lpc_ieval_variables_eq[OF _ member(3)] term_equal by (simp add: lp_ieval_subst)
 qed
 show ?thesis by (rule exI[of _ delta]) (use pair caller in blast)
qed

lemma lpp_normalized_pair_preserves_caller_leaf:
 fixes eta tau :: "string \<Rightarrow> ('f,string) lp_iterm"
 and f :: 'f and x y :: string and a b left right :: "('f,string) lp_iterm"
 defines "left \<equiv> LPIFun f [LPIVar x,LPIVar y]"
 and "right \<equiv> LPIFun f [a,b]"
 assumes first: "lpc_mgu_unify input_term input_term
   (LPCUnify left right#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma"
 and second: "lpc_mgu_unify (lp_isubst left sigma) (lp_isubst right sigma)
   (map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma)) gs) tau"
 and known: "lpp_runtime_leaf_effect A initial_structure (eta v)"
 and finite: "lpp_finite_term a" "lpp_finite_term b"
 and distinct: "x\<noteq>y"
 and fresh: "{x,y}\<inter>(set2_lp_iterm a\<union>set2_lp_iterm b)={}"
 and protected: "{x,y}\<inter>set2_lp_iterm (eta v)={}"
 and covered: "v\<in>(\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 shows "lpp_runtime_leaf_effect A initial_structure (lp_isubst (lp_isubst (eta v) sigma) tau)"
proof -
 obtain delta where inverse_left: "lp_isubst (lp_isubst left sigma) delta=left"
 and inverse_right: "lp_isubst (lp_isubst right sigma) delta=right"
 and inverse_v: "lp_isubst (lp_isubst (eta v) sigma) delta=eta v"
  using lpp_reflexive_pair_context_inverses[OF first] covered by blast
 have finite_left: "lpp_finite_term left" by (simp add: left_def)
 have finite_right: "lpp_finite_term right" using finite by (simp add: right_def)
 have finite_v: "lpp_finite_term (eta v)" by (rule lpp_runtime_leaf_effect_finite[OF known])
 obtain n r where images: "sigma x=LPIVar n" "sigma y=LPIVar r"
 and inverse_images: "delta n=LPIVar x" "delta r=LPIVar y"
  using lpp_finite_inverse_variable[OF finite_left inverse_left, of x]
    lpp_finite_inverse_variable[OF finite_left inverse_left, of y]
  by (auto simp: left_def)
 have unequal: "n\<noteq>r" using inverse_images distinct by auto
 have separated_right: "set2_lp_iterm (lp_isubst left sigma)\<inter>set2_lp_iterm (lp_isubst right sigma)={}"
  by (rule lpp_finite_inverse_separation[OF finite_left finite_right inverse_left inverse_right])
    (use fresh in \<open>simp add: left_def right_def\<close>)
 have separated_v: "set2_lp_iterm (lp_isubst left sigma)\<inter>set2_lp_iterm (lp_isubst (eta v) sigma)={}"
  by (rule lpp_finite_inverse_separation[OF finite_left finite_v inverse_left inverse_v])
    (use protected in \<open>simp add: left_def\<close>)
 have finite_new_right: "lpp_finite_term (lp_isubst right sigma)"
  using lpp_finite_inverse_structural_observation[OF finite_right inverse_right]
    lpp_runtime_structure_finite by blast
 have fin: "lpp_finite_term (lp_isubst a sigma)" "lpp_finite_term (lp_isubst b sigma)"
  using finite_new_right by (simp_all add: right_def)
 obtain observed where before: "lpp_runtime_structure (eta v) observed"
 and after: "lpp_runtime_structure (lp_isubst (eta v) sigma) observed"
  using lpp_finite_inverse_structural_observation[OF finite_v inverse_v] by blast
 have preserved: "lpp_runtime_leaf_effect A initial_structure (lp_isubst (eta v) sigma)"
  by (rule lpp_runtime_leaf_effect_preserved_observation[OF known before after])
 show ?thesis
 proof (rule lpp_runtime_leaf_effect_separated_pair_context[where
   eta="\<lambda>z. lp_isubst (eta z) sigma" and x=n and y=r and
   a="lp_isubst a sigma" and b="lp_isubst b sigma" and f=f,
   OF preserved _ fin unequal _ _ covered])
  show "lpc_mgu_unify (LPIFun f [LPIVar n,LPIVar r])
    (LPIFun f [lp_isubst a sigma,lp_isubst b sigma])
    (map (lp_cut_map (\<lambda>t. lp_ieval t (\<lambda>z. lp_isubst (eta z) sigma))) gs) tau"
   using second images by (simp add: left_def right_def lp_ieval_subst)
  show "{n,r}\<inter>(set2_lp_iterm (lp_isubst a sigma)\<union>set2_lp_iterm (lp_isubst b sigma))={}"
   using separated_right images by (simp add: left_def right_def)
  show "{n,r}\<inter>set2_lp_iterm (lp_isubst (eta v) sigma)={}"
   using separated_v images by (simp add: left_def)
 qed
qed


lemma lpp_normalized_univ_preserves_caller_leaf:
 fixes eta tau :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes first: "lpc_mgu_unify (LPIFun f ts) (LPIFun f ts)
   (LPCUnify (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y])
     (lpp_argument_list (LPIFun (names f) []#ts))#
      map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma"
 and second: "lpc_mgu_unify
   (lp_isubst (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y]) sigma)
   (lp_isubst (lpp_argument_list (LPIFun (names f) []#ts)) sigma)
   (map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma)) gs) tau"
 and known: "lpp_runtime_leaf_effect A initial_structure (eta v)"
 and finite: "list_all lpp_finite_term ts"
 and distinct: "x\<noteq>y"
 and fresh: "x\<notin>set2_lp_iterm (LPIFun f ts)" "y\<notin>set2_lp_iterm (LPIFun f ts)"
 and protected: "{x,y}\<inter>set2_lp_iterm (eta v)={}"
 and covered: "v\<in>(\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 shows "lpp_runtime_leaf_effect A initial_structure (lp_isubst (lp_isubst (eta v) sigma) tau)"
proof (rule lpp_normalized_pair_preserves_caller_leaf[where
 f="LPCUser ''2:prolog_data_2e''" and x=x and y=y and
 a="LPIFun (names f) []" and b="lpp_argument_list ts" and input_term="LPIFun f ts" and eta=eta and v=v and gs=gs and sigma=sigma and tau=tau,
 OF _ _ known _ _ distinct _ protected covered])
 show "lpc_mgu_unify (LPIFun f ts) (LPIFun f ts)
   (LPCUnify (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y])
    (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIFun (names f) [],lpp_argument_list ts])#
     map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma"
  using first by simp
 show "lpc_mgu_unify
   (lp_isubst (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y]) sigma)
   (lp_isubst (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIFun (names f) [],lpp_argument_list ts]) sigma)
   (map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma)) gs) tau"
  using second by simp
 show "lpp_finite_term (LPIFun (names f) [])" by simp
 show "lpp_finite_term (lpp_argument_list ts)" using finite
  by (induct ts) auto
 show "{x,y}\<inter>(set2_lp_iterm (LPIFun (names f) [])\<union>set2_lp_iterm (lpp_argument_list ts))={}"
  using fresh by (auto simp: lpp_argument_list_support)
qed

ML \<open>
val checked = @{thms lpp_reflexive_pair_context_inverses lpp_normalized_pair_preserves_caller_leaf
 lpp_normalized_univ_preserves_caller_leaf};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted normalized pair caller transport" else ();
\<close>
end
