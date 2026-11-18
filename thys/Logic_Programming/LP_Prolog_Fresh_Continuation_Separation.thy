theory LP_Prolog_Fresh_Continuation_Separation
 imports LP_Prolog_Finite_Fresh_Body LP_Prolog_Separated_Context_Structure
begin

text \<open>Fresh clause outputs are separated from finite live caller values,
including values absent from the selected atom. Both caller continuation and
clause body must be covered by the same actual resolution MGU.\<close>

lemma lpp_mgu_fresh_body_avoids_continuation_variable:
 fixes eta :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_resolve a (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) h bs sigma rho"
 and body: "g\<in>set bs" "t\<in>set (lp_cut_terms g)" "x\<in>vars_term t"
 and fresh: "x\<notin>vars_term h"
 and variable: "rho x=LPIVar y"
 and covered: "v\<in>(\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 and finite: "lpp_finite_term (lp_isubst (eta v) sigma)"
 shows "y\<notin>set2_lp_iterm (lp_isubst (eta v) sigma)"
proof
 assume occurs: "y\<in>set2_lp_iterm (lp_isubst (eta v) sigma)"
 let ?nu = "rho(x := LPIFun undefined [])"
 have head: "lp_ieval h ?nu=lp_ieval h rho"
  by (rule lp_ieval_cong) (use fresh in auto)
 have comparison: "lp_isubst a sigma=lp_ieval h ?nu"
  using mgu head by (simp add: lpc_mgu_resolve_def)
 obtain delta where caller:
   "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta))
      (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) =
    map (lp_cut_map (\<lambda>t. lp_isubst t sigma))
      (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
 and mapped: "map (lp_cut_map (\<lambda>u. lp_isubst (lp_ieval u rho) delta)) bs =
   map (lp_cut_map (\<lambda>u. lp_ieval u ?nu)) bs"
  using mgu comparison unfolding lpc_mgu_resolve_def by blast
 obtain cg ct where member: "cg\<in>set gs" "ct\<in>set (lp_cut_terms cg)" "v\<in>vars_term ct"
  using covered by blast
 have caller_goal: "lp_cut_map (\<lambda>t. lp_isubst (lp_isubst (lp_ieval t eta) sigma) delta) cg =
    lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma) cg"
  using caller member(1) by (simp add: map_map o_def lp_cut_map_comp map_eq_conv)
 have caller_term: "lp_isubst (lp_isubst (lp_ieval ct eta) sigma) delta = lp_isubst (lp_ieval ct eta) sigma"
  using caller_goal member(2) by (cases cg) auto
 have fixed: "lp_isubst (lp_isubst (eta v) sigma) delta=lp_isubst (eta v) sigma"
  using lpc_ieval_variables_eq[OF _ member(3)] caller_term by (simp add: lp_ieval_subst)
 have fixed_y: "delta y=LPIVar y"
  by (rule lpp_finite_subst_fixed_variable[OF finite fixed occurs])
 have goal_equal: "lp_cut_map (\<lambda>u. lp_isubst (lp_ieval u rho) delta) g =
   lp_cut_map (\<lambda>u. lp_ieval u ?nu) g"
  using mapped body(1) by (simp add: map_eq_conv)
 have term_equal: "lp_isubst (lp_ieval t rho) delta=lp_ieval t ?nu"
  using goal_equal body(2) by (cases g) auto
 have evaluated: "lp_ieval t (\<lambda>z. lp_isubst (rho z) delta)=lp_ieval t ?nu"
  using term_equal by (simp add: lp_ieval_subst)
 have image: "lp_isubst (rho x) delta=?nu x"
  using lpc_ieval_variables_eq[OF evaluated body(3)] by simp
 show False using image variable fixed_y by simp
qed

lemma lpp_mgu_body_only_separate_live_caller:
 fixes eta :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_resolve a (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) h bs sigma rho"
 and body_only: "x\<in>lpc_body_only_variables h bs"
 and covered: "v\<in>(\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 and finite: "lpp_finite_term (lp_isubst (eta v) sigma)"
 shows "set2_lp_iterm (rho x)\<inter>set2_lp_iterm (lp_isubst (eta v) sigma)={}"
proof -
 have free: "lpc_free_knowledge (lpc_body_only_variables h bs) rho"
  by (rule lpc_mgu_body_only_knowledge[OF mgu])
 obtain y where variable: "rho x=LPIVar y"
  using free body_only by (auto simp: lpc_free_knowledge_def)
 obtain g t where body: "g\<in>set bs" "t\<in>set (lp_cut_terms g)" "x\<in>vars_term t"
 and fresh: "x\<notin>vars_term h"
  using body_only by (auto simp: lpc_body_only_variables_def)
 have "y\<notin>set2_lp_iterm (lp_isubst (eta v) sigma)"
  by (rule lpp_mgu_fresh_body_avoids_continuation_variable[OF mgu body fresh variable covered finite])
 then show ?thesis by (simp add: variable)
qed


lemma lpp_matching_acquires_separation_and_leaf_invariant:
 fixes eta :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_resolve (lp_ieval call eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) h bs sigma rho"
 and matching: "lp_ieval h nu = lp_ieval call eta"
 and known: "lpp_runtime_leaf_effect A initial_structure (eta v)"
 and body_only: "x\<in>lpc_body_only_variables h bs"
 and covered: "v\<in>(\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 shows "lpp_runtime_leaf_effect A initial_structure (lp_isubst (eta v) sigma) \<and>
   set2_lp_iterm (rho x)\<inter>set2_lp_iterm (lp_isubst (eta v) sigma)={}"
proof -
 have live: "v\<in>vars_term call \<union>
   (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
  using covered by blast
 have preserved: "lpp_runtime_leaf_effect A initial_structure (lp_isubst (eta v) sigma)"
  by (rule lpp_runtime_leaf_effect_matching[OF known mgu matching live])
 have finite: "lpp_finite_term (lp_isubst (eta v) sigma)"
  by (rule lpp_runtime_leaf_effect_finite[OF preserved])
 have separated: "set2_lp_iterm (rho x)\<inter>set2_lp_iterm (lp_isubst (eta v) sigma)={}"
  by (rule lpp_mgu_body_only_separate_live_caller[OF mgu body_only covered finite])
 show ?thesis using preserved separated by blast
qed

ML \<open>
val checked = @{thms lpp_mgu_fresh_body_avoids_continuation_variable lpp_mgu_body_only_separate_live_caller
 lpp_matching_acquires_separation_and_leaf_invariant};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted fresh caller separation" else ();
\<close>
end
