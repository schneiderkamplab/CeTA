theory LP_Prolog_Ground_Return_Leaf_Coverage
 imports LP_Prolog_Relational_Ground_Equality
begin

lemma lpp_ground_runtime_support:
 "lp_seg_ground t \<Longrightarrow> set2_lp_iterm t={}"
 by (induct rule: lp_seg_ground.induct) (auto simp: list_all_iff)

definition lpp_check_ground_relational_leaf_coverage where
 "lpp_check_ground_relational_leaf_coverage G facts slots payload call gs =
  (\<forall>slot\<in>set slots. slot < length payload \<and>
    vars_term (payload!slot) \<subseteq> lpp_functor_support_closure facts
     (G \<union> vars_term call \<union> (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)))"

lemma lpp_ground_relational_leaf_coverage_sound:
 assumes checked: "lpp_check_ground_relational_leaf_coverage G facts slots payload call gs"
 and facts: "list_all (lpp_functor_fact_holds names eta) facts"
 and ground: "\<And>x. x\<in>G \<Longrightarrow> lp_seg_ground (eta x)"
 and member: "slot\<in>set slots"
 shows "set2_lp_iterm (lpc_return_env payload eta slot) \<subseteq>
   set2_lp_iterm (lp_ieval call eta) \<union>
    (\<Union>g\<in>set (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs).
      \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
proof -
 let ?V = "G \<union> vars_term call \<union> (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 let ?S = "set2_lp_iterm (lp_ieval call eta) \<union>
    (\<Union>g\<in>set (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs).
      \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
 have initial: "set2_lp_iterm (eta x) \<subseteq> ?S" if "x\<in>?V" for x
  using that lpp_ground_runtime_support[OF ground]
  by (auto simp: lpp_evaluation_runtime_support lpp_finite_goal_map; blast)
 have covered: "set2_lp_iterm (eta x) \<subseteq> ?S"
  if "x\<in>lpp_functor_support_closure facts ?V" for x
  by (rule lpp_functor_support_closure_sound[OF facts initial that])
 show ?thesis using checked member covered
  by (auto simp: lpp_check_ground_relational_leaf_coverage_def lpc_return_env_def lpp_evaluation_runtime_support; blast)
qed

lemma lpp_ground_covered_equality_leaf_transport:
 assumes coverage: "lpp_check_ground_relational_leaf_coverage G facts (map fst specs) payload a gs"
 and facts: "list_all (lpp_functor_fact_holds names eta) facts"
 and ground_known: "\<And>x. x\<in>G \<Longrightarrow> lp_seg_ground (eta x)"
 and mgu: "lpc_mgu_unify (lp_ieval a eta) b
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma"
 and ground: "lp_seg_ground b"
 and finite_call: "lpp_finite_term (lp_ieval a eta)"
 and finite_rest: "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
 shows "lpp_leaf_environment_transport {u. vars_term u={}} specs
   (lpc_return_env payload eta) sigma"
proof (unfold lpp_leaf_environment_transport_def, intro ballI impI, clarify)
 fix slot shape
 assume member: "(slot,shape)\<in>set specs"
 and known: "lpp_runtime_leaf_effect {u. vars_term u={}} shape (lpc_return_env payload eta slot)"
 have support: "set2_lp_iterm (lpc_return_env payload eta slot) \<subseteq>
   set2_lp_iterm (lp_ieval a eta) \<union>
    (\<Union>g\<in>set (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs).
      \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
  by (rule lpp_ground_relational_leaf_coverage_sound[OF coverage facts ground_known]) (use member in auto)
 show "lpp_runtime_leaf_effect {u. vars_term u={}} shape
   (lp_isubst (lpc_return_env payload eta slot) sigma)"
  by (rule lpp_runtime_leaf_effect_substitute[OF known
    lpp_runtime_ground_equality_leaf_images[OF mgu ground finite_call finite_rest support]]) simp
qed

lemma lpp_ground_return_coverage_positive:
 "lpp_check_ground_relational_leaf_coverage {''known''} [] [0]
   [Var ''known''] (Var ''active'') []"
 by (simp add: lpp_check_ground_relational_leaf_coverage_def)

lemma lpp_ground_return_coverage_missing_knowledge:
 "\<not> lpp_check_ground_relational_leaf_coverage {} [] [0]
   [Var ''known''] (Var ''active'') []"
 by (simp add: lpp_check_ground_relational_leaf_coverage_def)

ML \<open>
val checked = @{thms lpp_ground_runtime_support lpp_ground_relational_leaf_coverage_sound
 lpp_ground_covered_equality_leaf_transport lpp_ground_return_coverage_positive
 lpp_ground_return_coverage_missing_knowledge};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted ground return coverage" else ();
\<close>
end
