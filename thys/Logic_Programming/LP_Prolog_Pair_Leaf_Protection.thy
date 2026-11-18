theory LP_Prolog_Pair_Leaf_Protection
 imports LP_Prolog_Pair_Leaf_Images LP_Prolog_Separation_Pair_Control
begin

fun lpp_separated_support_seeds where
 "lpp_separated_support_seeds left [] = {}"
| "lpp_separated_support_seeds left (LPPSeparate a b#facts) =
   (if left=a then vars_term b else {}) \<union>
   (if left=b then vars_term a else {}) \<union> lpp_separated_support_seeds left facts"

lemma lpp_separated_support_seeds_sound:
 assumes held: "list_all (lpp_separation_holds eta) facts"
 and member: "x\<in>lpp_separated_support_seeds left facts"
 shows "set2_lp_iterm (eta x) \<subseteq> - set2_lp_iterm (lp_ieval left eta)"
 using held member
proof (induct facts)
 case Nil then show ?case by simp
next
 case (Cons fact facts)
 then show ?case by (cases fact)
  (auto simp: lpp_evaluation_runtime_support split: if_splits; blast)
qed

definition lpp_check_leaf_pair_protection where
 "lpp_check_leaf_pair_protection G functors separation left slots payload =
  (\<forall>slot\<in>set slots. slot<length payload \<and>
   vars_term (payload!slot) \<subseteq> lpp_functor_support_closure functors
    (G \<union> lpp_separated_support_seeds left separation))"

lemma lpp_leaf_pair_protection_sound:
 assumes checked: "lpp_check_leaf_pair_protection G functors separation left slots payload"
 and functors: "list_all (lpp_functor_fact_holds names eta) functors"
 and separation: "list_all (lpp_separation_holds eta) separation"
 and ground: "\<And>x. x\<in>G \<Longrightarrow> lp_seg_ground (eta x)"
 and member: "slot\<in>set slots"
 shows "set2_lp_iterm (lpc_return_env payload eta slot) \<inter>
   set2_lp_iterm (lp_ieval left eta) = {}"
proof -
 let ?V = "G \<union> lpp_separated_support_seeds left separation"
 let ?S = "- set2_lp_iterm (lp_ieval left eta)"
 have initial: "set2_lp_iterm (eta x) \<subseteq> ?S" if "x\<in>?V" for x
  using that lpp_ground_runtime_support[OF ground]
    lpp_separated_support_seeds_sound[OF separation] by blast
 have closed: "set2_lp_iterm (eta x) \<subseteq> ?S"
  if "x\<in>lpp_functor_support_closure functors ?V" for x
  by (rule lpp_functor_support_closure_sound[OF functors initial that])
 show ?thesis using checked member closed
  by (auto simp: lpp_check_leaf_pair_protection_def lpc_return_env_def lpp_evaluation_runtime_support; blast)
qed

lemma lpp_checked_pair_leaf_transport:
 assumes pair: "lpp_check_separated_pair F separation a b"
 and free: "lpc_free_knowledge (set F) eta"
 and separation: "list_all (lpp_separation_holds eta) separation"
 and coverage: "lpp_check_ground_relational_leaf_coverage G functors (map fst specs) payload b gs"
 and protection: "lpp_check_leaf_pair_protection G functors separation a (map fst specs) payload"
 and functors: "list_all (lpp_functor_fact_holds names eta) functors"
 and ground: "\<And>x. x\<in>G \<Longrightarrow> lp_seg_ground (eta x)"
 and mgu: "lpc_mgu_unify (lp_ieval a eta) (lp_ieval b eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma"
 and finite_rhs: "lpp_finite_term (lp_ieval b eta)"
 and finite_rest: "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
 shows "lpp_leaf_environment_transport {u. vars_term u={}} specs (lpc_return_env payload eta) sigma"
proof -
 obtain f x y c d where shape: "a=Fun f [Var x,Var y]" "b=Fun f [c,d]"
  and distinct: "x\<noteq>y" and members: "x\<in>set F" "y\<in>set F"
  and fact: "LPPSeparate a b\<in>set separation"
  using pair by (induction F separation a b rule: lpp_check_separated_pair.induct) auto
 obtain u v where images: "eta x=LPIVar u" "eta y=LPIVar v"
  using free members unfolding lpc_free_knowledge_def by blast
 have unequal: "u\<noteq>v"
  using free members distinct images by (auto simp: lpc_free_knowledge_def inj_on_def)
 have fresh: "{u,v}\<inter>(set2_lp_iterm (lp_ieval c eta)\<union>set2_lp_iterm (lp_ieval d eta))={}"
  using separation fact by (auto simp: list_all_iff shape images)
 have actual_mgu: "lpc_mgu_unify (LPIFun f [LPIVar u,LPIVar v])
   (LPIFun f [lp_ieval c eta,lp_ieval d eta])
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma"
  using mgu by (simp add: shape images)
 have fin: "lpp_finite_term (lp_ieval c eta)" "lpp_finite_term (lp_ieval d eta)"
  using finite_rhs by (simp_all add: shape)
 show ?thesis
 proof (unfold lpp_leaf_environment_transport_def, intro ballI impI, clarify)
  fix slot initial
  assume member: "(slot,initial)\<in>set specs"
  and known: "lpp_runtime_leaf_effect {u. vars_term u={}} initial (lpc_return_env payload eta slot)"
  have slot: "slot\<in>set (map fst specs)" using member by force
  have protected: "set2_lp_iterm (lpc_return_env payload eta slot)\<inter>{u,v}={}"
   using lpp_leaf_pair_protection_sound[OF protection functors separation ground slot]
   by (simp add: shape images)
  have covered: "set2_lp_iterm (lpc_return_env payload eta slot) \<subseteq>
   set2_lp_iterm (LPIFun f [lp_ieval c eta,lp_ieval d eta]) \<union>
    (\<Union>g\<in>set (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs).
      \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
   using lpp_ground_relational_leaf_coverage_sound[OF coverage functors ground slot]
   by (simp add: shape)
  show "lpp_runtime_leaf_effect {u. vars_term u={}} initial
    (lp_isubst (lpc_return_env payload eta slot) sigma)"
   by (rule lpp_runtime_leaf_effect_substitute[OF known
     lpp_pair_protected_leaf_images[OF actual_mgu fin finite_rest unequal fresh protected covered]]) simp
 qed
qed

lemma lpp_pair_leaf_relational_positive:
 "lpp_check_leaf_pair_protection {}
   [LPPFunctorFact (Var ''whole'') (Var ''name'') (Var ''children'')]
   [LPPSeparate (Fun f [Var ''x'',Var ''y'']) (Fun f [Var ''name'',Var ''children''])]
   (Fun f [Var ''x'',Var ''y'']) [0] [Var ''whole'']"
 by (simp add: lpp_check_leaf_pair_protection_def)

lemma lpp_pair_leaf_missing_separation_rejected:
 "\<not> lpp_check_leaf_pair_protection {}
   [LPPFunctorFact (Var ''whole'') (Var ''name'') (Var ''children'')] []
   (Fun f [Var ''x'',Var ''y'']) [0] [Var ''whole'']"
 by (simp add: lpp_check_leaf_pair_protection_def)

lemma lpp_pair_leaf_bound_output_rejected:
 "\<not> lpp_check_leaf_pair_protection {}
   [LPPFunctorFact (Var ''whole'') (Var ''name'') (Var ''children'')]
   [LPPSeparate (Fun f [Var ''x'',Var ''y'']) (Fun f [Var ''name'',Var ''children''])]
   (Fun f [Var ''x'',Var ''y'']) [0] [Var ''x'']"
 by (simp add: lpp_check_leaf_pair_protection_def)

ML \<open>
val checked = @{thms lpp_separated_support_seeds_sound lpp_leaf_pair_protection_sound lpp_checked_pair_leaf_transport
 lpp_pair_leaf_relational_positive lpp_pair_leaf_missing_separation_rejected lpp_pair_leaf_bound_output_rejected};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted checked pair leaf protection" else ();
\<close>
end
