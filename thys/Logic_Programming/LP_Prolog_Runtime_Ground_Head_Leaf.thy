theory LP_Prolog_Runtime_Ground_Head_Leaf
 imports LP_Prolog_Ground_Head_Leaf
begin

lemma lpp_finite_goal_templates:
 fixes gs :: "('f,'v) lp_iterm lp_cut_goal list"
 assumes finite: "lpp_finite_goals gs"
 shows "\<exists>qs. map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) qs=gs"
proof -
 define encode :: "('f,'v) lp_iterm \<Rightarrow> ('f,'v) term" where "encode t=(SOME u. t=lp_ieval u LPIVar)" for t
 have represented: "lp_ieval (encode t) LPIVar=t" if "lpp_finite_term t" for t
  unfolding encode_def using someI_ex[OF lpp_finite_runtime_template[OF that]] by simp
 have each: "lp_cut_map (\<lambda>t. lp_ieval t LPIVar) (lp_cut_map encode g)=g"
  if "g\<in>set gs" for g
  using finite that represented
  by (cases g) (auto simp: lpp_finite_goals_def list_all_iff)
 show ?thesis by (rule exI[of _ "map (lp_cut_map encode) gs"])
  (use each in \<open>simp add: map_map o_def map_idI\<close>)
qed

lemma lpp_evaluated_goals_runtime_support:
 "(\<Union>g\<in>set (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) qs).
     \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t) =
   (\<Union>g\<in>set qs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 by (simp add: lpp_finite_goal_map lpp_template_runtime_support)

lemma lpp_runtime_ground_head_bounded_images:
 assumes mgu: "lpc_mgu_resolve call gs h bs sigma rho"
 and finite_call: "lpp_finite_term call"
 and finite_rest: "lpp_finite_goals gs"
 and finite_head: "lpp_finite_term (lp_ieval h rho)"
 and ground_head: "lp_seg_ground (lp_ieval h rho)"
 and covered: "V \<subseteq> set2_lp_iterm call \<union>
   (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
 shows "lpp_bounded_images {u. vars_term u={}} sigma V"
proof -
 obtain c where call: "call=lp_ieval c LPIVar"
  using lpp_finite_runtime_template[OF finite_call] by blast
 obtain qs where rest: "map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) qs=gs"
  using lpp_finite_goal_templates[OF finite_rest] by blast
 have represented_mgu: "lpc_mgu_resolve (lp_ieval c LPIVar)
   (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) qs) h bs sigma rho"
  using mgu call rest by simp
 have support: "V \<subseteq> vars_term c \<union>
   (\<Union>g\<in>set qs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
  using covered unfolding call rest[symmetric]
  by (simp add: lpp_template_runtime_support lpp_evaluated_goals_runtime_support lpp_finite_goal_map)
 show ?thesis by (rule lpp_ground_instance_resolution_leaf_images[OF represented_mgu finite_head ground_head support])
qed

lemma lpp_runtime_ground_head_leaf_transport:
 assumes mgu: "lpc_mgu_resolve call gs h bs sigma rho"
 and finite_call: "lpp_finite_term call"
 and finite_rest: "lpp_finite_goals gs"
 and finite_head: "lpp_finite_term (lp_ieval h rho)"
 and ground_head: "lp_seg_ground (lp_ieval h rho)"
 and covered: "\<And>slot shape. (slot,shape)\<in>set specs \<Longrightarrow>
   set2_lp_iterm (eta slot) \<subseteq> set2_lp_iterm call \<union>
    (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
 shows "lpp_leaf_environment_transport {u. vars_term u={}} specs eta sigma"
proof (unfold lpp_leaf_environment_transport_def, intro ballI impI, clarify)
 fix slot shape
 assume member: "(slot,shape)\<in>set specs"
 and known: "lpp_runtime_leaf_effect {u. vars_term u={}} shape (eta slot)"
 show "lpp_runtime_leaf_effect {u. vars_term u={}} shape (lp_isubst (eta slot) sigma)"
  by (rule lpp_runtime_leaf_effect_substitute[OF known
    lpp_runtime_ground_head_bounded_images[OF mgu finite_call finite_rest finite_head ground_head covered[OF member]]]) simp
qed


lemma lpp_checked_anchored_leaf_transport:
 assumes checked: "lpp_check_anchored_head G actuals hs"
 and lengths: "length actuals=length hs"
 and known: "\<And>x. x\<in>set G \<Longrightarrow> lp_seg_ground (eta x)"
 and mgu: "lpc_mgu_resolve (LPIFun f (map (\<lambda>t. lp_ieval t eta) actuals))
   gs (Fun f hs) bs sigma rho"
 and finite: "list_all lpp_finite_term (map (\<lambda>t. lp_ieval t eta) actuals)"
 and continuation: "lpp_finite_goals gs"
 and covered: "\<And>slot shape. (slot,shape)\<in>set specs \<Longrightarrow>
   set2_lp_iterm (eta slot) \<subseteq>
    set2_lp_iterm (LPIFun f (map (\<lambda>t. lp_ieval t eta) actuals)) \<union>
     (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
 shows "lpp_leaf_environment_transport {u. vars_term u={}} specs eta sigma"
proof -
 have equation: "map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma) actuals=map (\<lambda>t. lp_ieval t rho) hs"
  using mgu by (simp add: lpc_mgu_resolve_def map_map o_def)
 have head_ground: "lp_seg_ground (lp_ieval (Fun f hs) rho)"
  by (rule lpp_checked_anchored_head_ground[OF checked lengths known equation])
 have head_finite: "lpp_finite_term (lp_ieval (Fun f hs) rho)"
  by (rule lpp_ground_finite_term[OF head_ground])
 have call_finite: "lpp_finite_term (LPIFun f (map (\<lambda>t. lp_ieval t eta) actuals))"
  using finite by simp
 show ?thesis by (rule lpp_runtime_ground_head_leaf_transport[OF mgu call_finite continuation head_finite head_ground covered])
qed

ML \<open>
val checked = @{thms lpp_finite_goal_templates lpp_evaluated_goals_runtime_support
 lpp_runtime_ground_head_bounded_images lpp_runtime_ground_head_leaf_transport lpp_checked_anchored_leaf_transport};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted runtime ground head transport" else ();
\<close>
end
