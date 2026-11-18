theory LP_Prolog_Return_Leaf_Coverage
 imports LP_Prolog_Runtime_Ground_Head_Leaf LP_Cut_Return_State
begin

text \<open>Return slots index evaluated payload terms, not source variables.
Coverage is checked against the actual selected call and active continuation.
Saved frames and absent caller goals cannot supply this coverage.\<close>

definition lpp_check_return_leaf_coverage where
 "lpp_check_return_leaf_coverage slots payload call gs =
  (\<forall>slot\<in>set slots. slot < length payload \<and>
    vars_term (payload!slot) \<subseteq> vars_term call \<union>
      (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t))"

lemma lpp_evaluation_runtime_support:
 "set2_lp_iterm (lp_ieval t eta) = (\<Union>x\<in>vars_term t. set2_lp_iterm (eta x))"
 by (induct t) auto

lemma lpp_return_leaf_coverage_sound:
 assumes checked: "lpp_check_return_leaf_coverage slots payload call gs"
 and member: "slot\<in>set slots"
 shows "set2_lp_iterm (lpc_return_env payload eta slot) \<subseteq>
   set2_lp_iterm (lp_ieval call eta) \<union>
    (\<Union>g\<in>set (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs).
      \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
 using checked member
 by (auto simp: lpp_check_return_leaf_coverage_def lpc_return_env_def
   lpp_evaluation_runtime_support lpp_finite_goal_map; blast)

lemma lpp_return_ground_head_leaf_transport:
 assumes checked: "lpp_check_return_leaf_coverage (map fst specs) payload call gs"
 and mgu: "lpc_mgu_resolve (lp_ieval call eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) h bs sigma rho"
 and finite_call: "lpp_finite_term (lp_ieval call eta)"
 and finite_rest: "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
 and ground_head: "lp_seg_ground (lp_ieval h rho)"
 shows "lpp_leaf_environment_transport {u. vars_term u={}} specs
   (lpc_return_env payload eta) sigma"
 by (rule lpp_runtime_ground_head_leaf_transport[OF mgu finite_call finite_rest
   lpp_ground_finite_term[OF ground_head] ground_head])
   (use lpp_return_leaf_coverage_sound[OF checked] in fastforce)


lemma lpp_return_anchored_head_leaf_transport:
 assumes coverage: "lpp_check_return_leaf_coverage (map fst specs) payload (Fun f actuals) gs"
 and checked: "lpp_check_anchored_head G actuals hs"
 and lengths: "length actuals=length hs"
 and known: "\<And>x. x\<in>set G \<Longrightarrow> lp_seg_ground (eta x)"
 and mgu: "lpc_mgu_resolve (lp_ieval (Fun f actuals) eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) (Fun f hs) bs sigma rho"
 and finite_call: "lpp_finite_term (lp_ieval (Fun f actuals) eta)"
 and finite_rest: "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
 shows "lpp_leaf_environment_transport {u. vars_term u={}} specs
   (lpc_return_env payload eta) sigma"
proof -
 have equation: "map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma) actuals =
   map (\<lambda>t. lp_ieval t rho) hs"
  using mgu by (simp add: lpc_mgu_resolve_def map_map o_def)
 have ground: "lp_seg_ground (lp_ieval (Fun f hs) rho)"
  by (rule lpp_checked_anchored_head_ground[OF checked lengths known equation])
 show ?thesis by (rule lpp_return_ground_head_leaf_transport[OF coverage mgu finite_call finite_rest ground])
qed

lemma lpp_return_anchored_leaf_base_step:
 assumes step: "lpc_answer_transition P
   (lpc_return_eval eta ((LPCClause (LPCAtom (Fun f actuals)#gs) c m,payload)#saved)) event tt"
 and invariant: "lpp_leaf_stack_invariant {u. vars_term u={}} specs
   (lpc_return_eval eta ((LPCClause (LPCAtom (Fun f actuals)#gs) c m,payload)#saved))"
 and coverage: "lpp_check_return_leaf_coverage (map fst specs) payload (Fun f actuals) gs"
 and checked: "lpp_check_anchored_head G actuals hs"
 and head: "fst (P!c)=Fun f hs"
 and lengths: "length actuals=length hs"
 and known: "\<And>x. x\<in>set G \<Longrightarrow> lp_seg_ground (eta x)"
 and finite_call: "lpp_finite_term (lp_ieval (Fun f actuals) eta)"
 and finite_rest: "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
 shows "lpp_leaf_stack_invariant {u. vars_term u={}} specs tt"
proof (rule lpp_leaf_stack_base_step[OF step invariant])
 fix a qs d n ret es sigma rho
 assume shape: "lpc_return_eval eta ((LPCClause (LPCAtom (Fun f actuals)#gs) c m,payload)#saved) =
   (LPCClause (LPCAtom a#qs) d n,ret)#es"
 and bound: "d<length P"
 and mgu: "lpc_mgu_resolve a qs (fst (P!d)) (snd (P!d)) sigma rho"
 have actual_mgu: "lpc_mgu_resolve (lp_ieval (Fun f actuals) eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) (Fun f hs) (snd (P!c)) sigma rho"
  using mgu shape head by (auto simp: lpc_return_eval_def)
 have ret: "ret=lpc_return_env payload eta"
  using shape by (simp add: lpc_return_eval_def)
 show "lpp_leaf_environment_transport {u. vars_term u={}} specs ret sigma"
  unfolding ret by (rule lpp_return_anchored_head_leaf_transport[OF coverage checked lengths known actual_mgu finite_call finite_rest])
qed (auto simp: lpc_return_eval_def)

lemma lpp_return_leaf_coverage_missing_slot:
 "slot \<ge> length payload \<Longrightarrow>
  \<not> lpp_check_return_leaf_coverage [slot] payload call gs"
 by (simp add: lpp_check_return_leaf_coverage_def)

lemma lpp_return_leaf_coverage_absent_caller:
 "x\<noteq>y \<Longrightarrow>
  \<not> lpp_check_return_leaf_coverage [0] [Var y] (Var x) []"
 by (simp add: lpp_check_return_leaf_coverage_def)

ML \<open>
val checked = @{thms lpp_evaluation_runtime_support lpp_return_leaf_coverage_sound
 lpp_return_ground_head_leaf_transport lpp_return_anchored_head_leaf_transport
 lpp_return_anchored_leaf_base_step lpp_return_leaf_coverage_missing_slot
 lpp_return_leaf_coverage_absent_caller};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted return leaf coverage" else ();
\<close>
end
