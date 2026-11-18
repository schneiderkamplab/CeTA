theory LP_Prolog_Checked_Head_Return_Effect
 imports LP_Prolog_Attached_Resolution_Leaf
begin

text \<open>The existing head witness supplies the effect of an actual successful
resolution with any continuation, including an attached caller. The caller and
source environments need not have the same coordinate type.\<close>

lemma lpp_checked_head_actual_return_effect:
 fixes SP :: "string lpp_success_clause list"
 assumes checked: "lpp_check_separation_head P nd ctx a c witness"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and observed: "lpp_stable_context_holds operation SP ctx eta"
 and mgu: "lpc_mgu_resolve (lp_ieval a eta) pending_goals (fst (P!c)) (snd (P!c)) sigma rho"
 shows "(\<exists>nu. lp_ieval (fst (P!c)) nu=lp_ieval a eta) \<or> lp_seg_ground (lp_ieval (fst (P!c)) rho)"
proof (cases witness)
 case (LPPSMatching bindings)
 have matching: "lp_cut_check_match a (fst (P!c)) bindings" using checked LPPSMatching by simp
 have exact: "lp_ieval (fst (P!c)) (\<lambda>x. lp_ieval (lp_cut_match_subst bindings x) eta)=lp_ieval a eta"
  using matching unfolding lp_cut_check_match_def by (simp add: lp_ieval_finite_subst[symmetric])
 show ?thesis using exact by blast
next
 case (LPPSAnchored f actuals hs G)
 have call: "a=Fun f actuals" and head: "fst (P!c)=Fun f hs"
 and lengths: "length actuals=length hs" and anchored: "lpp_check_anchored_head G actuals hs"
 and ground: "set G\<subseteq> set (lpcn_ground nd)\<union> lpp_source_context_ground ctx"
  using checked LPPSAnchored by auto
 have runtime_ground: "lp_seg_ground (eta x)" if "x\<in>set G" for x
  using ground known lpp_stable_context_ground_sound[OF observed] that
  by (auto simp: lp_cut_knowledge_def)
 have equation: "map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma) actuals=map (\<lambda>t. lp_ieval t rho) hs"
  using mgu by (auto simp: call head lpc_mgu_resolve_def o_def)
 have result: "lp_seg_ground (lp_ieval (Fun f hs) rho)"
  by (rule lpp_checked_anchored_head_ground[OF anchored lengths runtime_ground equation])
 show ?thesis using result by (simp add: head)
next
 case (LPPSSpine f arg actuals x y H)
 have call: "a=Fun f (arg#actuals)"
 and head: "fst (P!c)=Fun f (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y]#map Var H)"
 and distinct: "distinct (x#y#H)" and lengths: "length H=length actuals"
 and spine: "LPPOShape lpp_spine_grammar (LPReturnShape 0) arg\<in>set (snd (snd ctx))"
  using checked LPPSSpine by auto
 have observed_shape: "lp_return_shape_holds lpp_spine_grammar (LPReturnShape 0) (lp_ieval arg eta)"
  using spine observed by (cases ctx)
   (auto simp: lpp_stable_context_holds_def lpp_evaluation_context_holds_def list_all_iff)
 obtain n where runtime_spine: "lpp_list_length (lp_ieval arg eta) n"
  using lpp_return_shape_list_length[OF observed_shape] by blast
 have actual: "lpc_mgu_resolve (LPIFun f (lp_ieval arg eta#map (\<lambda>t. lp_ieval t eta) actuals)) pending_goals
  (Fun f (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y]#map Var H)) (snd (P!c)) sigma rho"
  using mgu by (simp add: call head)
 have runtime_lengths: "length H=length (map (\<lambda>t. lp_ieval t eta) actuals)" using lengths by simp
 have matches: "\<exists>nu. lp_ieval (fst (P!c)) nu=lp_ieval a eta"
  using lpp_spine_head_matching_witness[OF runtime_spine actual distinct runtime_lengths]
  by (simp add: call head)
 show ?thesis using matches by simp
qed

lemma lpp_checked_head_attached_leaf_step:
 fixes SP :: "string lpp_success_clause list"
 and ret :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes checked: "lpp_check_separation_head P nd ctx a c witness"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and observed: "lpp_stable_context_holds operation SP ctx eta"
 and step: "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCClause (LPCAtom (lp_ieval a eta)#gs) c m,ret)#saved)) event tt"
 and invariant: "lpp_leaf_stack_invariant {u. vars_term u={}} specs
   ((LPCClause (LPCAtom (lp_ieval a eta)#gs) c m,ret)#saved)"
 and finite_call: "lpp_finite_term (lp_ieval a eta)"
 and finite_rest: "lpp_finite_goals (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t ret)) rest)"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 shows "lpp_leaf_stack_invariant {u. vars_term u={}} specs tt"
proof (rule lpp_attached_resolution_leaf_base_step[OF step invariant _ finite_call finite_rest])
 fix sigma rho
 assume actual: "lpc_mgu_resolve (lp_ieval a eta)
   (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t ret)) rest) (fst (P!c)) (snd (P!c)) sigma rho"
 show "(\<exists>nu. lp_ieval (fst (P!c)) nu=lp_ieval a eta) \<or> lp_seg_ground (lp_ieval (fst (P!c)) rho)"
  by (rule lpp_checked_head_actual_return_effect[OF checked known observed actual])
next
 show "set (map fst specs) \<subseteq> (\<Union>g\<in>set rest. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
  by (rule lpp_check_attached_leaf_slots_sound[OF covered])
qed

lemma lpp_checked_ground_equality_attached_leaf_step:
 fixes SP :: "string lpp_success_clause list"
 and ret :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes ground: "vars_term b \<subseteq> set (lpcn_ground nd) \<union> lpp_source_context_ground ctx"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and observed: "lpp_stable_context_holds operation SP ctx eta"
 and step: "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCGoals (LPCUnify (lp_ieval a eta) (lp_ieval b eta)#gs),ret)#saved)) event tt"
 and invariant: "lpp_leaf_stack_invariant {u. vars_term u={}} specs
   ((LPCGoals (LPCUnify (lp_ieval a eta) (lp_ieval b eta)#gs),ret)#saved)"
 and finite_call: "lpp_finite_term (lp_ieval a eta)"
 and finite_rest: "lpp_finite_goals (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t ret)) rest)"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 shows "lpp_leaf_stack_invariant {u. vars_term u={}} specs tt"
proof (rule lpp_attached_ground_equality_leaf_base_step[OF step invariant finite_call finite_rest _ covered])
 have each: "lp_seg_ground (eta x)" if "x\<in>vars_term b" for x
  using ground known lpp_stable_context_ground_sound[OF observed] that
  by (auto simp: lp_cut_knowledge_def)
 show "lp_seg_ground (lp_ieval b eta)" using each by (simp add: lp_seg_ground_eval)
qed

ML \<open>
val checked = @{thms lpp_checked_head_actual_return_effect lpp_checked_head_attached_leaf_step
 lpp_checked_ground_equality_attached_leaf_step};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted checked head return effect" else ();
\<close>
end
