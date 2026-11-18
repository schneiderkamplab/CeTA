theory LP_Prolog_Attached_Ground_Leaf
 imports LP_Prolog_Return_Slot_Univ
begin

lemma lpp_attached_ground_head_leaf_transport:
 fixes eta :: "nat \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_resolve a (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest) h bs sigma rho"
 and finite_call: "lpp_finite_term a"
 and finite_rest: "lpp_finite_goals (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest)"
 and ground: "lp_seg_ground (lp_ieval h rho)"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 shows "lpp_leaf_environment_transport {u. vars_term u={}} specs eta sigma"
proof (rule lpp_runtime_ground_head_leaf_transport[OF mgu finite_call finite_rest lpp_ground_finite_term[OF ground] ground])
 fix slot shape assume member: "(slot,shape)\<in>set specs"
 have live: "slot\<in>(\<Union>g\<in>set rest. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
  using lpp_check_attached_leaf_slots_sound[OF covered] member by force
 show "set2_lp_iterm (eta slot) \<subseteq> set2_lp_iterm a \<union>
  (\<Union>g\<in>set (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest).
    \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
  using lpp_attached_slot_runtime_coverage[OF live, of eta gs] by blast
qed

lemma lpp_attached_ground_equality_leaf_transport:
 fixes eta :: "nat \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_unify a b (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest) sigma"
 and finite_call: "lpp_finite_term a"
 and finite_rest: "lpp_finite_goals (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest)"
 and ground: "lp_seg_ground b"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 shows "lpp_leaf_environment_transport {u. vars_term u={}} specs eta sigma"
proof (unfold lpp_leaf_environment_transport_def, intro ballI impI, clarify)
 fix slot shape
 assume member: "(slot,shape)\<in>set specs"
 and known: "lpp_runtime_leaf_effect {u. vars_term u={}} shape (eta slot)"
 have live: "slot\<in>(\<Union>g\<in>set rest. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
  using lpp_check_attached_leaf_slots_sound[OF covered] member by force
 have support: "set2_lp_iterm (eta slot) \<subseteq> set2_lp_iterm a \<union>
  (\<Union>g\<in>set (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest).
    \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
  using lpp_attached_slot_runtime_coverage[OF live, of eta gs] by blast
 show "lpp_runtime_leaf_effect {u. vars_term u={}} shape (lp_isubst (eta slot) sigma)"
  by (rule lpp_runtime_leaf_effect_substitute[OF known
    lpp_runtime_ground_equality_leaf_images[OF mgu ground finite_call finite_rest support]]) simp
qed

lemma lpp_attached_ground_equality_leaf_base_step:
 fixes eta :: "nat \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
 assumes step: "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCGoals (LPCUnify a b#gs),eta)#saved)) event tt"
 and invariant: "lpp_leaf_stack_invariant {u. vars_term u={}} specs
   ((LPCGoals (LPCUnify a b#gs),eta)#saved)"
 and finite_call: "lpp_finite_term a"
 and finite_rest: "lpp_finite_goals (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest)"
 and ground: "lp_seg_ground b"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 shows "lpp_leaf_stack_invariant {u. vars_term u={}} specs tt"
proof -
 have attached: "lpp_leaf_stack_invariant {u. vars_term u={}} specs
   (lpc_attach_answers rest ((LPCGoals (LPCUnify a b#gs),eta)#saved))"
  using invariant by (simp only: lpp_leaf_stack_attachment)
 show ?thesis
 proof (rule lpp_leaf_stack_base_step[OF step attached])
  fix a' gs' c m ret es sigma rho
  assume "lpc_attach_answers rest ((LPCGoals (LPCUnify a b#gs),eta)#saved) =
    (LPCClause (LPCAtom a'#gs') c m,ret)#es"
  then show "lpp_leaf_environment_transport {u. vars_term u={}} specs ret sigma"
   by (simp add: lpc_attach_answers_def)
 next
  fix a' b' gs' ret es sigma
  assume shape: "lpc_attach_answers rest ((LPCGoals (LPCUnify a b#gs),eta)#saved) =
    (LPCGoals (LPCUnify a' b'#gs'),ret)#es"
  and mgu: "lpc_mgu_unify a' b' gs' sigma"
  have actual: "lpc_mgu_unify a b (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest) sigma"
  and ret: "ret=eta"
   using shape mgu by (auto simp: lpc_attach_answers_def)
  show "lpp_leaf_environment_transport {u. vars_term u={}} specs ret sigma"
   unfolding ret by (rule lpp_attached_ground_equality_leaf_transport[OF actual finite_call finite_rest ground covered])
 qed
qed

ML \<open>
val checked = @{thms lpp_attached_ground_head_leaf_transport lpp_attached_ground_equality_leaf_transport
 lpp_attached_ground_equality_leaf_base_step};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted attached ground leaf transport" else ();
\<close>
end
