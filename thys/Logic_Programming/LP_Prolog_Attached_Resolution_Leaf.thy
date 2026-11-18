theory LP_Prolog_Attached_Resolution_Leaf
 imports LP_Prolog_Attached_Ground_Leaf
begin

lemma lpp_attached_resolution_leaf_base_step:
 fixes eta :: "nat \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
 assumes step: "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCClause (LPCAtom a#gs) c m,eta)#saved)) event tt"
 and invariant: "lpp_leaf_stack_invariant {u. vars_term u={}} specs
   ((LPCClause (LPCAtom a#gs) c m,eta)#saved)"
 and head_effect: "\<And>sigma rho. lpc_mgu_resolve a
   (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest) (fst (P!c)) (snd (P!c)) sigma rho \<Longrightarrow>
   (\<exists>nu. lp_ieval (fst (P!c)) nu=a) \<or> lp_seg_ground (lp_ieval (fst (P!c)) rho)"
 and finite_call: "lpp_finite_term a"
 and finite_rest: "lpp_finite_goals (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest)"
 and live: "set (map fst specs) \<subseteq>
   (\<Union>g\<in>set rest. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 shows "lpp_leaf_stack_invariant {u. vars_term u={}} specs tt"
proof -
 have attached: "lpp_leaf_stack_invariant {u. vars_term u={}} specs
   (lpc_attach_answers rest ((LPCClause (LPCAtom a#gs) c m,eta)#saved))"
   using invariant by (simp only: lpp_leaf_stack_attachment)
 show ?thesis
 proof (rule lpp_leaf_stack_base_step[OF step attached])
 fix a' gs' c' m' ret es sigma rho
 assume shape: "lpc_attach_answers rest ((LPCClause (LPCAtom a#gs) c m,eta)#saved) =
   (LPCClause (LPCAtom a'#gs') c' m',ret)#es"
 and bound: "c'<length P"
 and mgu: "lpc_mgu_resolve a' gs' (fst (P!c')) (snd (P!c')) sigma rho"
 have actual: "lpc_mgu_resolve a (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest)
   (fst (P!c)) (snd (P!c)) sigma rho"
 and ret: "ret=eta"
  using shape mgu by (auto simp: lpc_attach_answers_def)
 have cases: "(\<exists>nu. lp_ieval (fst (P!c)) nu=a) \<or> lp_seg_ground (lp_ieval (fst (P!c)) rho)"
  by (rule head_effect[OF actual])
 from cases show "lpp_leaf_environment_transport {u. vars_term u={}} specs ret sigma"
 proof (elim disjE)
  assume matching_exists: "\<exists>nu. lp_ieval (fst (P!c)) nu=a"
  then obtain nu where matching: "lp_ieval (fst (P!c)) nu=a" by blast
  show ?thesis
  proof (unfold lpp_leaf_environment_transport_def, intro ballI impI, clarify)
   fix slot initial_shape
   assume member: "(slot,initial_shape)\<in>set specs"
    and known: "lpp_runtime_leaf_effect {u. vars_term u={}} initial_shape (ret slot)"
   have occurrence: "slot\<in>(\<Union>g\<in>set rest. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
    using live member by force
   have support: "set2_lp_iterm (eta slot) \<subseteq>
     set2_lp_iterm a \<union> (\<Union>g\<in>set (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest).
       \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
    using lpp_attached_slot_runtime_coverage[OF occurrence, of eta gs] by blast
   show "lpp_runtime_leaf_effect {u. vars_term u={}} initial_shape (lp_isubst (ret slot) sigma)"
    by (rule lpp_runtime_leaf_effect_substitute[OF known])
     (use lpp_runtime_matching_leaf_images[OF actual matching finite_call finite_rest support] ret in auto)
  qed
 next
  assume ground: "lp_seg_ground (lp_ieval (fst (P!c)) rho)"
  have coverage: "lpp_check_attached_leaf_slots (map fst specs) rest"
   using live by (simp add: lpp_check_attached_leaf_slots_def lpp_leaf_goals_variables_correct)
  show ?thesis unfolding ret
   by (rule lpp_attached_ground_head_leaf_transport[OF actual finite_call finite_rest ground coverage])
 qed
next
 fix a' b' gs' ret es sigma
 assume "lpc_attach_answers rest ((LPCClause (LPCAtom a#gs) c m,eta)#saved) =
   (LPCGoals (LPCUnify a' b'#gs'),ret)#es"
 then show "lpp_leaf_environment_transport {u. vars_term u={}} specs ret sigma"
  by (simp add: lpc_attach_answers_def)
qed

qed

ML \<open>
val checked = @{thms lpp_attached_resolution_leaf_base_step};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted attached resolution leaf step" else ();
\<close>
end
