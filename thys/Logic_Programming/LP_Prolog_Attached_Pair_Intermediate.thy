theory LP_Prolog_Attached_Pair_Intermediate
 imports LP_Prolog_Attached_Arithmetic_Leaf
begin

lemma lpp_attached_reflexive_pair_inverses:
 fixes eta :: "nat \<Rightarrow> ('f,string) lp_iterm"
 assumes first: "lpc_mgu_unify input_term input_term
   (LPCUnify left right#(pending_goals @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)) sigma"
 and covered: "slot\<in>(\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 shows "\<exists>delta. lp_isubst (lp_isubst left sigma) delta=left \<and>
   lp_isubst (lp_isubst right sigma) delta=right \<and>
   lp_isubst (lp_isubst (eta slot) sigma) delta=eta slot"
proof -
 have projected: "lpc_mgu_unify input_term input_term
   (LPCUnify left right#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma"
  by (rule lpc_mgu_unify_continuation_subset[OF first]) auto
 have mapped: "lpc_mgu_unify input_term input_term
   (LPCUnify left right#map (lp_cut_map (\<lambda>t. lp_ieval t (\<lambda>name. eta (length name)))) (lpp_named_return_goals gs)) sigma"
  using projected by (simp add: lpp_named_return_goals_eval)
 have occurrence: "lpp_return_slot_name slot\<in>(\<Union>g\<in>set (lpp_named_return_goals gs). \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
  using covered by (simp add: lpp_named_return_goals_support)
 obtain delta where il: "lp_isubst (lp_isubst left sigma) delta=left"
 and ir: "lp_isubst (lp_isubst right sigma) delta=right"
 and all_slots: "\<forall>v\<in>(\<Union>g\<in>set (lpp_named_return_goals gs). \<Union>t\<in>set (lp_cut_terms g). vars_term t).
   lp_isubst (lp_isubst (eta (length v)) sigma) delta=eta (length v)"
  using lpp_reflexive_pair_context_inverses[OF mapped] by blast
 have iv: "lp_isubst (lp_isubst (eta slot) sigma) delta=eta slot"
  using bspec[OF all_slots occurrence] by simp
 show ?thesis using il ir iv by blast
qed

lemma lpp_attached_pair_intermediate_leaf_and_separation:
 fixes eta :: "nat \<Rightarrow> ('f,string) lp_iterm"
 assumes first: "lpc_mgu_unify input_term input_term
   (LPCUnify left right#(pending_goals @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)) sigma"
 and covered: "slot\<in>(\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 and known: "lpp_runtime_leaf_effect A shape (eta slot)"
 and finite_left: "lpp_finite_term left"
 and finite_right: "lpp_finite_term right"
 and separated: "set2_lp_iterm left\<inter>set2_lp_iterm right={}"
 and protected: "set2_lp_iterm left\<inter>set2_lp_iterm (eta slot)={}"
 shows "lpp_runtime_leaf_effect A shape (lp_isubst (eta slot) sigma) \<and>
   lpp_finite_term (lp_isubst right sigma) \<and>
   set2_lp_iterm (lp_isubst left sigma)\<inter>set2_lp_iterm (lp_isubst right sigma)={} \<and>
   set2_lp_iterm (lp_isubst left sigma)\<inter>set2_lp_iterm (lp_isubst (eta slot) sigma)={}"
proof -
 obtain delta where il: "lp_isubst (lp_isubst left sigma) delta=left"
 and ir: "lp_isubst (lp_isubst right sigma) delta=right"
 and iv: "lp_isubst (lp_isubst (eta slot) sigma) delta=eta slot"
  using lpp_attached_reflexive_pair_inverses[OF first covered] by blast
 have finite_v: "lpp_finite_term (eta slot)" by (rule lpp_runtime_leaf_effect_finite[OF known])
 obtain observed where before: "lpp_runtime_structure (eta slot) observed"
 and after: "lpp_runtime_structure (lp_isubst (eta slot) sigma) observed"
  using lpp_finite_inverse_structural_observation[OF finite_v iv] by blast
 have leaf: "lpp_runtime_leaf_effect A shape (lp_isubst (eta slot) sigma)"
  by (rule lpp_runtime_leaf_effect_preserved_observation[OF known before after])
 have finite: "lpp_finite_term (lp_isubst right sigma)"
  using lpp_finite_inverse_structural_observation[OF finite_right ir] lpp_runtime_structure_finite by blast
 have sep: "set2_lp_iterm (lp_isubst left sigma)\<inter>set2_lp_iterm (lp_isubst right sigma)={}"
  by (rule lpp_finite_inverse_separation[OF finite_left finite_right il ir separated])
 have protect: "set2_lp_iterm (lp_isubst left sigma)\<inter>set2_lp_iterm (lp_isubst (eta slot) sigma)={}"
  by (rule lpp_finite_inverse_separation[OF finite_left finite_v il iv protected])
 show ?thesis using leaf finite sep protect by blast
qed

lemma lpp_attached_pair_intermediate_stack:
 fixes eta :: "nat \<Rightarrow> ('f,string) lp_iterm"
 assumes first: "lpc_mgu_unify input_term input_term
   (LPCUnify left right#(pending_goals @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)) sigma"
 and invariant: "lpp_leaf_stack_invariant A specs ((entry,eta)#saved)"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) gs"
 and finite_left: "lpp_finite_term left"
 and finite_right: "lpp_finite_term right"
 and separated: "set2_lp_iterm left\<inter>set2_lp_iterm right={}"
 and protected: "\<And>slot shape. (slot,shape)\<in>set specs \<Longrightarrow>
   set2_lp_iterm left\<inter>set2_lp_iterm (eta slot)={}"
 shows "lpp_leaf_stack_invariant A specs ((next_entry,\<lambda>slot. lp_isubst (eta slot) sigma)#saved) \<and>
   (\<forall>(slot,shape)\<in>set specs.
     set2_lp_iterm (lp_isubst left sigma)\<inter>set2_lp_iterm (lp_isubst (eta slot) sigma)={})"
proof -
 have each: "lpp_runtime_leaf_effect A shape (lp_isubst (eta slot) sigma) \<and>
   set2_lp_iterm (lp_isubst left sigma)\<inter>set2_lp_iterm (lp_isubst (eta slot) sigma)={}"
  if member: "(slot,shape)\<in>set specs" for slot shape
 proof -
  have live: "slot\<in>(\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
   using lpp_check_attached_leaf_slots_sound[OF covered] member by force
  have known: "lpp_runtime_leaf_effect A shape (eta slot)"
   by (rule lpp_leaf_stack_head[OF invariant member])
  show ?thesis using lpp_attached_pair_intermediate_leaf_and_separation[
    OF first live known finite_left finite_right separated protected[OF member]] by blast
 qed
 have stack: "lpp_leaf_stack_invariant A specs ((next_entry,\<lambda>slot. lp_isubst (eta slot) sigma)#saved)"
  by (rule lpp_leaf_stack_active_update[OF invariant]) (use each in blast)
 show ?thesis using stack each by auto
qed

ML \<open>
val checked = @{thms lpp_attached_reflexive_pair_inverses lpp_attached_pair_intermediate_leaf_and_separation
 lpp_attached_pair_intermediate_stack};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted attached intermediate preservation" else ();
\<close>
end
