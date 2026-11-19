theory LP_Prolog_Attached_Subterm_Equality
 imports LP_Prolog_Attached_Ground_Leaf LP_Prolog_Subterm_Ground_Equality
begin

text \<open>Restricted leaf effects lift through an actual equality step with
an attached caller continuation. The shared stack-step theorem preserves saved
alternatives separately; success facts never initialize a failure branch.\<close>

lemma lpp_attached_subterm_equality_leaf_transport:
 fixes eta :: "nat \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_unify a b (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest) sigma"
 and finite_rest: "lpp_finite_goals (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest)"
 and finite_call: "lpp_finite_term a"
 and replacement: "b=lp_ieval u LPIVar"
 and allowed: "u\<in>A"
 and ground: "\<And>v. v\<in>A \<Longrightarrow> vars_term v={}"
 and closed: "\<And>v. lpp_finite_template_subterm v u \<Longrightarrow> v\<in>A"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 shows "lpp_leaf_environment_transport A specs eta sigma"
proof (unfold lpp_leaf_environment_transport_def, intro ballI impI, clarify)
 fix slot shape
 assume member: "(slot,shape)\<in>set specs"
 and known: "lpp_runtime_leaf_effect A shape (eta slot)"
 have live: "slot\<in>(\<Union>g\<in>set rest. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
  using lpp_check_attached_leaf_slots_sound[OF covered] member by force
 have support: "set2_lp_iterm (eta slot) \<subseteq> set2_lp_iterm a \<union>
  (\<Union>g\<in>set (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest).
    \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
  using lpp_attached_slot_runtime_coverage[OF live, of eta gs] by blast
 show "lpp_runtime_leaf_effect A shape (lp_isubst (eta slot) sigma)"
 proof (rule lpp_runtime_leaf_effect_substitute[OF known _ ground])
  show "lpp_bounded_images A sigma (set2_lp_iterm (eta slot))"
   by (rule lpp_subterm_ground_equality_images[OF _ finite_call finite_rest ground[OF allowed] allowed closed])
    (use mgu support in \<open>simp_all add: replacement\<close>)
 qed
qed

lemma lpp_attached_subterm_equality_leaf_base_step:
 fixes eta :: "nat \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
 assumes step: "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCGoals (LPCUnify a b#gs),eta)#saved)) event tt"
 and invariant: "lpp_leaf_stack_invariant A specs
   ((LPCGoals (LPCUnify a b#gs),eta)#saved)"
 and finite_rest: "lpp_finite_goals (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest)"
 and finite_call: "lpp_finite_term a"
 and replacement: "b=lp_ieval u LPIVar"
 and allowed: "u\<in>A"
 and ground: "\<And>v. v\<in>A \<Longrightarrow> vars_term v={}"
 and closed: "\<And>v. lpp_finite_template_subterm v u \<Longrightarrow> v\<in>A"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 shows "lpp_leaf_stack_invariant A specs tt"
proof -
 have attached: "lpp_leaf_stack_invariant A specs
   (lpc_attach_answers rest ((LPCGoals (LPCUnify a b#gs),eta)#saved))"
  using invariant by (simp only: lpp_leaf_stack_attachment)
 show ?thesis
 proof (rule lpp_leaf_stack_base_step[OF step attached])
  fix a' gs' c m ret es sigma rho
  assume "lpc_attach_answers rest ((LPCGoals (LPCUnify a b#gs),eta)#saved) =
    (LPCClause (LPCAtom a'#gs') c m,ret)#es"
  then show "lpp_leaf_environment_transport A specs ret sigma"
   by (simp add: lpc_attach_answers_def)
 next
  fix a' b' gs' ret es sigma
  assume shape: "lpc_attach_answers rest ((LPCGoals (LPCUnify a b#gs),eta)#saved) =
    (LPCGoals (LPCUnify a' b'#gs'),ret)#es"
  and mgu: "lpc_mgu_unify a' b' gs' sigma"
  have actual: "lpc_mgu_unify a b (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest) sigma"
  and ret: "ret=eta"
   using shape mgu by (auto simp: lpc_attach_answers_def)
  show "lpp_leaf_environment_transport A specs ret sigma"
   unfolding ret by (rule lpp_attached_subterm_equality_leaf_transport[OF actual finite_rest finite_call replacement allowed ground closed covered])
 qed
qed

ML \<open>
val checked = @{thms lpp_attached_subterm_equality_leaf_transport lpp_attached_subterm_equality_leaf_base_step};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted attached allowed equality" else ();
\<close>
end
