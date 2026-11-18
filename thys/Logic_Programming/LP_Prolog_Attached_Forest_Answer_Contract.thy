theory LP_Prolog_Attached_Forest_Answer_Contract
 imports LP_Prolog_Attached_Forest_Composition
begin

lemma lpp_attached_forest_answer_contract:
 fixes head_shape :: "(string lp_cut_symbol+unit,unit) term"
 and xs :: "(string lp_cut_symbol+unit,unit) term list"
 assumes program: "lp_cut_source_program P"
 and prefix: "lp_answer_contract (lpp_domain_answers P B U D) ss R subject helper_return"
 and valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss"
 and separated: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst ss)) = {}"
 and initial: "lpp_leaf_stack_invariant A specs ss"
 and preserve: "\<And>us ev vs. lpp_leaf_stack_invariant A specs us \<Longrightarrow>
   (ss,us)\<in>(lp_answer_steps (lpp_domain_answers P B U D))\<^sup>* \<Longrightarrow>
   lpc_prefix_active us \<Longrightarrow>
   lpp_domain_answers P B U D (lpc_attach_answers rest us) ev (lpc_attach_answers rest vs)
   \<Longrightarrow> lpp_leaf_stack_invariant A specs vs"
 and member: "(slot,lpp_structural_argument_list xs)\<in>set specs"
 and ground: "\<And>u. u\<in>A \<Longrightarrow> vars_term u = {}"
 and observed_head: "lpp_runtime_structure head_value head_shape"
 and lower: "\<And>eta ys. lp_actual_answer (lpp_domain_answers P B U D) ss eta \<Longrightarrow>
   lpp_runtime_structure (eta slot) (lpp_structural_argument_list ys) \<Longrightarrow>
   ((Inr ys :: (string lp_cut_symbol+unit,unit) term + (string lp_cut_symbol+unit,unit) term list),Inr (head_shape#xs))\<in>lpp_forest_call_order \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P B U D)
    [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] R (helper_return eta) returned"
 shows "lp_answer_contract (lpp_domain_answers P B U D) (lpc_attach_answers rest ss) R subject returned"
proof (rule lpp_domain_contract_compose_actual_invariant[where I="lpp_leaf_stack_invariant A specs",
 OF program prefix valid separated initial preserve])
 fix eta vs
 assume invariant: "lpp_leaf_stack_invariant A specs ((LPCGoals [],eta)#vs)"
 show "lpp_leaf_stack_invariant A specs vs"
  by (rule lpp_leaf_stack_tail[OF invariant])
next
 fix eta vs
 assume actual: "lp_actual_answer (lpp_domain_answers P B U D) ss eta"
 and invariant: "lpp_leaf_stack_invariant A specs ((LPCGoals [],eta)#vs)"
 have returned: "lpp_runtime_leaf_effect A (lpp_structural_argument_list xs) (eta slot)"
  by (rule lpp_leaf_stack_head[OF invariant member])
 obtain ys where observed: "lpp_runtime_structure (eta slot) (lpp_structural_argument_list ys)"
 and smaller: "((Inr ys :: (string lp_cut_symbol+unit,unit) term + (string lp_cut_symbol+unit,unit) term list),Inr (head_shape#xs))\<in>lpp_forest_call_order"
  using lpp_runtime_returned_argument_tail_decreases[OF returned ground observed_head] by blast
 show "lp_answer_contract (lpp_domain_answers P B U D)
    [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] R (helper_return eta) returned"
  by (rule lower[OF actual observed smaller])
qed

end
