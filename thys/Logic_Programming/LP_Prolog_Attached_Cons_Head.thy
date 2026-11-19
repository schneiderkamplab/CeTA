theory LP_Prolog_Attached_Cons_Head
 imports LP_Prolog_Observer_Conditioned_Matching LP_Prolog_Leaf_Spine_Head
begin

text \<open>Successful resolution of a linear cons head on a proper spine is actual
matching. Preserve a restricted ground replacement set and the finite attached
caller state; neither spine length nor helper finiteness replaces caller coverage.\<close>

lemma lpp_attached_cons_leaf_step:
 fixes eta :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes step: "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCClause (LPCAtom (LPIFun p (input_value#actuals))#gs) c m,eta)#saved)) event tt"
 and invariant: "lpp_leaf_stack_invariant allowed_templates specs
   ((LPCClause (LPCAtom (LPIFun p (input_value#actuals))#gs) c m,eta)#saved)"
 and ground_templates: "\<And>u. u\<in>allowed_templates \<Longrightarrow> vars_term u={}"
 and head: "fst (P!c)=Fun p (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y]#map Var H)"
 and spine: "lpp_list_length input_value spine_length"
 and distinct: "distinct (x#y#H)"
 and lengths: "length H=length actuals"
 and finite_call: "lpp_finite_term (LPIFun p (input_value#actuals))"
 and finite_rest: "lpp_finite_goals (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest)"
 and live: "set (map fst specs) \<subseteq>
   (\<Union>g\<in>set rest. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 shows "lpp_leaf_stack_invariant allowed_templates specs tt"
proof -
 have attached: "lpp_leaf_stack_invariant allowed_templates specs
   (lpc_attach_answers rest ((LPCClause (LPCAtom (LPIFun p (input_value#actuals))#gs) c m,eta)#saved))"
   using invariant by (simp only: lpp_leaf_stack_attachment)
 show ?thesis
 proof (rule lpp_leaf_stack_base_step[OF step attached])
 fix a' gs' c' m' ret es sigma rho
 assume shape: "lpc_attach_answers rest ((LPCClause (LPCAtom (LPIFun p (input_value#actuals))#gs) c m,eta)#saved) =
   (LPCClause (LPCAtom a'#gs') c' m',ret)#es"
 and bound: "c'<length P"
 and mgu: "lpc_mgu_resolve a' gs' (fst (P!c')) (snd (P!c')) sigma rho"
 have actual: "lpc_mgu_resolve (LPIFun p (input_value#actuals)) (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest)
   (fst (P!c)) (snd (P!c)) sigma rho"
 and ret: "ret=eta"
  using shape mgu by (auto simp: lpc_attach_answers_def)
 obtain nu where matching: "lp_ieval (fst (P!c)) nu=LPIFun p (input_value#actuals)"
  using lpp_spine_head_matching_witness[OF spine actual[unfolded head] distinct lengths]
  unfolding head by blast
 show "lpp_leaf_environment_transport allowed_templates specs ret sigma"
 proof (unfold lpp_leaf_environment_transport_def, intro ballI impI, clarify)
  fix slot initial_shape
  assume member: "(slot,initial_shape)\<in>set specs"
   and known: "lpp_runtime_leaf_effect allowed_templates initial_shape (ret slot)"
  have occurrence: "slot\<in>(\<Union>g\<in>set rest. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
   using live member by force
  have support: "set2_lp_iterm (eta slot) \<subseteq>
    set2_lp_iterm (LPIFun p (input_value#actuals)) \<union> (\<Union>g\<in>set (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest).
      \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
   using lpp_attached_slot_runtime_coverage[OF occurrence, of eta gs] by blast
  show "lpp_runtime_leaf_effect allowed_templates initial_shape (lp_isubst (ret slot) sigma)"
   by (rule lpp_runtime_leaf_effect_substitute[OF known])
    (use lpp_runtime_matching_leaf_images[OF actual matching finite_call finite_rest support] ret ground_templates in auto)
 qed
next
 fix a' b' gs' ret es sigma
 assume "lpc_attach_answers rest ((LPCClause (LPCAtom (LPIFun p (input_value#actuals))#gs) c m,eta)#saved) =
   (LPCGoals (LPCUnify a' b'#gs'),ret)#es"
 then show "lpp_leaf_environment_transport allowed_templates specs ret sigma"
  by (simp add: lpc_attach_answers_def)
qed

qed


lemma lpp_cons_head_finite_instance:
 assumes spine: "lpp_list_length input_value spine_length"
 and mgu: "lpc_mgu_resolve (LPIFun p (input_value#actuals)) gs
  (Fun p (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y]#map Var H)) bs sigma rho"
 and distinct: "distinct (x#y#H)"
 and lengths: "length H=length actuals"
 and finite_call: "lpp_finite_term (LPIFun p (input_value#actuals))"
 shows "lpp_finite_term (lp_isubst (LPIFun p (input_value#actuals)) sigma)"
proof -
 obtain nu where matching: "lp_ieval
   (Fun p (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y]#map Var H)) nu=LPIFun p (input_value#actuals)"
  using lpp_spine_head_matching_witness[OF spine mgu distinct lengths] by blast
 have finite_head: "lpp_finite_term (lp_ieval
   (Fun p (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y]#map Var H)) rho)"
  by (rule lpp_matching_head_finite_instance[OF mgu matching finite_call])
 show ?thesis using finite_head mgu by (simp add: lpc_mgu_resolve_def)
qed

lemma lpp_attached_cons_finite_step:
 assumes step: "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCClause (LPCAtom (LPIFun p (input_value#actuals))#gs) c m,env)#saved)) event tt"
 and finite: "lpp_finite_execution
   (lpc_attach_answers rest ((LPCClause (LPCAtom (LPIFun p (input_value#actuals))#gs) c m,env)#saved))"
 and head: "fst (P!c)=Fun p (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y]#map Var H)"
 and spine: "lpp_list_length input_value spine_length"
 and distinct: "distinct (x#y#H)"
 and lengths: "length H=length actuals"
 shows "lpp_finite_execution tt"
proof (rule lpp_finite_base_answer_step[OF step finite])
 fix call pending clause mark ret alternatives sigma rho
 assume shape: "lpc_attach_answers rest ((LPCClause (LPCAtom (LPIFun p (input_value#actuals))#gs) c m,env)#saved)=
  (LPCClause (LPCAtom call#pending) clause mark,ret)#alternatives"
 and bound: "clause<length P"
 and mgu: "lpc_mgu_resolve call pending (fst (P!clause)) (snd (P!clause)) sigma rho"
 have actual: "call=LPIFun p (input_value#actuals)" "clause=c"
  using shape by (auto simp: lpc_attach_answers_def)
 have finite_call: "lpp_finite_term (LPIFun p (input_value#actuals))"
  using finite by (auto simp: lpc_attach_answers_def lpp_finite_execution_def lpp_finite_goals_def)
 have finite_subst: "lpp_finite_term (lp_isubst call sigma)"
  unfolding actual by (rule lpp_cons_head_finite_instance[OF spine mgu[unfolded actual head] distinct lengths finite_call])
 show "lpp_finite_term (lp_ieval (fst (P!clause)) rho)"
  using finite_subst mgu by (simp add: lpc_mgu_resolve_def)
qed (auto simp: lpc_attach_answers_def)

lemma lpp_cons_tail_successor:
 assumes coordinate: "lpp_check_clause_coordinate l (Var y) target_tail bindings"
 and spine: "lpp_list_length input_value spine_length"
 and mgu: "lpc_mgu_resolve (LPIFun p (input_value#actuals)) gs
  (Fun p (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y]#hs)) bs sigma rho"
 shows "\<exists>tail_length. spine_length=Suc tail_length \<and>
  lpp_list_length (lp_ieval target_tail
   (\<lambda>v. lp_ieval (lp_cut_instance_subst bindings v) (lp_cut_resolution_env k l eta sigma rho))) tail_length"
 using lpp_checked_clause_coordinate_value[OF coordinate, of k eta sigma rho]
  lpp_list_head_tail_observation[OF spine mgu] by auto

ML \<open>
val checked = @{thms lpp_attached_cons_leaf_step lpp_cons_head_finite_instance
 lpp_attached_cons_finite_step lpp_cons_tail_successor};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted attached cons head" else ();
\<close>
end
