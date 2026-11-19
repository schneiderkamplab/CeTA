theory LP_Prolog_Attached_Partial_Copy
 imports LP_Prolog_Attached_Caller_Copy LP_Prolog_Partial_Copy_Continuation
begin

lemma lpp_attached_partial_caller_copy_leaf_step:
 fixes eta :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes step: "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCClause (LPCAtom (LPIFun p [input_value,(lp_ieval parameter_template LPIVar),output_value])#gs) c m,eta)#saved)) event tt"
 and invariant: "lpp_leaf_stack_invariant (lpp_parameter_subterm_templates f g parameter_template) specs
   ((LPCClause (LPCAtom (LPIFun p [input_value,(lp_ieval parameter_template LPIVar),output_value])#gs) c m,eta)#saved)"
 and head: "fst (P!c)=Fun p [Fun nil [],Var n,Var n]"
 and spine: "lpp_finite_spine cons nil input_value spine_length"
 and ground: "vars_term parameter_template={}"
 and finite_call: "lpp_finite_term (LPIFun p [input_value,(lp_ieval parameter_template LPIVar),output_value])"
 and finite_rest: "lpp_finite_goals (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest)"
 and live: "set (map fst specs) \<subseteq>
   (\<Union>g\<in>set rest. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 shows "lpp_leaf_stack_invariant (lpp_parameter_subterm_templates f g parameter_template) specs tt"
proof -
 have attached: "lpp_leaf_stack_invariant (lpp_parameter_subterm_templates f g parameter_template) specs
   (lpc_attach_answers rest ((LPCClause (LPCAtom (LPIFun p [input_value,(lp_ieval parameter_template LPIVar),output_value])#gs) c m,eta)#saved))"
   using invariant by (simp only: lpp_leaf_stack_attachment)
 show ?thesis
 proof (rule lpp_leaf_stack_base_step[OF step attached])
 fix a' gs' c' m' ret es sigma rho
 assume shape: "lpc_attach_answers rest ((LPCClause (LPCAtom (LPIFun p [input_value,(lp_ieval parameter_template LPIVar),output_value])#gs) c m,eta)#saved) =
   (LPCClause (LPCAtom a'#gs') c' m',ret)#es"
 and bound: "c'<length P"
 and mgu: "lpc_mgu_resolve a' gs' (fst (P!c')) (snd (P!c')) sigma rho"
 have actual: "lpc_mgu_resolve (LPIFun p [input_value,(lp_ieval parameter_template LPIVar),output_value]) (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest)
   (fst (P!c)) (snd (P!c)) sigma rho"
 and ret: "ret=eta"
  using shape mgu by (auto simp: lpc_attach_answers_def)
 have finite_output: "lpp_finite_term output_value" using finite_call by simp
 show "lpp_leaf_environment_transport (lpp_parameter_subterm_templates f g parameter_template) specs ret sigma"
 proof (unfold lpp_leaf_environment_transport_def, intro ballI impI, clarify)
  fix slot initial_shape
  assume member: "(slot,initial_shape)\<in>set specs"
   and known: "lpp_runtime_leaf_effect (lpp_parameter_subterm_templates f g parameter_template) initial_shape (ret slot)"
  have occurrence: "slot\<in>(\<Union>g\<in>set rest. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
   using live member by force
  have support: "set2_lp_iterm (eta slot) \<subseteq>
    (\<Union>g\<in>set (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest).
      \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
   using lpp_attached_slot_runtime_coverage[OF occurrence, of eta gs] by blast
  show "lpp_runtime_leaf_effect (lpp_parameter_subterm_templates f g parameter_template) initial_shape (lp_isubst (ret slot) sigma)"
   unfolding ret
   by (rule lpp_partial_copy_caller_leaf[OF actual[unfolded head] spine ground finite_output finite_rest
     known[unfolded ret] support])

 qed
next
 fix a' b' gs' ret es sigma
 assume "lpc_attach_answers rest ((LPCClause (LPCAtom (LPIFun p [input_value,(lp_ieval parameter_template LPIVar),output_value])#gs) c m,eta)#saved) =
   (LPCGoals (LPCUnify a' b'#gs'),ret)#es"
 then show "lpp_leaf_environment_transport (lpp_parameter_subterm_templates f g parameter_template) specs ret sigma"
  by (simp add: lpc_attach_answers_def)
qed

qed


lemma lpp_attached_tracked_partial_copy_leaf_step:
 fixes eta :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes step: "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCClause (LPCAtom (LPIFun p [input_value,parameter,output_value])#gs) c m,eta)#saved)) event tt"
 and invariant: "lpp_leaf_stack_invariant (lpp_parameter_subterm_templates f g initial_parameter) specs
   ((LPCClause (LPCAtom (LPIFun p [input_value,parameter,output_value])#gs) c m,eta)#saved)"
 and head: "fst (P!c)=Fun p [Fun nil [],Var n,Var n]"
 and spine: "lpp_finite_spine cons nil input_value spine_length"
 and tracked: "lpp_runtime_parameter initial_parameter parameter"
 and finite_call: "lpp_finite_term (LPIFun p [input_value,parameter,output_value])"
 and finite_rest: "lpp_finite_goals (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest)"
 and live: "set (map fst specs) \<subseteq>
   (\<Union>g\<in>set rest. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 shows "lpp_leaf_stack_invariant (lpp_parameter_subterm_templates f g initial_parameter) specs tt"
proof -
 have attached: "lpp_leaf_stack_invariant (lpp_parameter_subterm_templates f g initial_parameter) specs
   (lpc_attach_answers rest ((LPCClause (LPCAtom (LPIFun p [input_value,parameter,output_value])#gs) c m,eta)#saved))"
   using invariant by (simp only: lpp_leaf_stack_attachment)
 show ?thesis
 proof (rule lpp_leaf_stack_base_step[OF step attached])
 fix a' gs' c' m' ret es sigma rho
 assume shape: "lpc_attach_answers rest ((LPCClause (LPCAtom (LPIFun p [input_value,parameter,output_value])#gs) c m,eta)#saved) =
   (LPCClause (LPCAtom a'#gs') c' m',ret)#es"
 and bound: "c'<length P"
 and mgu: "lpc_mgu_resolve a' gs' (fst (P!c')) (snd (P!c')) sigma rho"
 have actual: "lpc_mgu_resolve (LPIFun p [input_value,parameter,output_value]) (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest)
   (fst (P!c)) (snd (P!c)) sigma rho"
 and ret: "ret=eta"
  using shape mgu by (auto simp: lpc_attach_answers_def)
 have finite_output: "lpp_finite_term output_value" using finite_call by simp
 show "lpp_leaf_environment_transport (lpp_parameter_subterm_templates f g initial_parameter) specs ret sigma"
 proof (unfold lpp_leaf_environment_transport_def, intro ballI impI, clarify)
  fix slot initial_shape
  assume member: "(slot,initial_shape)\<in>set specs"
   and known: "lpp_runtime_leaf_effect (lpp_parameter_subterm_templates f g initial_parameter) initial_shape (ret slot)"
  have occurrence: "slot\<in>(\<Union>g\<in>set rest. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
   using live member by force
  have support: "set2_lp_iterm (eta slot) \<subseteq>
    (\<Union>g\<in>set (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest).
      \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
   using lpp_attached_slot_runtime_coverage[OF occurrence, of eta gs] by blast
  show "lpp_runtime_leaf_effect (lpp_parameter_subterm_templates f g initial_parameter) initial_shape (lp_isubst (ret slot) sigma)"
   unfolding ret
   by (rule lpp_partial_copy_tracked_caller_leaf[OF actual[unfolded head] spine tracked finite_output finite_rest
     known[unfolded ret] support])

 qed
next
 fix a' b' gs' ret es sigma
 assume "lpc_attach_answers rest ((LPCClause (LPCAtom (LPIFun p [input_value,parameter,output_value])#gs) c m,eta)#saved) =
   (LPCGoals (LPCUnify a' b'#gs'),ret)#es"
 then show "lpp_leaf_environment_transport (lpp_parameter_subterm_templates f g initial_parameter) specs ret sigma"
  by (simp add: lpc_attach_answers_def)
qed

qed


ML \<open>
val checked = @{thms lpp_attached_partial_caller_copy_leaf_step lpp_attached_tracked_partial_copy_leaf_step};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted attached partial copy" else ();
val _ = writeln "ATTACHED_PARTIAL_COPY_KERNEL_CHECKED";
\<close>
end
