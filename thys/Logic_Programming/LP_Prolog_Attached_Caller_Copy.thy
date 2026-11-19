theory LP_Prolog_Attached_Caller_Copy
 imports LP_Prolog_Attached_Parameter_Copy LP_Prolog_Ground_Caller_Continuation
begin

text \<open>Extend the repeated-parameter attached transition to free or ground
caller outputs. Failed resolution and saved environments use the shared base
step rules; all caller coverage and finiteness premises remain explicit.\<close>

lemma lpp_attached_ground_caller_copy_leaf_step:
 fixes eta :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes step: "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCClause (LPCAtom (LPIFun p [input_value,parameter,output_value])#gs) c m,eta)#saved)) event tt"
 and invariant: "lpp_leaf_stack_invariant allowed_templates specs
   ((LPCClause (LPCAtom (LPIFun p [input_value,parameter,output_value])#gs) c m,eta)#saved)"
 and ground_templates: "\<And>u. u\<in>allowed_templates \<Longrightarrow> vars_term u={}"
 and head: "fst (P!c)=Fun p [Fun nil [],Var n,Var n]"
 and spine: "lpp_finite_spine cons nil input_value spine_length"
 and parameter: "lp_seg_ground parameter"
 and ground_output: "lp_seg_ground output_value"
 and finite_call: "lpp_finite_term (LPIFun p [input_value,parameter,output_value])"
 and finite_rest: "lpp_finite_goals (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest)"
 and live: "set (map fst specs) \<subseteq>
   (\<Union>g\<in>set rest. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 shows "lpp_leaf_stack_invariant allowed_templates specs tt"
proof -
 have attached: "lpp_leaf_stack_invariant allowed_templates specs
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
 have matching: "lp_ieval (fst (P!c)) (\<lambda>_. parameter)=LPIFun p [input_value,parameter,output_value]"
  using lpp_ground_caller_copy_matching[OF spine actual[unfolded head] parameter ground_output]
  unfolding head by simp
 show "lpp_leaf_environment_transport allowed_templates specs ret sigma"
 proof (unfold lpp_leaf_environment_transport_def, intro ballI impI, clarify)
  fix slot initial_shape
  assume member: "(slot,initial_shape)\<in>set specs"
   and known: "lpp_runtime_leaf_effect allowed_templates initial_shape (ret slot)"
  have occurrence: "slot\<in>(\<Union>g\<in>set rest. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
   using live member by force
  have support: "set2_lp_iterm (eta slot) \<subseteq>
    set2_lp_iterm (LPIFun p [input_value,parameter,output_value]) \<union> (\<Union>g\<in>set (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest).
      \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
   using lpp_attached_slot_runtime_coverage[OF occurrence, of eta gs] by blast
  show "lpp_runtime_leaf_effect allowed_templates initial_shape (lp_isubst (ret slot) sigma)"
   by (rule lpp_runtime_leaf_effect_substitute[OF known])
    (use lpp_runtime_matching_leaf_images[OF actual matching finite_call finite_rest support] ret ground_templates in auto)
 qed
next
 fix a' b' gs' ret es sigma
 assume "lpc_attach_answers rest ((LPCClause (LPCAtom (LPIFun p [input_value,parameter,output_value])#gs) c m,eta)#saved) =
   (LPCGoals (LPCUnify a' b'#gs'),ret)#es"
 then show "lpp_leaf_environment_transport allowed_templates specs ret sigma"
  by (simp add: lpc_attach_answers_def)
qed

qed


lemma lpp_attached_caller_copy_leaf_step:
 fixes env :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes step: "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCClause (LPCAtom (LPIFun p [input_value,parameter,output_value])#gs) c m,env)#saved)) event tt"
 and head: "fst (P!c)=Fun p [Fun nil [],Var n,Var n]"
 and spine: "lpp_finite_spine cons nil input_value spine_length"
 and tracked: "lpp_runtime_parameter initial_parameter parameter"
 and caller_mode: "lpp_caller_output_mode output_value"
 and finite_call: "lpp_finite_term (LPIFun p [input_value,parameter,output_value])"
 and finite_rest: "lpp_finite_goals (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t env)) rest)"
 and invariant: "lpp_leaf_stack_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs
   ((LPCClause (LPCAtom (LPIFun p [input_value,parameter,output_value])#gs) c m,env)#saved)"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 shows "lpp_leaf_stack_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs tt"
proof (cases "lp_seg_ground output_value")
 case True
 show ?thesis
  by (rule lpp_attached_ground_caller_copy_leaf_step[OF step invariant _ head spine
    lpp_runtime_parameter_ground[OF tracked] True finite_call finite_rest
    lpp_check_attached_leaf_slots_sound[OF covered]])
   (rule lpp_parameter_leaf_templates_ground[OF _]; use tracked in \<open>simp add: lpp_runtime_parameter_def\<close>)
next
 case False
 obtain x where output_eq: "output_value=LPIVar x"
  using caller_mode False by (auto simp: lpp_caller_output_mode_def)
 show ?thesis by (rule lpp_attached_parameter_copy_leaf_step[OF step[unfolded output_eq]
   head spine tracked finite_rest invariant[unfolded output_eq] covered])
qed

lemma lpp_caller_copy_head_finite_instance:
 fixes sigma rho :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_resolve (LPIFun p [input_value,parameter,output_value]) gs
   (Fun p [Fun nil [],Var n,Var n]) bs sigma rho"
 and spine: "lpp_finite_spine cons nil input_value spine_length"
 and tracked: "lpp_runtime_parameter initial_parameter parameter"
 shows "lpp_finite_term (lp_ieval (Fun p [Fun nil [],Var n,Var n]) rho)"
proof -
 have copied: "rho n= parameter"
  using mgu lpp_runtime_parameter_ground[OF tracked]
  by (auto simp: lpc_mgu_resolve_def lp_seg_ground_subst)
 have finite_parameter: "lpp_finite_term parameter"
  by (rule lpp_ground_finite_term[OF lpp_runtime_parameter_ground[OF tracked]])
 show ?thesis using finite_parameter by (simp add: copied)
qed

lemma lpp_attached_caller_copy_finite_step:
 fixes env :: "nat \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
 assumes step: "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCClause (LPCAtom (LPIFun p [input_value,parameter,output_value])#gs) c m,env)#saved)) event tt"
 and finite: "lpp_finite_execution
   (lpc_attach_answers rest ((LPCClause (LPCAtom (LPIFun p [input_value,parameter,output_value])#gs) c m,env)#saved))"
 and head: "fst (P!c)=Fun p [Fun nil [],Var n,Var n]"
 and spine: "lpp_finite_spine cons nil input_value spine_length"
 and tracked: "lpp_runtime_parameter initial_parameter parameter"
 shows "lpp_finite_execution tt"
proof (rule lpp_finite_base_answer_step[OF step finite])
 fix call pending clause mark ret alternatives sigma rho
 assume shape: "lpc_attach_answers rest ((LPCClause (LPCAtom (LPIFun p [input_value,parameter,output_value])#gs) c m,env)#saved)=
  (LPCClause (LPCAtom call#pending) clause mark,ret)#alternatives"
 and bound: "clause<length P"
 and mgu: "lpc_mgu_resolve call pending (fst (P!clause)) (snd (P!clause)) sigma rho"
 have actual: "call=LPIFun p [input_value,parameter,output_value]" "clause=c"
  using shape by (auto simp: lpc_attach_answers_def)
 show "lpp_finite_term (lp_ieval (fst (P!clause)) rho)"
  unfolding actual head by (rule lpp_caller_copy_head_finite_instance[OF mgu[unfolded actual head] spine tracked])
qed (auto simp: lpc_attach_answers_def)

lemma lpp_ground_caller_copy_backtrack:
 fixes env :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes bound: "c<length P"
 and head: "fst (P!c)=Fun p [Fun nil [],Var n,Var n]"
 and parameter: "lp_seg_ground parameter"
 and ground_output: "lp_seg_ground output_value"
 and mismatch: "output_value\<noteq>parameter"
 shows "lpc_answer_transition P
  ((LPCClause (LPCAtom (LPIFun p [input_value,parameter,output_value])#gs) c m,env)#saved)
  None saved"
proof (rule lpc_answer_transition.backtrack[OF bound])
 show "\<not>(\<exists>sigma :: string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm. \<exists>rho.
  lp_isubst (LPIFun p [input_value,parameter,output_value]) sigma=lp_ieval (fst (P!c)) rho)"
  using parameter ground_output mismatch by (auto simp: head lp_seg_ground_subst)
qed

ML \<open>
val checked = @{thms lpp_attached_ground_caller_copy_leaf_step lpp_attached_caller_copy_leaf_step
 lpp_caller_copy_head_finite_instance lpp_attached_caller_copy_finite_step lpp_ground_caller_copy_backtrack};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted attached caller copy" else ();
\<close>
end
