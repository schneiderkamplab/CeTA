theory LP_Prolog_Acquired_Joint_Witness_Product
 imports LP_Prolog_Acquired_Actual_Witness_Product LP_Prolog_Acquired_Univ_Joint_Row
begin

lemma lpp_acquired_joint_constructor_product:
 fixes SP :: "string lpp_success_clause list"
 and combined_env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes acquired: "lpp_check_fresh_univ_clause h bs x y z"
 and mgu: "lpc_mgu_resolve a
   (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t (\<lambda>slot. combined_env (Inr slot)))) rest)
   h bs sigma rho"
 and matching: "lp_ieval h witness=a"
 and incoming: "lpp_observer_invariant A specs rest
   ((LPCClause (LPCAtom a#gs) c mark,combined_env)#saved)"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and ground: "\<And>v. v\<in>A \<Longrightarrow> vars_term v={}"
 and constructor: "rho x=LPIFun f ts"
 and body_shape: "bs=LPCAtom (Fun (LPCUser ''2:=..'')
   [Var x,Fun (LPCUser ''2:prolog_data_2e'') [Var y,Var z]])#body_tail"
 and pending_shape: "pending=map (lp_cut_bind mark (\<lambda>t. lp_ieval t rho)) body_tail @
   map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs"
 and tail: "pending\<noteq>[]"
 and joint_shape: "joint=(LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t rho)) bs @
   map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs),
    \<lambda>slot. lp_isubst (combined_env slot) sigma)#saved"
 and actual: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env slot. env (Inr slot)) joint)) event result"
 and program: "lp_cut_source_program P"
 and equality_rows: "\<And>i. i<length nds \<Longrightarrow>
   lpp_observer_continuing_equality_frame (states!i) \<Longrightarrow>
   lpp_check_observer_equality_row T fuel P Q nds states contexts Fs functors separation_contexts
    i (actions!i) (witnesses!i)"
 and compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and normalization: "lpp_check_univ_evaluation_context T fs fuel Q nds states contexts functors Fs nd F ss source_context source_functors
   input_template requested source_goals source_active source_saved value_variable name_variable arguments_variable link"
 and separation_bound: "lpcl_target link<length separation_contexts"
 and separation_transport: "lpp_check_separation_transport
   [LPPSeparate (Fun (LPCUser ''2:prolog_data_2e'') [Var output_name,Var output_args])
    (Fun (LPCUser ''2:prolog_data_2e'') [Var name_variable,Var arguments_variable])]
   (separation_contexts!lpcl_target link) (lp_cut_instance_subst (lpcl_bindings link))"
 and input_coordinate: "lp_ieval input_template eta=rho x"
 and name_coordinate: "eta output_name=rho y"
 and args_coordinate: "eta output_args=rho z"
 and free_coverage: "set F \<subseteq> {output_name,output_args}"
 and requested: "requested=Fun (LPCUser ''2:prolog_data_2e'') [Var output_name,Var output_args]"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and context_held: "lpp_stable_context_holds operation SP source_context eta"
 and source_functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
 and helper_payload: "(\<lambda>slot. lp_isubst (combined_env (Inl slot)) sigma)=lpc_return_env source_active eta"
 and helper_pending: "pending=map (lp_cut_map (\<lambda>t. lp_ieval t eta)) source_goals"
 and helper_saved: "lpc_reinterface (\<lambda>env slot. env (Inl slot)) saved=lpc_return_eval eta source_saved"
 shows "event=None \<and> (result=[] \<or> (\<exists>joint_result target.
   result=lpc_attach_answers rest (lpc_reinterface (\<lambda>env slot. env (Inr slot)) joint_result) \<and>
   lpp_observer_invariant A specs rest joint_result \<and>
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],target)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functors
    (lpp_separation_node_conditions separation_contexts) (lpc_reinterface (\<lambda>env slot. env (Inl slot)) joint_result) target))"
proof -
 let ?helper = "\<lambda>slot. lp_isubst (combined_env (Inl slot)) sigma"
 let ?runtime = "(LPCGoals (LPCUnify (rho x) (rho x)#
   LPCUnify (LPIFun (LPCUser ''2:prolog_data_2e'') [rho y,rho z])
    (lpp_argument_list (LPIFun (names f) []#ts))#pending),
    case_sum ?helper (\<lambda>slot. lp_isubst (combined_env (Inr slot)) sigma))#saved"
 have selected: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_attach_answers rest ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'')
     [rho x,LPIFun (LPCUser ''2:prolog_data_2e'') [rho y,rho z]])#pending),
     \<lambda>slot. lp_isubst (combined_env (Inr slot)) sigma)#
     lpc_reinterface (\<lambda>env slot. env (Inr slot)) saved)) event result"
  using actual by (simp add: joint_shape body_shape pending_shape lpc_reinterface_def)
 show ?thesis
  by (rule lpp_acquired_actual_witness_product[where runtime="?runtime" and helper_env="?helper" and SP=SP,
    OF acquired mgu matching incoming covered ground constructor body_shape pending_shape tail refl
     selected program equality_rows compatible transfer normalization separation_bound separation_transport
     input_coordinate name_coordinate args_coordinate free_coverage requested known context_held source_functors
     helper_payload helper_pending helper_saved])
qed

lemma lpp_acquired_joint_witness_product:
 fixes SP :: "string lpp_success_clause list"
 and combined_env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes acquired: "lpp_check_fresh_univ_clause h bs x y z"
 and mgu: "lpc_mgu_resolve a
   (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t (\<lambda>slot. combined_env (Inr slot)))) rest)
   h bs sigma rho"
 and matching: "lp_ieval h witness=a"
 and incoming: "lpp_observer_invariant A specs rest
   ((LPCClause (LPCAtom a#gs) c mark,combined_env)#saved)"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and ground: "\<And>v. v\<in>A \<Longrightarrow> vars_term v={}"
 and body_shape: "bs=LPCAtom (Fun (LPCUser ''2:=..'')
   [Var x,Fun (LPCUser ''2:prolog_data_2e'') [Var y,Var z]])#body_tail"
 and pending_shape: "pending=map (lp_cut_bind mark (\<lambda>t. lp_ieval t rho)) body_tail @
   map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs"
 and tail: "pending\<noteq>[]"
 and joint_shape: "joint=(LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t rho)) bs @
   map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs),
    \<lambda>slot. lp_isubst (combined_env slot) sigma)#saved"
 and actual: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env slot. env (Inr slot)) joint)) event result"
 and program: "lp_cut_source_program P"
 and equality_rows: "\<And>i. i<length nds \<Longrightarrow>
   lpp_observer_continuing_equality_frame (states!i) \<Longrightarrow>
   lpp_check_observer_equality_row T fuel P Q nds states contexts Fs functors separation_contexts
    i (actions!i) (witnesses!i)"
 and compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and normalization: "lpp_check_univ_evaluation_context T fs fuel Q nds states contexts functors Fs nd F ss source_context source_functors
   input_template requested source_goals source_active source_saved value_variable name_variable arguments_variable link"
 and separation_bound: "lpcl_target link<length separation_contexts"
 and separation_transport: "lpp_check_separation_transport
   [LPPSeparate (Fun (LPCUser ''2:prolog_data_2e'') [Var output_name,Var output_args])
    (Fun (LPCUser ''2:prolog_data_2e'') [Var name_variable,Var arguments_variable])]
   (separation_contexts!lpcl_target link) (lp_cut_instance_subst (lpcl_bindings link))"
 and input_coordinate: "lp_ieval input_template eta=rho x"
 and name_coordinate: "eta output_name=rho y"
 and args_coordinate: "eta output_args=rho z"
 and free_coverage: "set F \<subseteq> {output_name,output_args}"
 and requested: "requested=Fun (LPCUser ''2:prolog_data_2e'') [Var output_name,Var output_args]"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and context_held: "lpp_stable_context_holds operation SP source_context eta"
 and source_functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
 and helper_payload: "(\<lambda>slot. lp_isubst (combined_env (Inl slot)) sigma)=lpc_return_env source_active eta"
 and helper_pending: "pending=map (lp_cut_map (\<lambda>t. lp_ieval t eta)) source_goals"
 and helper_saved: "lpc_reinterface (\<lambda>env slot. env (Inl slot)) saved=lpc_return_eval eta source_saved"
 shows "event=None \<and> (result=[] \<or> (\<exists>joint_result target.
   result=lpc_attach_answers rest (lpc_reinterface (\<lambda>env slot. env (Inr slot)) joint_result) \<and>
   lpp_observer_invariant A specs rest joint_result \<and>
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],target)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functors
    (lpp_separation_node_conditions separation_contexts) (lpc_reinterface (\<lambda>env slot. env (Inl slot)) joint_result) target))"
proof (cases "rho x")
 case (LPIFun f ts)
 show ?thesis
  by (rule lpp_acquired_joint_constructor_product[where f=f and ts=ts and SP=SP,
   OF acquired mgu matching incoming covered ground LPIFun body_shape pending_shape tail joint_shape actual
    program equality_rows compatible transfer normalization separation_bound separation_transport
    input_coordinate name_coordinate args_coordinate free_coverage requested known context_held source_functors
    helper_payload helper_pending helper_saved])
next
 case (LPIVar v)
 have finite_call: "lpp_finite_term a"
  using incoming by (auto simp: lpp_observer_invariant_def lpc_reinterface_def
   lpc_attach_answers_def lpp_finite_execution_def lpp_finite_goals_def)
 have finite_head: "lpp_finite_term (lp_ieval h rho)"
  by (rule lpp_matching_head_finite_instance[OF mgu matching finite_call])
 have finite_subst: "lpp_finite_term (lp_isubst a sigma)"
  using finite_head mgu by (simp add: lpc_mgu_resolve_def)
 obtain u where fresh_name: "rho y=LPIVar u"
  using lpp_check_fresh_univ_clause_sound[OF acquired mgu finite_subst] by blast
 have domain: "lpp_univ_view_domain (rho x) (LPIFun (LPCUser ''2:prolog_data_2e'') [rho y,rho z])"
  by (simp add: fresh_name lpp_univ_free_name_domain)
 have selected: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'')
     [rho x,LPIFun (LPCUser ''2:prolog_data_2e'') [rho y,rho z]])#
      (pending @ map (lp_cut_map (\<lambda>t. lp_ieval t (\<lambda>slot. lp_isubst (combined_env (Inr slot)) sigma))) rest)),
     \<lambda>slot. lp_isubst (combined_env (Inr slot)) sigma)#
     lpc_attach_answers rest (lpc_reinterface (\<lambda>env slot. env (Inr slot)) saved)) event result"
  using actual by (simp add: joint_shape body_shape pending_shape lpc_reinterface_def lpc_attach_answers_def)
 have stopped: "event=None \<and> result=[]"
  using lpp_observer_univ_actual_normalized_path[OF domain selected] LPIVar by simp
 show ?thesis using stopped by simp
qed

ML \<open>
val checked = @{thms lpp_acquired_joint_constructor_product lpp_acquired_joint_witness_product};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted joint witness product" else ();
val _ = writeln "JOINT_WITNESS_PRODUCT_CHECKED";
\<close>
end
