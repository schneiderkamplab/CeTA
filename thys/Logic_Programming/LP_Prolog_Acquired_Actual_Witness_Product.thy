theory LP_Prolog_Acquired_Actual_Witness_Product
 imports LP_Prolog_Acquired_Actual_Univ_Product LP_Prolog_Acquired_Univ_Witness_Product
begin

text \<open>Instantiate the helper representation using the acquired
normalization witness and compose its residual edge with the synchronized
product. Payload, pending goals and saved-frame correspondence remain explicit.\<close>

lemma lpp_acquired_actual_witness_product:
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
 and shape: "runtime=(LPCGoals (LPCUnify (rho x) (rho x)#
   LPCUnify (LPIFun (LPCUser ''2:prolog_data_2e'') [rho y,rho z])
    (lpp_argument_list (LPIFun (names f) []#ts))#pending),
    case_sum helper_env (\<lambda>slot. lp_isubst (combined_env (Inr slot)) sigma))#saved"
 and actual: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_attach_answers rest ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'')
     [rho x,LPIFun (LPCUser ''2:prolog_data_2e'') [rho y,rho z]])#pending),
     \<lambda>slot. lp_isubst (combined_env (Inr slot)) sigma)#
     lpc_reinterface (\<lambda>env slot. env (Inr slot)) saved)) event result"
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
 and helper_payload: "helper_env=lpc_return_env source_active eta"
 and helper_pending: "pending=map (lp_cut_map (\<lambda>t. lp_ieval t eta)) source_goals"
 and helper_saved: "lpc_reinterface (\<lambda>env slot. env (Inl slot)) saved=lpc_return_eval eta source_saved"
 shows "event=None \<and> (result=[] \<or> (\<exists>joint_result target.
   result=lpc_attach_answers rest (lpc_reinterface (\<lambda>env slot. env (Inr slot)) joint_result) \<and>
   lpp_observer_invariant A specs rest joint_result \<and>
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],target)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functors
    (lpp_separation_node_conditions separation_contexts) (lpc_reinterface (\<lambda>env slot. env (Inl slot)) joint_result) target))"
proof -
 have coverage: "lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functors
    (lpp_separation_node_conditions separation_contexts) lpp_finite_execution i"
  if bound: "i<length nds" and frame: "lpp_observer_continuing_equality_frame (lpc_return_eval nu (states!i))"
  for i and nu :: "string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm"
 proof -
  have shape: "lpp_observer_continuing_equality_frame (states!i)"
   using frame by (simp add: lpp_observer_continuing_equality_template)
  show ?thesis by (rule lpp_checked_observer_equality_row[OF compatible transfer equality_rows[OF bound shape]])
 qed

 let ?L = "\<lambda>env slot. env (Inl slot)"
 let ?start = "[(lpcn_pred nd,map eta (lpcn_vars nd))]"
 let ?C = "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functors
   (lpp_separation_node_conditions separation_contexts)"
 have finite_call: "lpp_finite_term a"
  using incoming by (auto simp: lpp_observer_invariant_def lpc_reinterface_def
   lpc_attach_answers_def lpp_finite_execution_def lpp_finite_goals_def)
 have input: "lp_ieval input_template eta=LPIFun f ts"
  using input_coordinate constructor by simp
 have helper_exact: "lpc_reinterface ?L runtime =
   ((LPCGoals (LPCUnify (LPIFun f ts) (LPIFun f ts)#
     LPCUnify (lp_ieval requested eta) (lpp_argument_list (LPIFun (names f) []#ts))#
     map (lp_cut_map (\<lambda>t. lp_ieval t eta)) source_goals),lpc_return_env source_active eta)#
     lpc_return_eval eta source_saved)"
  using helper_saved
  by (simp add: shape lpc_reinterface_def constructor helper_payload helper_pending requested
    name_coordinate args_coordinate)
 obtain nu where exact: "lpc_reinterface ?L runtime=lpc_return_eval nu (states!lpcl_target link)"
 and edge: "(?start,[(lpcn_pred (nds!lpcl_target link),map nu (lpcn_vars (nds!lpcl_target link)))])\<in>lp_ild Q"
 and target_known: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target link))) (lpcn_guards (nds!lpcl_target link)) nu"
 and target_free: "lpc_free_knowledge (set (Fs!lpcl_target link)) nu"
 and target_context: "lpp_stable_context_holds operation SP (contexts!lpcl_target link) nu"
 and target_functors: "list_all (lpp_functor_fact_holds names nu) (functors!lpcl_target link)"
 and target_separation: "lpp_separation_node_conditions separation_contexts (lpcl_target link) nu"
  using lpp_acquired_univ_normalization_witness[OF compatible transfer normalization separation_bound
   separation_transport acquired mgu matching finite_call input_coordinate name_coordinate args_coordinate
   free_coverage requested known context_held source_functors input]
  unfolding helper_exact by blast
 have bounds: "lpcl_target link<length nds" "lpcl_target link<length states"
   "lpcl_target link<length contexts" "lpcl_target link<length Fs" "lpcl_target link<length functors"
  using normalization by (auto simp: lpp_check_univ_evaluation_context_def lpp_check_evaluation_functor_link_def
   lpp_check_evaluation_link_def lpc_check_return_table_link_def lpc_check_return_link_def lpc_check_link_def)
 let ?subject = "[(lpcn_pred (nds!lpcl_target link),map nu (lpcn_vars (nds!lpcl_target link)))]"
 have represented: "?C (lpc_reinterface ?L runtime) ?subject"
  unfolding exact
  by (rule lpp_premised_functor_module_intro[where node_conditions="lpp_separation_node_conditions separation_contexts",
    OF bounds target_known target_free target_context target_separation target_functors])
 have product: "event=None \<and> (result=[] \<or> (\<exists>joint_result target.
   result=lpc_attach_answers rest (lpc_reinterface (\<lambda>env slot. env (Inr slot)) joint_result) \<and>
   lpp_observer_invariant A specs rest joint_result \<and>
   (?subject,target)\<in>(lp_ild Q)\<^sup>+ \<and> ?C (lpc_reinterface ?L joint_result) target))"
  by (rule lpp_acquired_actual_univ_product[where SP=SP and node_conditions="lpp_separation_node_conditions separation_contexts",
   OF acquired mgu matching incoming covered ground constructor body_shape pending_shape tail shape
     actual program coverage represented])
 have strict: "(?start,target)\<in>(lp_ild Q)\<^sup>+" if "(?subject,target)\<in>(lp_ild Q)\<^sup>+" for target
  using edge that by (meson r_into_trancl trancl_trans)
 show ?thesis using product strict by blast
qed

ML \<open>
val checked = @{thms lpp_acquired_actual_witness_product};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted acquired witness product" else ();
val _ = writeln "ACTUAL_WITNESS_PRODUCT_KERNEL_CHECKED";
\<close>
end
