theory LP_Prolog_Checked_Acquired_Block
 imports LP_Prolog_Acquired_Joint_Witness_Product
begin

lemma lpp_checked_acquired_block:
 fixes SP :: "string lpp_success_clause list"
 and combined_env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_resolution_node T yes_facts no_facts fuel P Q nds states contexts Fs functors
   nd F a gs c mark active saved k l resolution_A next anchors bindings mode outputs incoming_context incoming_functors yes no"
 and matching: "lp_cut_check_match a (fst (P!c)) match_bindings"
 and acquired: "lpp_check_fresh_univ_clause (fst (P!c)) (snd (P!c)) x y z"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and free: "lpc_free_knowledge (set F) eta"
 and observed: "lpp_stable_context_holds operation SP incoming_context eta"
 and functor_facts: "list_all (lpp_functor_fact_holds names eta) incoming_functors"
 and helper_payload: "(\<lambda>slot. combined_env (Inl slot))=lpc_return_env active eta"
 and helper_saved: "lpc_reinterface (\<lambda>env slot. env (Inl slot)) joint_saved=lpc_return_eval eta saved"
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env slot. env (Inr slot))
    ((LPCClause (LPCAtom (lp_ieval a eta)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) c mark,combined_env)#joint_saved))) acquisition_event resolved"
 and swaps: "lpcl_swaps yes=[]"
 and target_shape: "states!lpcl_target yes=
   (LPCGoals (LPCAtom (Fun (LPCUser ''2:=..'')
     [input_template,Fun (LPCUser ''2:prolog_data_2e'') [Var output_name,Var output_args]])#source_goals),source_active)#source_saved"
 and incoming: "lpp_observer_invariant replacements specs rest
   ((LPCClause (LPCAtom (lp_ieval a eta)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) c mark,combined_env)#joint_saved)"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and ground: "\<And>v. v\<in>replacements \<Longrightarrow> vars_term v={}"
 and continuation: "source_goals\<noteq>[]"
 and actual: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain resolved event result"
 and program: "lp_cut_source_program P"
 and equality_rows: "\<And>i. i<length nds \<Longrightarrow>
   lpp_observer_continuing_equality_frame (states!i) \<Longrightarrow>
   lpp_check_observer_equality_row T fuel P Q nds states contexts Fs functors separation_contexts
    i (actions!i) (witnesses!i)"
 and normalization: "lpp_check_univ_evaluation_context T fs fuel Q nds states contexts functors Fs
   (nds!lpcl_target yes) (Fs!lpcl_target yes) (states!lpcl_target yes)
   (contexts!lpcl_target yes) (functors!lpcl_target yes)
   input_template (Fun (LPCUser ''2:prolog_data_2e'') [Var output_name,Var output_args]) source_goals source_active source_saved
   value_variable name_variable arguments_variable link"
 and separation_bound: "lpcl_target link<length separation_contexts"
 and separation_transport: "lpp_check_separation_transport
   [LPPSeparate (Fun (LPCUser ''2:prolog_data_2e'') [Var output_name,Var output_args])
    (Fun (LPCUser ''2:prolog_data_2e'') [Var name_variable,Var arguments_variable])]
   (separation_contexts!lpcl_target link) (lp_cut_instance_subst (lpcl_bindings link))"
 and free_coverage: "set (Fs!lpcl_target yes) \<subseteq> {output_name,output_args}"
 shows "acquisition_event=None \<and> event=None \<and> (result=[] \<or> (\<exists>final_joint target.
   result=lpc_attach_answers rest (lpc_reinterface (\<lambda>env slot. env (Inr slot)) final_joint) \<and>
   lpp_observer_invariant replacements specs rest final_joint \<and>
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],target)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functors
    (lpp_separation_node_conditions separation_contexts) (lpc_reinterface (\<lambda>env slot. env (Inl slot)) final_joint) target))"
proof -
 obtain sigma rho joint body_tail nu where
full_mgu: "lpc_mgu_resolve (lp_ieval a eta)
    (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs @
     map (lp_cut_map (\<lambda>t. lp_ieval t (\<lambda>slot. combined_env (Inr slot)))) rest)
    (fst (P!c)) (snd (P!c)) sigma rho"
 and resolved_shape: "resolved=lpc_attach_answers rest (lpc_reinterface (\<lambda>env slot. env (Inr slot)) joint)"
 and joint_shape: "joint=(LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t rho)) (snd (P!c)) @
     map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)),
     \<lambda>slot. lp_isubst (combined_env slot) sigma)#joint_saved"
 and prefix_mgu: "lpc_mgu_resolve (lp_ieval a eta) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)
     (fst (P!c)) (snd (P!c)) sigma rho"
 and helper_exact: "lpc_reinterface (\<lambda>env slot. env (Inl slot)) joint=lpc_return_eval (lp_cut_resolution_env k l eta sigma rho) ((LPCGoals next,outputs)#saved)"
 and body_shape: "snd (P!c)=LPCAtom (Fun (LPCUser ''2:=..'')
     [Var x,Fun (LPCUser ''2:prolog_data_2e'') [Var y,Var z]])#body_tail"
 and target_known: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target yes))) (lpcn_guards (nds!lpcl_target yes)) nu"
 and target_free: "lpc_free_knowledge (set (Fs!lpcl_target yes)) nu"
 and target_context: "lpp_stable_context_holds operation SP (contexts!lpcl_target yes) nu"
 and target_functors: "list_all (lpp_functor_fact_holds names nu) (functors!lpcl_target yes)"
 and edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],
    [(lpcn_pred (nds!lpcl_target yes),map nu (lpcn_vars (nds!lpcl_target yes)))])\<in>lp_ild Q"
 and coordinates: "lp_ieval input_template nu=rho x \<and> nu output_name=rho y \<and> nu output_args=rho z"
 and pending_exact: "(map (lp_cut_bind mark (\<lambda>t. lp_ieval t rho)) body_tail @
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma)) gs)=map (lp_cut_map (\<lambda>t. lp_ieval t nu)) source_goals"
 and payload_exact: "(\<lambda>slot. lp_isubst (lpc_return_env active eta slot) sigma)=lpc_return_env source_active nu \<and> lpc_return_eval eta saved=lpc_return_eval nu source_saved"
  using lpp_checked_attached_acquired_row[OF compatible transfer checked matching acquired known free observed
    functor_facts helper_payload helper_saved step swaps target_shape] by blast
 have silent: "acquisition_event=None"
  using lpp_checked_attached_acquired_row[OF compatible transfer checked matching acquired known free observed
    functor_facts helper_payload helper_saved step swaps target_shape] by blast
 let ?pending = "map (lp_cut_bind mark (\<lambda>t. lp_ieval t rho)) body_tail @
   map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma)) gs"
 have pending_shape: "?pending=map (lp_cut_bind mark (\<lambda>t. lp_ieval t rho)) body_tail @
   map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
  by (simp add: lp_cut_map_comp o_def)
 have tail: "?pending\<noteq>[]" using pending_exact continuation by simp
 have match_instance: "lp_ieval (fst (P!c)) (\<lambda>x. lp_ieval (lp_cut_match_subst match_bindings x) eta)=lp_ieval a eta"
  using matching by (simp add: lp_cut_check_match_def flip: lp_ieval_finite_subst)
 have input_coordinate: "lp_ieval input_template nu=rho x" and name_coordinate: "nu output_name=rho y"
 and args_coordinate: "nu output_args=rho z" using coordinates by auto
 have payload: "(\<lambda>slot. lp_isubst (combined_env (Inl slot)) sigma)=lpc_return_env source_active nu"
  using payload_exact helper_payload by (metis)
 have saved: "lpc_reinterface (\<lambda>env slot. env (Inl slot)) joint_saved=lpc_return_eval nu source_saved"
  using helper_saved payload_exact by simp
 have builtin: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env slot. env (Inr slot)) joint)) event result"
  using actual resolved_shape by simp
 have product: "event=None \<and> (result=[] \<or> (\<exists>final_joint target.
   result=lpc_attach_answers rest (lpc_reinterface (\<lambda>env slot. env (Inr slot)) final_joint) \<and>
   lpp_observer_invariant replacements specs rest final_joint \<and>
   ([(lpcn_pred (nds!lpcl_target yes),map nu (lpcn_vars (nds!lpcl_target yes)))],target)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functors
    (lpp_separation_node_conditions separation_contexts) (lpc_reinterface (\<lambda>env slot. env (Inl slot)) final_joint) target))"
  by (rule lpp_acquired_joint_witness_product[where SP=SP and eta=nu and pending="?pending" and rho=rho and sigma=sigma and x=x and y=y and z=z,
    OF acquired full_mgu match_instance incoming covered ground body_shape pending_shape tail joint_shape builtin
      program equality_rows compatible transfer normalization separation_bound separation_transport
      input_coordinate name_coordinate args_coordinate free_coverage refl target_known target_context target_functors
      payload pending_exact saved])
 have strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],target)\<in>(lp_ild Q)\<^sup>+"
  if "([(lpcn_pred (nds!lpcl_target yes),map nu (lpcn_vars (nds!lpcl_target yes)))],target)\<in>(lp_ild Q)\<^sup>+" for target
  using edge that by (meson r_into_trancl trancl_trans)
 show ?thesis using silent product strict by blast
qed

ML \<open>
val checked = @{thms lpp_checked_acquired_block};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted checked acquired block" else ();
val _ = writeln "CHECKED_ACQUIRED_BLOCK_KERNEL_CHECKED";
\<close>
end
