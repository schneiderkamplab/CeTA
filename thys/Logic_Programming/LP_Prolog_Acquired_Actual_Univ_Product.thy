theory LP_Prolog_Acquired_Actual_Univ_Product
 imports LP_Prolog_Attached_Univ_Actual_Path
begin

lemma lpp_acquired_actual_univ_product:
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
 and coverage: "\<And>i (eta :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). i<length nds \<Longrightarrow>
   lpp_observer_continuing_equality_frame (lpc_return_eval eta (states!i)) \<Longrightarrow>
   lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functors
    node_conditions lpp_finite_execution i"
 and represented: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functors
   node_conditions (lpc_reinterface (\<lambda>env slot. env (Inl slot)) runtime) subject"
 shows "event=None \<and> (result=[] \<or> (\<exists>joint_result target.
   result=lpc_attach_answers rest (lpc_reinterface (\<lambda>env slot. env (Inr slot)) joint_result) \<and>
   lpp_observer_invariant A specs rest joint_result \<and>
   (subject,target)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functors
    node_conditions (lpc_reinterface (\<lambda>env slot. env (Inl slot)) joint_result) target))"
proof -
 let ?R = "\<lambda>env slot. env (Inr slot)"
 have path: "event=None \<and> (result=[] \<or> (\<exists>middle.
   lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
    (lpc_attach_answers rest (lpc_reinterface ?R runtime)) None middle \<and>
   lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain middle None result))"
  using lpp_attached_univ_actual_path[OF actual[unfolded constructor]]
  by (simp add: shape constructor lpc_reinterface_def)
 have finish: "\<exists>joint_result target.
   result=lpc_attach_answers rest (lpc_reinterface ?R joint_result) \<and>
   lpp_observer_invariant A specs rest joint_result \<and>
   (subject,target)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functors
    node_conditions (lpc_reinterface (\<lambda>env slot. env (Inl slot)) joint_result) target"
  if nonempty: "result\<noteq>[]"
 proof -
  obtain middle where first: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
    (lpc_attach_answers rest (lpc_reinterface ?R runtime)) None middle"
   and second: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain middle None result"
   using path nonempty by blast
  show ?thesis using lpp_acquired_normalized_univ_product[where SP=SP and node_conditions=node_conditions,
    OF acquired mgu matching incoming covered ground constructor body_shape pending_shape tail shape
      first second program coverage represented] by simp
 qed
 show ?thesis using path finish by blast
qed

ML \<open>
val checked = @{thms lpp_acquired_actual_univ_product};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted actual univ product" else ();
val _ = writeln "ACTUAL_UNIV_PRODUCT_CHECKED";
\<close>
end
