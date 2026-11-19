theory Global_Copy_Contract_Check
 imports Global_Copy_Context_Check
begin

text \<open>The retained copy choices have one frame and no pending goals.
Failure therefore empties this local helper. Success passes the actual cut-body
state and preserved joint invariant to an explicit continuation contract.\<close>

theorem global_simple_copy_answer_contract:
 fixes env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes invariant: "lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest oi hi
   [(LPCClause [LPCAtom (LPIFun p [input_value,parameter,output_value])] c m,env)]"
 and head: "fst (P!c) = Fun p [Fun nil [],Var n,Var n]"
 and body: "snd (P!c) = [LPCCut 0]"
 and spine: "lpp_finite_spine cons nil input_value spine_length"
 and tracked: "lpp_runtime_parameter initial_parameter parameter"
 and mode: "lpp_caller_output_mode output_value"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and effect: "lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter) initial_tree output_value"
 and observed: "observed_leaf_coordinate encode B parameter_tree parameter shadow"
 and clause: "((source_symbol,map Var [x0,x1,x2,s0,sn,s2]),[(target_symbol,map Var [rn,sn])]) \<in> set Q"
 and distinct: "distinct [x0,x1,x2,s0,sn,s2,rn]"
 and continuation: "\<And>sigma rho.
   lpc_mgu_resolve (LPIFun p [input_value,parameter,output_value]) []
    (Fun p [Fun nil [],Var n,Var n]) [LPCCut 0] sigma rho \<Longrightarrow>
   lp_isubst output_value sigma = parameter \<Longrightarrow>
   observed_leaf_coordinate encode (lpp_parameter_leaf_templates f g initial_parameter)
    initial_tree (lp_isubst output_value sigma) shadow \<Longrightarrow>
   lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest oi hi
    [(LPCGoals [LPCCut m],\<lambda>x. lp_isubst (env x) sigma)] \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>e x. e (Inr x))
     [(LPCGoals [LPCCut m],\<lambda>x. lp_isubst (env x) sigma)])) (lp_ild Q)
    [(target_symbol,[parameter,shadow])] returned"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>e x. e (Inr x))
    [(LPCClause [LPCAtom (LPIFun p [input_value,parameter,output_value])] c m,env)])) (lp_ild Q)
   [(source_symbol,[input_value,parameter,output_value,input_shadow,shadow,output_shadow])] returned"
proof -
 let ?runtime = "[(LPCClause [LPCAtom (LPIFun p [input_value,parameter,output_value])] c m,env)]"
 let ?T = "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain"
 let ?R = "\<lambda>e x. e (Inr x)"
 let ?start = "[(source_symbol,[input_value,parameter,output_value,input_shadow,shadow,output_shadow])]"
 let ?finish = "[(target_symbol,[parameter,shadow])]"
 show ?thesis
 proof (rule lp_answer_contract_intro)
  fix event result
  assume step: "?T (lpc_attach_answers rest (lpc_reinterface ?R ?runtime)) event result"
  obtain child where silent: "event = None" and joint: "?T ?runtime None child"
   and actual: "result = lpc_attach_answers rest (lpc_reinterface ?R child)"
   and child_inv: "lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest oi hi child"
   using copy_actual_step_preserves_observer[OF refl invariant head spine tracked mode covered step] by blast
  have base: "lpc_answer_transition P ?runtime None child"
   using joint by (auto intro: lpp_observer_clause_base)
  have child_contract: "lp_answer_contract ?T result (lp_ild Q) ?start returned"
  proof (cases "child = []")
   case True
   have empty: "result = []" using actual True by (simp add: lpc_attach_answers_def lpc_reinterface_def)
   show ?thesis unfolding empty by (rule lpp_domain_contract_singletons) simp
  next
   case False
   obtain sigma :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm" and rho where
    mgu: "lpc_mgu_resolve (LPIFun p [input_value,parameter,output_value]) []
      (Fun p [Fun nil [],Var n,Var n]) [LPCCut 0] sigma rho"
    and child_shape: "child = [(LPCGoals [LPCCut m],\<lambda>x. lp_isubst (env x) sigma)]"
    using base False head body by (cases rule: lpc_answer_transition.cases) auto
   have copied: "lp_isubst output_value sigma = parameter \<and>
    observed_leaf_coordinate encode (lpp_parameter_leaf_templates f g initial_parameter)
     initial_tree (lp_isubst output_value sigma) shadow"
    using copy_resolution_reuses_observation[OF mgu spine tracked mode _ effect observed]
    by (auto simp: lpp_finite_goals_def)
   have path: "(?start,?finish) \<in> (lp_ild Q)\<^sup>+"
    using copy_six_to_two_global_step[OF clause distinct] by (rule r_into_trancl)
   have lower: "lp_answer_contract ?T (lpc_attach_answers rest (lpc_reinterface ?R child)) (lp_ild Q) ?finish returned"
    unfolding child_shape using continuation[OF mgu] copied child_inv[unfolded child_shape] by blast
   show ?thesis unfolding actual
    by (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF path] lower])
  qed
  show "(\<forall>rho. event = Some rho \<longrightarrow> (?start,returned rho) \<in> (lp_ild Q)\<^sup>*) \<and>
    lp_answer_contract ?T result (lp_ild Q) ?start returned"
   using silent child_contract by simp
 qed
qed

ML \<open>
val checked = @{thms global_simple_copy_answer_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted copy contract" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-global-copy-contract/kernel-receipt.txt")
 ("Kernel checked; no skips or oracles. Successful cut continuation remains explicit.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "GLOBAL_COPY_CONTRACT_KERNEL_CHECKED";
\<close>
end
