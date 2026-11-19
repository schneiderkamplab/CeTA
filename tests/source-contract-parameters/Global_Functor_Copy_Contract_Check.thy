theory Global_Functor_Copy_Contract_Check
 imports Global_Copy_Boundary_Check
begin

text \<open>The retained copy choices have one frame and no pending goals.
Failure therefore empties this local helper. Success passes the actual cut-body
state and preserved joint invariant to an explicit continuation contract.\<close>

theorem global_functor_copy_answer_contract:
 fixes env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes invariant: "lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest oi hi
   [(LPCClause [LPCAtom (LPIFun p [input_value,parameter,output_value])] c m,env)]"
 and head: "fst (P!c) = Fun p [Fun (LPCUser ''0:prolog_data_5b5d'') [],Var n,Var n]"
 and body: "snd (P!c) = [LPCCut 0]"
 and spine: "lpp_finite_spine cons (LPCUser ''0:prolog_data_5b5d'') input_value spine_length"
 and tracked: "lpp_runtime_parameter initial_parameter parameter"
 and mode: "lpp_caller_output_mode output_value"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and effect: "lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter) initial_tree output_value"
 and observed: "observed_leaf_coordinate encode B parameter_tree parameter shadow"
 and functor_fact: "lpp_functor_observation names functor_value name_value input_value"
 and name_observed: "observed_leaf_coordinate encode C name_tree name_value name_shadow"
 and functor_observed: "observed_leaf_coordinate encode D functor_tree functor_value functor_shadow"
 and clause: "((source_symbol,map Var [x0,rn,x2,x3,x4,s0,sn,s2,s3,s4]),
   [(target_symbol,map Var [rn,x3,y,sn,s3,sy])]) \<in> set Q"
 and distinct: "distinct [x0,rn,x2,x3,x4,s0,sn,s2,s3,s4,y,sy]"
 and continuation: "\<And>sigma rho.
   lpc_mgu_resolve (LPIFun p [input_value,parameter,output_value]) []
    (Fun p [Fun (LPCUser ''0:prolog_data_5b5d'') [],Var n,Var n]) [LPCCut 0] sigma rho \<Longrightarrow>
   lp_isubst output_value sigma = parameter \<Longrightarrow>
   observed_leaf_coordinate encode (lpp_parameter_leaf_templates f g initial_parameter)
    initial_tree (lp_isubst output_value sigma) shadow \<Longrightarrow>
   lp_isubst name_value sigma = name_value \<Longrightarrow>
   lp_isubst functor_value sigma = functor_value \<Longrightarrow>
   observed_leaf_coordinate encode C name_tree (lp_isubst name_value sigma) name_shadow \<Longrightarrow>
   observed_leaf_coordinate encode D functor_tree (lp_isubst functor_value sigma) functor_shadow \<Longrightarrow>
   lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest oi hi
    [(LPCGoals [LPCCut m],\<lambda>x. lp_isubst (env x) sigma)] \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>e x. e (Inr x))
     [(LPCGoals [LPCCut m],\<lambda>x. lp_isubst (env x) sigma)])) (lp_ild Q)
    [(target_symbol,[parameter,name_value,functor_value,shadow,name_shadow,functor_shadow])] returned"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>e x. e (Inr x))
    [(LPCClause [LPCAtom (LPIFun p [input_value,parameter,output_value])] c m,env)])) (lp_ild Q)
   [(source_symbol,[input_value,parameter,output_value,name_value,functor_value,input_shadow,shadow,output_shadow,name_shadow,functor_shadow])] returned"
proof -
 let ?runtime = "[(LPCClause [LPCAtom (LPIFun p [input_value,parameter,output_value])] c m,env)]"
 let ?T = "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain"
 let ?R = "\<lambda>e x. e (Inr x)"
 let ?start = "[(source_symbol,[input_value,parameter,output_value,name_value,functor_value,input_shadow,shadow,output_shadow,name_shadow,functor_shadow])]"
 let ?finish = "[(target_symbol,[parameter,name_value,functor_value,shadow,name_shadow,functor_shadow])]"
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
      (Fun p [Fun (LPCUser ''0:prolog_data_5b5d'') [],Var n,Var n]) [LPCCut 0] sigma rho"
    and child_shape: "child = [(LPCGoals [LPCCut m],\<lambda>x. lp_isubst (env x) sigma)]"
    using base False head body by (cases rule: lpc_answer_transition.cases) auto
   have copied: "lp_isubst output_value sigma = parameter \<and>
    observed_leaf_coordinate encode (lpp_parameter_leaf_templates f g initial_parameter)
     initial_tree (lp_isubst output_value sigma) shadow"
    using copy_resolution_reuses_observation[OF mgu spine tracked mode _ effect observed]
    by (auto simp: lpp_finite_goals_def)
   have empty: "input_value = LPIFun (LPCUser ''0:prolog_data_5b5d'') []"
    by (rule lpp_parameter_copy_head_input[OF spine mgu])
   obtain ctor where scalar: "functor_value = LPIFun ctor []"
    and named: "name_value = LPIFun (names ctor) []"
    using copy_empty_arguments_functor[OF functor_fact[unfolded empty]] by blast
   have fixed: "lp_isubst name_value sigma = name_value" "lp_isubst functor_value sigma = functor_value"
    by (simp_all add: scalar named)
   have observations: "observed_leaf_coordinate encode C name_tree (lp_isubst name_value sigma) name_shadow"
    "observed_leaf_coordinate encode D functor_tree (lp_isubst functor_value sigma) functor_shadow"
    using name_observed functor_observed fixed by simp_all
   have path: "(?start,?finish) \<in> (lp_ild Q)\<^sup>+"
    using copy_ten_to_six_global_step[OF clause distinct] by (rule r_into_trancl)
   have lower: "lp_answer_contract ?T (lpc_attach_answers rest (lpc_reinterface ?R child)) (lp_ild Q) ?finish returned"
    unfolding child_shape using continuation[OF mgu] copied fixed observations child_inv[unfolded child_shape] by blast
   show ?thesis unfolding actual
    by (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF path] lower])
  qed
  show "(\<forall>rho. event = Some rho \<longrightarrow> (?start,returned rho) \<in> (lp_ild Q)\<^sup>*) \<and>
    lp_answer_contract ?T result (lp_ild Q) ?start returned"
   using silent child_contract by simp
 qed
qed

theorem global_functor_copy_caller_contract:
 fixes env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes invariant: "lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest oi hi
   [(LPCClause [LPCAtom (LPIFun p [input_value,parameter,output_value])] c m,env)]"
 and head: "fst (P!c) = Fun p [Fun (LPCUser ''0:prolog_data_5b5d'') [],Var n,Var n]"
 and body: "snd (P!c) = [LPCCut 0]"
 and spine: "lpp_finite_spine cons (LPCUser ''0:prolog_data_5b5d'') input_value spine_length"
 and tracked: "lpp_runtime_parameter initial_parameter parameter"
 and mode: "lpp_caller_output_mode output_value"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and effect: "lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter) initial_tree output_value"
 and observed: "observed_leaf_coordinate encode B parameter_tree parameter shadow"
 and functor_fact: "lpp_functor_observation names functor_value name_value input_value"
 and name_observed: "observed_leaf_coordinate encode C name_tree name_value name_shadow"
 and functor_observed: "observed_leaf_coordinate encode D functor_tree functor_value functor_shadow"
 and clause: "((source_symbol,map Var [x0,rn,x2,x3,x4,s0,sn,s2,s3,s4]),
   [(target_symbol,map Var [rn,x3,y,sn,s3,sy])]) \<in> set Q"
 and distinct: "distinct [x0,rn,x2,x3,x4,s0,sn,s2,s3,s4,y,sy]"
 and helper_coordinate: "env (Inl oi) = output_value"
 and caller: "\<And>rho. rho hi = parameter \<Longrightarrow>
   lpp_runtime_parameter initial_parameter (rho hi) \<Longrightarrow>
   observed_leaf_coordinate encode (lpp_parameter_leaf_templates f g initial_parameter)
    initial_tree (rho hi) shadow \<Longrightarrow>
   list_all (\<lambda>(slot,tree). lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter) tree (rho slot)) specs \<Longrightarrow>
   lpp_finite_execution [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) rest),rho)] \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) rest),rho)] (lp_ild Q)
    [(target_symbol,[parameter,name_value,functor_value,shadow,name_shadow,functor_shadow])] returned"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>e x. e (Inr x))
    [(LPCClause [LPCAtom (LPIFun p [input_value,parameter,output_value])] c m,env)])) (lp_ild Q)
   [(source_symbol,[input_value,parameter,output_value,name_value,functor_value,input_shadow,shadow,output_shadow,name_shadow,functor_shadow])] returned"

proof (rule global_functor_copy_answer_contract[OF invariant head body spine tracked mode covered effect observed functor_fact name_observed functor_observed clause distinct])
 fix sigma rho
 assume actual: "lpc_mgu_resolve (LPIFun p [input_value,parameter,output_value]) []
    (Fun p [Fun (LPCUser ''0:prolog_data_5b5d'') [],Var n,Var n]) [LPCCut 0] sigma rho"
 and copied: "lp_isubst output_value sigma = parameter"
 and output_observed: "observed_leaf_coordinate encode (lpp_parameter_leaf_templates f g initial_parameter)
    initial_tree (lp_isubst output_value sigma) shadow"
 and fixed_name: "lp_isubst name_value sigma = name_value"
 and fixed_functor: "lp_isubst functor_value sigma = functor_value"
 and name_obs: "observed_leaf_coordinate encode C name_tree (lp_isubst name_value sigma) name_shadow"
 and functor_obs: "observed_leaf_coordinate encode D functor_tree (lp_isubst functor_value sigma) functor_shadow"
 and child_inv: "lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest oi hi
    [(LPCGoals [LPCCut m],\<lambda>x. lp_isubst (env x) sigma)]"
 have helper: "(\<lambda>x. lp_isubst (env x) sigma) (Inl oi) = parameter"
  using copied helper_coordinate by simp
 show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>e x. e (Inr x))
     [(LPCGoals [LPCCut m],\<lambda>x. lp_isubst (env x) sigma)])) (lp_ild Q)
    [(target_symbol,[parameter,name_value,functor_value,shadow,name_shadow,functor_shadow])] returned"
 proof (rule tracked_copy_cut_return[OF child_inv helper tracked])
  fix caller_env
  assume value_eq: "caller_env hi = parameter"
  and caller_tracked: "lpp_runtime_parameter initial_parameter (caller_env hi)"
  and leaf: "list_all (\<lambda>(slot,tree). lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter) tree (caller_env slot)) specs"
  and finite: "lpp_finite_execution [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x caller_env)) rest),caller_env)]"
  have obs: "observed_leaf_coordinate encode (lpp_parameter_leaf_templates f g initial_parameter)
    initial_tree (caller_env hi) shadow" using output_observed copied value_eq by simp
  show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x caller_env)) rest),caller_env)] (lp_ild Q)
    [(target_symbol,[parameter,name_value,functor_value,shadow,name_shadow,functor_shadow])] returned"
   by (rule caller[OF value_eq caller_tracked obs leaf finite])
 qed
qed

ML \<open>
val checked = @{thms global_functor_copy_answer_contract global_functor_copy_caller_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted copy contract" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-global-functor-copy-contract/kernel-receipt.txt")
 ("Kernel checked; no skips or oracles. Entry theorem exposes cut continuation; composed theorem requires caller contract.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "GLOBAL_FUNCTOR_COPY_CONTRACT_KERNEL_CHECKED";
\<close>
end
