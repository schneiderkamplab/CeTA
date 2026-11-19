theory Global_Cons_Contract_Check
 imports Global_Cons_Context_Check
begin

theorem global_simple_cons_answer_contract:
 fixes k :: nat
 and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 and successor_env
 and env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes invariant: "lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest oi hi [(LPCClause [LPCAtom (LPIFun p [(eta input_slot),(eta parameter_slot),(eta output_slot)])] c m,env)]"
 and head: "fst (P!c) = Fun p [Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y],Var n,Var out]"
 and body: "snd (P!c) = bs"
 and spine: "lpp_list_length (eta input_slot) spine_length"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and distinct: "distinct [x,y,n,out]"
 and tracked: "lpp_runtime_parameter initial_parameter (eta parameter_slot)"
 and input_observed: "observed_leaf_coordinate encode C input_tree (eta input_slot) input_shadow"
 and parameter_observed: "observed_leaf_coordinate encode A parameter_tree (eta parameter_slot) parameter_shadow"
 and output_observed: "observed_leaf_coordinate encode B output_tree (eta output_slot) output_shadow"
 and head_map: "lpp_check_clause_coordinate l (Var x) target_head bindings"
 and parameter_map: "lpp_check_clause_coordinate l (Var n) target_parameter bindings"
 and tail_map: "lpp_check_clause_coordinate l (Var y) target_tail bindings"
 and output_map: "lpp_check_clause_coordinate l (Var out) target_output bindings"
 and fresh_map: "lpp_check_body_output
  (Fun p [Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y],Var n,Var out]) bs l body_variable target_fresh bindings"
 and clause: "((source_symbol,[Var r0,Var r1,Var r2,
  Fun (encode LPPStructureNode) [Fun (encode (LPPStructureLabel (LPCUser ''2:prolog_data_2e''))) [],
   Fun (encode LPPStructureCons) [Var sh,Fun (encode LPPStructureCons) [Var st,Fun (encode LPPStructureNil) []]]],
  Var sp,Var so]),[(target_symbol,map Var [rh,rn,rf,rt,ro,sh,sp,sf,st,so])]) \<in> set Q"
 and residual_distinct: "distinct [r0,r1,r2,sh,st,sp,so,rh,rn,rf,rt,ro,sf]"

 defines successor_env_def: "successor_env \<equiv> \<lambda>sigma rho x. lp_ieval (lp_cut_instance_subst bindings x)
  (lp_cut_resolution_env k l eta sigma rho)"
 assumes continuation: "\<And>sigma rho head_tree tail_tree head_shadow tail_shadow.
  lpc_mgu_resolve (LPIFun p [(eta input_slot),(eta parameter_slot),(eta output_slot)]) [] (Fun p [Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y],Var n,Var out]) bs sigma rho \<Longrightarrow>
  lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest oi hi [(LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) bs),\<lambda>x. lp_isubst (env x) sigma)] \<Longrightarrow>
  lp_ieval target_parameter (successor_env sigma rho) = (eta parameter_slot) \<and>
  lpp_runtime_parameter initial_parameter (lp_ieval target_parameter (successor_env sigma rho)) \<and>
  observed_leaf_coordinate encode C head_tree (lp_ieval target_head (successor_env sigma rho)) head_shadow \<and>
  observed_leaf_coordinate encode A parameter_tree (lp_ieval target_parameter (successor_env sigma rho)) parameter_shadow \<and>
  observed_leaf_coordinate encode C (Fun (Inr ()) []) (lp_ieval target_fresh (successor_env sigma rho)) ((LPIFun (encode LPPStructureLeaf) [] :: (string lp_cut_symbol,string) lp_iterm)) \<and>
  observed_leaf_coordinate encode C tail_tree (lp_ieval target_tail (successor_env sigma rho)) tail_shadow \<and>
  observed_leaf_coordinate encode B output_tree (lp_ieval target_output (successor_env sigma rho)) output_shadow \<Longrightarrow>
  lpc_return_env [Fun (LPCUser ''2:prolog_data_2e'') [target_head,target_tail],target_parameter,target_output] (successor_env sigma rho) =
   (\<lambda>i. lp_isubst (lpc_return_env [Var input_slot,Var parameter_slot,Var output_slot] eta i) sigma) \<and>
  lpp_runtime_parameter initial_parameter (lp_ieval target_parameter (successor_env sigma rho)) \<and>
  lpp_stable_context_holds operation SP
   ([],[LPPSOpaque target_parameter],[LPPOGround target_parameter,
    LPPOShape lpp_spine_grammar (LPReturnShape 0)
     (Fun (LPCUser ''2:prolog_data_2e'') [target_head,target_tail])]) (successor_env sigma rho) \<and>
  (\<exists>v. lp_ieval target_fresh (successor_env sigma rho) = LPIVar v) \<Longrightarrow>
  lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain) (lpc_attach_answers rest (lpc_reinterface (\<lambda>e x. e (Inr x)) [(LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) bs),\<lambda>x. lp_isubst (env x) sigma)])) (lp_ild Q) [(target_symbol,[lp_ieval target_head (successor_env sigma rho),lp_ieval target_parameter (successor_env sigma rho),lp_ieval target_fresh (successor_env sigma rho),
 lp_ieval target_tail (successor_env sigma rho),lp_ieval target_output (successor_env sigma rho),
 head_shadow,parameter_shadow,(LPIFun (encode LPPStructureLeaf) [] :: (string lp_cut_symbol,string) lp_iterm),tail_shadow,output_shadow])] returned"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain) (lpc_attach_answers rest (lpc_reinterface (\<lambda>e x. e (Inr x)) [(LPCClause [LPCAtom (LPIFun p [(eta input_slot),(eta parameter_slot),(eta output_slot)])] c m,env)])) (lp_ild Q) [(source_symbol,[(eta input_slot),(eta parameter_slot),(eta output_slot),input_shadow,parameter_shadow,output_shadow])] returned"
proof -
 let ?runtime = "[(LPCClause [LPCAtom (LPIFun p [(eta input_slot),(eta parameter_slot),(eta output_slot)])] c m,env)]"
 let ?T = "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain"
 let ?R = "\<lambda>e x. e (Inr x)"
 let ?start = "[(source_symbol,[(eta input_slot),(eta parameter_slot),(eta output_slot),input_shadow,parameter_shadow,output_shadow])]"
 have finite: "lpp_finite_term (LPIFun p [(eta input_slot),(eta parameter_slot),(eta output_slot)])"
  using invariant by (auto simp: lpp_observer_output_invariant_def lpp_observer_invariant_def
    lpp_finite_execution_def lpp_finite_goals_def lpc_attach_answers_def lpc_reinterface_def)
 show ?thesis
 proof (rule lp_answer_contract_intro)
  fix event result
  assume step: "?T (lpc_attach_answers rest (lpc_reinterface ?R ?runtime)) event result"
  obtain child where silent: "event = None" and joint: "?T ?runtime None child"
   and actual: "result = lpc_attach_answers rest (lpc_reinterface ?R child)"
   and child_inv: "lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest oi hi child"
   using cons_actual_step_preserves_observer[OF refl invariant head spine tracked distinct covered step] by blast
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
    mgu: "lpc_mgu_resolve (LPIFun p [(eta input_slot),(eta parameter_slot),(eta output_slot)]) [] (Fun p [Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y],Var n,Var out]) bs sigma rho"
    and child_shape: "child = [(LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) bs),\<lambda>x. lp_isubst (env x) sigma)]"
    using base False head body by (cases rule: lpc_answer_transition.cases) auto
   obtain head_tree tail_tree head_shadow tail_shadow where facts: "lp_ieval target_parameter (successor_env sigma rho) = (eta parameter_slot) \<and>
  lpp_runtime_parameter initial_parameter (lp_ieval target_parameter (successor_env sigma rho)) \<and>
  observed_leaf_coordinate encode C head_tree (lp_ieval target_head (successor_env sigma rho)) head_shadow \<and>
  observed_leaf_coordinate encode A parameter_tree (lp_ieval target_parameter (successor_env sigma rho)) parameter_shadow \<and>
  observed_leaf_coordinate encode C (Fun (Inr ()) []) (lp_ieval target_fresh (successor_env sigma rho)) ((LPIFun (encode LPPStructureLeaf) [] :: (string lp_cut_symbol,string) lp_iterm)) \<and>
  observed_leaf_coordinate encode C tail_tree (lp_ieval target_tail (successor_env sigma rho)) tail_shadow \<and>
  observed_leaf_coordinate encode B output_tree (lp_ieval target_output (successor_env sigma rho)) output_shadow"
    and path: "(?start,[(target_symbol,[lp_ieval target_head (successor_env sigma rho),lp_ieval target_parameter (successor_env sigma rho),lp_ieval target_fresh (successor_env sigma rho),
 lp_ieval target_tail (successor_env sigma rho),lp_ieval target_output (successor_env sigma rho),
 head_shadow,parameter_shadow,(LPIFun (encode LPPStructureLeaf) [] :: (string lp_cut_symbol,string) lp_iterm),tail_shadow,output_shadow])]) \<in> (lp_ild Q)\<^sup>+"
    using actual_cons_six_to_ten_observations[OF spine mgu distinct finite tracked input_observed
      parameter_observed output_observed head_map parameter_map tail_map output_map fresh_map clause residual_distinct, of k eta]
    by (auto simp: successor_env_def)
   have context_payload: "lpc_return_env [Fun (LPCUser ''2:prolog_data_2e'') [target_head,target_tail],target_parameter,target_output] (successor_env sigma rho) =
   (\<lambda>i. lp_isubst (lpc_return_env [Var input_slot,Var parameter_slot,Var output_slot] eta i) sigma) \<and>
  lpp_runtime_parameter initial_parameter (lp_ieval target_parameter (successor_env sigma rho)) \<and>
  lpp_stable_context_holds operation SP
   ([],[LPPSOpaque target_parameter],[LPPOGround target_parameter,
    LPPOShape lpp_spine_grammar (LPReturnShape 0)
     (Fun (LPCUser ''2:prolog_data_2e'') [target_head,target_tail])]) (successor_env sigma rho) \<and>
  (\<exists>v. lp_ieval target_fresh (successor_env sigma rho) = LPIVar v)"
    using actual_cons_simple_context_payload[OF mgu spine tracked head_map parameter_map tail_map output_map fresh_map, of k operation SP]
    by (simp add: successor_env_def)
   have lower: "lp_answer_contract ?T (lpc_attach_answers rest (lpc_reinterface ?R child)) (lp_ild Q) [(target_symbol,[lp_ieval target_head (successor_env sigma rho),lp_ieval target_parameter (successor_env sigma rho),lp_ieval target_fresh (successor_env sigma rho),
 lp_ieval target_tail (successor_env sigma rho),lp_ieval target_output (successor_env sigma rho),
 head_shadow,parameter_shadow,(LPIFun (encode LPPStructureLeaf) [] :: (string lp_cut_symbol,string) lp_iterm),tail_shadow,output_shadow])] returned"
    unfolding child_shape by (rule continuation[OF mgu child_inv[unfolded child_shape] facts context_payload])
   show ?thesis unfolding actual
    by (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF path] lower])
  qed
  show "(\<forall>rho. event = Some rho \<longrightarrow> (?start,returned rho) \<in> (lp_ild Q)\<^sup>*) \<and>
    lp_answer_contract ?T result (lp_ild Q) ?start returned"
   using silent child_contract by simp
 qed
qed

ML \<open>
val checked = @{thms global_simple_cons_answer_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted cons contract" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-global-cons-contract/kernel-receipt.txt")
 ("Kernel checked; no skips or oracles. Actual successful continuation remains an explicit premise.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "CONS_CONTRACT_KERNEL_CHECKED";
\<close>
end
