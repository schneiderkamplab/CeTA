theory Global_Copy_Return_Check
 imports Global_Copy_Contract_Check
begin

text \<open>Copy returns retain the tracked parameter itself, including compound
finite ground values. Tracking is supplied by the actual copy theorem, not
inferred from groundness. The caller continuation remains a real contract.\<close>

lemma tracked_copy_cut_return:
 fixes env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes invariant: "lpp_observer_output_invariant A specs rest oi hi [(LPCGoals [LPCCut m],env)]"
 and helper_value: "env (Inl oi) = parameter"
 and tracked: "lpp_runtime_parameter initial_parameter parameter"
 and continuation: "\<And>rho. rho hi = parameter \<Longrightarrow>
   lpp_runtime_parameter initial_parameter (rho hi) \<Longrightarrow>
   list_all (\<lambda>(slot,tree). lpp_runtime_leaf_effect A tree (rho slot)) specs \<Longrightarrow>
   lpp_finite_execution [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) rest),rho)] \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P B U D)
    [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) rest),rho)] R subject returned"
 shows "lp_answer_contract (lpp_domain_answers P B U D)
  (lpc_attach_answers rest (lpc_reinterface (\<lambda>e x. e (Inr x)) [(LPCGoals [LPCCut m],env)])) R subject returned"
proof -
 let ?rho = "\<lambda>x. env (Inr x)"
 let ?gs = "map (lp_cut_map (\<lambda>x. lp_ieval x ?rho)) rest"
 have copied: "?rho hi = parameter"
  using invariant helper_value
  by (simp add: lpp_observer_output_invariant_def lpp_observer_output_alias_def)
 have caller_tracked: "lpp_runtime_parameter initial_parameter (?rho hi)" using tracked copied by simp
 have leaf: "list_all (\<lambda>(slot,tree). lpp_runtime_leaf_effect A tree (?rho slot)) specs"
 and finite: "lpp_finite_execution [(LPCGoals ?gs,?rho)]"
  using invariant by (simp_all add: lpp_observer_output_invariant_def lpp_observer_invariant_def
   lpc_reinterface_def lpc_attach_answers_def lpp_leaf_stack_invariant_def
   lpp_finite_execution_def lpp_finite_goals_def)
 have lower: "lp_answer_contract (lpp_domain_answers P B U D) [(LPCGoals ?gs,?rho)] R subject returned"
  by (rule continuation[OF copied caller_tracked leaf finite])
 show ?thesis
  unfolding lpc_attach_answers_def lpc_reinterface_def
 proof (simp, rule lp_answer_contract_intro)
  fix event result
  assume step: "lpp_domain_answers P B U D [(LPCGoals (LPCCut m # ?gs),?rho)] event result"
  have base: "lpc_answer_transition P [(LPCGoals (LPCCut m # ?gs),?rho)] event result"
   using step by (auto simp: lpp_domain_answers_def elim: lpp_answer_transition.cases)
  have exact: "event = None \<and> result = [(LPCGoals ?gs,?rho)]"
   using base by (cases rule: lpc_answer_transition.cases) auto
  show "(\<forall>rho. event = Some rho \<longrightarrow> (subject,returned rho) \<in> R\<^sup>*) \<and>
   lp_answer_contract (lpp_domain_answers P B U D) result R subject returned"
   using exact lower by simp
 qed
qed

theorem global_simple_copy_caller_contract:
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

 and helper_coordinate: "env (Inl oi) = output_value"
 and caller: "\<And>rho. rho hi = parameter \<Longrightarrow>
   lpp_runtime_parameter initial_parameter (rho hi) \<Longrightarrow>
   observed_leaf_coordinate encode (lpp_parameter_leaf_templates f g initial_parameter)
    initial_tree (rho hi) shadow \<Longrightarrow>
   list_all (\<lambda>(slot,tree). lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter) tree (rho slot)) specs \<Longrightarrow>
   lpp_finite_execution [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) rest),rho)] \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) rest),rho)] (lp_ild Q)
    [(target_symbol,[parameter,shadow])] returned"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>e x. e (Inr x))
    [(LPCClause [LPCAtom (LPIFun p [input_value,parameter,output_value])] c m,env)])) (lp_ild Q)
   [(source_symbol,[input_value,parameter,output_value,input_shadow,shadow,output_shadow])] returned"

proof (rule global_simple_copy_answer_contract[OF invariant head body spine tracked mode covered effect observed clause distinct])
 fix sigma rho
 assume actual: "lpc_mgu_resolve (LPIFun p [input_value,parameter,output_value]) []
    (Fun p [Fun nil [],Var n,Var n]) [LPCCut 0] sigma rho"
 and copied: "lp_isubst output_value sigma = parameter"
 and output_observed: "observed_leaf_coordinate encode (lpp_parameter_leaf_templates f g initial_parameter)
    initial_tree (lp_isubst output_value sigma) shadow"
 and child_inv: "lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest oi hi
    [(LPCGoals [LPCCut m],\<lambda>x. lp_isubst (env x) sigma)]"
 have helper: "(\<lambda>x. lp_isubst (env x) sigma) (Inl oi) = parameter"
  using copied helper_coordinate by simp
 show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>e x. e (Inr x))
     [(LPCGoals [LPCCut m],\<lambda>x. lp_isubst (env x) sigma)])) (lp_ild Q)
    [(target_symbol,[parameter,shadow])] returned"
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
    [(target_symbol,[parameter,shadow])] returned"
   by (rule caller[OF value_eq caller_tracked obs leaf finite])
 qed
qed

ML \<open>
val checked = @{thms tracked_copy_cut_return global_simple_copy_caller_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted copy return" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-global-copy-return/kernel-receipt.txt")
 ("Kernel checked; no skips or oracles. Caller continuation remains explicit.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "GLOBAL_COPY_RETURN_KERNEL_CHECKED";
\<close>
end
