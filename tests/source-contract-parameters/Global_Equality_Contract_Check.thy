theory Global_Equality_Contract_Check
 imports Global_Equality_Return_Check
begin

text \<open>Assemble the actual singleton equality fragment against the retained
global residual clauses. Caller continuation remains a real answer contract.\<close>

theorem global_scalar_equality_answer_contract:
 fixes env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes invariant: "lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest 0 hi
   [(LPCGoals [LPCUnify a (LPIFun (LPCUser scalar) [])],env)]"
 and output_slot: "env (Inl 0) = a"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and ground: "vars_term initial_parameter = {}"
 and success_clause: "((eq_symbol,map Var [x0,x1,s0,s1]),[(success_symbol,map Var [x1,s1])]) \<in> set Q"
 and return_clause: "((success_symbol,map Var [y,t]),[(return_symbol,map Var [y,y,t,t])]) \<in> set Q"
 and distinct: "distinct [x0,x1,s0,s1]" "y \<noteq> t"
 and continuation: "\<And>rho. rho hi = LPIFun (LPCUser scalar) [] \<Longrightarrow>
   lpp_runtime_parameter initial_parameter (rho hi) \<Longrightarrow>
   list_all (\<lambda>(slot,tree). lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter) tree (rho slot)) specs \<Longrightarrow>
   lpp_finite_execution [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) rest),rho)] \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) rest),rho)] (lp_ild Q)
    [(return_symbol,[LPIFun (LPCUser scalar) [],LPIFun (LPCUser scalar) [],shadow,shadow])] returned"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>e x. e (Inr x))
     [(LPCGoals [LPCUnify a (LPIFun (LPCUser scalar) [])],env)])) (lp_ild Q)
   [(eq_symbol,[a,LPIFun (LPCUser scalar) [],old_shadow,shadow])] returned"
proof -
 let ?runtime = "[(LPCGoals [LPCUnify a (LPIFun (LPCUser scalar) [])],env)]"
 let ?T = "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain"
 let ?R = "\<lambda>e x. e (Inr x)"
 let ?start = "[(eq_symbol,[a,LPIFun (LPCUser scalar) [],old_shadow,shadow])]"
 let ?finish = "[(return_symbol,[LPIFun (LPCUser scalar) [],LPIFun (LPCUser scalar) [],shadow,shadow])]"
 have path: "(?start,?finish) \<in> (lp_ild Q)\<^sup>+"
  by (rule equality_global_return_path[OF success_clause return_clause distinct])
 show ?thesis
 proof (rule lp_answer_contract_intro)
  fix event result
  assume step: "?T (lpc_attach_answers rest (lpc_reinterface ?R ?runtime)) event result"
  obtain child where silent: "event = None" and joint: "?T ?runtime None child"
  and actual: "result = lpc_attach_answers rest (lpc_reinterface ?R child)"
  and child_inv: "lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest 0 hi child"
   using lpp_observer_output_scalar_equality_preservation[OF refl invariant covered ground step] by blast
  have base: "lpc_answer_transition P ?runtime None child"
   using joint by (auto intro: lpp_observer_equality_base)
  have child_contract: "lp_answer_contract ?T result (lp_ild Q) ?start returned"
  proof (cases "child = []")
   case True
   have empty: "result = []" using actual True by (simp add: lpc_attach_answers_def lpc_reinterface_def)
   show ?thesis unfolding empty by (rule lpp_domain_contract_singletons) simp
  next
   case False
   obtain sigma :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm" where
    mgu: "lpc_mgu_unify a (LPIFun (LPCUser scalar) []) [] sigma"
    and child_shape: "child = [(LPCGoals [],\<lambda>x. lp_isubst (env x) sigma)]"
    using base False by (cases rule: lpc_answer_transition.cases) auto
   have result_value: "lp_isubst a sigma = LPIFun (LPCUser scalar) []"
    using mgu by (simp add: lpc_mgu_unify_def)
   have helper: "lpc_reinterface (\<lambda>e x. e (Inl x)) child =
     [(LPCGoals [],\<lambda>x. lp_isubst (env (Inl x)) sigma)]"
    by (simp add: child_shape lpc_reinterface_def)
   have scalar_value: "(\<lambda>x. lp_isubst (env (Inl x)) sigma) 0 = LPIFun (LPCUser scalar) []"
    using output_slot result_value by simp
   have at_return: "lp_answer_contract ?T
     (lpc_attach_answers rest (lpc_reinterface ?R child)) (lp_ild Q) ?finish returned"
    by (rule lpp_observer_output_single_return[OF helper child_inv scalar_value ground continuation])
   show ?thesis unfolding actual
    by (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF path] at_return])
  qed
  show "(\<forall>rho. event = Some rho \<longrightarrow> (?start,returned rho) \<in> (lp_ild Q)\<^sup>*) \<and>
    lp_answer_contract ?T result (lp_ild Q) ?start returned"
   using silent child_contract by simp
 qed
qed

ML \<open>
val checked = @{thms global_scalar_equality_answer_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted global equality contract" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-global-equality-contract/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. Caller continuation remains explicit.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "GLOBAL_EQUALITY_CONTRACT_KERNEL_CHECKED";
\<close>
end
