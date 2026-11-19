theory Global_Arithmetic_Contract_Check
 imports Global_Equality_Contract_Check Actual_Global_Arithmetic_Check
begin

theorem global_arithmetic_equality_answer_contract:
 fixes env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 and encode :: "(string lp_cut_symbol) lpp_structure_symbol \<Rightarrow> string lp_cut_symbol"
 assumes invariant: "lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest 2 hi
   [(LPCGoals [LPCAtom (LPIFun (LPCUser ''2:is'') [eta x,expression])],env)]"
 and output_slot: "env (Inl 2) = eta x"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and ground: "vars_term initial_parameter = {}"
 and observed: "observed_leaf_coordinate encode (lpp_parameter_leaf_templates f g initial_parameter) initial_tree (eta x) (eta sx)"
 and arithmetic: "((arithmetic_symbol,map Var [x,p,sx,sp]),[(boundary_symbol,map Var [x,z,p,sx,sz,sp])]) \<in> set Q"
 and projection: "((boundary_symbol,map Var [v0,v1,v2,t0,t1,t2]),[(eq_symbol,map Var [v0,v1,t0,t1])]) \<in> set Q"
 and success_clause: "((eq_symbol,map Var [u0,u1,r0,r1]),[(success_symbol,map Var [u1,r1])]) \<in> set Q"
 and return_clause: "((success_symbol,map Var [y,t]),[(return_symbol,map Var [y,y,t,t])]) \<in> set Q"
 and distinct: "distinct [v0,v1,v2,t0,t1,t2]" "distinct [u0,u1,r0,r1]" "y \<noteq> t"
 and fresh: "z \<notin> {x,p,sx,sp}" "sz \<notin> {x,p,sx,sp}" "z \<noteq> sz"
 and continuation: "\<And>scalar shadow rho.
   lpp_stable_scalar_evaluation operation expression (LPIFun (LPCUser scalar) []) \<Longrightarrow>
   observed_leaf_coordinate encode (lpp_parameter_leaf_templates f g initial_parameter) (Fun (Inl (LPCUser scalar)) [])
    (LPIFun (LPCUser scalar) [] :: (string lp_cut_symbol,string) lp_iterm) shadow \<Longrightarrow>
   rho hi = LPIFun (LPCUser scalar) [] \<Longrightarrow>
   lpp_runtime_parameter initial_parameter (rho hi) \<Longrightarrow>
   list_all (\<lambda>(slot,tree). lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter) tree (rho slot)) specs \<Longrightarrow>
   lpp_finite_execution [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) rest),rho)] \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) rest),rho)] (lp_ild Q)
    [(return_symbol,[LPIFun (LPCUser scalar) [],LPIFun (LPCUser scalar) [],shadow,shadow])] returned"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>e x. e (Inr x))
    [(LPCGoals [LPCAtom (LPIFun (LPCUser ''2:is'') [eta x,expression])],env)])) (lp_ild Q)
   [(arithmetic_symbol,map eta [x,p,sx,sp])] returned"
proof -
 let ?A = "lpp_parameter_leaf_templates f g initial_parameter"
 let ?R = "\<lambda>e x. e (Inr x)"
 let ?T = "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain"
 let ?start = "[(arithmetic_symbol,map eta [x,p,sx,sp])]"
 have finite_expression: "lpp_finite_term expression"
  using invariant by (auto simp: lpp_observer_output_invariant_def lpp_observer_invariant_def
   lpc_reinterface_def lpc_attach_answers_def lpp_finite_execution_def lpp_finite_goals_def)
 have domain: "lpp_finite_source_domain ''2:is'' [eta x,expression]"
  by (rule lpp_finite_is_source_domain[OF finite_expression])
 have normalized_contract: "lp_answer_contract ?T
   [(LPCGoals (LPCUnify (eta x) (LPIFun (LPCUser scalar) []) # map (lp_cut_map (\<lambda>t. lp_ieval t (?R env))) rest),?R env)]
   (lp_ild Q) ?start returned"
  if evaluated: "lpp_stable_scalar_evaluation operation expression (LPIFun (LPCUser scalar) [])" for scalar
 proof -
  let ?normal = "[(LPCGoals [LPCUnify (eta x) (LPIFun (LPCUser scalar) [])],env)]"
  have normal_inv: "lpp_observer_output_invariant ?A specs rest 2 hi ?normal"
   using invariant by (auto simp: lpp_observer_output_invariant_def lpp_observer_output_alias_def
    lpp_observer_invariant_def lpc_reinterface_def lpc_attach_answers_def lpp_finite_execution_def
    lpp_finite_goals_def lpp_leaf_stack_invariant_def)
  obtain shadow :: "(string lp_cut_symbol,string) lp_iterm" where scalar_observed:
   "observed_leaf_coordinate encode ?A (Fun (Inl (LPCUser scalar)) [])
    (LPIFun (LPCUser scalar) [] :: (string lp_cut_symbol,string) lp_iterm) shadow"
  and path: "(?start,[(eq_symbol,[eta x,LPIFun (LPCUser scalar) [],eta sx,shadow])]) \<in> (lp_ild Q)\<^sup>+"
   using arithmetic_to_equality_observed_path[OF arithmetic projection distinct(1) fresh observed, of "LPCUser scalar"] by blast
  let ?helper = "\<lambda>(_::(string lp_cut_symbol,string) lp_iterm lp_cut_entry) (_::nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm) (i::nat).
    if i = 0 then eta x else LPIFun (LPCUser scalar) []"
  let ?child = "lpp_observer_rebase ?helper ?normal"
  let ?env = "case_sum (\<lambda>(i::nat). if i = 0 then eta x else LPIFun (LPCUser scalar) []) (?R env)"
  have child_inv: "lpp_observer_output_invariant ?A specs rest 0 hi ?child"
   by (rule lpp_observer_output_rebase_invariant[where helper="?helper" and new_oi=0, OF normal_inv])
    (use output_slot in auto)
  have child_shape: "?child = [(LPCGoals [LPCUnify (eta x) (LPIFun (LPCUser scalar) [])],?env)]"
   by (simp add: lpp_observer_rebase_def)
  have equality_contract: "lp_answer_contract ?T
   (lpc_attach_answers rest (lpc_reinterface ?R ?child)) (lp_ild Q)
   [(eq_symbol,[eta x,LPIFun (LPCUser scalar) [],eta sx,shadow])] returned"
   unfolding child_shape
   apply (rule global_scalar_equality_answer_contract[where env="?env" and f=f and g=g
     and initial_parameter=initial_parameter and specs=specs and hi=hi
     and a="eta x" and scalar=scalar and old_shadow="eta sx" and shadow=shadow and rest=rest
     and Q=Q and returned=returned and eq_symbol=eq_symbol])
   apply (rule child_inv[unfolded child_shape])
   apply simp
   apply (rule covered)
   apply (rule ground)
   apply (rule success_clause)
   apply (rule return_clause)
   apply (rule distinct(2))
   apply (rule distinct(3))
   apply (rule continuation[OF evaluated scalar_observed]; assumption)
   done
  have at_start: "lp_answer_contract ?T (lpc_attach_answers rest (lpc_reinterface ?R ?child)) (lp_ild Q) ?start returned"
   by (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF path] equality_contract])
  show ?thesis using at_start
   by (simp add: child_shape lpc_reinterface_def lpc_attach_answers_def)
 qed
 show ?thesis
  apply (simp add: lpc_reinterface_def lpc_attach_answers_def)
  apply (rule lpp_univ_evaluation_domain_contract[OF domain])
  using normalized_contract by simp
qed

ML \<open>
val checked = @{thms global_arithmetic_equality_answer_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted global arithmetic/equality contract" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-global-equality-contract/arithmetic-kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. Caller continuation remains explicit.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "GLOBAL_ARITHMETIC_CONTRACT_KERNEL_CHECKED";
\<close>
end
