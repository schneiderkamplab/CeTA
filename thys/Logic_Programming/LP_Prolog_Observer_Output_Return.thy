theory LP_Prolog_Observer_Output_Return
 imports LP_Prolog_Observer_Output_Copy_Node LP_Prolog_Observer_Return_Boundary
begin

lemma lpp_observer_output_single_return:
 assumes shape: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime = [(LPCGoals [],helper_env)]"
 and invariant: "lpp_observer_output_invariant A specs rest oi hi runtime"
 and scalar_value: "helper_env oi = LPIFun (LPCUser scalar) []"
 and ground: "vars_term initial_parameter = {}"
 and continuation: "\<And>rho. rho hi = LPIFun (LPCUser scalar) [] \<Longrightarrow>
   lpp_runtime_parameter initial_parameter (rho hi) \<Longrightarrow>
   list_all (\<lambda>(slot,tree). lpp_runtime_leaf_effect A tree (rho slot)) specs \<Longrightarrow>
   lpp_finite_execution [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) rest),rho)] \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P B U D)
    [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) rest),rho)] R subject returned"
 shows "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)) R subject returned"
proof -
 obtain env where runtime_shape: "runtime = [(LPCGoals [],env)]"
 and helper: "(\<lambda>x. env (Inl x)) = helper_env"
  using shape by (auto simp: lpc_reinterface_def map_eq_Cons_conv)
 let ?rho = "\<lambda>x. env (Inr x)"
 have scalar: "?rho hi = LPIFun (LPCUser scalar) []"
  using invariant fun_cong[OF helper, of oi] scalar_value
  by (simp add: runtime_shape lpp_observer_output_invariant_def lpp_observer_output_alias_def)
 have tracked: "lpp_runtime_parameter initial_parameter (?rho hi)"
  using ground scalar by (auto simp: lpp_runtime_parameter_def lpp_parameter_return_def)
 have leaf: "list_all (\<lambda>(slot,tree). lpp_runtime_leaf_effect A tree (?rho slot)) specs"
 and finite: "lpp_finite_execution [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x ?rho)) rest),?rho)]"
  using invariant by (simp_all add: runtime_shape lpp_observer_output_invariant_def
    lpp_observer_invariant_def lpc_reinterface_def lpc_attach_answers_def lpp_leaf_stack_invariant_def)
 show ?thesis using continuation[OF scalar tracked leaf finite]
  by (simp add: runtime_shape lpc_reinterface_def lpc_attach_answers_def)
qed

lemma lpp_observer_output_return_node:
 fixes SP :: "string lpp_success_clause list"
 and rest :: "(string lp_cut_symbol,nat) term lp_cut_goal list"
 assumes source_shape: "states ! i = [(LPCGoals [],payload)]"
 and coordinate: "oi < length payload" "payload ! oi = output_term"
 and scalar_condition: "\<And>eta. node_conditions i eta \<Longrightarrow>
   \<exists>scalar. lp_ieval output_term eta = LPIFun (LPCUser scalar) []"
 and ground: "vars_term initial_parameter = {}"
 and continuation: "\<And>eta scalar rho. node_conditions i eta \<Longrightarrow>
   lp_ieval output_term eta = LPIFun (LPCUser scalar) [] \<Longrightarrow>
   rho hi = LPIFun (LPCUser scalar) [] \<Longrightarrow>
   lpp_runtime_parameter initial_parameter (rho hi) \<Longrightarrow>
   list_all (\<lambda>(slot,tree). lpp_runtime_leaf_effect A tree (rho slot)) specs \<Longrightarrow>
   lpp_finite_execution [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) rest),rho)] \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P B U D)
    [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) rest),rho)] (lp_ild Q)
    [(lpcn_pred (nds ! i),map eta (lpcn_vars (nds ! i)))] returned"
 shows "lpp_observer_node_contract names operation SP P B U D Q nds states contexts Fs functor_contexts
   node_conditions (lpp_observer_output_invariant A specs rest oi hi) rest returned i"
proof -
 have empty_scopes: "lpc_return_scope_word swaps [(LPCGoals [],env)] = [(LPCGoals [],env)]" for swaps env
  by (induct swaps) (auto split: prod.splits)
 show ?thesis unfolding lpp_observer_node_contract_def
 proof (intro allI impI)
  fix eta swaps runtime
  assume conditions: "node_conditions i eta"
  and known: "lp_cut_knowledge (set (lpcn_ground (nds ! i))) (lpcn_guards (nds ! i)) eta"
  and free: "lpc_free_knowledge (set (Fs ! i)) eta"
  and observed: "lpp_stable_context_holds operation SP (contexts ! i) eta"
  and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts ! i)"
  and shape: "lpc_return_scope_word swaps (lpc_reinterface (\<lambda>env x. env (Inl x)) runtime) = lpc_return_eval eta (states ! i)"
  and invariant: "lpp_observer_output_invariant A specs rest oi hi runtime"
  and residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds ! i),map eta (lpcn_vars (nds ! i)))]}"
  and lower: "\<forall>child u. ([(lpcn_pred (nds ! i),map eta (lpcn_vars (nds ! i)))],u) \<in> (lp_ild Q)\<^sup>+ \<longrightarrow>
    lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts node_conditions
     (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<longrightarrow>
    lpp_observer_output_invariant A specs rest oi hi child \<longrightarrow>
    lp_answer_contract (lpp_domain_answers P B U D)
     (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned"
  have direct: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime = [(LPCGoals [],lpc_return_env payload eta)]"
   using arg_cong[OF shape, of "lpc_return_scope_word (rev swaps)"]
   by (simp add: source_shape lpc_return_eval_def lpc_return_scope_word_inverse empty_scopes)
  obtain scalar where scalar: "lp_ieval output_term eta = LPIFun (LPCUser scalar) []"
   using scalar_condition[OF conditions] by blast
  have result_value: "lpc_return_env payload eta oi = LPIFun (LPCUser scalar) []"
   using coordinate scalar by (simp add: lpc_return_env_def)
  show "lp_answer_contract (lpp_domain_answers P B U D)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)) (lp_ild Q)
    [(lpcn_pred (nds ! i),map eta (lpcn_vars (nds ! i)))] returned"
   by (rule lpp_observer_output_single_return[OF direct invariant result_value ground])
    (rule continuation[OF conditions scalar]; assumption)
 qed
qed

ML \<open>
val checked = @{thms lpp_observer_output_single_return lpp_observer_output_return_node};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted output return" else ();
\<close>
end
