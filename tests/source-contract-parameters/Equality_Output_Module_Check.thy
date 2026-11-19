theory Equality_Output_Module_Check
 imports Conditioned_Output_Link_Check "../../thys/Logic_Programming/LP_Prolog_Observer_Output_Return"
begin

text \<open>Assemble every row of the retained equality module. The caller
continuation remains an explicit contract, with its actual scalar and leaf facts;
it is not assumed terminated merely because this helper returned.\<close>

theorem retained_equality_output_module_contract:
 fixes SP :: "string lpp_success_clause list"
 and rest :: "(string lp_cut_symbol,nat) term lp_cut_goal list"
 assumes program: "lp_cut_source_program P"
 and clear: "lpc_rest_scopes rest = {}"
 and compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_equality_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds ! 0) (Fs ! 0) (Var ''V0'') (Var ''V1'') [] [Var ''V0'',Var ''V1''] [] 3 6 next mode outputs
   (contexts ! 0) (functor_contexts ! 0) yes no"
 and states_shape: "states = [[(LPCGoals [LPCUnify (Var ''V0'') (Var ''V1'')],[Var ''V0'',Var ''V1''])],
   [(LPCGoals [],[Var ''V0'',Var ''V0''])],[],[]]"
 and ground: "''V1'' \<in> set (lpcn_ground (nds ! 0)) \<union> lpp_source_context_ground (contexts ! 0)"
 and initial_ground: "vars_term initial_parameter = {}"
 and success: "lpcl_target yes = 1" "lpcl_bindings yes = [(''V0'',Var ''V1'')]"
 and failure: "lpcl_target no = 2"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and table: "lpp_check_functor_control T fuel P Q nds states contexts Fs functor_contexts returned_symbol arity actions"
 and node_count: "length nds = 4"
 and continuation: "\<And>eta scalar rho. eta ''V0'' = LPIFun (LPCUser scalar) [] \<Longrightarrow>
   rho hi = LPIFun (LPCUser scalar) [] \<Longrightarrow>
   lpp_runtime_parameter initial_parameter (rho hi) \<Longrightarrow>
   list_all (\<lambda>(slot,tree). lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter) tree (rho slot)) specs \<Longrightarrow>
   lpp_finite_execution [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) rest),rho)] \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) rest),rho)] (lp_ild Q)
    [(lpcn_pred (nds ! 1),map eta (lpcn_vars (nds ! 1)))] returned"
 and represented: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts equality_scalar_conditions
   (lpc_reinterface (\<lambda>env x. env (Inl x)) runtime) subject"
 and invariant: "lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest 0 hi runtime"
 and residual: "SN_on (lp_ild Q) {subject}"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)) (lp_ild Q) subject returned"
proof -
 let ?J = "lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest 0 hi"
 let ?node = "lpp_observer_node_contract names operation SP P lpp_builtin_signature (lpp_univ_source_builtin names operation)
   lpp_univ_source_domain Q nds states contexts Fs functor_contexts equality_scalar_conditions ?J rest returned"
 have source_shape: "states ! 0 = [(LPCGoals [LPCUnify (Var ''V0'') (Var ''V1'')],[Var ''V0'',Var ''V1''])]"
  by (simp add: states_shape)
 have equality: "?node 0"
  by (rule retained_equality_row_conditioned_contract[OF program clear compatible transfer checked source_shape
    ground initial_ground success failure covered])
 have returned_node: "?node 1"
 proof (rule lpp_observer_output_return_node[where payload="[Var ''V0'',Var ''V0'']"
   and output_term="Var ''V0''" and initial_parameter=initial_parameter])
  show "states ! 1 = [(LPCGoals [],[Var ''V0'',Var ''V0''])]" by (simp add: states_shape)
  show "0 < length [Var ''V0'',Var ''V0'']" by simp
  show "[Var ''V0'',Var ''V0''] ! 0 = Var ''V0''" by simp
  show "\<And>eta. equality_scalar_conditions 1 eta \<Longrightarrow>
    \<exists>scalar. lp_ieval (Var ''V0'') eta = LPIFun (LPCUser scalar) []"
   by (simp add: equality_scalar_conditions_def)
  show "vars_term initial_parameter = {}" by (rule initial_ground)
  show "\<And>eta scalar rho. equality_scalar_conditions 1 eta \<Longrightarrow>
   lp_ieval (Var ''V0'') eta = LPIFun (LPCUser scalar) [] \<Longrightarrow>
   rho hi = LPIFun (LPCUser scalar) [] \<Longrightarrow>
   lpp_runtime_parameter initial_parameter (rho hi) \<Longrightarrow>
   list_all (\<lambda>(slot,tree). lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter) tree (rho slot)) specs \<Longrightarrow>
   lpp_finite_execution [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) rest),rho)] \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) rest),rho)] (lp_ild Q)
    [(lpcn_pred (nds ! 1),map eta (lpcn_vars (nds ! 1)))] returned"
   using continuation by simp
 qed
 have nodes: "?node j" if bound: "j < length nds" for j
 proof (cases "j = 0")
  case True then show ?thesis using equality by simp
 next
  case False
  show ?thesis
  proof (cases "j = 1")
   case True then show ?thesis using returned_node by simp
  next
   case other: False
   have choices: "j = 2 \<or> j = 3" using bound node_count False other by arith
   have empty: "states ! j = []" using choices by (auto simp: states_shape)
   show ?thesis by (rule lpp_observer_empty_node_contract[OF empty])
  qed
 qed
 show ?thesis
  apply (rule lpp_observer_table_contract[where J="?J" and node_conditions=equality_scalar_conditions, OF table _ _ represented invariant residual])
  using nodes by blast+
qed

ML \<open>
val checked = @{thms retained_equality_output_module_contract lpp_observer_output_single_return lpp_observer_output_return_node};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted equality module assembly" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-equality-output-module/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. Caller continuation contract remains explicit.\n" ^
 cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "EQUALITY_OUTPUT_MODULE_KERNEL_CHECKED";
\<close>
end
