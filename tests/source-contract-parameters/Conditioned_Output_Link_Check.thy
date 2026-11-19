theory Conditioned_Output_Link_Check
 imports "../../thys/Logic_Programming/LP_Prolog_Observer_Conditioned_Output_Link"
   "../../thys/Logic_Programming/LP_Prolog_Partial_Equality_Successor"
   "../../thys/Logic_Programming/LP_Prolog_Observer_Output_Scalar_Equality_Node"
begin

text \<open>The retained equality module tests V1 at row 0, returns V0 at
row 1, and has no scalar condition on empty failure rows.\<close>

definition equality_scalar_conditions where
 "equality_scalar_conditions i eta =
   (if i = (0::nat) then (\<exists>s. eta ''V1'' = LPIFun (LPCUser s) [])
    else if i = 1 then (\<exists>s. eta ''V0'' = LPIFun (LPCUser s) []) else True)"

lemma equality_scalar_entry:
 assumes scalar_value: "eta ''V1'' = LPIFun (LPCUser scalar) []"
 shows "equality_scalar_conditions 0 eta"
 using scalar_value by (auto simp: equality_scalar_conditions_def)

lemma equality_scalar_success_condition:
 fixes initial_parameter :: "(string lp_cut_symbol,string) term"
 and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes initial_ground: "vars_term initial_parameter = {}"
 and conditions: "equality_scalar_conditions 0 eta"
 and actual: "lpc_mgu_unify (eta ''V0'') (eta ''V1'') gs sigma"
 shows "equality_scalar_conditions 1
   (\<lambda>x. lp_ieval (lp_cut_instance_subst [(''V0'',Var ''V1'')] x)
    (lp_cut_resolution_env 3 6 eta sigma eta))"
proof -
 obtain scalar where scalar_value: "eta ''V1'' = LPIFun (LPCUser scalar) []"
  using conditions by (auto simp: equality_scalar_conditions_def)
 have tracked: "lpp_runtime_parameter initial_parameter (lp_ieval (Var ''V1'') eta)"
  using scalar_value initial_ground by (auto simp: lpp_runtime_parameter_def lpp_parameter_return_def)
 have coordinate: "lpp_check_parameter_refresh 3 6 [''V1''] (Var ''V1'') (Var ''V0'') [(''V0'',Var ''V1'')]"
  by (simp add: lpp_check_parameter_refresh_def lp_cut_instance_subst_def lp_cut_refresh_def)
 have known: "\<forall>x\<in>set [''V1'']. lp_seg_ground (eta x)"
  using scalar_value by simp
 have mgu: "lpc_mgu_unify (lp_ieval (Var ''V0'') eta) (lp_ieval (Var ''V1'') eta) gs sigma"
  using actual by simp
 have result: "lp_ieval (Var ''V0'')
    (\<lambda>x. lp_ieval (lp_cut_instance_subst [(''V0'',Var ''V1'')] x)
      (lp_cut_resolution_env 3 6 eta sigma eta)) = eta ''V1''"
  using lpp_partial_equality_successor_values[OF coordinate known tracked mgu] by simp
 show ?thesis using result scalar_value by (auto simp: equality_scalar_conditions_def)
qed

lemma equality_scalar_failure_condition:
 "equality_scalar_conditions 2 eta"
 by (simp add: equality_scalar_conditions_def)

lemma ground_compound_is_not_scalar_condition:
 "\<not> equality_scalar_conditions 0 (\<lambda>_. LPIFun (LPCUser ''outer'') [LPIFun (LPCUser ''inner'') []])"
 by (simp add: equality_scalar_conditions_def)

lemma wrong_scalar_binding_rejected:
 "\<not> lpp_check_parameter_coordinate (Var ''V1'' :: (nat,string) term) (Var ''V1'')
   (lp_cut_instance_subst [(''V1'',Var ''V0'')])"
 by (simp add: lpp_check_parameter_coordinate_def lp_cut_instance_subst_def)


lemma retained_equality_row_conditioned_contract:
 fixes SP :: "string lpp_success_clause list"
 and rest :: "(string lp_cut_symbol,nat) term lp_cut_goal list"
 assumes program: "lp_cut_source_program P"
 and clear: "lpc_rest_scopes rest = {}"
 and compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_equality_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds ! 0) (Fs ! 0) (Var ''V0'') (Var ''V1'') [] [Var ''V0'',Var ''V1''] [] 3 6 next mode outputs
   (contexts ! 0) (functor_contexts ! 0) yes no"
 and source_shape: "states ! 0 = [(LPCGoals [LPCUnify (Var ''V0'') (Var ''V1'')],[Var ''V0'',Var ''V1''])]"
 and ground: "''V1'' \<in> set (lpcn_ground (nds ! 0)) \<union> lpp_source_context_ground (contexts ! 0)"
 and initial_ground: "vars_term initial_parameter = {}"
 and success: "lpcl_target yes = 1" "lpcl_bindings yes = [(''V0'',Var ''V1'')]"
 and failure: "lpcl_target no = 2"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 shows "lpp_observer_node_contract names operation SP P lpp_builtin_signature
   (lpp_univ_source_builtin names operation) lpp_univ_source_domain Q nds states contexts Fs functor_contexts
   equality_scalar_conditions
   (lpp_observer_output_invariant (lpp_parameter_leaf_templates f g initial_parameter) specs rest 0 hi)
   rest returned 0"
proof (rule lpp_observer_output_scalar_equality_node_contract[OF program clear compatible transfer checked source_shape _ initial_ground _ _ _ covered])
 show "vars_term (Var ''V1'') \<subseteq> set (lpcn_ground (nds ! 0)) \<union> lpp_source_context_ground (contexts ! 0)"
  using ground by simp
next
 fix eta assume "equality_scalar_conditions 0 eta"
 then show "\<exists>scalar. lp_ieval (Var ''V1'') eta = LPIFun (LPCUser scalar) []"
  by (simp add: equality_scalar_conditions_def)
next
 fix eta sigma
 assume conditions: "equality_scalar_conditions 0 eta"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds ! 0))) (lpcn_guards (nds ! 0)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts ! 0) eta"
 and actual: "lpc_mgu_unify (lp_ieval (Var ''V0'') eta) (lp_ieval (Var ''V1'') eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) []) sigma"
 show "equality_scalar_conditions (lpcl_target yes)
   (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings yes) x) (lp_cut_resolution_env 3 6 eta sigma eta))"
  using equality_scalar_success_condition[OF initial_ground conditions actual[simplified]]
  by (simp add: success)
next
 fix eta
 show "equality_scalar_conditions 0 eta \<Longrightarrow>
  lp_cut_knowledge (set (lpcn_ground (nds ! 0))) (lpcn_guards (nds ! 0)) eta \<Longrightarrow>
  lpp_stable_context_holds operation SP (contexts ! 0) eta \<Longrightarrow>
  equality_scalar_conditions (lpcl_target no)
   (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings no) x) eta)"
  by (simp add: failure equality_scalar_conditions_def)
qed

ML \<open>
val checked = @{thms retained_equality_row_conditioned_contract lpp_conditioned_functor_module_link lpp_scalar_parameter_coordinate_transport
 lpp_checked_conditioned_output_module_link_contract equality_scalar_entry
 equality_scalar_success_condition equality_scalar_failure_condition
 ground_compound_is_not_scalar_condition wrong_scalar_binding_rejected};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted conditioned output link fixture" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-conditioned-output-link/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "CONDITIONED_OUTPUT_LINK_KERNEL_CHECKED";
\<close>
end
