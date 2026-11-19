theory Observer_Output_Rebase_Check
 imports Conditioned_Output_Link_Check
begin

lemma arithmetic_equality_payload_rebase:
 assumes represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime = lpc_return_eval eta
   [(LPCGoals [LPCUnify (Var ''V0'') (Var ''V1'')],
     [Fun f [Fun g [],Var ''V2''],Var ''V2'',Var ''V0''])]"
 and invariant: "lpp_observer_output_invariant A specs rest 2 hi runtime"
 defines child_def: "child \<equiv> lpp_observer_rebase (\<lambda>_ _. lpc_return_env [Var ''V0'',Var ''V1''] eta) runtime"
 shows "lpc_reinterface (\<lambda>env x. env (Inl x)) child =
   lpc_return_eval eta [(LPCGoals [LPCUnify (Var ''V0'') (Var ''V1'')],[Var ''V0'',Var ''V1''])] \<and>
   lpp_observer_output_invariant A specs rest 0 hi child \<and>
   lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child) =
   lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)"
 unfolding child_def
 apply (rule lpp_observer_singleton_output_rebase[where oi=2 and new_oi=0, OF represented _ _ _ invariant])
 by simp_all

text \<open>The incoming arithmetic boundary now establishes the full equality
module representation and combined invariant together, with strict residual
descent. Static link checking and the arithmetic scalar fact remain premises.\<close>

lemma arithmetic_equality_conditioned_boundary:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and program: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts
   nd [(LPCGoals [LPCUnify (Var ''V0'') (Var ''V1'')],[Var ''V0'',Var ''V1''])]
   G K eqs F source_context source_functors e"
 and equations: "lp_equations eqs eta'"
 and old: "map eta' (lpcn_vars nd) = map eta (lpcn_vars nd)"
 and known: "lp_cut_knowledge (set G) K eta'"
 and free: "lpc_free_knowledge (set F) eta'"
 and observed: "lpp_stable_context_holds operation SP source_context eta'"
 and functors: "list_all (lpp_functor_fact_holds names eta') source_functors"
 and entry_row: "lpcl_target e = 0"
 and scalar_coordinate: "lpp_check_parameter_coordinate (Var ''V1'') (Var ''V1'')
   (lp_cut_instance_subst (lpcl_bindings e))"
 and scalar_value: "eta' ''V1'' = LPIFun (LPCUser scalar) []"
 and represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime = lpc_return_eval eta'
   [(LPCGoals [LPCUnify (Var ''V0'') (Var ''V1'')],
     [Fun f [Fun g [],Var ''V2''],Var ''V2'',Var ''V0''])]"
 and invariant: "lpp_observer_output_invariant A specs rest 2 hi runtime"
 defines child_def: "child \<equiv> lpp_observer_rebase (\<lambda>_ _. lpc_return_env [Var ''V0'',Var ''V1''] eta') runtime"
 shows "\<exists>u. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u) \<in> (lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    equality_scalar_conditions (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<and>
   lpp_observer_output_invariant A specs rest 0 hi child \<and>
   lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child) =
   lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)"
proof -
 have scalar_target: "(\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings e) x) eta') ''V1'' = LPIFun (LPCUser scalar) []"
  using lpp_checked_parameter_coordinate_value[OF scalar_coordinate, of eta'] scalar_value by simp
 have conditions: "equality_scalar_conditions (lpcl_target e)
   (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings e) x) eta')"
  using scalar_target entry_row by (auto simp: equality_scalar_conditions_def)
 have rebased: "lpc_reinterface (\<lambda>env x. env (Inl x)) child =
   lpc_return_eval eta' [(LPCGoals [LPCUnify (Var ''V0'') (Var ''V1'')],[Var ''V0'',Var ''V1''])] \<and>
   lpp_observer_output_invariant A specs rest 0 hi child \<and>
   lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child) =
   lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)"
  unfolding child_def by (rule arithmetic_equality_payload_rebase[OF represented invariant])
 obtain u where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],u) \<in> (lp_ild Q)\<^sup>+"
 and target_rep: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
   equality_scalar_conditions
   (lpc_return_eval eta' [(LPCGoals [LPCUnify (Var ''V0'') (Var ''V1'')],[Var ''V0'',Var ''V1''])]) u"
  using lpp_conditioned_functor_module_link[where node_conditions=equality_scalar_conditions,
   OF compatible program checked equations old known free observed functors conditions] by blast
 show ?thesis using strict target_rep rebased by auto
qed

lemma wrong_scalar_coordinate_rejected:
 "\<not> lpp_observer_output_alias (1::nat) (0::nat)
   (lpp_observer_rebase
    (\<lambda>_ _. \<lambda>i. if i = 0 then LPIVar (''out''::string) else LPIFun (LPCUser ''scalar'') [])
    [(LPCGoals [],\<lambda>_. LPIVar ''out'')])"
 by (simp add: lpp_observer_output_alias_def lpp_observer_rebase_def)

lemma equality_identity_scalar_coordinate:
 "lpp_check_parameter_coordinate (Var ''V1'') (Var ''V1'')
   (lp_cut_instance_subst [(''V0'',Var ''V0''),(''V1'',Var ''V1'')])"
 by (simp add: lpp_check_parameter_coordinate_def lp_cut_instance_subst_def)

lemma equality_wrong_scalar_binding_rejected:
 "\<not> lpp_check_parameter_coordinate (Var ''V1'') (Var ''V1'')
   (lp_cut_instance_subst [(''V0'',Var ''V0''),(''V1'',Var ''V0'')])"
 by (simp add: lpp_check_parameter_coordinate_def lp_cut_instance_subst_def)

ML \<open>
val checked = @{thms lpp_observer_output_rebase_invariant lpp_observer_singleton_output_rebase
 lpp_checked_observer_output_module_link_contract arithmetic_equality_payload_rebase
 arithmetic_equality_conditioned_boundary wrong_scalar_coordinate_rejected
 equality_identity_scalar_coordinate equality_wrong_scalar_binding_rejected};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted output rebase fixture" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-equality-incoming-boundary/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "OBSERVER_OUTPUT_REBASE_KERNEL_CHECKED";
\<close>
end
