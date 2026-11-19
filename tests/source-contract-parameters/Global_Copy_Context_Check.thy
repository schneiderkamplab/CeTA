theory Global_Copy_Context_Check
 imports Global_Copy_Successor_Check
begin

definition copy_spine_grammar where
 "copy_spine_grammar nil cons = [[(nil,[]),(cons,[LPReturnAny,LPReturnShape 0])]]"

lemma copy_empty_shape:
 "lp_return_shape_holds (copy_spine_grammar nil cons) (LPReturnShape 0) (LPIFun nil [])"
 by (rule lp_return_shape_holds.node[where shapes="[]"])
   (simp_all add: copy_spine_grammar_def)

lemma copy_simple_context:
 assumes ground: "lp_seg_ground (lp_ieval parameter eta)"
 shows "lpp_stable_context_holds operation SP
  ([],[LPPSOpaque parameter],[LPPOGround parameter,
    LPPOShape (copy_spine_grammar nil cons) (LPReturnShape 0) (Fun nil [])]) eta"
 using ground copy_empty_shape[of nil cons]
 by (simp add: lpp_stable_context_holds_def lpp_evaluation_context_holds_def)

lemma copy_functor_context:
 assumes ground: "lp_seg_ground (eta parameter_slot)" "lp_seg_ground (eta name_slot)"
 shows "lp_cut_knowledge {parameter_slot,name_slot} [] eta \<and>
  lpp_stable_context_holds operation SP
   ([],map LPPSOpaque opaque_terms,[LPPOEquation constructed constructed,
    LPPOShape (copy_spine_grammar nil cons) (LPReturnShape 0) (Fun nil [])]) eta"
 using ground copy_empty_shape[of nil cons]
 by (simp add: lp_cut_knowledge_def lpp_stable_context_holds_def lpp_evaluation_context_holds_def list_all_iff)

lemma actual_copy_simple_context:
 fixes k :: nat
 and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes actual: "lpc_mgu_resolve (LPIFun p [eta input_slot,eta parameter_slot,eta output_slot]) gs
   (Fun p [Fun nil [],Var n,Var n]) bs sigma rho"
 and spine: "lpp_finite_spine cons nil (eta input_slot) spine_length"
 and tracked: "lpp_runtime_parameter initial_parameter (eta parameter_slot)"
 and parameter_map: "lpp_check_clause_coordinate l (Var n) target_parameter bindings"
 defines nu_def: "nu \<equiv> \<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) (lp_cut_resolution_env k l eta sigma rho)"

 shows "lpp_stable_context_holds operation SP
  ([],[LPPSOpaque target_parameter],[LPPOGround target_parameter,
    LPPOShape (copy_spine_grammar nil cons) (LPReturnShape 0) (Fun nil [])]) nu \<and>
  lpc_return_env [Fun nil [],target_parameter,target_parameter] nu =
   (\<lambda>i. lp_isubst (lpc_return_env [Var input_slot,Var parameter_slot,Var output_slot] eta i) sigma)"
proof -
 have result: "lp_ieval target_parameter nu = eta parameter_slot \<and>
  lpc_return_env [Fun nil [],target_parameter,target_parameter] nu =
   (\<lambda>i. lp_isubst (lpc_return_env [Var input_slot,Var parameter_slot,Var output_slot] eta i) sigma)"
  using copy_simple_successor_payload[OF actual spine tracked parameter_map, of k]
  by (simp add: nu_def)
 have ground: "lp_seg_ground (lp_ieval target_parameter nu)"
  using result lpp_runtime_parameter_ground[OF tracked] by simp
 show ?thesis using copy_simple_context[OF ground, of operation SP nil cons] result by blast
qed

lemma actual_copy_functor_context:
 fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes actual: "lpc_mgu_resolve (LPIFun p [eta input_slot,eta parameter_slot,eta output_slot]) gs
   (Fun p [Fun (LPCUser ''0:prolog_data_5b5d'') [],Var n,Var n]) bs sigma rho"
 and spine: "lpp_finite_spine cons (LPCUser ''0:prolog_data_5b5d'') (eta input_slot) spine_length"
 and tracked: "lpp_runtime_parameter initial_parameter (eta parameter_slot)"
 and functor_fact: "lpp_functor_fact_holds names eta
   (LPPFunctorFact (Var functor_slot) (Var name_slot) (Var input_slot))"
 and parameter_map: "lpp_check_clause_coordinate l (Var n) (Var parameter_target) bindings"
 and name_map: "(Var name_target) \<cdot> lp_cut_instance_subst bindings = Var name_slot"
 and functor_map: "target_functor \<cdot> lp_cut_instance_subst bindings = Var (lp_prefix k functor_slot)"
 and short: "length name_slot < k" "length functor_slot < k"
 and bounds: "2 * k \<le> l"
 defines nu_def: "nu \<equiv> \<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) (lp_cut_resolution_env k l eta sigma rho)"

 shows "lp_cut_knowledge {parameter_target,name_target} [] nu \<and>
  lpp_stable_context_holds operation SP
   ([],map LPPSOpaque opaque_terms,[LPPOEquation target_functor target_functor,
    LPPOShape (copy_spine_grammar (LPCUser ''0:prolog_data_5b5d'') cons)
     (LPReturnShape 0) (Fun (LPCUser ''0:prolog_data_5b5d'') [])]) nu \<and>
  lpp_functor_fact_holds names nu
   (LPPFunctorFact target_functor (Var name_target) (Fun (LPCUser ''0:prolog_data_5b5d'') [])) \<and>
  lpc_return_env [target_functor,Var parameter_target,Var parameter_target] nu =
   (\<lambda>i. lp_isubst (lpc_return_env [Var functor_slot,Var parameter_slot,Var output_slot] eta i) sigma)"
proof -
 note coordinates = copy_functor_successor_coordinates[OF actual spine tracked functor_fact parameter_map name_map functor_map short bounds]
 have ground: "lp_seg_ground (nu parameter_target)" "lp_seg_ground (nu name_target)"
  using coordinates lpp_runtime_parameter_ground[OF tracked] by (simp_all add: nu_def)
 show ?thesis
  using copy_functor_context[OF ground, of operation SP opaque_terms target_functor
    "LPCUser ''0:prolog_data_5b5d''" cons] coordinates
  by (auto simp: nu_def)
qed

ML \<open>
val checked = @{thms copy_empty_shape copy_simple_context copy_functor_context actual_copy_simple_context actual_copy_functor_context};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted copy context" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-global-copy-context/kernel-receipt.txt")
 ("Kernel checked; no skips or oracles. Full node assembly remains open.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "GLOBAL_COPY_CONTEXT_KERNEL_CHECKED";
\<close>
end
