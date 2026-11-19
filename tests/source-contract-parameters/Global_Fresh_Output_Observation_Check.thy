theory Global_Fresh_Output_Observation_Check
 imports Global_Cons_Observation_Check
begin

lemma actual_fresh_output_observation:
 fixes k :: nat
 and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes checked: "lpp_check_body_output h bs l body_variable target_term bindings"
 and actual: "lpc_mgu_resolve a gs h bs sigma rho"
 and finite: "lpp_finite_term (lp_isubst a sigma)"
 defines nu_def: "nu \<equiv> \<lambda>x. lp_ieval (lp_cut_instance_subst bindings x)
   (lp_cut_resolution_env k l eta sigma rho)"
 shows "(\<exists>v. lp_ieval target_term nu = LPIVar v) \<and>
  observed_leaf_coordinate encode A (Fun (Inr ()) []) (lp_ieval target_term nu)
   (LPIFun (encode LPPStructureLeaf) []) \<and>
  set2_lp_iterm (lp_ieval target_term nu) \<inter> set2_lp_iterm (lp_isubst a sigma) = {}"
proof -
 obtain v where fresh: "lp_ieval target_term nu = LPIVar v"
  using lpp_checked_body_output_free[OF checked actual, of k eta] by (auto simp: nu_def)
 have structure_fact: "lpp_runtime_structure (lp_ieval target_term nu) (Fun (Inr ()) [])"
  unfolding lpp_runtime_structure_def
  by (rule exI[of _ "Var v"]) (simp add: fresh)
 have reflexive: "lpp_leaf_effect A (Fun (Inr ()) []) (Fun (Inr ()) [])"
  using lpp_template_leaf_effect_reflexive[of A "Var v"] by simp
 have observation: "observed_leaf_coordinate encode A (Fun (Inr ()) []) (lp_ieval target_term nu)
   (LPIFun (encode LPPStructureLeaf) [])"
  unfolding observed_leaf_coordinate_def
  by (rule exI[of _ "Fun (Inr ()) []"]) (simp add: structure_fact reflexive)
 have separate: "set2_lp_iterm (lp_ieval target_term nu) \<inter> set2_lp_iterm (lp_isubst a sigma) = {}"
  using lpp_checked_body_output_separate_head[OF checked actual finite, of k eta] by (simp add: nu_def)
 show ?thesis using fresh observation separate by blast
qed

lemma fresh_output_observation_not_runtime_leaf:
 "(LPIVar v :: (string lp_cut_symbol,string) lp_iterm) \<noteq> LPIFun leaf_symbol []"
 by simp


lemma cons_fresh_output_observation:
 fixes k :: nat
 and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes checked: "lpp_check_body_output
  (Fun p (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y]#map Var H)) bs l body_variable target_term bindings"
 and actual: "lpc_mgu_resolve (LPIFun p (input_value#actuals)) gs
  (Fun p (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y]#map Var H)) bs sigma rho"
 and spine: "lpp_list_length input_value spine_length"
 and distinct: "distinct (x#y#H)"
 and lengths: "length H=length actuals"
 and finite_call: "lpp_finite_term (LPIFun p (input_value#actuals))"
 defines nu_def: "nu \<equiv> \<lambda>x. lp_ieval (lp_cut_instance_subst bindings x)
   (lp_cut_resolution_env k l eta sigma rho)"
 shows "(\<exists>v. lp_ieval target_term nu = LPIVar v) \<and>
  observed_leaf_coordinate encode A (Fun (Inr ()) []) (lp_ieval target_term nu)
   (LPIFun (encode LPPStructureLeaf) []) \<and>
  set2_lp_iterm (lp_ieval target_term nu) \<inter> set2_lp_iterm (lp_isubst (LPIFun p (input_value#actuals)) sigma) = {}"
proof -
 have finite: "lpp_finite_term (lp_isubst (LPIFun p (input_value#actuals)) sigma)"
  by (rule lpp_cons_head_finite_instance[OF spine actual distinct lengths finite_call])
 show ?thesis using actual_fresh_output_observation[OF checked actual finite, of k eta encode A]
  by (simp add: nu_def)
qed

ML \<open>
val checked = @{thms actual_fresh_output_observation cons_fresh_output_observation fresh_output_observation_not_runtime_leaf};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted fresh output observation" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-global-fresh-output-observation/kernel-receipt.txt")
 ("Kernel checked; no skips or oracles. Fresh output observation and separation derived from actual MGU. Full assembly remains open.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "GLOBAL_FRESH_OUTPUT_OBSERVATION_KERNEL_CHECKED";
\<close>
end
