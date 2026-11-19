theory Global_Boundary_Valuation_Check
 imports Global_Boundary_Observation_Check
begin

lemma scalar_observation_exists:
 "\<exists>shadow. observed_leaf_coordinate encode A (Fun (Inl symbol) []) (LPIFun symbol [] :: ('f,string) lp_iterm) shadow"
proof -
 have observed: "lpp_runtime_structure (LPIFun symbol [] :: ('f,string) lp_iterm) (Fun (Inl symbol) [])"
  unfolding lpp_runtime_structure_def by (rule exI[of _ "Fun symbol []"]) simp
 have effect: "lpp_leaf_effect A (Fun (Inl symbol) []) (Fun (Inl symbol) [])"
  using lpp_template_leaf_effect_reflexive[of A "Fun symbol []"] by simp
 show ?thesis using observed effect by (auto simp: observed_leaf_coordinate_def)
qed

lemma initialize_boundary_structural_valuation:
 fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 and encode :: "(string lp_cut_symbol) lpp_structure_symbol \<Rightarrow> string lp_cut_symbol"
 assumes represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime = lpc_return_eval eta
   [(LPCGoals [LPCUnify (Var ''V0'') (Var ''V1'')],
     [Fun f [Fun g [],Var ''V2''],Var ''V2'',Var ''V0''])]"
 and invariant: "lpp_observer_output_invariant A specs rest 2 hi runtime"
 and covered: "(hi,initial_tree) \<in> set specs"
 and scalar_value: "eta ''V1'' = LPIFun scalar []"
 and fresh: "s0 \<notin> {''V0'',''V1'',''V2'',s2}" "s1 \<notin> {''V0'',''V1'',''V2'',s2}" "s0 \<noteq> s1"
 and clause: "((source_symbol,map Var [''V0'',''V1'',''V2'',s0,s1,s2]),
   [(target_symbol,map Var [''V0'',''V1'',s0,s1])]) \<in> set Q"
 shows "\<exists>nu. (\<forall>x. x \<notin> {s0,s1} \<longrightarrow> nu x = eta x) \<and>
   observed_leaf_coordinate encode A initial_tree (nu ''V0'') (nu s0) \<and>
   observed_leaf_coordinate encode A (Fun (Inl scalar) []) (nu ''V1'') (nu s1) \<and>
   lpc_reinterface (\<lambda>env x. env (Inl x)) runtime = lpc_return_eval nu
    [(LPCGoals [LPCUnify (Var ''V0'') (Var ''V1'')],
      [Fun f [Fun g [],Var ''V2''],Var ''V2'',Var ''V0''])] \<and>
   ([(source_symbol,map nu [''V0'',''V1'',''V2'',s0,s1,s2])],
    [(target_symbol,map nu [''V0'',''V1'',s0,s1])]) \<in> (lp_ild Q)\<^sup>+"
proof -
 obtain output_shadow :: "(string lp_cut_symbol,string) lp_iterm" where output_observed: "observed_leaf_coordinate encode A initial_tree (eta ''V0'') output_shadow"
  using boundary_output_observation_exists[OF represented invariant covered] by blast
 obtain scalar_shadow :: "(string lp_cut_symbol,string) lp_iterm" where scalar_observed: "observed_leaf_coordinate encode A (Fun (Inl scalar) []) (eta ''V1'') scalar_shadow"
  using scalar_observation_exists[of encode A scalar] scalar_value by auto
 let ?nu = "eta(s0 := output_shadow, s1 := scalar_shadow)"
 have old: "?nu ''V0'' = eta ''V0''" "?nu ''V1'' = eta ''V1''" "?nu ''V2'' = eta ''V2''"
  using fresh by auto
 have payload: "lpc_return_env [Fun f [Fun g [],Var ''V2''],Var ''V2'',Var ''V0''] ?nu =
   lpc_return_env [Fun f [Fun g [],Var ''V2''],Var ''V2'',Var ''V0''] eta"
  unfolding lpc_return_env_def using old by (intro ext) (auto simp: nth_Cons split: nat.splits)
 have same: "lpc_return_eval ?nu [(LPCGoals [LPCUnify (Var ''V0'') (Var ''V1'')],
   [Fun f [Fun g [],Var ''V2''],Var ''V2'',Var ''V0''])] =
   lpc_return_eval eta [(LPCGoals [LPCUnify (Var ''V0'') (Var ''V1'')],
   [Fun f [Fun g [],Var ''V2''],Var ''V2'',Var ''V0''])]"
  using old payload by (simp add: lpc_return_eval_def)
 show ?thesis
  apply (rule exI[of _ ?nu])
  using output_observed scalar_observed old fresh represented same
   global_equality_boundary_strict[OF clause, of ?nu]
  by auto
qed

lemma colliding_structural_coordinate_changes_source:
 assumes different: "shadow \<noteq> eta ''V0''"
 shows "(eta(''V0'' := shadow)) ''V0'' \<noteq> eta ''V0''"
 using different by simp

ML \<open>
val checked = @{thms scalar_observation_exists initialize_boundary_structural_valuation
 colliding_structural_coordinate_changes_source};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted boundary valuation" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-global-boundary-valuation/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. Native encoding and family preservation remain open.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "GLOBAL_BOUNDARY_VALUATION_KERNEL_CHECKED";
\<close>
end
