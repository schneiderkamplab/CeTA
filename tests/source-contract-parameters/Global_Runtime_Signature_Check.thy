theory Global_Runtime_Signature_Check
 imports Native_Structural_Encoding_Check
 "../../thys/Logic_Programming/LP_Residual_Signature"
begin

text \<open>Keep the operational runtime and its invariant in the shared source
alphabet. Map the residual witnesses, including their runtime data coordinates,
into the checker's alphabet. Unconstrained runtime constructors need not occur
in the residual program. This is forward simulation, not reflection of answers.\<close>

definition global_residual_symbol :: "string lp_cut_symbol \<Rightarrow> (string,nat list) lab" where
 "global_residual_symbol f = UnLab (native_source_label f)"

lemma global_signature_lifted_term:
 "map_term global_residual_symbol id (map_term LPCUser id t) = map_term UnLab id t"
 by (induct t) (auto simp: global_residual_symbol_def map_map o_def intro!: map_cong)

lemma global_signature_lifted_program:
 "lp_signature_program global_residual_symbol (lp_signature_program LPCUser Q) =
  lp_signature_program UnLab Q"
 by (auto simp: lp_signature_program_def lp_signature_atom_def global_residual_symbol_def
   map_map o_def global_signature_lifted_term split: prod.splits intro!: map_cong)

lemma global_signature_path:
 assumes "(s,t) \<in> (lp_ild Q)\<^sup>*"
 shows "(map (lp_signature_iatom f) s,map (lp_signature_iatom f) t)
  \<in> (lp_ild (lp_signature_program f Q))\<^sup>*"
 using assms by (induct rule: rtrancl_induct)
  (auto intro: rtrancl_into_rtrancl lp_signature_step)

lemma global_signature_strict_path:
 assumes "(s,t) \<in> (lp_ild Q)\<^sup>+"
 shows "(map (lp_signature_iatom f) s,map (lp_signature_iatom f) t)
  \<in> (lp_ild (lp_signature_program f Q))\<^sup>+"
 using assms by (induct rule: trancl_induct)
  (auto intro: trancl_into_trancl lp_signature_step)

lemma global_signature_answer_contract:
 assumes contract: "lp_answer_contract T ss (lp_ild Q) s returned"
 shows "lp_answer_contract T ss (lp_ild (lp_signature_program f Q))
  (map (lp_signature_iatom f) s) (\<lambda>rho. map (lp_signature_iatom f) (returned rho))"
 using contract global_signature_path
 unfolding lp_answer_contract_def lp_answers_covered_def by blast

lemmas native_arithmetic_equality_checked_signature =
 global_signature_answer_contract[where f=global_residual_symbol,
 OF native_arithmetic_equality_answer_contract]

lemma global_runtime_boundary_transport:
 fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime = lpc_return_eval eta
   [(LPCGoals [LPCUnify (Var ''V0'') (Var ''V1'')],
     [Fun f [Fun g [],Var ''V2''],Var ''V2'',Var ''V0''])]"
 and invariant: "lpp_observer_output_invariant A specs rest 2 hi runtime"
 and clause: "((source_symbol,map Var [''V0'',''V1'',''V2'',s0,s1,s2]),
   [(target_symbol,map Var [''V0'',''V1'',s0,s1])]) \<in> set Q"
 defines child_def: "child \<equiv> lpp_observer_rebase (\<lambda>_ _. lpc_return_env [Var ''V0'',Var ''V1''] eta) runtime"
 shows "lpc_reinterface (\<lambda>env x. env (Inl x)) child =
   lpc_return_eval eta [(LPCGoals [LPCUnify (Var ''V0'') (Var ''V1'')],[Var ''V0'',Var ''V1''])] \<and>
   lpp_observer_output_invariant A specs rest 0 hi child \<and>
   lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child) =
   lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime) \<and>
   ([(global_residual_symbol source_symbol,
     map (\<lambda>x. map_lp_iterm global_residual_symbol id (eta x)) [''V0'',''V1'',''V2'',s0,s1,s2])],
    [(global_residual_symbol target_symbol,
     map (\<lambda>x. map_lp_iterm global_residual_symbol id (eta x)) [''V0'',''V1'',s0,s1])])
    \<in> (lp_ild (lp_signature_program global_residual_symbol Q))\<^sup>+"
proof -
 have preserved: "lpc_reinterface (\<lambda>env x. env (Inl x)) child =
   lpc_return_eval eta [(LPCGoals [LPCUnify (Var ''V0'') (Var ''V1'')],[Var ''V0'',Var ''V1''])] \<and>
   lpp_observer_output_invariant A specs rest 0 hi child \<and>
   lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child) =
   lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)"
  unfolding child_def using arithmetic_equality_payload_rebase[OF represented invariant] by blast
 have path: "([(source_symbol,map eta [''V0'',''V1'',''V2'',s0,s1,s2])],
    [(target_symbol,map eta [''V0'',''V1'',s0,s1])]) \<in> (lp_ild Q)\<^sup>+"
  by (rule global_equality_boundary_strict[OF clause])
 show ?thesis using preserved global_signature_strict_path[OF path, of global_residual_symbol]
  by (simp add: lp_signature_iatom_def map_map o_def)
qed

lemma global_runtime_signature_termination:
 assumes "SN_on (lp_ild (lp_signature_program global_residual_symbol Q))
   {map (lp_signature_iatom global_residual_symbol) s}"
 shows "SN_on (lp_ild Q) {s}"
 by (rule lp_signature_termination_reflect[OF assms])

lemma global_reified_spine_variables:
 "vars_term (lpp_reified_spine ts) = (\<Union>t\<in>set ts. vars_term t)"
 by (induct ts) auto

lemma global_reified_ground:
 assumes "vars_term t = {}"
 shows "vars_term (lpp_reify_structure t) = {}"
 using assms
proof (induct t)
 case (Var x) then show ?case by simp
next
 case (Fun f ts)
 show ?case using Fun by (cases f) (auto simp: global_reified_spine_variables)
qed

lemma global_map_term_ground:
 assumes "vars_term t = {}"
 shows "vars_term (map_term f g t) = {}"
 using assms by (induct t) auto

lemma global_observation_ground:
 assumes "observed_leaf_coordinate encode A initial_tree runtime_value shadow"
 shows "lp_seg_ground shadow"
proof -
 obtain tree where observed: "lpp_runtime_structure runtime_value tree"
 and shadow: "shadow = lp_ieval (map_term encode id (lpp_reify_structure tree)) (\<lambda>_. LPIVar undefined)"
  using assms by (auto simp: observed_leaf_coordinate_def)
 have tree_ground: "vars_term tree = {}"
  using observed lpp_structure_template_ground unfolding lpp_runtime_structure_def by blast
 have ground: "vars_term (lpp_reify_structure tree) = {}"
  by (rule global_reified_ground[OF tree_ground])
 have encoded_ground: "vars_term (map_term encode id (lpp_reify_structure tree)) = {}"
  by (rule global_map_term_ground[OF ground])
 show ?thesis using encoded_ground by (simp only: shadow lp_seg_ground_eval) simp
qed

lemma global_paired_query_ground:
 assumes a: "observed_leaf_coordinate encode A ta a sa"
 and b: "observed_leaf_coordinate encode A tb b sb"
 and c: "observed_leaf_coordinate encode A tc c sc"
 and selected: "i \<in> set [3,4,5]"
 shows "lp_seg_ground ((map (map_lp_iterm global_residual_symbol id) [a,b,c,sa,sb,sc]) ! i)"
 using selected lpc_seg_ground_map[OF global_observation_ground[OF a], of global_residual_symbol]
  lpc_seg_ground_map[OF global_observation_ground[OF b], of global_residual_symbol]
  lpc_seg_ground_map[OF global_observation_ground[OF c], of global_residual_symbol]
 by auto

lemma global_free_runtime_ground_observation:
 fixes A :: "(string lp_cut_symbol,string) term set"
 shows "\<exists>shadow :: (string lp_cut_symbol,string) lp_iterm.
  observed_leaf_coordinate native_structural_symbol A (Fun (Inr ()) [])
   (LPIVar ''x'' :: (string lp_cut_symbol,string) lp_iterm) shadow \<and>
  lp_seg_ground shadow \<and> \<not> lp_seg_ground (LPIVar ''x'' :: (string lp_cut_symbol,string) lp_iterm)"
proof -
 have observed: "lpp_runtime_structure (LPIVar ''x'' :: (string lp_cut_symbol,string) lp_iterm) (Fun (Inr ()) [])"
  unfolding lpp_runtime_structure_def by (rule exI[of _ "Var (''x'')"]) simp
 have effect: "lpp_leaf_effect A (Fun (Inr ()) []) (Fun (Inr ()) [])"
  using lpp_template_leaf_effect_reflexive[of A "Var (''x'')"] by simp
 let ?shadow = "lp_ieval (native_structural_expression (Fun (Inr ()) [] :: (string lp_cut_symbol + unit,unit) term)) (\<lambda>_. LPIVar undefined) :: (string lp_cut_symbol,string) lp_iterm"
 have witness: "observed_leaf_coordinate native_structural_symbol A (Fun (Inr ()) [])
   (LPIVar ''x'' :: (string lp_cut_symbol,string) lp_iterm) ?shadow"
  by (rule native_observation_from_runtime[OF observed effect])
 have ground: "lp_seg_ground ?shadow" by (rule global_observation_ground[OF witness])
 show ?thesis by (rule exI[of _ ?shadow]) (use witness ground in \<open>auto simp: lp_seg_ground.simps\<close>)
qed

lemma global_free_shadow_rejected:
 "\<not> observed_leaf_coordinate encode A initial_tree runtime_value (LPIVar x)"
proof
 assume bad: "observed_leaf_coordinate encode A initial_tree runtime_value (LPIVar x)"
 from global_observation_ground[OF bad] show False by (cases rule: lp_seg_ground.cases)
qed

lemma global_signature_variable_sharing:
 "map_lp_iterm global_residual_symbol id (LPIFun f [LPIVar x,LPIVar x]) =
  LPIFun (global_residual_symbol f) [LPIVar x,LPIVar x]"
 by simp

lemma global_signature_does_not_merge_variables:
 assumes "x \<noteq> y"
 shows "map_lp_iterm global_residual_symbol id (LPIVar x) \<noteq>
  map_lp_iterm global_residual_symbol id (LPIVar y)"
 using assms by simp

ML \<open>
val checked = @{thms global_signature_lifted_term global_signature_lifted_program
 native_arithmetic_equality_checked_signature global_signature_path global_signature_strict_path
 global_signature_answer_contract global_runtime_boundary_transport
 global_runtime_signature_termination global_reified_spine_variables global_reified_ground
 global_map_term_ground global_observation_ground global_paired_query_ground
 global_free_runtime_ground_observation global_free_shadow_rejected global_signature_variable_sharing
 global_signature_does_not_merge_variables};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted global runtime signature transport" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-global-runtime-signature/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. Full-family assembly and concrete certificate instantiation remain open.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "GLOBAL_RUNTIME_SIGNATURE_KERNEL_CHECKED";
\<close>
end
