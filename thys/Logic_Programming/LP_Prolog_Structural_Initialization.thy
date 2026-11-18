theory LP_Prolog_Structural_Initialization
 imports LP_Prolog_Structural_Projection LP_Prolog_Reified_Argument_Program LP_Cut_Root
begin

text \<open>Observation initialization uses finite runtime values, not runtime
 groundness. Observations erase variable names and are ground even for a free
 source argument. The environment is shared across all retained coordinates.\<close>

lemma lpp_runtime_structure_ground:
 "lpp_runtime_structure t observed_tree \<Longrightarrow> vars_term observed_tree={}"
 unfolding lpp_runtime_structure_def using lpp_structure_template_ground by blast

lemma lpp_finite_structural_environment:
 fixes rho :: "'v \<Rightarrow> ('f,'w) lp_iterm"
 assumes finite: "\<And>x. x\<in>V \<Longrightarrow> lpp_finite_term (rho x)"
 shows "\<exists>eta. \<forall>x\<in>V. lpp_runtime_structure (rho x) (eta x) \<and> vars_term (eta x)={}"
proof -
 have exists: "\<exists>s. lpp_runtime_structure (rho x) s" if "x\<in>V" for x
  by (rule lpp_runtime_structure_exists[OF finite[OF that]])
 let ?eta = "\<lambda>x. SOME s. lpp_runtime_structure (rho x) s"
 have observed: "lpp_runtime_structure (rho x) (?eta x)" if "x\<in>V" for x
  by (rule someI_ex[OF exists[OF that]])
 show ?thesis by (rule exI[of _ ?eta]) (use observed lpp_runtime_structure_ground in blast)
qed

lemma lpp_query_structural_environment:
 assumes lengths: "length vs=length ts" and distinct: "distinct vs"
 and finite: "list_all lpp_finite_term ts"
 shows "\<exists>eta. \<forall>x\<in>set vs.
   lpp_runtime_structure (lp_cut_query_env vs ts x) (eta x) \<and> vars_term (eta x)={}"
proof -
 have vals: "map (lp_cut_query_env vs ts) vs=ts"
  by (rule lp_cut_query_env_values[OF lengths distinct])
 have bounded: "lpp_finite_term (lp_cut_query_env vs ts x)" if "x\<in>set vs" for x
  proof -
  have member: "lp_cut_query_env vs ts x\<in>set ts"
   using that by (subst vals[symmetric]) auto
  show ?thesis using finite member by (simp add: list_all_iff)
 qed
 show ?thesis by (rule lpp_finite_structural_environment[OF bounded])
qed

lemma lpp_free_argument_has_ground_observation:
 "lpp_runtime_structure (LPIVar x) (Fun (Inr ()) []) \<and>
  vars_term (Fun (Inr ()) [])={}"
 unfolding lpp_runtime_structure_def
 by (auto intro!: exI[of _ "Var x"])


lemma lpp_actual_univ_reified_program_success:
 assumes actual: "lpp_constructor_arguments value f arguments"
 and node: "lpp_runtime_structure value node_structure"
 and observed_args: "lpp_runtime_structure arguments arguments_structure"
 shows "\<exists>children.
   lpp_reified_observation node_structure =
    Fun LPPStructureNode [Fun (LPPStructureLabel f) [],lpp_reified_spine children] \<and>
   (([lp_atom_eval (predicate,[lpp_reified_spine children,
       lpp_reified_observation arguments_structure]) LPIVar],env),([],env))
    \<in> (lp_seg_answer_step (lpp_reified_argument_program predicate))\<^sup>*"
proof -
 have relation: "lpp_structural_univ node_structure f arguments_structure"
  by (rule lpp_constructor_arguments_structural_univ[OF actual node observed_args])
 obtain ts where shape: "node_structure=Fun (Inl f) ts"
 and arg_shape: "arguments_structure=lpp_structural_argument_list ts"
  using relation by (cases "(node_structure,f,arguments_structure)" rule: lpp_structural_univ.cases) auto
 let ?children = "map (\<lambda>t. map_term id (\<lambda>_. 0::nat) (lpp_reify_structure t)) ts"
 have converted: "lpp_reified_observation arguments_structure=lpp_reified_arguments ?children"
  by (simp add: arg_shape lpp_reified_observation_def lpp_reify_argument_list lpp_reified_arguments_map map_map o_def)
 show ?thesis
  by (rule exI[of _ ?children])
   (simp add: shape lpp_reified_observation_def lpp_reified_spine_map map_map o_def
      arg_shape lpp_reify_argument_list lpp_reified_arguments_map lpp_reified_argument_program_success)
qed

ML \<open>
val checked = @{thms lpp_runtime_structure_ground lpp_finite_structural_environment
 lpp_query_structural_environment lpp_free_argument_has_ground_observation
 lpp_actual_univ_reified_program_success};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted structural initialization" else ();
\<close>
end
