theory LP_Prolog_Structural_Observation
 imports LP_Prolog_Matching_Structure
 "Proof_Checker_Base.Forest_Return_Order"
begin

text \<open>Structural observations erase runtime variable names, not constructors.
They are additional residual data; runtime sharing and source contexts remain
separate. Only a finite runtime template can initialize this observation.\<close>

definition lpp_runtime_structure where
 "lpp_runtime_structure t structure = (\<exists>template.
   t=lp_ieval template LPIVar \<and> structure=lpp_structure_template template)"

lemma lpp_structure_template_rename:
 "lpp_structure_template (map_term id rename t)=lpp_structure_template t"
 by (induct t) (auto simp: map_map o_def intro!: map_cong)

lemma lpp_structure_template_ground:
 "vars_term (lpp_structure_template t)={}"
 by (induct t) auto

lemma lpp_runtime_structure_finite:
 "lpp_runtime_structure t structure \<Longrightarrow> lpp_finite_term t"
 unfolding lpp_runtime_structure_def using lpp_finite_term_initial by blast

lemma lpp_runtime_structure_exists:
 "lpp_finite_term t \<Longrightarrow> \<exists>structure. lpp_runtime_structure t structure"
 unfolding lpp_runtime_structure_def using lpp_finite_runtime_template by blast

lemma lpp_ieval_template_rename:
 "lp_ieval (map_term id rename t) LPIVar=lp_ieval t (LPIVar \<circ> rename)"
 by (induct t) (auto simp: map_map o_def intro!: map_cong)

theorem lpp_matching_head_structural_observation:
 assumes mgu: "lpc_mgu_resolve a gs h bs sigma rho"
 and matching: "lp_ieval h nu=a"
 and finite: "lpp_finite_term a"
 shows "\<exists>structure. lpp_runtime_structure a structure \<and>
   lpp_runtime_structure (lp_ieval h rho) structure"
proof -
 obtain template rename where initial: "a=lp_ieval template LPIVar"
 and final: "lp_ieval h rho=lp_ieval template (LPIVar \<circ> rename)"
  using lpp_matching_head_preserves_structure[OF mgu matching finite] by blast
 have target: "lp_ieval h rho=lp_ieval (map_term id rename template) LPIVar"
  by (simp only: final lpp_ieval_template_rename)
 have lhs: "lpp_runtime_structure a (lpp_structure_template template)"
  unfolding lpp_runtime_structure_def using initial by blast
 have rhs: "lpp_runtime_structure (lp_ieval h rho) (lpp_structure_template template)"
  unfolding lpp_runtime_structure_def
  by (rule exI[of _ "map_term id rename template"]) (simp add: target lpp_structure_template_rename)
 show ?thesis using lhs rhs by blast
qed

lemma lpp_constructor_arguments_structural_observation:
 assumes observed: "lpp_constructor_arguments value f arguments"
 and finite: "lpp_finite_term value"
 shows "\<exists>children. lpp_runtime_structure value
    (Fun (Inl f) (map lpp_structure_template children)) \<and>
   arguments=lpp_argument_list (map (\<lambda>t. lp_ieval t LPIVar) children) \<and>
   list_all (\<lambda>t. lpp_runtime_structure (lp_ieval t LPIVar)
     (lpp_structure_template t)) children"
proof -
 obtain children where represented: "value=lp_ieval (Fun f children) LPIVar"
 and args: "arguments=lpp_argument_list (map (\<lambda>t. lp_ieval t LPIVar) children)"
  using lpp_constructor_arguments_finite_template[OF observed finite] by blast
 have node: "lpp_runtime_structure value (Fun (Inl f) (map lpp_structure_template children))"
  unfolding lpp_runtime_structure_def
  by (rule exI[of _ "Fun f children"]) (simp add: represented)
 have child: "lpp_runtime_structure (lp_ieval t LPIVar) (lpp_structure_template t)" for t
  unfolding lpp_runtime_structure_def by blast
 show ?thesis by (rule exI[of _ children]) (simp add: node args child list_all_iff)
qed

lemma lpp_cyclic_runtime_has_no_structure:
 assumes cyclic: "t=LPIFun f [t]"
 shows "\<not> lpp_runtime_structure t structure"
 using lpp_cyclic_runtime_has_no_finite_template[OF cyclic]
 unfolding lpp_runtime_structure_def by blast

ML \<open>
val checked = @{thms lpp_structure_template_rename lpp_structure_template_ground
 lpp_runtime_structure_finite lpp_runtime_structure_exists lpp_ieval_template_rename
 lpp_matching_head_structural_observation lpp_constructor_arguments_structural_observation
 lpp_cyclic_runtime_has_no_structure};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted structural observation" else ();
\<close>
end
