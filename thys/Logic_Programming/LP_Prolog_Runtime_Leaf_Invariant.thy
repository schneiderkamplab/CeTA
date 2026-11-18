theory LP_Prolog_Runtime_Leaf_Invariant
 imports LP_Prolog_Leaf_Effect_Composition LP_Prolog_Matching_Context_Structure
   LP_Prolog_Bounded_Arithmetic LP_Prolog_Bounded_Unify
begin

text \<open>The invariant relates an initial observation to the current actual
runtime value. It is not an abstract residual answer set. Local transport keeps
its source side conditions, and saved environments are handled separately.\<close>

definition lpp_runtime_leaf_effect :: "('f,'v) term set \<Rightarrow>
 ('f+unit,unit) term \<Rightarrow> ('f,'v) lp_iterm \<Rightarrow> bool" where
 "lpp_runtime_leaf_effect A initial_structure runtime_value =
  (\<exists>current_structure. lpp_runtime_structure runtime_value current_structure \<and>
    lpp_leaf_effect A initial_structure current_structure)"

lemma lpp_template_runtime_support:
 "set2_lp_iterm (lp_ieval t LPIVar) = vars_term t"
 by (induct t) auto

lemma lpp_template_leaf_effect_reflexive:
 "lpp_leaf_effect A (lpp_structure_template t) (lpp_structure_template t)"
 by (induct t) (auto simp: list_all2_same intro: lpp_leaf_effect.intros)

lemma lpp_runtime_leaf_effect_initial:
 assumes observed: "lpp_runtime_structure runtime_value initial_structure"
 shows "lpp_runtime_leaf_effect A initial_structure runtime_value"
 using observed lpp_template_leaf_effect_reflexive
 unfolding lpp_runtime_leaf_effect_def lpp_runtime_structure_def by blast

lemma lpp_runtime_leaf_effect_finite:
 "lpp_runtime_leaf_effect A initial_structure runtime_value \<Longrightarrow> lpp_finite_term runtime_value"
 unfolding lpp_runtime_leaf_effect_def using lpp_runtime_structure_finite by blast

lemma lpp_runtime_leaf_effect_preserved_observation:
 assumes known: "lpp_runtime_leaf_effect A initial_structure before_value"
 and before: "lpp_runtime_structure before_value observed_tree"
 and after: "lpp_runtime_structure after_value observed_tree"
 shows "lpp_runtime_leaf_effect A initial_structure after_value"
 using known before after lpp_runtime_structure_unique
 unfolding lpp_runtime_leaf_effect_def by blast

lemma lpp_runtime_leaf_effect_substitute:
 assumes known: "lpp_runtime_leaf_effect A initial_structure runtime_value"
 and bounded: "lpp_bounded_images A sigma (set2_lp_iterm runtime_value)"
 and ground_templates: "\<And>u. u\<in>A \<Longrightarrow> vars_term u = {}"
 shows "lpp_runtime_leaf_effect A initial_structure (lp_isubst runtime_value sigma)"
proof -
 obtain t where represented: "runtime_value = lp_ieval t LPIVar"
 and earlier: "lpp_leaf_effect A initial_structure (lpp_structure_template t)"
  using known unfolding lpp_runtime_leaf_effect_def lpp_runtime_structure_def by blast
 have images: "lpp_bounded_images A sigma (vars_term t)"
  using bounded by (simp add: represented lpp_template_runtime_support)
 obtain u where returned: "lp_isubst (lp_ieval t LPIVar) sigma = lp_ieval u LPIVar"
 and later: "lpp_leaf_effect A (lpp_structure_template t) (lpp_structure_template u)"
  using lpp_bounded_runtime_structural_effect[OF images] by blast
 have composed: "lpp_leaf_effect A initial_structure (lpp_structure_template u)"
  by (rule lpp_leaf_effect_transitive[OF earlier later]) (rule ground_templates)
 show ?thesis unfolding lpp_runtime_leaf_effect_def lpp_runtime_structure_def
  using represented returned composed by blast
qed

lemma lpp_runtime_leaf_effect_matching:
 fixes eta sigma rho :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes known: "lpp_runtime_leaf_effect A initial_structure (eta x)"
 and mgu: "lpc_mgu_resolve (lp_ieval call eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) h bs sigma rho"
 and matching: "lp_ieval h nu = lp_ieval call eta"
 and covered: "x\<in>vars_term call \<union>
   (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 shows "lpp_runtime_leaf_effect A initial_structure (lp_isubst (eta x) sigma)"
proof -
 have finite: "lpp_finite_term (eta x)" by (rule lpp_runtime_leaf_effect_finite[OF known])
 obtain observed_tree where before: "lpp_runtime_structure (eta x) observed_tree"
 and after: "lpp_runtime_structure (lp_isubst (eta x) sigma) observed_tree"
  using lpp_matching_context_structural_observation[OF mgu matching covered finite] by blast
 show ?thesis by (rule lpp_runtime_leaf_effect_preserved_observation[OF known before after])
qed

lemma lpp_runtime_leaf_effect_arithmetic:
 assumes known: "lpp_runtime_leaf_effect A initial_structure runtime_value"
 and success: "lpp_stable_is_outcome operation a e (LPPBuiltinSuccess mu)"
 and atoms: "\<And>f. Fun (LPCUser f) []\<in>A"
 and ground_templates: "\<And>u. u\<in>A \<Longrightarrow> vars_term u = {}"
 shows "lpp_runtime_leaf_effect A initial_structure (lp_isubst runtime_value mu)"
 by (rule lpp_runtime_leaf_effect_substitute[OF known])
   (rule lpp_stable_is_bounded_images[OF success], rule atoms, rule ground_templates)


lemma lpp_runtime_leaf_effect_ground_binding:
 fixes sigma :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes known: "lpp_runtime_leaf_effect A initial_structure runtime_value"
 and mgu: "lpc_mgu_unify (LPIVar x) (lp_ieval u LPIVar)
   (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) sigma"
 and ground_templates: "\<And>t. t\<in>A \<Longrightarrow> vars_term t = {}"
 and allowed: "u\<in>A"
 and covered: "set2_lp_iterm runtime_value \<subseteq> insert x
   (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 shows "lpp_runtime_leaf_effect A initial_structure (lp_isubst runtime_value sigma)"
proof (rule lpp_runtime_leaf_effect_substitute[OF known])
 show "lpp_bounded_images A sigma (set2_lp_iterm runtime_value)"
  by (rule lpp_ground_binding_bounded_images[OF mgu ground_templates[OF allowed] allowed covered])
next
 fix t assume "t\<in>A"
 then show "vars_term t = {}" by (rule ground_templates)
qed

lemma lpp_runtime_leaf_effect_reflexive:
 fixes eta sigma :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes known: "lpp_runtime_leaf_effect A initial_structure (eta x)"
 and mgu: "lpc_mgu_unify (lp_ieval a eta) (lp_ieval b eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma"
 and equal: "lp_ieval a eta = lp_ieval b eta"
 and covered: "x\<in>(\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 shows "lpp_runtime_leaf_effect A initial_structure (lp_isubst (eta x) sigma)"
proof -
 have finite: "lpp_finite_term (eta x)" by (rule lpp_runtime_leaf_effect_finite[OF known])
 obtain observed_tree where before: "lpp_runtime_structure (eta x) observed_tree"
 and after: "lpp_runtime_structure (lp_isubst (eta x) sigma) observed_tree"
  using lpp_reflexive_context_structural_observation[OF mgu equal covered finite] by blast
 show ?thesis by (rule lpp_runtime_leaf_effect_preserved_observation[OF known before after])
qed

ML \<open>
val checked = @{thms lpp_template_runtime_support lpp_template_leaf_effect_reflexive
 lpp_runtime_leaf_effect_initial lpp_runtime_leaf_effect_finite
 lpp_runtime_leaf_effect_preserved_observation lpp_runtime_leaf_effect_substitute
 lpp_runtime_leaf_effect_matching lpp_runtime_leaf_effect_arithmetic
 lpp_runtime_leaf_effect_ground_binding lpp_runtime_leaf_effect_reflexive};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted runtime leaf invariant" else ();
\<close>
end
