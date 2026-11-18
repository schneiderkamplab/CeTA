theory LP_Prolog_Relational_Ground_Equality
 imports LP_Prolog_Relational_Fresh_Leaf
begin

text \<open>Ground equality reuses the resolution image theorem through the
same most-general substitution condition. This is a logical reduction of an
existing source step, not a second operational semantics.\<close>

lemma lpp_ground_unify_resolution:
 fixes a :: "('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_unify a (lp_ieval h LPIVar) gs sigma"
 and closed: "vars_term h={}"
 shows "lpc_mgu_resolve a gs h [] sigma LPIVar"
proof -
 have ground: "lp_seg_ground (lp_ieval h LPIVar)"
  using closed by (simp add: lp_seg_ground_eval)
 have same: "lp_ieval h nu=lp_ieval h LPIVar" for nu
  by (rule lp_ieval_cong) (use closed in auto)
 have equation: "lp_isubst a sigma=lp_ieval h LPIVar"
  using mgu by (simp only: lpc_mgu_unify_def lp_seg_ground_subst[OF ground])
 have factor: "\<And>tau. lp_isubst a tau=lp_ieval h LPIVar \<Longrightarrow>
   \<exists>delta. lp_isubst (lp_isubst a sigma) delta=lp_isubst a tau \<and>
    map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta)) gs =
    map (lp_cut_map (\<lambda>t. lp_isubst t tau)) gs"
  using mgu unfolding lpc_mgu_unify_def
  by (simp only: lp_seg_ground_subst[OF ground]; blast)
 show ?thesis unfolding lpc_mgu_resolve_def
 proof (intro conjI allI impI)
  show "lp_isubst a sigma=lp_ieval h LPIVar" by (rule equation)
 next
  fix theta nu :: "string \<Rightarrow> ('f,string) lp_iterm"
  assume comparison: "lp_isubst a theta=lp_ieval h nu"
  have fixed: "lp_isubst a theta=lp_ieval h LPIVar" by (rule HOL.trans[OF comparison same])
  obtain delta where one: "lp_isubst (lp_isubst a sigma) delta=lp_isubst a theta"
   and rest: "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta)) gs =
    map (lp_cut_map (\<lambda>t. lp_isubst t theta)) gs"
   using factor[OF fixed] by blast
  show "\<exists>delta. lp_isubst (lp_isubst a sigma) delta=lp_isubst a theta \<and>
   map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta)) gs =
    map (lp_cut_map (\<lambda>t. lp_isubst t theta)) gs \<and>
   map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t LPIVar) delta)) [] =
    map (lp_cut_map (\<lambda>t. lp_ieval t nu)) []"
   by (rule exI[of _ delta]) (use one rest in simp)
 qed
qed

lemma lpp_runtime_ground_equality_leaf_images:
 assumes mgu: "lpc_mgu_unify a b gs sigma"
 and ground: "lp_seg_ground b"
 and finite_call: "lpp_finite_term a"
 and finite_rest: "lpp_finite_goals gs"
 and covered: "V \<subseteq> set2_lp_iterm a \<union>
   (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
 shows "lpp_bounded_images {u. vars_term u={}} sigma V"
proof -
 have finite_b: "lpp_finite_term b" by (rule lpp_ground_finite_term[OF ground])
 obtain h where represented: "b=lp_ieval h LPIVar"
  using lpp_finite_runtime_template[OF finite_b] by blast
 have closed: "vars_term h={}"
  using ground by (auto simp: represented lp_seg_ground_eval elim: lp_seg_ground.cases)
 have resolution: "lpc_mgu_resolve a gs h [] sigma LPIVar"
  by (rule lpp_ground_unify_resolution[OF _ closed]) (use mgu represented in simp)
 show ?thesis by (rule lpp_runtime_ground_head_bounded_images[OF resolution finite_call finite_rest])
  (use finite_b ground covered in \<open>auto simp: represented\<close>)
qed

lemma lpp_relational_ground_equality_leaf_transport:
 assumes coverage: "lpp_check_relational_leaf_coverage facts (map fst specs) payload a gs"
 and facts: "list_all (lpp_functor_fact_holds names eta) facts"
 and mgu: "lpc_mgu_unify (lp_ieval a eta) b
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma"
 and ground: "lp_seg_ground b"
 and finite_call: "lpp_finite_term (lp_ieval a eta)"
 and finite_rest: "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
 shows "lpp_leaf_environment_transport {u. vars_term u={}} specs
   (lpc_return_env payload eta) sigma"
proof (unfold lpp_leaf_environment_transport_def, intro ballI impI, clarify)
 fix slot shape
 assume member: "(slot,shape)\<in>set specs"
 and known: "lpp_runtime_leaf_effect {u. vars_term u={}} shape (lpc_return_env payload eta slot)"
 have support: "set2_lp_iterm (lpc_return_env payload eta slot) \<subseteq>
   set2_lp_iterm (lp_ieval a eta) \<union>
    (\<Union>g\<in>set (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs).
      \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
  by (rule lpp_relational_leaf_coverage_sound[OF coverage facts]) (use member in auto)
 show "lpp_runtime_leaf_effect {u. vars_term u={}} shape
   (lp_isubst (lpc_return_env payload eta slot) sigma)"
  by (rule lpp_runtime_leaf_effect_substitute[OF known
    lpp_runtime_ground_equality_leaf_images[OF mgu ground finite_call finite_rest support]]) simp
qed

ML \<open>
val checked = @{thms lpp_ground_unify_resolution lpp_runtime_ground_equality_leaf_images
 lpp_relational_ground_equality_leaf_transport};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted relational ground equality" else ();
\<close>
end
