theory LP_Cut_Equality_Bridge
  imports LP_Cut_Equality LP_Cut_Resolution_Bridge
begin

lemma lp_cut_checked_unify_equations:
  assumes checked: "lp_cut_check_unify fuel k l G guards a b gs es next"
    and knowledge: "lp_cut_knowledge (set G) guards \<eta>"
    and unifier: "lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_isubst (lp_ieval b \<eta>) \<sigma>"
  shows "lp_equations [(a\<cdot>lp_cut_refresh k (set G),b\<cdot>lp_cut_refresh k (set G))]
    (lp_cut_resolution_env k l \<eta> \<sigma> \<eta>)"
proof -
  have short_a: "\<forall>x\<in>vars_term a. length x<k"
    and short_b: "\<forall>x\<in>vars_term b. length x<k"
    and bounds: "2 * k \<le> l"
    using checked by (auto simp: lp_cut_check_unify_def)
  have ground: "\<forall>x\<in>set G. lp_seg_ground (\<eta> x)"
    using knowledge by (simp add: lp_cut_knowledge_def)
  show ?thesis
    using unifier lp_cut_resolution_active[OF short_a bounds ground]
      lp_cut_resolution_active[OF short_b bounds ground]
    by (simp add: lp_equations_def)
qed

theorem lp_cut_unify_success_node_sound:
  fixes lhs rhs
  assumes program: "lp_cut_source_program P"
    and checked: "lp_cut_check_unify fuel k l G guards a b gs es next"
    and knowledge: "lp_cut_knowledge (set G) guards \<eta>"
    and unifier: "lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_isubst (lp_ieval b \<eta>) \<sigma>"
    and parent: "\<forall>x\<in>set vs. length x<k"
    and interface: "lp_cut_check_interface fuel
      [(a\<cdot>lp_cut_refresh k (set G),b\<cdot>lp_cut_refresh k (set G))] interface_vars interface_terms
      (LPCGoals next#es) G (guards@[LPCEqGuard a b True]) specialized H known"
    and inst: "lp_cut_check_instance specialized H known child J child_guards bindings swaps"
    and inputs: "lp_cut_normalize fuel [(a\<cdot>lp_cut_refresh k (set G),b\<cdot>lp_cut_refresh k (set G))]
      (map (\<lambda>x. LPCAtom (Var x)) vs) = Some (Some (map LPCAtom lhs))"
    and outputs: "lp_cut_normalize fuel [(a\<cdot>lp_cut_refresh k (set G),b\<cdot>lp_cut_refresh k (set G))]
      (map LPCAtom (map (lp_cut_instance_subst bindings) ws)) = Some (Some (map LPCAtom rhs))"
    and clause: "((f,lhs),[(g,rhs)]) \<in> set Q"
    and ih: "\<And>\<nu>. lp_cut_knowledge (set J) child_guards \<nu> \<Longrightarrow>
      ([(f,map \<eta> vs)],[(g,map \<nu> ws)]) \<in> lp_ild Q \<Longrightarrow>
      SN_on (lp_cut_source P) {lp_cut_state_eval child \<nu>}"
  shows "SN_on (lp_cut_source P)
    {LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t \<eta>) \<sigma>)) gs)#lp_cut_state_eval es \<eta>}"
proof -
  let ?env = "lp_cut_resolution_env k l \<eta> \<sigma> \<eta>"
  let ?eqs = "[(a\<cdot>lp_cut_refresh k (set G),b\<cdot>lp_cut_refresh k (set G))]"
  let ?mu = "lp_cut_instance_subst bindings"
  let ?child_env = "\<lambda>x. lp_ieval (?mu x) ?env"
  have equations: "lp_equations ?eqs ?env"
    by (rule lp_cut_checked_unify_equations[OF checked knowledge unifier])
  have bounds: "2 * k \<le> l" using checked by (simp add: lp_cut_check_unify_def)
  have kl: "k \<le> l" using bounds by arith
  have old: "map ?env vs=map \<eta> vs"
    by (rule lp_cut_resolution_parent_interface[OF kl parent])
  have resolved: "lp_cut_knowledge (set G) (guards@[LPCEqGuard a b True]) ?env"
    by (rule lp_cut_checked_unify_success(2)[OF checked knowledge unifier])
  have known: "lp_cut_knowledge (set H) known ?env"
    by (rule lp_cut_checked_interface_knowledge[OF interface equations resolved])
  have child_known: "lp_cut_knowledge (set J) child_guards ?child_env"
    by (rule lp_cut_checked_instance_knowledge[OF inst known])
  have rhs: "map (\<lambda>t. lp_ieval t ?env) rhs=map ?child_env ws"
    using lp_cut_normalized_terms[OF equations outputs]
    by (simp add: map_map o_def)
  have edge: "([(f,map \<eta> vs)],[(g,map ?child_env ws)]) \<in> lp_ild Q"
    using lp_cut_normalized_residual_step[OF clause equations inputs old] rhs by simp
  have child_sn: "SN_on (lp_cut_source P) {lp_cut_state_eval child ?child_env}"
    by (rule ih[OF child_known edge])
  have specialized_sn: "SN_on (lp_cut_source P) {lp_cut_state_eval specialized ?env}"
    by (rule lp_cut_checked_instance_SN[OF program inst child_sn])
  have original_sn: "SN_on (lp_cut_source P) {lp_cut_state_eval (LPCGoals next#es) ?env}"
    using specialized_sn lp_cut_checked_interface_state[OF interface equations] by simp
  show ?thesis
    using original_sn lp_cut_checked_unify_success(1)[OF checked knowledge unifier] by simp
qed

end
