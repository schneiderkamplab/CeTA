theory LP_Cut_Resolution_Bridge
  imports LP_Cut_Resolution_Check LP_Cut_Residual
begin

lemma lp_cut_checked_resolution_equations:
  assumes checked: "lp_cut_check_resolution P fuel k l G A guards a gs c m es next anchors"
    and knowledge: "lp_cut_knowledge (set G) guards \<eta>"
    and unifier: "lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_ieval (fst (P!c)) \<rho>"
  shows "lp_equations (lp_cut_resolution_equations k l G a (fst (P!c)))
    (lp_cut_resolution_env k l \<eta> \<sigma> \<rho>)"
proof -
  have short: "\<forall>x\<in>vars_term a. length x<k"
    and bounds: "2 * k \<le> l"
    using checked by (auto simp: lp_cut_check_resolution_def)
  have ground: "\<forall>x\<in>set G. lp_seg_ground (\<eta> x)"
    using knowledge by (simp add: lp_cut_knowledge_def)
  show ?thesis
    using unifier lp_cut_resolution_active[OF short bounds ground]
    by (simp add: lp_cut_resolution_equations_def lp_equations_def lp_cut_resolution_clause)
qed

lemma lp_cut_resolution_parent_interface:
  assumes "k \<le> l" "\<forall>x\<in>set vs. length x<k"
  shows "map (lp_cut_resolution_env k l \<eta> \<sigma> \<rho>) vs = map \<eta> vs"
  by (rule map_cong[OF refl])
    (use assms in \<open>auto simp: lp_cut_resolution_env_def\<close>)

text \<open>The normalized successor is connected to its separately addressed
graph node. Both interfaces are normalized under the same source-resolution
equations. No supplied unifier is trusted by a checker: the theorem quantifies
over every unifier of the source step.\<close>

theorem lp_cut_resolution_success_node_sound:
  fixes lhs rhs
  assumes program: "lp_cut_source_program P"
    and checked: "lp_cut_check_resolution P fuel k l G A guards a gs c m es next anchors"
    and knowledge: "lp_cut_knowledge (set G) guards \<eta>"
    and unifier: "lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_ieval (fst (P!c)) \<rho>"
    and parent: "\<forall>x\<in>set vs. length x<k"
    and interface: "lp_cut_check_interface fuel
      (lp_cut_resolution_equations k l G a (fst (P!c))) interface_vars interface_terms
      (LPCGoals next#es) (G@sorted_list_of_set (lp_cut_anchor_vars anchors))
      (guards@[LPCHeadGuard a (fst (P!c)) True]) specialized H known"
    and inst: "lp_cut_check_instance specialized H known child J child_guards bindings swaps"
    and inputs: "lp_cut_normalize fuel (lp_cut_resolution_equations k l G a (fst (P!c)))
      (map (\<lambda>x. LPCAtom (Var x)) vs) = Some (Some (map LPCAtom lhs))"
    and outputs: "lp_cut_normalize fuel (lp_cut_resolution_equations k l G a (fst (P!c)))
      (map LPCAtom (map (lp_cut_instance_subst bindings) ws)) = Some (Some (map LPCAtom rhs))"
    and clause: "((f,lhs),[(g,rhs)]) \<in> set Q"
    and ih: "\<And>\<nu>. lp_cut_knowledge (set J) child_guards \<nu> \<Longrightarrow>
      ([(f,map \<eta> vs)],[(g,map \<nu> ws)]) \<in> lp_ild Q \<Longrightarrow>
      SN_on (lp_cut_source P) {lp_cut_state_eval child \<nu>}"
  shows "SN_on (lp_cut_source P)
    {LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t \<rho>)) (snd (P!c)) @
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t \<eta>) \<sigma>)) gs)#lp_cut_state_eval es \<eta>}"
proof -
  let ?env = "lp_cut_resolution_env k l \<eta> \<sigma> \<rho>"
  let ?eqs = "lp_cut_resolution_equations k l G a (fst (P!c))"
  let ?mu = "lp_cut_instance_subst bindings"
  let ?child_env = "\<lambda>x. lp_ieval (?mu x) ?env"
  have equations: "lp_equations ?eqs ?env"
    by (rule lp_cut_checked_resolution_equations[OF checked knowledge unifier])
  have bounds: "2 * k \<le> l" using checked by (simp add: lp_cut_check_resolution_def)
  have kl: "k \<le> l" using bounds by arith
  have old: "map ?env vs=map \<eta> vs"
    by (rule lp_cut_resolution_parent_interface[OF kl parent])
  have resolved: "lp_cut_knowledge (set G \<union> lp_cut_anchor_vars anchors)
    (guards@[LPCHeadGuard a (fst (P!c)) True]) ?env"
    by (rule lp_cut_check_resolution_success(2)[OF checked knowledge unifier])
  have finite: "finite (lp_cut_anchor_vars anchors)"
    by (simp add: lp_cut_anchor_vars_def)
  have known: "lp_cut_knowledge (set H) known ?env"
    by (rule lp_cut_checked_interface_knowledge[OF interface equations])
      (use resolved finite in \<open>simp\<close>)
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
    using original_sn lp_cut_check_resolution_success(1)[OF checked knowledge unifier] by simp
qed

end
