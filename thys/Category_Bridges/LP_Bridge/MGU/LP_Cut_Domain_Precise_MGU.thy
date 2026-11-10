theory LP_Cut_Domain_Precise_MGU
  imports LP_Cut_Domain_Precise_Certificate
begin

text \<open>Most-generality is preserved by the explicit term and goal translations.
The factorization includes the whole continuation and clause body.\<close>

lemma logic_flat_equal_reflect:
  assumes eq: "map (logic_atom_map f) (map (\<lambda>t. ((),[t])) (concat (map logic_goal_terms gs))) =
    map (logic_atom_map g) (map (\<lambda>t. ((),[t])) (concat (map logic_goal_terms gs)))"
  shows "map (logic_goal_map f) gs = map (logic_goal_map g) gs"
proof -
  have pointwise: "\<And>t. t\<in>set (concat (map logic_goal_terms gs)) \<Longrightarrow> f t = g t"
    using eq by (auto simp: map_map logic_atom_map_def map_eq_conv)
  have single: "logic_goal_map f v = logic_goal_map g v" if "v\<in>set gs" for v
  proof -
    have local: "\<forall>t\<in>set (logic_goal_terms v). f t = g t"
      using pointwise that by auto
    show ?thesis using local by (cases v) auto
  qed
  show ?thesis by (rule map_cong[OF refl single])
qed

lemma cut_forward_maps_equal:
  assumes eq: "map (logic_goal_map f) gs = map (logic_goal_map g) gs"
    and f: "\<And>t. cut_tree (f t) = h (k t)"
    and g: "\<And>t. cut_tree (g t) = j (k t)"
  shows "map (lp_cut_map h) (map (cut_goal k) gs) =
    map (lp_cut_map j) (map (cut_goal k) gs)"
proof -
  have left: "cut_goal cut_tree (logic_goal_map f v) = lp_cut_map h (cut_goal k v)" for v
    by (rule cut_goal_map; rule f)
  have right: "cut_goal cut_tree (logic_goal_map g v) = lp_cut_map j (cut_goal k v)" for v
    by (rule cut_goal_map; rule g)
  show ?thesis using arg_cong[OF eq, of "map (cut_goal cut_tree)"]
    by (simp only: map_map o_def left right)
qed

context cut_runtime_domain
begin

lemma precise_mgu_resolve:
  assumes mgu: "logic_cut_mgu (\<lambda>t. D (cut_tree t)) a gs h bs sigma rho"
  shows "mgu_resolve (cut_tree a) (map (cut_goal cut_tree) gs) (cut_term h)
    (map (cut_goal cut_term) bs) (cut_tree \<circ> sigma) (cut_tree \<circ> rho)"
proof -
  have ds: "logic_substitution (\<lambda>t. D (cut_tree t)) sigma"
    and dr: "logic_substitution (\<lambda>t. D (cut_tree t)) rho"
    and eq: "logic_subst sigma a = logic_eval rho h"
    using mgu by (auto simp: logic_cut_mgu_def logic_mgu_def logic_atom_map_def)
  have factor: "\<exists>delta. (\<forall>x. D (delta x)) \<and>
    lp_isubst (lp_isubst (cut_tree a) (cut_tree \<circ> sigma)) delta = lp_isubst (cut_tree a) tau \<and>
    map (lp_cut_map (\<lambda>v. lp_isubst (lp_isubst v (cut_tree \<circ> sigma)) delta)) (map (cut_goal cut_tree) gs) =
      map (lp_cut_map (\<lambda>v. lp_isubst v tau)) (map (cut_goal cut_tree) gs) \<and>
    map (lp_cut_map (\<lambda>v. lp_isubst (lp_ieval v (cut_tree \<circ> rho)) delta)) (map (cut_goal cut_term) bs) =
      map (lp_cut_map (\<lambda>v. lp_ieval v nu)) (map (cut_goal cut_term) bs)"
    if dt: "\<forall>x. D (tau x)" and dn: "\<forall>x. D (nu x)"
      and equal: "lp_isubst (cut_tree a) tau = lp_ieval (cut_term h) nu" for tau nu
  proof -
    let ?t = "cut_tree_back \<circ> tau"
    let ?u = "cut_tree_back \<circ> nu"
    have dt': "logic_substitution (\<lambda>t. D (cut_tree t)) ?t"
      and du': "logic_substitution (\<lambda>t. D (cut_tree t)) ?u"
      using dt dn by (simp_all add: logic_substitution_def)
    have eq': "logic_subst ?t a = logic_eval ?u h"
      by (rule cut_tree_injective[THEN iffD1])
        (use equal in \<open>simp add: cut_tree_subst cut_tree_eval o_def\<close>)
    have mg: "logic_mgu (\<lambda>t. D (cut_tree t)) ((),[a])
      (map (\<lambda>t. ((),[t])) (concat (map logic_goal_terms gs))) ((),[h])
      (map (\<lambda>t. ((),[t])) (concat (map logic_goal_terms bs))) sigma rho"
      using mgu by (simp add: logic_cut_mgu_def)
    obtain delta where dd: "logic_substitution (\<lambda>t. D (cut_tree t)) delta"
      and atom: "logic_subst delta (logic_subst sigma a) = logic_subst ?t a"
      and goals: "map (logic_atom_map (logic_subst delta \<circ> logic_subst sigma))
        (map (\<lambda>t. ((),[t])) (concat (map logic_goal_terms gs))) =
        map (logic_atom_map (logic_subst ?t)) (map (\<lambda>t. ((),[t])) (concat (map logic_goal_terms gs)))"
      and body: "map (logic_atom_map (logic_subst delta \<circ> logic_eval rho))
        (map (\<lambda>t. ((),[t])) (concat (map logic_goal_terms bs))) =
        map (logic_atom_map (logic_eval ?u)) (map (\<lambda>t. ((),[t])) (concat (map logic_goal_terms bs)))"
      using spec[OF spec[OF conjunct2[OF conjunct2[OF conjunct2[OF mg[unfolded logic_mgu_def]]]], of ?t], of ?u] dt' du' eq'
      by (auto simp: logic_atom_map_def)
    have goals': "map (lp_cut_map (\<lambda>v. lp_isubst (lp_isubst v (cut_tree \<circ> sigma)) (cut_tree \<circ> delta)))
        (map (cut_goal cut_tree) gs) = map (lp_cut_map (\<lambda>v. lp_isubst v tau)) (map (cut_goal cut_tree) gs)"
      by (rule cut_forward_maps_equal[OF logic_flat_equal_reflect[OF goals]])
        (simp_all add: cut_tree_subst o_def)
    have body': "map (lp_cut_map (\<lambda>v. lp_isubst (lp_ieval v (cut_tree \<circ> rho)) (cut_tree \<circ> delta)))
        (map (cut_goal cut_term) bs) = map (lp_cut_map (\<lambda>v. lp_ieval v nu)) (map (cut_goal cut_term) bs)"
      by (rule cut_forward_maps_equal[OF logic_flat_equal_reflect[OF body]])
        (simp_all add: cut_tree_subst cut_tree_eval o_def)
    show ?thesis by (rule exI[of _ "cut_tree \<circ> delta"])
      (use dd arg_cong[OF atom, of cut_tree] goals' body' in
        \<open>simp add: logic_substitution_def cut_tree_subst o_def\<close>)
  qed
  show ?thesis unfolding mgu_resolve_def
    using ds dr arg_cong[OF eq, of cut_tree] factor
    by (auto simp: logic_substitution_def cut_tree_subst cut_tree_eval)
qed

lemma precise_mgu_unify:
  assumes mgu: "logic_unify_mgu (\<lambda>t. D (cut_tree t)) a b gs sigma"
  shows "mgu_unify (cut_tree a) (cut_tree b) (map (cut_goal cut_tree) gs) (cut_tree \<circ> sigma)"
proof -
  have ds: "logic_substitution (\<lambda>t. D (cut_tree t)) sigma"
    and eq: "logic_subst sigma a = logic_subst sigma b"
    using mgu by (auto simp: logic_unify_mgu_def)
  have factor: "\<exists>delta. (\<forall>x. D (delta x)) \<and>
    lp_isubst (lp_isubst (cut_tree a) (cut_tree \<circ> sigma)) delta = lp_isubst (cut_tree a) tau \<and>
    map (lp_cut_map (\<lambda>v. lp_isubst (lp_isubst v (cut_tree \<circ> sigma)) delta)) (map (cut_goal cut_tree) gs) =
      map (lp_cut_map (\<lambda>v. lp_isubst v tau)) (map (cut_goal cut_tree) gs)"
    if dt: "\<forall>x. D (tau x)"
      and equal: "lp_isubst (cut_tree a) tau = lp_isubst (cut_tree b) tau" for tau
  proof -
    let ?t = "cut_tree_back \<circ> tau"
    have dt': "logic_substitution (\<lambda>t. D (cut_tree t)) ?t"
      using dt by (simp add: logic_substitution_def)
    have eq': "logic_subst ?t a = logic_subst ?t b"
      by (rule cut_tree_injective[THEN iffD1])
        (use equal in \<open>simp add: cut_tree_subst o_def\<close>)
    obtain delta where dd: "logic_substitution (\<lambda>t. D (cut_tree t)) delta"
      and atom: "logic_subst delta (logic_subst sigma a) = logic_subst ?t a"
      and goals: "map (logic_goal_map (logic_subst delta \<circ> logic_subst sigma)) gs =
        map (logic_goal_map (logic_subst ?t)) gs"
      using spec[OF conjunct2[OF conjunct2[OF mgu[unfolded logic_unify_mgu_def]]], of ?t] dt' eq'
      by blast
    have goals': "map (lp_cut_map (\<lambda>v. lp_isubst (lp_isubst v (cut_tree \<circ> sigma)) (cut_tree \<circ> delta)))
        (map (cut_goal cut_tree) gs) = map (lp_cut_map (\<lambda>v. lp_isubst v tau)) (map (cut_goal cut_tree) gs)"
      by (rule cut_forward_maps_equal[OF goals]) (simp_all add: cut_tree_subst o_def)
    show ?thesis by (rule exI[of _ "cut_tree \<circ> delta"])
      (use dd arg_cong[OF atom, of cut_tree] goals' in
        \<open>simp add: logic_substitution_def cut_tree_subst o_def\<close>)
  qed
  show ?thesis unfolding mgu_unify_def
    using ds arg_cong[OF eq, of cut_tree] factor
    by (auto simp: logic_substitution_def cut_tree_subst)
qed

end
end
