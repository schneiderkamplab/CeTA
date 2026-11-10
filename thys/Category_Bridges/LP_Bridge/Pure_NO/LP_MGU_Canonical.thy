theory LP_MGU_Canonical
  imports LP_Finite_MGU_Lifting
begin

abbreviation lp_finite_tree where
  "lp_finite_tree t \<equiv> logic_embed (from_term t)"
lemma lp_finite_tree_translation[simp]:
  "logic_to_native (lp_finite_tree t)=lp_ieval t LPIVar"
  by (simp add: logic_embed_translation)
lemma logic_subst_embed_eval:
  "logic_subst s (logic_embed t)=logic_eval s t"
  by (induct t) (auto simp: map_map o_def)
lemma logic_subst_eval_compose:
  "logic_subst d (logic_eval s t)=logic_eval (\<lambda>x. logic_subst d (s x)) t"
  by (induct t) (auto simp: map_map o_def)
lemma lp_finite_tree_substitution:
  "logic_eval (\<lambda>x. lp_finite_tree (sigma x)) (from_term t)=lp_finite_tree (t\<cdot>sigma)"
  by (induct t) (auto simp: map_map o_def)
lemma logic_finite_eval_substitution:
  "logic_eval (\<lambda>x. lp_finite_tree (sigma x)) t=lp_finite_tree (to_term t\<cdot>sigma)"
  using lp_finite_tree_substitution[of sigma "to_term t"] by simp
lemma lp_atom_tree_evaluation:
  "logic_atom_map logic_to_native (logic_atom_map (logic_eval s \<circ> from_term) a)=
    lp_atom_eval a (logic_to_native \<circ> s)"
  by (simp add: logic_atom_map_def lp_atom_eval_def logic_eval_translation map_map o_def)

lemma lp_universal_mgu_canonical:
  fixes D :: "'f logic_tree \<Rightarrow> bool"
    and a h :: "('f,string) lp_atom"
  assumes mgu: "lp_universal_mgu a h sigma rho"
    and finite: "\<And>t. D (logic_embed t)"
  shows "logic_mgu D (logic_atom_map lp_finite_tree a)
    (map (logic_atom_map lp_finite_tree) gs)
    (logic_atom_map from_term h) (map (logic_atom_map from_term) bs)
    (\<lambda>x. lp_finite_tree (sigma x)) (\<lambda>x. lp_finite_tree (rho x))"
proof -
  let ?s = "\<lambda>x. lp_finite_tree (sigma x)"
  let ?r = "\<lambda>x. lp_finite_tree (rho x)"
  have sd: "logic_substitution D ?s" and rd: "logic_substitution D ?r"
    using finite by (auto simp: logic_substitution_def)
  have match: "lp_atom_subst a sigma=lp_atom_subst h rho"
    using mgu by (simp add: lp_universal_mgu_def)
  have equal: "logic_atom_map (logic_subst ?s) (logic_atom_map lp_finite_tree a)=
    logic_atom_map (logic_eval ?r) (logic_atom_map from_term h)"
    using arg_cong[OF match, of "logic_atom_map lp_finite_tree"]
    by (simp add: logic_atom_map_def lp_atom_subst_def map_map o_def
      logic_subst_embed_eval lp_finite_tree_substitution)
  show ?thesis
  proof (unfold logic_mgu_def, intro conjI)
    show "logic_substitution D ?s" by (rule sd)
    show "logic_substitution D ?r" by (rule rd)
    show "logic_atom_map (logic_subst ?s) (logic_atom_map lp_finite_tree a)=
      logic_atom_map (logic_eval ?r) (logic_atom_map from_term h)" by (rule equal)
    show "\<forall>t u. logic_substitution D t \<longrightarrow> logic_substitution D u \<longrightarrow>
      logic_atom_map (logic_subst t) (logic_atom_map lp_finite_tree a)=
        logic_atom_map (logic_eval u) (logic_atom_map from_term h) \<longrightarrow>
      (\<exists>d. logic_substitution D d \<and>
        logic_atom_map (logic_subst d \<circ> logic_subst ?s) (logic_atom_map lp_finite_tree a)=
          logic_atom_map (logic_subst t) (logic_atom_map lp_finite_tree a) \<and>
        map (logic_atom_map (logic_subst d \<circ> logic_subst ?s)) (map (logic_atom_map lp_finite_tree) gs)=
          map (logic_atom_map (logic_subst t)) (map (logic_atom_map lp_finite_tree) gs) \<and>
        map (logic_atom_map (logic_subst d \<circ> logic_eval ?r)) (map (logic_atom_map from_term) bs)=
          map (logic_atom_map (logic_eval u)) (map (logic_atom_map from_term) bs))"
    proof (intro allI impI)
      fix t u
      assume td: "logic_substitution D t" and ud: "logic_substitution D u"
        and eq: "logic_atom_map (logic_subst t) (logic_atom_map lp_finite_tree a)=
          logic_atom_map (logic_eval u) (logic_atom_map from_term h)"
      let ?t = "logic_to_native \<circ> t"
      let ?u = "logic_to_native \<circ> u"
      have eq': "lp_atom_eval a ?t=lp_atom_eval h ?u"
        using arg_cong[OF eq, of "logic_atom_map logic_to_native"]
        by (simp add: logic_atom_map_def lp_atom_eval_def logic_subst_embed_eval logic_eval_translation map_map o_def)
      obtain delta where sf: "\<And>x. lp_ieval (sigma x) delta=?t x"
        and rf: "\<And>x. lp_ieval (rho x) delta=?u x"
        and dom: "\<And>x. delta x\<in>range ?t\<union>range ?u\<union>range LPIVar"
        using mgu eq' unfolding lp_universal_mgu_def by blast
      let ?d = "logic_from_native \<circ> delta"
      have dd: "logic_substitution D ?d"
      proof (unfold logic_substitution_def, intro allI)
        fix x
        have var: "D (LVar y)" for y using finite[of "SVar y"] by simp
        show "D (?d x)" using dom[of x] td ud var
          by (auto simp: logic_substitution_def o_def)
      qed
      have native_d: "logic_to_native \<circ> ?d=delta" by (rule ext) simp
      have sf': "logic_subst ?d (?s x)=t x" for x
        by (rule logic_translation_inj[THEN iffD1])
          (simp add: logic_subst_translation native_d lp_ieval_subst sf)
      have rf': "logic_subst ?d (?r x)=u x" for x
        by (rule logic_translation_inj[THEN iffD1])
          (simp add: logic_subst_translation native_d lp_ieval_subst rf)
      show "\<exists>d. logic_substitution D d \<and>
        logic_atom_map (logic_subst d \<circ> logic_subst ?s) (logic_atom_map lp_finite_tree a)=
          logic_atom_map (logic_subst t) (logic_atom_map lp_finite_tree a) \<and>
        map (logic_atom_map (logic_subst d \<circ> logic_subst ?s)) (map (logic_atom_map lp_finite_tree) gs)=
          map (logic_atom_map (logic_subst t)) (map (logic_atom_map lp_finite_tree) gs) \<and>
        map (logic_atom_map (logic_subst d \<circ> logic_eval ?r)) (map (logic_atom_map from_term) bs)=
          map (logic_atom_map (logic_eval u)) (map (logic_atom_map from_term) bs)"
        by (rule exI[of _ ?d])
          (simp add: dd[simplified o_def] logic_atom_map_def map_map o_def logic_subst_embed_eval
            logic_subst_eval_compose sf'[simplified logic_subst_embed_eval o_def] rf'[simplified logic_subst_embed_eval o_def])
    qed
  qed
qed

end
