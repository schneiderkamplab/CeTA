theory LP_MGU_Representation
  imports LP_Runtime_MGU
begin

text \<open>A bijective tree representation commuting with substitution also
preserves and reflects global most-generality. The domain is transported
explicitly, including both competing unifiers and factor substitutions.\<close>
locale lp_tree_representation =
  fixes encode :: "('f,'v) logic_tree \<Rightarrow> ('g,'v) lp_iterm"
    and decode :: "('g,'v) lp_iterm \<Rightarrow> ('f,'v) logic_tree"
  assumes decode_encode[simp]: "decode (encode t) = t"
    and encode_decode[simp]: "encode (decode u) = u"
    and subst: "encode (logic_subst s t) = lp_isubst (encode t) (encode \<circ> s)"
begin

lemma injective[simp]: "encode a = encode b \<longleftrightarrow> a=b"
  by (metis decode_encode)
lemma atom_injective[simp]:
  "logic_to_atom encode a = logic_to_atom encode b \<longleftrightarrow> a=b"
proof
  assume eq: "logic_to_atom encode a = logic_to_atom encode b"
  have inverse: "logic_from_atom decode (logic_to_atom encode t) = t" for t
    by (cases t) (simp add: map_map o_def)
  show "a=b" using arg_cong[OF eq, where f="logic_from_atom decode"] by (simp add: inverse)
qed simp
lemma atom_subst:
  "logic_to_atom encode (logic_atom_map (logic_subst s) a) =
    lp_iatom_subst (logic_to_atom encode a) (encode \<circ> s)"
  by (cases a) (simp add: lp_iatom_subst_def map_map o_def subst)

lemma mgu_iff:
  "logic_mgu (\<lambda>t. D (encode t)) a b s \<longleftrightarrow>
    lp_runtime_mgu D (logic_to_atom encode a) (logic_to_atom encode b) (encode \<circ> s)"
proof
  assume mgu: "logic_mgu (\<lambda>t. D (encode t)) a b s"
  have dom: "\<forall>x. D ((encode \<circ> s) x)"
    using mgu by (simp add: logic_mgu_def logic_substitution_in_def)
  have eq: "lp_iatom_subst (logic_to_atom encode a) (encode \<circ> s) =
    lp_iatom_subst (logic_to_atom encode b) (encode \<circ> s)"
    using mgu by (simp add: logic_mgu_def atom_subst[symmetric])
  have factor: "\<exists>v. (\<forall>x. D (v x)) \<and> (\<forall>x. u x = lp_isubst ((encode \<circ> s) x) v)"
    if ud: "\<forall>x. D (u x)"
      and ue: "lp_iatom_subst (logic_to_atom encode a) u = lp_iatom_subst (logic_to_atom encode b) u"
    for u :: "'v \<Rightarrow> ('g,'v) lp_iterm"
  proof -
    have cd: "logic_substitution_in (\<lambda>t. D (encode t)) (decode \<circ> u)"
      using ud by (simp add: logic_substitution_in_def)
    have ce: "logic_atom_map (logic_subst (decode \<circ> u)) a = logic_atom_map (logic_subst (decode \<circ> u)) b"
      by (rule atom_injective[THEN iffD1]) (simp add: atom_subst o_def ue)
    obtain v where vd: "logic_substitution_in (\<lambda>t. D (encode t)) v"
      and vf: "\<And>x. decode (u x) = logic_subst v (s x)"
      using mgu cd ce unfolding logic_mgu_def by auto
    have native_factor: "u x = lp_isubst (encode (s x)) (encode \<circ> v)" for x
      using arg_cong[OF vf[of x], where f=encode] by (simp add: subst)
    show ?thesis by (intro exI[of _ "encode \<circ> v"])
      (simp add: vd[unfolded logic_substitution_in_def] native_factor)
  qed
  show "lp_runtime_mgu D (logic_to_atom encode a) (logic_to_atom encode b) (encode \<circ> s)"
    unfolding lp_runtime_mgu_def using dom eq factor by blast
next
  assume mgu: "lp_runtime_mgu D (logic_to_atom encode a) (logic_to_atom encode b) (encode \<circ> s)"
  have dom: "logic_substitution_in (\<lambda>t. D (encode t)) s"
    using mgu by (simp add: lp_runtime_mgu_def logic_substitution_in_def)
  have eq: "logic_atom_map (logic_subst s) a = logic_atom_map (logic_subst s) b"
    using mgu by (simp add: lp_runtime_mgu_def atom_subst[symmetric])
  have factor: "\<exists>v. logic_substitution_in (\<lambda>t. D (encode t)) v \<and>
      (\<forall>x. u x = logic_subst v (s x))"
    if ud: "logic_substitution_in (\<lambda>t. D (encode t)) u"
      and ue: "logic_atom_map (logic_subst u) a = logic_atom_map (logic_subst u) b" for u
  proof -
    have nd: "\<forall>x. D ((encode \<circ> u) x)" using ud by (simp add: logic_substitution_in_def)
    have ne: "lp_iatom_subst (logic_to_atom encode a) (encode \<circ> u) =
        lp_iatom_subst (logic_to_atom encode b) (encode \<circ> u)"
      using ue by (simp add: atom_subst[symmetric])
    obtain v where vd: "\<forall>x. D (v x)"
      and vf: "\<And>x. encode (u x) = lp_isubst (encode (s x)) v"
      using spec[where x="encode \<circ> u", OF conjunct2[OF conjunct2[OF mgu[unfolded lp_runtime_mgu_def]]]] nd ne
      by (auto simp only: o_apply)
    have canonical_factor: "u x = logic_subst (decode \<circ> v) (s x)" for x
      by (rule injective[THEN iffD1]) (simp add: subst o_def vf)
    show ?thesis by (intro exI[of _ "decode \<circ> v"])
      (simp add: logic_substitution_in_def vd canonical_factor)
  qed
  show "logic_mgu (\<lambda>t. D (encode t)) a b s"
    unfolding logic_mgu_def using dom eq factor by blast
qed

end

interpretation logic_tree_native: lp_tree_representation logic_to_native logic_from_native
  by unfold_locales (simp_all add: logic_subst_translation)

end
