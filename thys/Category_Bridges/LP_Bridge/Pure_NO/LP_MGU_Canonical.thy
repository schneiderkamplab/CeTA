theory LP_MGU_Canonical
  imports LP_Fresh_Finite_Lifting Category_LP_Bridge.LP_Ranked_Representation
begin

abbreviation lp_finite_tree where
  "lp_finite_tree t \<equiv> logic_embed (from_term t)"
lemma lp_finite_tree_translation[simp]:
  "logic_to_native (lp_finite_tree t)=lp_ieval t LPIVar"
  by (simp add: logic_embed_translation)
lemma lp_finite_tree_substitution:
  "logic_eval (\<lambda>x. lp_finite_tree (sigma x)) (from_term t)=lp_finite_tree (t\<cdot>sigma)"
  by (induct t) (auto simp: map_map o_def)
lemma lp_finite_atom_translation:
  "logic_to_atom logic_to_native (logic_from_atom lp_finite_tree a) = lp_atom_eval a LPIVar"
  by (cases a) (simp add: lp_atom_eval_def map_map o_def)

lemma lp_normalized_mgu_canonical:
  assumes mgu: "lp_normalized_mgu a b sigma"
    and finite: "\<And>t. D (logic_embed t)"
  shows "logic_mgu D (logic_from_atom lp_finite_tree a) (logic_from_atom lp_finite_tree b)
    (\<lambda>x. lp_finite_tree (sigma x))"
proof -
  have native: "lp_runtime_mgu (\<lambda>t. D (logic_from_native t))
      (lp_atom_eval a LPIVar) (lp_atom_eval b LPIVar) (\<lambda>x. lp_ieval (sigma x) LPIVar)"
    by (rule lp_normalized_mgu_runtime[OF mgu])
      (use finite in \<open>metis lp_finite_tree_translation logic_roundtrip\<close>)
  show ?thesis using native logic_tree_native.mgu_iff[
      where D="\<lambda>t. D (logic_from_native t)" and a="logic_from_atom lp_finite_tree a"
        and b="logic_from_atom lp_finite_tree b" and s="\<lambda>x. lp_finite_tree (sigma x)"]
    by (simp add: lp_finite_atom_translation o_def)
qed

lemma lp_normalized_mgu_ranked:
  assumes mgu: "lp_normalized_mgu a b sigma"
    and finite: "\<And>t. D (logic_embed t)"
  shows "logic_mgu (\<lambda>t. D (logic_unrank_tree t) \<and> logic_tree_arity_correct snd t)
    (logic_rank_runtime_atom (logic_from_atom lp_finite_tree a))
    (logic_rank_runtime_atom (logic_from_atom lp_finite_tree b))
    (logic_rank_tree \<circ> (\<lambda>x. lp_finite_tree (sigma x)))"
  by (simp add: logic_rank_runtime_atom_mgu lp_normalized_mgu_canonical[where D=D, OF mgu finite])

end
