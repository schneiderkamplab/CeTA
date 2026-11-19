theory LP_Cut_MGU_Representation
  imports LP_MGU_Representation LP_Cut_Execution_Representation
begin

text \<open>The cut runtime representation is a bijection commuting with
substitution. Thus global most-generality is transported with exactly the same
domain for candidate substitutions, competing unifiers and factors. This lemma
does not enlarge a signature-restricted domain.\<close>
interpretation cut_tree_native: lp_tree_representation cut_tree cut_tree_back
  by unfold_locales (simp_all add: cut_tree_subst)

lemma cut_global_unification_mgu:
  "logic_mgu (\<lambda>t. D (cut_tree t)) (LAtom () [a]) (LAtom () [b]) s \<longleftrightarrow>
    (\<forall>x. D (cut_tree (s x))) \<and>
    lp_isubst (cut_tree a) (cut_tree \<circ> s) = lp_isubst (cut_tree b) (cut_tree \<circ> s) \<and>
    (\<forall>u. (\<forall>x. D (u x)) \<and> lp_isubst (cut_tree a) u = lp_isubst (cut_tree b) u
      \<longrightarrow> (\<exists>v. (\<forall>x. D (v x)) \<and>
        (\<forall>x. u x = lp_isubst (cut_tree (s x)) v)))"
  by (simp add: cut_tree_native.mgu_iff lp_runtime_mgu_def lp_iatom_subst_def)

end
