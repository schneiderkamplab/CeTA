theory LP_MGU_Arity_Extension
  imports LP_MGU_Abstraction_Names
begin

lemma logic_atom_arity_abstract_subst:
  assumes "list_all (logic_tree_arity_correct A) (logic_arguments a)"
  shows "logic_atom_map (logic_arity_abstract A r b) (logic_atom_map (logic_subst s) a) =
    logic_atom_map (logic_subst (logic_arity_abstract A r b \<circ> s)) a"
  using assms by (cases a)
    (auto simp: map_map o_def list_all_iff intro!: map_cong; simp add: logic_arity_abstract_subst o_def)

text \<open>Each competing unifier is abstracted into the typed domain and then
reconstructed. This proves unrestricted most-generality directly, without an
MGU-existence premise. Domain closure obligations are explicit here and are
discharged by the concrete finite, rational and unrestricted tree instances.\<close>
lemma logic_mgu_arity_extension_by_abstraction:
  fixes s :: "string \<Rightarrow> ('f,string) logic_tree"
  assumes mgu: "logic_mgu (\<lambda>t. D t \<and> logic_tree_arity_correct A t) a b s"
    and left: "list_all (logic_tree_arity_correct A) (logic_arguments a)"
    and right: "list_all (logic_tree_arity_correct A) (logic_arguments b)"
    and variables: "\<And>x. D (LVar x)"
    and subtrees: "\<And>u t. D t \<Longrightarrow> logic_subtree u t \<Longrightarrow> D u"
    and abstract: "\<And>r b t. D t \<Longrightarrow> D (logic_arity_abstract A r b t)"
    and closed: "\<And>v t. logic_substitution_in D v \<Longrightarrow> D t \<Longrightarrow> D (logic_subst v t)"
  shows "logic_mgu D a b s"
proof -
  have sd: "logic_substitution_in D s"
    and se: "logic_atom_map (logic_subst s) a = logic_atom_map (logic_subst s) b"
    using mgu by (auto simp: logic_mgu_def logic_substitution_in_def)
  have factors: "\<exists>v. logic_substitution_in D v \<and> (\<forall>x. u x = logic_subst v (s x))"
    if ud: "logic_substitution_in D u"
      and ue: "logic_atom_map (logic_subst u) a = logic_atom_map (logic_subst u) b" for u
  proof -
    obtain r :: "string \<Rightarrow> string" and c :: "('f,string) logic_tree \<Rightarrow> string"
      and gamma :: "string \<Rightarrow> ('f,string) logic_tree" where gd: "logic_substitution_in D gamma"
      and recover: "\<And>x. logic_subst gamma (logic_arity_abstract A r c (u x)) = u x"
    proof (rule logic_substitution_abstraction_names[where A=A, OF ud variables subtrees])
      fix r c gamma
      assume gd: "logic_substitution_in D gamma"
        and rec: "\<And>x. logic_subst gamma (logic_arity_abstract A r c (u x)) = u x"
      show thesis by (rule that[OF gd rec])
    qed
    let ?F = "logic_arity_abstract A r c"
    have typed: "logic_substitution_in (\<lambda>t. D t \<and> logic_tree_arity_correct A t) (?F \<circ> u)"
      using ud abstract logic_arity_abstract_correct by (auto simp: logic_substitution_in_def)
    have eq: "logic_atom_map (logic_subst (?F \<circ> u)) a = logic_atom_map (logic_subst (?F \<circ> u)) b"
      using arg_cong[OF ue, where f="logic_atom_map ?F"]
      by (simp only: logic_atom_arity_abstract_subst[OF left] logic_atom_arity_abstract_subst[OF right])
    obtain v where vd: "logic_substitution_in (\<lambda>t. D t \<and> logic_tree_arity_correct A t) v"
      and vf: "\<And>x. ?F (u x) = logic_subst v (s x)"
      using mgu typed eq unfolding logic_mgu_def by auto
    have comp: "logic_substitution_in D (\<lambda>x. logic_subst gamma (v x))"
      using vd closed[OF gd] by (auto simp: logic_substitution_in_def)
    have result: "u x = logic_subst (\<lambda>x. logic_subst gamma (v x)) (s x)" for x
      using arg_cong[OF vf[of x], where f="logic_subst gamma"]
      by (simp only: recover logic_subst_composition)
    show ?thesis by (intro exI[of _ "\<lambda>x. logic_subst gamma (v x)"] conjI comp allI result)
  qed
  show ?thesis using sd se factors unfolding logic_mgu_def by blast
qed

ML \<open>
  val results = @{thms logic_mgu_arity_extension_by_abstraction}
  val _ = if Thm_Deps.has_skip_proof results then error "Arity extension: admitted proof" else ()
  val _ = if null (Thm_Deps.all_oracles results) then () else error "Arity extension: oracle dependency"
\<close>
end
