theory LP_Cut_MGU_Knowledge
  imports LP_Cut_MGU_Normalize
begin

definition lpc_free_knowledge where
  "lpc_free_knowledge F \<eta> =
    ((\<forall>x\<in>F. \<exists>y. \<eta> x = LPIVar y) \<and> inj_on \<eta> F)"

definition lpc_body_only_variables where
  "lpc_body_only_variables h bs =
    (\<Union>g\<in>set bs. \<Union>t\<in>set (lp_cut_terms g). vars_term t) - vars_term h"

fun lpc_term_variable_list where
  "lpc_term_variable_list (Var x) = [x]"
| "lpc_term_variable_list (Fun f ts) = concat (map lpc_term_variable_list ts)"

lemma lpc_term_variable_list_set [simp]:
  "set (lpc_term_variable_list t) = vars_term t"
  by (induct t) simp_all

lemma lpc_body_only_variables_code [code]:
  "lpc_body_only_variables h bs =
    set (filter (\<lambda>x. x\<notin>vars_term h)
      (concat (map (\<lambda>g. concat (map lpc_term_variable_list (lp_cut_terms g))) bs)))"
  by (auto simp: lpc_body_only_variables_def)

theorem lpc_mgu_body_only_knowledge:
  assumes mgu: "lpc_mgu_resolve a gs h bs \<sigma> \<rho>"
  shows "lpc_free_knowledge (lpc_body_only_variables h bs) \<rho>"
proof (unfold lpc_free_knowledge_def, intro conjI)
  show "\<forall>x\<in>lpc_body_only_variables h bs. \<exists>y. \<rho> x = LPIVar y"
    using lpc_mgu_body_only_variable_free[OF mgu]
    by (auto simp: lpc_body_only_variables_def)
  show "inj_on \<rho> (lpc_body_only_variables h bs)"
  proof (rule inj_onI)
    fix x y assume x: "x\<in>lpc_body_only_variables h bs"
      and y: "y\<in>lpc_body_only_variables h bs" and eq: "\<rho> x=\<rho> y"
    show "x=y"
    proof (rule ccontr)
      assume "x\<noteq>y"
      then have "\<rho> x\<noteq>\<rho> y"
        using lpc_mgu_body_only_variables_separate[OF mgu] x y
        by (auto simp: lpc_body_only_variables_def)
      then show False using eq by contradiction
    qed
  qed
qed

lemma lpc_free_knowledge_subset:
  "lpc_free_knowledge F \<eta> \<Longrightarrow> E\<subseteq>F \<Longrightarrow> lpc_free_knowledge E \<eta>"
  by (auto simp: lpc_free_knowledge_def inj_on_def)

lemma lpc_free_knowledge_not_ground:
  assumes "lpc_free_knowledge F \<eta>" "x\<in>F"
  shows "\<not>lp_seg_ground (\<eta> x)"
proof -
  obtain y where eq: "\<eta> x = LPIVar y"
    using assms by (auto simp: lpc_free_knowledge_def)
  have "\<not>lp_seg_ground (LPIVar y)"
    by (auto elim: lp_seg_ground.cases)
  then show ?thesis by (simp only: eq)
qed

text \<open>This knowledge may be consumed only in an MGU-aware graph theorem.
It must not be fed to the existing all-unifier table checker as an assumption.
Separateness from older free variables needs its own invariant; the theorem
above establishes pairwise separation of body-only variables, not that stronger
cross-state property.\<close>

end
