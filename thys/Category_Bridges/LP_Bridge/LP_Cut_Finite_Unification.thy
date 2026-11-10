theory LP_Cut_Finite_Unification
  imports Category_LP_Library.LP_Cut_MGU_Normalize LP_Cut_Representation Category_Properties.LP_Properties
begin

text \<open>The concrete solved-substitution check has a stronger property than
its unrestricted-tree theorem alone states. Its factor is the competing solution
itself, so most-generality holds separately in every substitution domain closed
under finite term construction. These are proved algebraic facts, not assumed
checker soundness.\<close>
lemma cut_domain_eval:
  assumes variables: "\<And>x. D (eta x)"
    and constructors: "\<And>f ts. list_all D ts \<Longrightarrow> D (LPIFun f ts)"
  shows "D (lp_ieval t eta)"
  by (induct t) (auto intro: variables constructors simp: list_all_iff)

theorem cut_checked_mgu_domain:
  fixes D :: "('f,'v) lp_iterm \<Rightarrow> bool"
  assumes variables: "\<And>x. D (LPIVar x)"
    and constructors: "\<And>f ts. list_all D ts \<Longrightarrow> D (LPIFun f ts)"
    and checked: "lpc_check_mgu fuel equations V images"
  defines "sigma \<equiv> \<lambda>x. lp_ieval (lpc_mgu_substitution V images x) LPIVar"
  shows "(\<forall>x. D (sigma x)) \<and> lp_equations equations sigma \<and>
    (\<forall>tau. (\<forall>x. D (tau x)) \<longrightarrow> lp_equations equations tau \<longrightarrow>
      (\<exists>delta. (\<forall>x. D (delta x)) \<and> (\<forall>x. lp_isubst (sigma x) delta = tau x)))"
proof (intro conjI)
  show "\<forall>x. D (sigma x)"
    unfolding sigma_def by (intro allI; rule cut_domain_eval[OF variables constructors])
  show "lp_equations equations sigma"
    unfolding sigma_def by (rule lpc_checked_mgu_unifies[OF checked])
  show "\<forall>tau. (\<forall>x. D (tau x)) \<longrightarrow> lp_equations equations tau \<longrightarrow>
    (\<exists>delta. (\<forall>x. D (delta x)) \<and> (\<forall>x. lp_isubst (sigma x) delta = tau x))"
  proof (intro allI impI)
    fix tau assume domain: "\<forall>x. D (tau x)" and solution: "lp_equations equations tau"
    show "\<exists>delta. (\<forall>x. D (delta x)) \<and> (\<forall>x. lp_isubst (sigma x) delta = tau x)"
      by (rule exI[of _ tau])
        (simp add: domain sigma_def lp_ieval_subst lpc_checked_mgu_factor[OF checked solution])
  qed
qed

definition cut_finite_runtime where
  "cut_finite_runtime t \<longleftrightarrow> (\<exists>u. t = lp_ieval u LPIVar)"
lemma cut_finite_variable: "cut_finite_runtime (LPIVar x)"
  unfolding cut_finite_runtime_def by (rule exI[of _ "Var x"]) simp
lemma cut_finite_function:
  assumes "list_all cut_finite_runtime ts"
  shows "cut_finite_runtime (LPIFun f ts)"
proof -
  let ?rep = "\<lambda>t. SOME u. t = lp_ieval u LPIVar"
  have rep: "lp_ieval (?rep t) LPIVar = t" if "t\<in>set ts" for t
    using assms that someI_ex[of "\<lambda>u. t = lp_ieval u LPIVar"]
    by (auto simp: list_all_iff cut_finite_runtime_def)
  have mapped: "map (\<lambda>u. lp_ieval u LPIVar) (map ?rep ts) = ts"
    by (simp add: map_map o_def; rule map_idI; rule rep)
  show ?thesis unfolding cut_finite_runtime_def
    by (rule exI[of _ "Fun f (map ?rep ts)"]) (simp only: lp_ieval.simps mapped)
qed

corollary cut_checked_mgu_finite:
  fixes sigma :: "'v \<Rightarrow> ('f,'v) lp_iterm"
  assumes "lpc_check_mgu fuel equations V images"
  defines "sigma \<equiv> \<lambda>x. lp_ieval (lpc_mgu_substitution V images x) LPIVar"
  shows "(\<forall>x. cut_finite_runtime (sigma x)) \<and> lp_equations equations sigma \<and>
    (\<forall>tau :: 'v \<Rightarrow> ('f,'v) lp_iterm. (\<forall>x. cut_finite_runtime (tau x)) \<longrightarrow> lp_equations equations tau \<longrightarrow>
      (\<exists>delta. (\<forall>x. cut_finite_runtime (delta x)) \<and>
        (\<forall>x. lp_isubst (sigma x) delta = tau x)))"
  unfolding sigma_def
  by (rule cut_checked_mgu_domain; (rule cut_finite_variable | rule cut_finite_function | rule assms(1)))


fun cut_term_back where
  "cut_term_back (Var x) = SVar x"
| "cut_term_back (Fun f ts) = SFun (cut_symbol_back f) (map cut_term_back ts)"
lemma cut_back_finite:
  "cut_tree_back (lp_ieval t LPIVar) = logic_embed (cut_term_back t)"
  by (induct t) (auto simp: map_map o_def)
lemma cut_finite_domain_iff:
  "cut_finite_runtime (cut_tree t) \<longleftrightarrow> logic_finite t"
proof
  assume "cut_finite_runtime (cut_tree t)"
  then obtain u where eq: "cut_tree t = lp_ieval u LPIVar"
    by (auto simp: cut_finite_runtime_def)
  from arg_cong[OF eq, of cut_tree_back]
  have "t = logic_embed (cut_term_back u)"
    by (simp only: cut_tree_roundtrip cut_back_finite)
  then show "logic_finite t" unfolding logic_finite_def by blast
next
  assume "logic_finite t"
  then obtain u where "t = logic_embed u" by (auto simp: logic_finite_def)
  then show "cut_finite_runtime (cut_tree t)"
    unfolding cut_finite_runtime_def using cut_tree_embed by blast
qed

definition cut_rational_runtime where
  "cut_rational_runtime t \<longleftrightarrow> logic_rational (cut_tree_back t)"
lemma cut_rational_variable: "cut_rational_runtime (LPIVar x)"
  by (simp add: cut_rational_runtime_def)
lemma cut_rational_function:
  "list_all cut_rational_runtime ts \<Longrightarrow> cut_rational_runtime (LPIFun f ts)"
  unfolding cut_rational_runtime_def cut_tree_back_simps
  by (rule logic_rational_function) (auto simp: list_all_iff cut_rational_runtime_def)
corollary cut_checked_mgu_rational:
  assumes "lpc_check_mgu fuel equations V images"
  defines "sigma \<equiv> \<lambda>x. lp_ieval (lpc_mgu_substitution V images x) LPIVar"
  shows "(\<forall>x. cut_rational_runtime (sigma x)) \<and> lp_equations equations sigma \<and>
    (\<forall>tau. (\<forall>x. cut_rational_runtime (tau x)) \<longrightarrow> lp_equations equations tau \<longrightarrow>
      (\<exists>delta. (\<forall>x. cut_rational_runtime (delta x)) \<and>
        (\<forall>x. lp_isubst (sigma x) delta = tau x)))"
  unfolding sigma_def
  by (rule cut_checked_mgu_domain[OF cut_rational_variable cut_rational_function assms(1)])

end
