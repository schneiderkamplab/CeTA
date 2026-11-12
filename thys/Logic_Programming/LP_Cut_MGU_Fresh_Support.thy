theory LP_Cut_MGU_Fresh_Support
 imports LP_Cut_MGU_Fresh_Resolve
begin

text \<open>Only clause variables that occur in the head or body need a fresh
renaming. This finite support can be moved away from an accumulated continuation
without reserving an entire infinite namespace.\<close>

theorem lpc_checked_mgu_resolve_fresh_support:
  fixes a h :: "('f,string) term"
    and rename_clause_var :: "string \<Rightarrow> string"
  assumes checked: "lpc_check_mgu fuel [(a,h\<cdot>(\<lambda>x. Var (rename_clause_var x)))] V images"
    and injective: "inj_on rename_clause_var B"
    and head_vars: "vars_term h \<subseteq> B"
    and body_vars: "\<forall>g\<in>set bs. \<forall>t\<in>set (lp_cut_terms g). vars_term t \<subseteq> B"
    and fresh_a: "vars_term a \<inter> rename_clause_var ` B = {}"
    and fresh_gs: "\<forall>g\<in>set gs. \<forall>t\<in>set (lp_cut_terms g). vars_term t \<inter> rename_clause_var ` B = {}"
  shows "lpc_mgu_resolve (lp_ieval a LPIVar)
    (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) h bs
    (\<lambda>x. lp_ieval (lpc_mgu_substitution V images x) LPIVar)
    (\<lambda>x. lp_ieval (lpc_mgu_substitution V images (rename_clause_var x)) LPIVar)"
proof -
  let ?s = "\<lambda>x. lp_ieval (lpc_mgu_substitution V images x) LPIVar"
  let ?r = "\<lambda>x. ?s (rename_clause_var x)"
  let ?eqs = "[(a,h\<cdot>(\<lambda>x. Var (rename_clause_var x)))]"
  have unifies: "lp_isubst (lp_ieval a LPIVar) ?s = lp_ieval h ?r"
    using lpc_checked_mgu_unifies[OF checked]
    by (simp add: lp_equations_def lp_ieval_subst lp_ieval_finite_subst)
  have factor: "\<And>\<tau> \<nu> :: string \<Rightarrow> ('f,string) lp_iterm.
    lp_isubst (lp_ieval a LPIVar) \<tau> = lp_ieval h \<nu> \<Longrightarrow>
    \<exists>\<delta>.
      lp_isubst (lp_isubst (lp_ieval a LPIVar) ?s) \<delta> = lp_isubst (lp_ieval a LPIVar) \<tau> \<and>
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t ?s) \<delta>))
        (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) =
      map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>))
        (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) \<and>
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t ?r) \<delta>)) bs =
      map (lp_cut_map (\<lambda>t. lp_ieval t \<nu>)) bs"
  proof -
    fix \<tau> \<nu> :: "string \<Rightarrow> ('f,string) lp_iterm"
    assume comparison: "lp_isubst (lp_ieval a LPIVar) \<tau> = lp_ieval h \<nu>"
    let ?d = "\<lambda>x. if x\<in>rename_clause_var ` B then \<nu> (inv_into B rename_clause_var x) else \<tau> x"
    have renamed: "\<And>x. x\<in>B \<Longrightarrow> ?d (rename_clause_var x) = \<nu> x"
      by (simp add: inv_into_f_f[OF injective])
    have renamed_eval: "lp_ieval t (\<lambda>x. ?d (rename_clause_var x)) = lp_ieval t \<nu>"
      if "vars_term t \<subseteq> B" for t
      by (rule lp_ieval_cong) (use that renamed in auto)
    have old: "\<And>t. (vars_term t \<inter> rename_clause_var ` B = {}) \<Longrightarrow> lp_ieval t ?d = lp_ieval t \<tau>"
      by (rule lp_ieval_cong) auto
    have solution: "lp_equations ?eqs ?d"
      using comparison old[OF fresh_a] renamed_eval[OF head_vars]
      by (simp add: lp_equations_def lp_ieval_finite_subst lp_ieval_subst)
    have composed: "(\<lambda>x. lp_isubst (?s x) ?d) = ?d"
      by (rule ext) (simp add: lp_ieval_subst lpc_checked_mgu_factor[OF checked solution])
    have composed_eval: "(\<lambda>x. lp_ieval (lpc_mgu_substitution V images x) ?d) = ?d"
      using composed by (simp add: lp_ieval_subst)
    have active: "\<And>t. (vars_term t \<inter> rename_clause_var ` B = {}) \<Longrightarrow>
      lp_isubst (lp_isubst (lp_ieval t LPIVar) ?s) ?d = lp_isubst (lp_ieval t LPIVar) \<tau>"
      by (simp add: lp_ieval_subst composed_eval old)
    show "\<exists>\<delta>.
      lp_isubst (lp_isubst (lp_ieval a LPIVar) ?s) \<delta> = lp_isubst (lp_ieval a LPIVar) \<tau> \<and>
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t ?s) \<delta>))
        (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) =
      map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>))
        (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) \<and>
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t ?r) \<delta>)) bs =
      map (lp_cut_map (\<lambda>t. lp_ieval t \<nu>)) bs"
    proof (rule exI[of _ ?d], intro conjI)
      show "lp_isubst (lp_isubst (lp_ieval a LPIVar) ?s) ?d = lp_isubst (lp_ieval a LPIVar) \<tau>"
        by (rule active[OF fresh_a])
      show "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t ?s) ?d))
        (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) =
        map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>))
        (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs)"
        unfolding map_map o_def lp_cut_map_comp
        by (rule map_cong[OF refl], rule lp_cut_goal_map_cong, rule active)
          (use fresh_gs in \<open>auto simp:\<close>)
      show "map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t ?r) ?d)) bs =
        map (lp_cut_map (\<lambda>t. lp_ieval t \<nu>)) bs"
      proof -
        have mapped: "lp_isubst (?r x) ?d = \<nu> x" if "x\<in>B" for x
          using fun_cong[OF composed, of "rename_clause_var x"] renamed[OF that] by simp
        show ?thesis unfolding map_map o_def lp_cut_map_comp
          by (rule map_cong[OF refl], rule lp_cut_goal_map_cong)
            (use body_vars mapped in \<open>auto simp: lp_ieval_subst intro!: lp_ieval_cong\<close>)
      qed
    qed
  qed
  show ?thesis unfolding lpc_mgu_resolve_def using unifies factor by blast
qed

ML \<open>
val checked = [@{thm lpc_checked_mgu_resolve_fresh_support}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite-support MGU dependency" else ();
\<close>
end
