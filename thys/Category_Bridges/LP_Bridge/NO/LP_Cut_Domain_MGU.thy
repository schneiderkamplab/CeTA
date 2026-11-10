theory LP_Cut_Domain_MGU
  imports Category_LP_Cut_Checker_Bridge.LP_Cut_Domain_Checker Category_LP_Library.LP_Cut_NO_XML
begin

text \<open>NO certificates require actual most-general transitions. Both the
competing substitutions and the factor substitution belong to the selected
domain. This proof layer interprets the existing finite solved-substitution
checks; it does not introduce a new certificate format.\<close>

context cut_runtime_domain
begin

definition mgu_resolve ::
  "('f lp_cut_symbol,string) lp_iterm \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm lp_cut_goal list \<Rightarrow>
   ('f lp_cut_symbol,string) term \<Rightarrow> ('f lp_cut_symbol,string) term lp_cut_goal list \<Rightarrow>
   (string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm) \<Rightarrow>
   (string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm) \<Rightarrow> bool" where
  "mgu_resolve a gs h bs \<sigma> \<rho> =
    (lp_isubst a \<sigma> = lp_ieval h \<rho> \<and> (\<forall>x. D (\<sigma> x)) \<and> (\<forall>x. D (\<rho> x)) \<and>
     (\<forall>\<tau> \<nu> :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm. (\<forall>x. D (\<tau> x)) \<longrightarrow> (\<forall>x. D (\<nu> x)) \<longrightarrow> lp_isubst a \<tau> = lp_ieval h \<nu> \<longrightarrow>
       (\<exists>\<delta>. (\<forall>x. D (\<delta> x)) \<and>
         lp_isubst (lp_isubst a \<sigma>) \<delta> = lp_isubst a \<tau> \<and>
         map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t \<sigma>) \<delta>)) gs =
           map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>)) gs \<and>
         map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t \<rho>) \<delta>)) bs =
           map (lp_cut_map (\<lambda>t. lp_ieval t \<nu>)) bs)))"

definition mgu_unify ::
  "('f lp_cut_symbol,string) lp_iterm \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm \<Rightarrow>
   ('f lp_cut_symbol,string) lp_iterm lp_cut_goal list \<Rightarrow>
   (string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm) \<Rightarrow> bool" where
  "mgu_unify a b gs \<sigma> =
    (lp_isubst a \<sigma> = lp_isubst b \<sigma> \<and> (\<forall>x. D (\<sigma> x)) \<and>
     (\<forall>\<tau> :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm. (\<forall>x. D (\<tau> x)) \<longrightarrow> lp_isubst a \<tau> = lp_isubst b \<tau> \<longrightarrow>
       (\<exists>\<delta>. (\<forall>x. D (\<delta> x)) \<and>
         lp_isubst (lp_isubst a \<sigma>) \<delta> = lp_isubst a \<tau> \<and>
         map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t \<sigma>) \<delta>)) gs =
           map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>)) gs)))"

theorem checked_mgu_unify:
  fixes a b :: "('f lp_cut_symbol,string) term"
  assumes checked: "lpc_check_mgu fuel [(a,b)] V images"
  shows "mgu_unify (lp_ieval a LPIVar) (lp_ieval b LPIVar)
    (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs)
    (\<lambda>x. lp_ieval (lpc_mgu_substitution V images x) LPIVar)"
proof -
  let ?s = "\<lambda>x. lp_ieval (lpc_mgu_substitution V images x) LPIVar"
  have unifies: "lp_isubst (lp_ieval a LPIVar) ?s = lp_isubst (lp_ieval b LPIVar) ?s"
    using lpc_checked_mgu_unifies[OF checked]
    by (simp add: lp_equations_def lp_ieval_subst)
  have factor: "\<And>\<tau> :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm.
    lp_isubst (lp_ieval a LPIVar) \<tau> = lp_isubst (lp_ieval b LPIVar) \<tau> \<Longrightarrow>
    (\<lambda>x. lp_isubst (?s x) \<tau>) = \<tau>"
  proof -
    fix \<tau> :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
    assume "lp_isubst (lp_ieval a LPIVar) \<tau> = lp_isubst (lp_ieval b LPIVar) \<tau>"
    then have solution: "lp_equations [(a,b)] \<tau>"
      by (simp add: lp_equations_def lp_ieval_subst)
    show "(\<lambda>x. lp_isubst (?s x) \<tau>) = \<tau>"
      by (rule ext) (simp add: lp_ieval_subst lpc_checked_mgu_factor[OF checked solution])
  qed
  have domain: "\<forall>x. D (?s x)"
    by (intro allI; rule cut_domain_eval[OF variables constructors])
  show ?thesis
    unfolding mgu_unify_def
    apply (intro conjI)
      apply (rule unifies)
     apply (rule domain)
    apply (intro allI impI)
    subgoal for \<tau>
      apply (rule exI[of _ \<tau>])
      apply (simp add: lpc_isubst_comp factor map_map o_def lp_cut_map_comp)
      done
    done
qed

theorem checked_mgu_resolve:
  fixes a h :: "('f lp_cut_symbol,string) term"
  assumes checked: "lpc_check_mgu fuel [(a,h\<cdot>(\<lambda>x. Var (lp_prefix k x)))] V images"
    and short_a: "\<forall>x\<in>vars_term a. length x<k"
    and short_gs: "lp_cut_short_goals k gs"
  shows "mgu_resolve (lp_ieval a LPIVar)
    (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) h bs
    (\<lambda>x. lp_ieval (lpc_mgu_substitution V images x) LPIVar)
    (\<lambda>x. lp_ieval (lpc_mgu_substitution V images (lp_prefix k x)) LPIVar)"
proof -
  let ?s = "\<lambda>x. lp_ieval (lpc_mgu_substitution V images x) LPIVar"
  let ?r = "\<lambda>x. ?s (lp_prefix k x)"
  let ?eqs = "[(a,h\<cdot>(\<lambda>x. Var (lp_prefix k x)))]"
  have unifies: "lp_isubst (lp_ieval a LPIVar) ?s = lp_ieval h ?r"
    using lpc_checked_mgu_unifies[OF checked]
    by (simp add: lp_equations_def lp_ieval_subst lp_ieval_finite_subst)
  have factor: "\<And>\<tau> \<nu> :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm.
    (\<forall>x. D (\<tau> x)) \<Longrightarrow> (\<forall>x. D (\<nu> x)) \<Longrightarrow>
    lp_isubst (lp_ieval a LPIVar) \<tau> = lp_ieval h \<nu> \<Longrightarrow>
    \<exists>\<delta>. (\<forall>x. D (\<delta> x)) \<and>
      lp_isubst (lp_isubst (lp_ieval a LPIVar) ?s) \<delta> = lp_isubst (lp_ieval a LPIVar) \<tau> \<and>
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t ?s) \<delta>))
        (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) =
      map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>))
        (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) \<and>
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t ?r) \<delta>)) bs =
      map (lp_cut_map (\<lambda>t. lp_ieval t \<nu>)) bs"
  proof -
    fix \<tau> \<nu> :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
    assume dt: "\<forall>x. D (\<tau> x)" and dn: "\<forall>x. D (\<nu> x)"
    assume comparison: "lp_isubst (lp_ieval a LPIVar) \<tau> = lp_ieval h \<nu>"
    let ?d = "\<lambda>x. if length x<k then \<tau> x else \<nu> (drop k x)"
    have fresh: "\<And>x. ?d (lp_prefix k x) = \<nu> x" by (simp add: lp_prefix_def)
    have old: "\<And>t. (\<forall>x\<in>vars_term t. length x<k) \<Longrightarrow> lp_ieval t ?d = lp_ieval t \<tau>"
      by (rule lp_ieval_cong) auto
    have solution: "lp_equations ?eqs ?d"
      using comparison old[OF short_a]
      by (simp add: lp_equations_def lp_ieval_finite_subst lp_ieval_subst fresh)
    have composed: "(\<lambda>x. lp_isubst (?s x) ?d) = ?d"
      by (rule ext) (simp add: lp_ieval_subst lpc_checked_mgu_factor[OF checked solution])
    have composed_eval: "(\<lambda>x. lp_ieval (lpc_mgu_substitution V images x) ?d) = ?d"
      using composed by (simp add: lp_ieval_subst)
    have active: "\<And>t. (\<forall>x\<in>vars_term t. length x<k) \<Longrightarrow>
      lp_isubst (lp_isubst (lp_ieval t LPIVar) ?s) ?d = lp_isubst (lp_ieval t LPIVar) \<tau>"
      by (simp add: lp_ieval_subst composed_eval old)
    show "\<exists>\<delta>. (\<forall>x. D (\<delta> x)) \<and>
      lp_isubst (lp_isubst (lp_ieval a LPIVar) ?s) \<delta> = lp_isubst (lp_ieval a LPIVar) \<tau> \<and>
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t ?s) \<delta>))
        (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) =
      map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>))
        (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) \<and>
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t ?r) \<delta>)) bs =
      map (lp_cut_map (\<lambda>t. lp_ieval t \<nu>)) bs"
    proof (rule exI[of _ ?d], intro conjI)
      show "\<forall>x. D (?d x)" using dt dn by simp
      show "lp_isubst (lp_isubst (lp_ieval a LPIVar) ?s) ?d = lp_isubst (lp_ieval a LPIVar) \<tau>"
        by (rule active[OF short_a])
      show "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t ?s) ?d))
        (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) =
        map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>))
        (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs)"
        unfolding map_map o_def lp_cut_map_comp
        by (rule map_cong[OF refl], rule lp_cut_goal_map_cong, rule active)
          (use short_gs in \<open>auto simp: lp_cut_short_goals_def\<close>)
      show "map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t ?r) ?d)) bs =
        map (lp_cut_map (\<lambda>t. lp_ieval t \<nu>)) bs"
      proof -
        have "(\<lambda>x. lp_isubst (?r x) ?d) = \<nu>"
          using fun_cong[OF composed, of "lp_prefix k _"] by (auto simp: fresh)
        then show ?thesis by (simp add: lp_ieval_subst)
      qed
    qed
  qed
  have ds: "\<forall>x. D (?s x)"
    by (intro allI; rule cut_domain_eval[OF variables constructors])
  have dr: "\<forall>x. D (?r x)" using ds by simp
  show ?thesis unfolding mgu_resolve_def using unifies ds dr factor by blast
qed


end
end
