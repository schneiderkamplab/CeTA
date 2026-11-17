theory LP_Cut_Domain_MGU
  imports Category_LP_Bridge.LP_Fresh_MGU_Context Category_LP_Cut_Checker_Bridge.LP_Cut_Domain_Checker Category_LP_Library.LP_Cut_NO_XML
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

lemma fresh_resolution_mgu_resolve:
  assumes fresh: "lp_fresh_resolution D a gs h bs sigma rho"
  shows "mgu_resolve a gs h bs sigma rho"
proof -
  have basic: "lp_isubst a sigma = lp_ieval h rho"
    "\<forall>x. D (sigma x)" "\<forall>x. D (rho x)"
    using fresh unfolding lp_fresh_resolution_def lp_runtime_mgu_def
    by (auto simp: lp_iatom_subst_def lp_ieval_subst o_def)
  have factor: "\<exists>delta. (\<forall>x. D (delta x)) \<and>
      lp_isubst (lp_isubst a sigma) delta = lp_isubst a tau \<and>
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta)) gs =
        map (lp_cut_map (\<lambda>t. lp_isubst t tau)) gs \<and>
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t rho) delta)) bs =
        map (lp_cut_map (\<lambda>t. lp_ieval t nu)) bs"
    if dt: "\<forall>x. D (tau x)" and dn: "\<forall>x. D (nu x)"
      and eq: "lp_isubst a tau = lp_ieval h nu"
    for tau nu :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
  proof -
    obtain delta where dd: "\<And>x. D (delta x)"
      and caller: "\<And>t. t\<in>set (a # concat (map lp_cut_terms gs)) \<Longrightarrow>
        lp_isubst (lp_isubst t sigma) delta = lp_isubst t tau"
      and clause: "\<And>t. t\<in>set (h # concat (map lp_cut_terms bs)) \<Longrightarrow>
        lp_isubst (lp_ieval t rho) delta = lp_ieval t nu"
      by (rule lp_fresh_resolution_factors_context[OF fresh _ _ eq]) (use dt dn in auto)
    show ?thesis
      apply (intro exI[of _ delta] conjI allI dd)
        apply (rule caller; simp)
       apply (intro map_cong refl lp_cut_goal_map_cong)
       apply (rule caller; auto)[1]
      apply (intro map_cong refl lp_cut_goal_map_cong)
      apply (rule clause; auto)
      done
  qed
  show ?thesis unfolding mgu_resolve_def using basic factor by blast
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
  by (rule fresh_resolution_mgu_resolve)
    (rule lp_checked_fresh_resolution[OF variables constructors checked short_a short_gs])


end
end
