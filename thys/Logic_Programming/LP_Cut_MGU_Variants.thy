theory LP_Cut_MGU_Variants
  imports LP_Cut_MGU_Knowledge
begin

text \<open>Mutual factorization of a finite interface yields a single injective
variable renaming, even when the intermediate valuation ranges over infinite
trees. This is the bridge needed to cover all MGUs, rather than certify just
one solver-selected substitution.\<close>

theorem lpc_finite_roundtrip_renaming:
  fixes ts :: "('f,'v) term list"
    and \<sigma> :: "'v \<Rightarrow> ('f,'w) lp_iterm"
    and \<tau> :: "'w \<Rightarrow> ('f,'v) lp_iterm"
  assumes roundtrip: "\<And>t. t\<in>set ts \<Longrightarrow>
    lp_isubst (lp_ieval t \<sigma>) \<tau> = lp_ieval t LPIVar"
  defines "V \<equiv> \<Union>(vars_term ` set ts)"
  shows "\<exists>r. inj_on r V \<and> (\<forall>x\<in>V. \<sigma> x = LPIVar (r x)) \<and>
    map (\<lambda>t. lp_ieval t \<sigma>) ts = map (\<lambda>t. lp_ieval t (LPIVar \<circ> r)) ts"
proof -
  have inverse: "\<And>x. x\<in>V \<Longrightarrow> lp_isubst (\<sigma> x) \<tau> = LPIVar x"
  proof -
    fix x assume "x\<in>V"
    then obtain t where t: "t\<in>set ts" "x\<in>vars_term t" by (auto simp: V_def)
    have "lp_ieval t (\<lambda>x. lp_isubst (\<sigma> x) \<tau>) = lp_ieval t LPIVar"
      using roundtrip[OF t(1)] by (simp only: lp_ieval_subst)
    then show "lp_isubst (\<sigma> x) \<tau> = LPIVar x"
      by (rule lpc_ieval_variables_eq[OF _ t(2)])
  qed
  let ?r = "\<lambda>x. case \<sigma> x of LPIVar y \<Rightarrow> y | LPIFun f ss \<Rightarrow> undefined"
  have variable: "\<And>x. x\<in>V \<Longrightarrow> \<sigma> x = LPIVar (?r x)"
  proof -
    fix x assume "x\<in>V"
    then have "\<exists>y. \<sigma> x = LPIVar y" by (rule lpc_isubst_variable_reflect[OF inverse])
    then show "\<sigma> x = LPIVar (?r x)" by auto
  qed
  have injective: "inj_on ?r V"
  proof (rule inj_onI)
    fix x y assume x: "x\<in>V" and y: "y\<in>V" and same: "?r x=?r y"
    have same_sigma: "\<sigma> x=\<sigma> y" using variable[OF x] variable[OF y] same by simp
    have same_eval: "lp_isubst (\<sigma> x) \<tau> = lp_isubst (\<sigma> y) \<tau>"
      by (rule arg_cong[OF same_sigma])
    have "LPIVar x=(LPIVar y :: ('f,'v) lp_iterm)"
      by (rule HOL.trans[OF inverse[OF x, symmetric] HOL.trans[OF same_eval inverse[OF y]]])
    then show "x=y" by (rule lp_iterm.inject(1)[THEN iffD1])
  qed
  have mapped: "map (\<lambda>t. lp_ieval t \<sigma>) ts = map (\<lambda>t. lp_ieval t (LPIVar \<circ> ?r)) ts"
    by (rule map_cong[OF refl], rule lp_ieval_cong)
      (use variable in \<open>auto simp: V_def\<close>)
  show ?thesis by (rule exI[of _ ?r]) (use injective variable mapped in auto)
qed

theorem lpc_checked_mgu_interface_variants:
  assumes checked: "lpc_check_mgu fuel equations V images"
    and solution: "lp_equations equations \<sigma>"
    and backward: "\<And>t. t\<in>set ts \<Longrightarrow>
      lp_isubst (lp_ieval t \<sigma>) \<tau> =
        lp_ieval (t\<cdot>lpc_mgu_substitution V images) LPIVar"
  defines "us \<equiv> map (\<lambda>t. t\<cdot>lpc_mgu_substitution V images) ts"
  shows "\<exists>r. inj_on r (\<Union>(vars_term ` set us)) \<and>
    map (\<lambda>t. lp_ieval t \<sigma>) ts = map (\<lambda>t. lp_ieval t (LPIVar \<circ> r)) us"
proof -
  have env: "(\<lambda>x. lp_ieval (lpc_mgu_substitution V images x) \<sigma>) = \<sigma>"
    by (rule ext, rule lpc_checked_mgu_factor[OF checked solution])
  have forward: "\<And>t. lp_ieval (t\<cdot>lpc_mgu_substitution V images) \<sigma> = lp_ieval t \<sigma>"
    by (simp only: lp_ieval_finite_subst env)
  have roundtrip: "\<And>u. u\<in>set us \<Longrightarrow>
    lp_isubst (lp_ieval u \<sigma>) \<tau> = lp_ieval u LPIVar"
    using backward by (auto simp: us_def forward)
  obtain r where injective: "inj_on r (\<Union>(vars_term ` set us))"
    and mapped: "map (\<lambda>t. lp_ieval t \<sigma>) us = map (\<lambda>t. lp_ieval t (LPIVar \<circ> r)) us"
    using lpc_finite_roundtrip_renaming[OF roundtrip] by blast
  have forward_map: "map (\<lambda>t. lp_ieval t \<sigma>) ts = map (\<lambda>t. lp_ieval t \<sigma>) us"
    by (simp add: us_def map_map forward)
  show ?thesis
    by (rule exI[of _ r], rule conjI[OF injective], rule HOL.trans[OF forward_map mapped])
qed

theorem lpc_mgu_unify_interface_coverage:
  fixes a b :: "('f,string) term" and \<sigma> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes checked: "lpc_check_mgu fuel [(a,b)] V images"
    and mgu: "lpc_mgu_unify (lp_ieval a LPIVar) (lp_ieval b LPIVar)
      (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) \<sigma>"
  defines "ts \<equiv> a # concat (map lp_cut_terms gs)"
    and "us \<equiv> map (\<lambda>t. t\<cdot>lpc_mgu_substitution V images) (a # concat (map lp_cut_terms gs))"
  shows "\<exists>r. inj_on r (\<Union>(vars_term ` set us)) \<and>
    map (\<lambda>t. lp_ieval t \<sigma>) ts = map (\<lambda>t. lp_ieval t (LPIVar \<circ> r)) us"
proof -
  let ?s = "\<lambda>x. lp_ieval (lpc_mgu_substitution V images x) LPIVar"
  have solution: "lp_equations [(a,b)] \<sigma>"
    using mgu by (simp add: lpc_mgu_unify_def lp_ieval_subst lp_equations_def)
  have candidate: "lp_isubst (lp_ieval a LPIVar) ?s = lp_isubst (lp_ieval b LPIVar) ?s"
    using lpc_checked_mgu_unifies[OF checked]
    by (simp add: lp_equations_def lp_ieval_subst)
  obtain \<delta> :: "string \<Rightarrow> ('f,string) lp_iterm" where atom:
    "lp_isubst (lp_isubst (lp_ieval a LPIVar) \<sigma>) \<delta> = lp_isubst (lp_ieval a LPIVar) ?s"
    and goals:
    "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t \<sigma>) \<delta>))
      (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) =
     map (lp_cut_map (\<lambda>t. lp_isubst t ?s))
      (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs)"
    using mgu candidate unfolding lpc_mgu_unify_def by blast
  have atom_back: "lp_isubst (lp_ieval a \<sigma>) \<delta> =
      lp_ieval (a\<cdot>lpc_mgu_substitution V images) LPIVar"
    using atom by (simp add: lp_ieval_subst lp_ieval_finite_subst)
  have goals_back:
    "map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t \<sigma>) \<delta>)) gs =
      map (lp_cut_map (\<lambda>t. lp_ieval (t\<cdot>lpc_mgu_substitution V images) LPIVar)) gs"
    using goals by (simp add: map_map o_def lp_cut_map_comp lp_ieval_subst lp_ieval_finite_subst)
  have backward: "\<And>t. t\<in>set ts \<Longrightarrow>
    lp_isubst (lp_ieval t \<sigma>) \<delta> = lp_ieval (t\<cdot>lpc_mgu_substitution V images) LPIVar"
  proof -
    fix t assume "t\<in>set ts"
    then consider "t=a" | g where "g\<in>set gs" "t\<in>set (lp_cut_terms g)"
      by (auto simp: ts_def)
    then show "lp_isubst (lp_ieval t \<sigma>) \<delta> = lp_ieval (t\<cdot>lpc_mgu_substitution V images) LPIVar"
    proof cases
      case 1 then show ?thesis by (simp only: atom_back)
    next
      case (2 g)
      have "lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t \<sigma>) \<delta>) g =
        lp_cut_map (\<lambda>t. lp_ieval (t\<cdot>lpc_mgu_substitution V images) LPIVar) g"
        using goals_back 2(1) by (simp add: map_eq_conv)
      then show ?thesis using 2(2) by (cases g) auto
    qed
  qed
  show ?thesis unfolding us_def ts_def[symmetric]
    by (rule lpc_checked_mgu_interface_variants[OF checked solution backward])
qed

definition lpc_resolution_interface where
  "lpc_resolution_interface k a gs bs =
    a # (concat (map lp_cut_terms gs) @
      map (\<lambda>t. t\<cdot>(\<lambda>x. Var (lp_prefix k x))) (concat (map lp_cut_terms bs)))"

theorem lpc_mgu_resolve_interface_coverage:
  fixes a h :: "('f,string) term"
    and \<sigma> \<rho> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes checked: "lpc_check_mgu fuel [(a,h\<cdot>(\<lambda>x. Var (lp_prefix k x)))] V images"
    and short_a: "\<forall>x\<in>vars_term a. length x<k"
    and short_gs: "lp_cut_short_goals k gs"
    and mgu: "lpc_mgu_resolve (lp_ieval a LPIVar)
      (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) h bs \<sigma> \<rho>"
  defines "ts \<equiv> lpc_resolution_interface k a gs bs"
    and "\<eta> \<equiv> \<lambda>x. if length x<k then \<sigma> x else \<rho> (drop k x)"
  shows "\<exists>r. inj_on r (\<Union>(vars_term ` set (map (\<lambda>t. t\<cdot>lpc_mgu_substitution V images) ts))) \<and>
    map (\<lambda>t. lp_ieval t \<eta>) ts =
      map (\<lambda>t. lp_ieval t (LPIVar \<circ> r)) (map (\<lambda>t. t\<cdot>lpc_mgu_substitution V images) ts)"
proof -
  let ?s = "\<lambda>x. lp_ieval (lpc_mgu_substitution V images x) LPIVar"
  let ?r = "\<lambda>x. ?s (lp_prefix k x)"
  have fresh: "\<And>x. \<eta> (lp_prefix k x) = \<rho> x" by (simp add: \<eta>_def lp_prefix_def)
  have old: "\<And>t. (\<forall>x\<in>vars_term t. length x<k) \<Longrightarrow> lp_ieval t \<eta> = lp_ieval t \<sigma>"
    by (rule lp_ieval_cong) (auto simp: \<eta>_def)
  have solution: "lp_equations [(a,h\<cdot>(\<lambda>x. Var (lp_prefix k x)))] \<eta>"
    using mgu old[OF short_a]
    by (simp add: lpc_mgu_resolve_def lp_equations_def lp_ieval_finite_subst lp_ieval_subst fresh)
  have candidate: "lp_isubst (lp_ieval a LPIVar) ?s = lp_ieval h ?r"
    using lpc_checked_mgu_unifies[OF checked]
    by (simp add: lp_equations_def lp_ieval_subst lp_ieval_finite_subst)
  obtain \<delta> :: "string \<Rightarrow> ('f,string) lp_iterm" where atom:
    "lp_isubst (lp_isubst (lp_ieval a LPIVar) \<sigma>) \<delta> = lp_isubst (lp_ieval a LPIVar) ?s"
    and goals:
    "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t \<sigma>) \<delta>))
      (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) =
     map (lp_cut_map (\<lambda>t. lp_isubst t ?s)) (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs)"
    and body: "map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t \<rho>) \<delta>)) bs =
      map (lp_cut_map (\<lambda>t. lp_ieval t ?r)) bs"
    using mgu candidate unfolding lpc_mgu_resolve_def by blast
  have atom_back: "lp_isubst (lp_ieval a \<eta>) \<delta> = lp_ieval (a\<cdot>lpc_mgu_substitution V images) LPIVar"
    using atom old[OF short_a] by (simp add: lp_ieval_subst lp_ieval_finite_subst)
  have goals_back: "\<And>g t. g\<in>set gs \<Longrightarrow> t\<in>set (lp_cut_terms g) \<Longrightarrow>
    lp_isubst (lp_ieval t \<eta>) \<delta> = lp_ieval (t\<cdot>lpc_mgu_substitution V images) LPIVar"
  proof -
    fix g t assume g: "g\<in>set gs" and t: "t\<in>set (lp_cut_terms g)"
    have eq: "lp_cut_map (\<lambda>t. lp_isubst (lp_isubst (lp_ieval t LPIVar) \<sigma>) \<delta>) g =
      lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t LPIVar) ?s) g"
      using goals g by (simp add: map_map o_def lp_cut_map_comp map_eq_conv)
    have "lp_isubst (lp_ieval t \<sigma>) \<delta> = lp_ieval (t\<cdot>lpc_mgu_substitution V images) LPIVar"
      using eq t by (cases g) (auto simp: lp_ieval_subst lp_ieval_finite_subst)
    moreover have "lp_ieval t \<eta> = lp_ieval t \<sigma>"
      by (rule old) (use short_gs g t in \<open>auto simp: lp_cut_short_goals_def\<close>)
    ultimately show "lp_isubst (lp_ieval t \<eta>) \<delta> = lp_ieval (t\<cdot>lpc_mgu_substitution V images) LPIVar" by simp
  qed
  have body_back: "\<And>g t. g\<in>set bs \<Longrightarrow> t\<in>set (lp_cut_terms g) \<Longrightarrow>
    lp_isubst (lp_ieval (t\<cdot>(\<lambda>x. Var (lp_prefix k x))) \<eta>) \<delta> =
      lp_ieval ((t\<cdot>(\<lambda>x. Var (lp_prefix k x)))\<cdot>lpc_mgu_substitution V images) LPIVar"
  proof -
    fix g t assume g: "g\<in>set bs" and t: "t\<in>set (lp_cut_terms g)"
    have "lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t \<rho>) \<delta>) g = lp_cut_map (\<lambda>t. lp_ieval t ?r) g"
      using body g by (simp add: map_eq_conv)
    then have "lp_isubst (lp_ieval t \<rho>) \<delta> = lp_ieval t ?r" using t by (cases g) auto
    then show "lp_isubst (lp_ieval (t\<cdot>(\<lambda>x. Var (lp_prefix k x))) \<eta>) \<delta> =
      lp_ieval ((t\<cdot>(\<lambda>x. Var (lp_prefix k x)))\<cdot>lpc_mgu_substitution V images) LPIVar"
      by (simp add: lp_ieval_finite_subst fresh)
  qed
  have backward: "\<And>t. t\<in>set ts \<Longrightarrow>
    lp_isubst (lp_ieval t \<eta>) \<delta> = lp_ieval (t\<cdot>lpc_mgu_substitution V images) LPIVar"
    using atom_back goals_back body_back by (auto simp: ts_def lpc_resolution_interface_def)
  show ?thesis by (rule lpc_checked_mgu_interface_variants[OF checked solution backward])
qed

end
