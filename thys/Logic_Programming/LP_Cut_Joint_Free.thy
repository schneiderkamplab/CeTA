theory LP_Cut_Joint_Free
  imports LP_Cut_Uniform_Free
begin

lemma lpc_joint_comparison:
  fixes a h :: "('f,string) term" and eta theta :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes vars: "vars_term a \<subseteq> G\<union>F"
    and ground: "\<forall>x\<in>G. lp_seg_ground (eta x)"
    and free: "lpc_free_knowledge F eta"
    and same: "\<forall>x\<in>G\<inter>vars_term a. s x=Var x"
    and theta: "\<forall>x\<in>G. theta x=eta x"
    and eq: "a\<cdot>s=h\<cdot>r"
  shows "\<exists>tau :: string \<Rightarrow> ('f,string) lp_iterm.
    lp_isubst (lp_ieval a eta) tau=lp_ieval h (\<lambda>x. lp_ieval (r x) theta) \<and>
    (\<forall>x\<in>F. lp_isubst (eta x) tau=lp_ieval (s x) theta)"
proof -
  obtain f where inj: "inj_on f F" and repr: "\<forall>x\<in>F. eta x=LPIVar (f x)"
    using lpc_free_knowledge_representation[OF free] by blast
  let ?tau="\<lambda>y. if y\<in>f ` F then lp_ieval (s (inv_into F f y)) theta else LPIVar y"
  have free_images: "lp_isubst (eta x) ?tau=lp_ieval (s x) theta" if "x\<in>F" for x
    using that repr inj by (simp add: inv_into_f_f)
  have images: "lp_isubst (eta x) ?tau=lp_ieval (s x) theta" if x: "x\<in>vars_term a" for x
  proof (cases "x\<in>F")
    case True then show ?thesis by (rule free_images)
  next
    case False
    have g: "x\<in>G" using vars x False by blast
    have gr: "lp_seg_ground (eta x)" using ground g by blast
    have sx: "s x=Var x" using same g x by blast
    have th: "theta x=eta x" using theta g by blast
    show ?thesis using gr by (simp add: sx th lp_seg_ground_subst)
  qed
  have "lp_isubst (lp_ieval a eta) ?tau=lp_ieval (a\<cdot>s) theta"
    unfolding lp_ieval_subst lp_ieval_finite_subst by (rule lp_ieval_cong[OF images])
  also have "...=lp_ieval h (\<lambda>x. lp_ieval (r x) theta)"
    by (simp add: eq lp_ieval_finite_subst)
  finally show ?thesis using free_images by blast
qed

lemma lpc_joint_mgu_factor:
  fixes eta :: "string \<Rightarrow> ('f,string) lp_iterm"
    and sigma rho tau nu :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes mgu: "lpc_mgu_resolve (lp_ieval a eta)
    (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) h bs sigma rho"
    and comparison: "lp_isubst (lp_ieval a eta) tau=lp_ieval h nu"
  shows "\<exists>delta :: string \<Rightarrow> ('f,string) lp_iterm.
    (\<forall>x\<in>vars_term h \<union> (\<Union>g\<in>set bs. \<Union>t\<in>set (lp_cut_terms g). vars_term t).
      lp_isubst (rho x) delta=nu x) \<and>
    (\<forall>x\<in>(\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t).
      lp_isubst (lp_isubst (eta x) sigma) delta=lp_isubst (eta x) tau)"
proof -
  obtain delta :: "string \<Rightarrow> ('f,string) lp_iterm" where body:
    "map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t rho) delta)) (LPCAtom h#bs)=
      map (lp_cut_map (\<lambda>t. lp_ieval t nu)) (LPCAtom h#bs)"
    and cont: "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta))
      (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)=
      map (lp_cut_map (\<lambda>t. lp_isubst t tau)) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
    using lpc_mgu_head_observation[OF mgu] comparison unfolding lpc_mgu_resolve_def by blast
  have bf: "lp_isubst (rho x) delta=nu x"
    if g: "g\<in>set (LPCAtom h#bs)" and t: "t\<in>set (lp_cut_terms g)" and x: "x\<in>vars_term t" for g t x
  proof -
    have mapped: "lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t rho) delta) g=lp_cut_map (\<lambda>t. lp_ieval t nu) g"
      using body g by (auto simp: map_eq_conv)
    have "lp_isubst (lp_ieval t rho) delta=lp_ieval t nu" using mapped t by (cases g) auto
    then show ?thesis using lpc_ieval_variables_eq[OF _ x] by (simp add: lp_ieval_subst)
  qed
  have cf: "lp_isubst (lp_isubst (eta x) sigma) delta=lp_isubst (eta x) tau"
    if g: "g\<in>set gs" and t: "t\<in>set (lp_cut_terms g)" and x: "x\<in>vars_term t" for g t x
  proof -
    have mapped: "lp_cut_map (\<lambda>t. lp_isubst (lp_isubst (lp_ieval t eta) sigma) delta) g=
      lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t eta) tau) g"
      using cont g by (simp add: map_map o_def lp_cut_map_comp map_eq_conv)
    have "lp_isubst (lp_isubst (lp_ieval t eta) sigma) delta=lp_isubst (lp_ieval t eta) tau"
      using mapped t by (cases g) auto
    then show ?thesis using lpc_ieval_variables_eq[OF _ x] by (simp add: lp_ieval_subst)
  qed
  have hf: "lp_isubst (rho x) delta=nu x" if "x\<in>vars_term h" for x
    by (rule bf[where g="LPCAtom h" and t=h]) (use that in auto)
  show ?thesis by (rule exI[of _ delta]) (use bf cf hf in auto)
qed

lemma lpc_joint_free_block:
  fixes eta :: "string \<Rightarrow> ('f,string) lp_iterm"
    and sigma rho :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes mgu: "lpc_mgu_resolve (lp_ieval a eta) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) h bs sigma rho"
    and vars: "vars_term a \<subseteq> G\<union>F"
    and ground: "\<forall>x\<in>G. lp_seg_ground (eta x)"
    and free: "lpc_free_knowledge F eta"
    and same: "\<forall>x\<in>G\<inter>vars_term a. s x=Var x"
    and eq: "a\<cdot>s=h\<cdot>r"
    and head: "\<And>x. (True,x)\<in>C \<Longrightarrow> x\<in>vars_term h \<union> (\<Union>g\<in>set bs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
    and cont: "\<And>x. (False,x)\<in>C \<Longrightarrow> x\<in>F \<inter> (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
    and images: "\<forall>p\<in>C. \<exists>v. (if fst p then r (snd p) else s (snd p))=Var v \<and> v\<notin>G"
    and distinct: "inj_on (\<lambda>p. if fst p then r (snd p) else s (snd p)) C"
  shows "(\<forall>p\<in>C. \<exists>v. (if fst p then rho (snd p) else lp_isubst (eta (snd p)) sigma)=LPIVar v) \<and>
    inj_on (\<lambda>p. if fst p then rho (snd p) else lp_isubst (eta (snd p)) sigma) C"
proof -
  let ?theta="\<lambda>x. if x\<in>G then eta x else LPIVar x"
  let ?nu="\<lambda>x. lp_ieval (r x) ?theta"
  let ?image="\<lambda>p. if fst p then r (snd p) else s (snd p)"
  let ?actual="\<lambda>p. if fst p then rho (snd p) else lp_isubst (eta (snd p)) sigma"
  obtain tau :: "string \<Rightarrow> ('f,string) lp_iterm" where comparison:
    "lp_isubst (lp_ieval a eta) tau=lp_ieval h ?nu"
    and source: "\<forall>x\<in>F. lp_isubst (eta x) tau=lp_ieval (s x) ?theta"
    using lpc_joint_comparison[OF vars ground free same _ eq, where theta="?theta"] by auto
  obtain delta :: "string \<Rightarrow> ('f,string) lp_iterm" where body_factor:
    "\<forall>x\<in>vars_term h \<union> (\<Union>g\<in>set bs. \<Union>t\<in>set (lp_cut_terms g). vars_term t). lp_isubst (rho x) delta=?nu x"
    and context_factor: "\<forall>x\<in>(\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t).
      lp_isubst (lp_isubst (eta x) sigma) delta=lp_isubst (eta x) tau"
    using lpc_joint_mgu_factor[OF mgu comparison] by blast
  have factor: "lp_isubst (?actual p) delta=lp_ieval (?image p) ?theta" if p: "p\<in>C" for p
  proof (cases p)
    case (Pair b x)
    then show ?thesis using p head[of x] cont[of x] body_factor context_factor source by (cases b) auto
  qed
  have variable: "\<exists>v. ?actual p=LPIVar v" if p: "p\<in>C" for p
  proof -
    obtain v where val_eq: "?image p=Var v" "v\<notin>G" using images p by blast
    have "lp_isubst (?actual p) delta=LPIVar v" using factor[OF p] by (simp add: val_eq)
    then show ?thesis by (rule lpc_isubst_variable_reflect)
  qed
  have injective: "inj_on ?actual C"
  proof (rule inj_onI)
    fix p q assume p: "p\<in>C" and q: "q\<in>C" and same: "?actual p=?actual q"
    obtain u v where pv: "?image p=Var u" "u\<notin>G" and qv: "?image q=Var v" "v\<notin>G"
      using images p q by blast
    have "lp_ieval (?image p) ?theta=lp_ieval (?image q) ?theta" using factor[OF p] factor[OF q] same by simp
    then have "u=v" by (simp add: pv qv)
    then have "?image p=?image q" by (simp add: pv qv)
    then show "p=q" by (rule inj_onD[OF distinct _ p q])
  qed
  show ?thesis using variable injective by blast
qed

end
