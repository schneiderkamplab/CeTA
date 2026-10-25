theory LP_Cut_MGU_Context_Free
  imports LP_Cut_MGU_Head_Knowledge
begin

lemma lpc_mgu_head_observation:
  fixes a :: "('f,string) lp_iterm" and sigma rho :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes mgu: "lpc_mgu_resolve a gs h bs sigma rho"
  shows "lpc_mgu_resolve a gs h (LPCAtom h#bs) sigma rho"
proof -
  have eq: "lp_isubst a sigma=lp_ieval h rho" using mgu by (simp add: lpc_mgu_resolve_def)
  show ?thesis
    unfolding lpc_mgu_resolve_def
  proof (rule conjI[OF eq], intro allI impI)
    fix tau nu :: "string \<Rightarrow> ('f,string) lp_iterm"
    assume comparison: "lp_isubst a tau=lp_ieval h nu"
    obtain delta :: "string \<Rightarrow> ('f,string) lp_iterm" where first: "lp_isubst (lp_isubst a sigma) delta=lp_isubst a tau"
      and cont: "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta)) gs = map (lp_cut_map (\<lambda>t. lp_isubst t tau)) gs"
      and body: "map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t rho) delta)) bs = map (lp_cut_map (\<lambda>t. lp_ieval t nu)) bs"
      using mgu comparison unfolding lpc_mgu_resolve_def by blast
    have head_eq: "lp_isubst (lp_ieval h rho) delta=lp_ieval h nu"
      using first eq comparison by simp
    show "\<exists>delta :: string \<Rightarrow> ('f,string) lp_iterm. lp_isubst (lp_isubst a sigma) delta=lp_isubst a tau \<and>
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta)) gs = map (lp_cut_map (\<lambda>t. lp_isubst t tau)) gs \<and>
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t rho) delta)) (LPCAtom h#bs) =
      map (lp_cut_map (\<lambda>t. lp_ieval t nu)) (LPCAtom h#bs)"
      by (rule exI[of _ delta]) (simp add: first cont body head_eq)
  qed
qed

lemma lpc_mgu_context_factor:
  fixes eta :: "string \<Rightarrow> ('f,string) lp_iterm"
    and sigma rho tau nu :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes mgu: "lpc_mgu_resolve (lp_ieval a eta)
      (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) h bs sigma rho"
    and comparison: "lp_isubst (lp_ieval a eta) tau=lp_ieval h nu"
  shows "\<exists>delta :: string \<Rightarrow> ('f,string) lp_iterm.
    \<forall>g\<in>set gs. \<forall>t\<in>set (lp_cut_terms g). \<forall>x\<in>vars_term t.
      lp_isubst (lp_isubst (eta x) sigma) delta=lp_isubst (eta x) tau"
proof -
  obtain delta :: "string \<Rightarrow> ('f,string) lp_iterm" where factor:
    "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta))
      (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) =
     map (lp_cut_map (\<lambda>t. lp_isubst t tau)) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
    using mgu comparison unfolding lpc_mgu_resolve_def by blast
  show ?thesis
  proof (rule exI[of _ delta], intro ballI)
    fix g t x assume g: "g\<in>set gs" and t: "t\<in>set (lp_cut_terms g)" and x: "x\<in>vars_term t"
    have mapped: "lp_cut_map (\<lambda>u. lp_isubst (lp_isubst (lp_ieval u eta) sigma) delta) g =
      lp_cut_map (\<lambda>u. lp_isubst (lp_ieval u eta) tau) g"
      using factor g by (simp add: map_map o_def lp_cut_map_comp map_eq_conv)
    have "lp_isubst (lp_isubst (lp_ieval t eta) sigma) delta=lp_isubst (lp_ieval t eta) tau"
      using mapped t by (cases g) auto
    then show "lp_isubst (lp_isubst (eta x) sigma) delta=lp_isubst (eta x) tau"
      using lpc_ieval_variables_eq[OF _ x] by (simp add: lp_ieval_subst)
  qed
qed

lemma lpc_mgu_untouched_context_free:
  fixes eta :: "string \<Rightarrow> ('f,string) lp_iterm"
    and sigma rho :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes mgu: "lpc_mgu_resolve (lp_ieval a eta)
      (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) h bs sigma rho"
    and free: "lpc_free_knowledge F eta"
    and ground: "\<forall>x\<in>G. lp_seg_ground (eta x)"
    and vars: "vars_term a \<subseteq> G\<union>F"
    and subset: "C\<subseteq>F"
    and disjoint: "C\<inter>vars_term a={}"
    and occurs: "C\<subseteq>(\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
  shows "lpc_free_knowledge C (\<lambda>x. lp_isubst (eta x) sigma)"
proof -
  obtain r where inj: "inj_on r F" and repr: "\<forall>x\<in>F. eta x=LPIVar (r x)"
    using lpc_free_knowledge_representation[OF free] by blast
  let ?tau = "\<lambda>y. if y\<in>r ` C then LPIVar y else sigma y"
  have same: "lp_isubst (eta x) ?tau=lp_isubst (eta x) sigma" if x: "x\<in>vars_term a" for x
  proof (cases "x\<in>G")
    case True
    then show ?thesis using ground by (simp add: lp_seg_ground_subst)
  next
    case False
    have f: "x\<in>F" using vars x False by blast
    have n: "r x\<notin>r ` C"
    proof
      assume "r x\<in>r ` C"
      then obtain y where y: "y\<in>C" and eq: "r x=r y" by blast
      have yf: "y\<in>F" using subset y by blast
      have "x=y" by (rule inj_onD[OF inj eq f yf])
      then have "x\<in>C" using y by simp
      then show False using disjoint x by blast
    qed
    show ?thesis using repr f n by simp
  qed
  have comparison: "lp_isubst (lp_ieval a eta) ?tau=lp_ieval h rho"
  proof -
    have "lp_isubst (lp_ieval a eta) ?tau=lp_isubst (lp_ieval a eta) sigma"
      unfolding lp_ieval_subst by (rule lp_ieval_cong[OF same])
    then show ?thesis using mgu by (simp add: lpc_mgu_resolve_def)
  qed
  obtain delta :: "string \<Rightarrow> ('f,string) lp_iterm" where factor:
    "\<forall>g\<in>set gs. \<forall>t\<in>set (lp_cut_terms g). \<forall>x\<in>vars_term t.
      lp_isubst (lp_isubst (eta x) sigma) delta=lp_isubst (eta x) ?tau"
    using lpc_mgu_context_factor[OF mgu comparison] by blast
  have equation: "lp_isubst (lp_isubst (eta x) sigma) delta=eta x" if x: "x\<in>C" for x
  proof -
    have "lp_isubst (lp_isubst (eta x) sigma) delta=lp_isubst (eta x) ?tau"
      using factor occurs x by blast
    then show ?thesis using repr subset x by auto
  qed
  have variables: "\<forall>x\<in>C. \<exists>y. lp_isubst (eta x) sigma=LPIVar y"
  proof (intro ballI)
    fix x assume x: "x\<in>C"
    have val_eq: "eta x=LPIVar (r x)" using repr subset x by blast
    have "lp_isubst (lp_isubst (eta x) sigma) delta=LPIVar (r x)"
      using equation[OF x] val_eq by simp
    then show "\<exists>y. lp_isubst (eta x) sigma=LPIVar y"
      by (rule lpc_isubst_variable_reflect)
  qed
  have distinct: "inj_on (\<lambda>x. lp_isubst (eta x) sigma) C"
  proof (rule inj_onI)
    fix x y assume x: "x\<in>C" and y: "y\<in>C" and eq: "lp_isubst (eta x) sigma=lp_isubst (eta y) sigma"
    have old_eq: "eta x=eta y"
    proof -
      have "eta x=lp_isubst (lp_isubst (eta x) sigma) delta" by (rule sym[OF equation[OF x]])
      also have "...=lp_isubst (lp_isubst (eta y) sigma) delta" by (rule arg_cong[OF eq])
      also have "...=eta y" by (rule equation[OF y])
      finally show ?thesis .
    qed
    have eta_inj: "inj_on eta F" using free unfolding lpc_free_knowledge_def by (rule conjunct2)
    have xf: "x\<in>F" using subset x by blast
    have yf: "y\<in>F" using subset y by blast
    show "x=y" by (rule inj_onD[OF eta_inj old_eq xf yf])
  qed
  show ?thesis using variables distinct by (simp add: lpc_free_knowledge_def)
qed

end
