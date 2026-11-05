theory LP_Cut_Ground_Recurrence
  imports LP_Cut_Uniform_Recursion
begin

text \<open>A ground recursive call may resolve to a body with fresh local
variables. Unlike uniform recursion, the body is not assumed ground. Its local
variables remain distinct and free; the complete pending alternative stack is
retained by the source resolution rules.\<close>

lemma lpc_ground_head_fresh_body_mgu:
  fixes rho :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes ground: "\<And>x. x\<in>set xs \<Longrightarrow> lp_seg_ground (rho x)"
    and fresh: "\<And>x. x\<notin>set xs \<Longrightarrow> rho x=LPIVar x"
  shows "lpc_mgu_resolve (lp_ieval (Fun f (map Var xs)) rho) []
    (Fun f (map Var xs)) bs LPIVar rho"
proof -
  let ?a = "lp_ieval (Fun f (map Var xs)) rho"
  have grounded: "lp_seg_ground ?a"
    by (rule lpc_uniform_ground_eval) (use ground in auto)
  have factor: "\<exists>delta. lp_isubst (lp_isubst ?a LPIVar) delta=lp_isubst ?a tau \<and>
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t rho) delta)) bs =
      map (lp_cut_map (\<lambda>t. lp_ieval t nu)) bs"
    if equation: "lp_isubst ?a tau=lp_ieval (Fun f (map Var xs)) nu" for tau nu :: "string \<Rightarrow> ('f,string) lp_iterm"
  proof -
    have head: "?a=lp_ieval (Fun f (map Var xs)) nu"
      using equation by (simp only: lp_seg_ground_subst[OF grounded])
    have known: "rho x=nu x" if "x\<in>set xs" for x
      using lpc_ieval_variables_eq[OF head, of x] that by simp
    have binding: "lp_isubst (rho x) nu=nu x" for x
    proof (cases "x\<in>set xs")
      case True
      have stable: "lp_isubst (rho x) nu=rho x"
        by (rule lp_seg_ground_subst[OF ground[OF True]])
      show ?thesis using stable known[OF True] by metis
    next
      case False show ?thesis by (simp add: fresh[OF False])
    qed
    have body: "lp_isubst (lp_ieval t rho) nu=lp_ieval t nu" for t
      by (simp add: lp_ieval_subst binding)
    have head_factor: "lp_isubst (lp_isubst ?a LPIVar) nu=lp_isubst ?a tau"
      by (simp only: lp_seg_ground_subst[OF grounded])
    show ?thesis by (rule exI[of _ nu]) (use head_factor body in auto)
  qed
  show ?thesis unfolding lpc_mgu_resolve_def using factor by auto
qed

lemma lpc_ground_first_clause_transition_pair:
  assumes first: "lp_cut_slice P (LPCUser f) (length xs)=c#cs"
    and index: "c<length P"
    and clause: "P!c=(Fun (LPCUser f) (map Var xs),bs)"
    and ground: "\<And>x. x\<in>set xs \<Longrightarrow> lp_seg_ground (rho x)"
    and fresh: "\<And>x. x\<notin>set xs \<Longrightarrow> rho x=LPIVar x"
  shows "\<exists>m. (LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) (map Var xs)) rho)]#es,
    LPCClause [LPCAtom (lp_ieval (Fun (LPCUser f) (map Var xs)) rho)] c m#
      (map (\<lambda>d. LPCClause [LPCAtom (lp_ieval (Fun (LPCUser f) (map Var xs)) rho)] d m) cs @
        LPCBarrier m#es))\<in>lp_cut_mgu_source P \<and>
    (LPCClause [LPCAtom (lp_ieval (Fun (LPCUser f) (map Var xs)) rho)] c m#
      (map (\<lambda>d. LPCClause [LPCAtom (lp_ieval (Fun (LPCUser f) (map Var xs)) rho)] d m) cs @
        LPCBarrier m#es),
    LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) bs)#
      (map (\<lambda>d. LPCClause [LPCAtom (lp_ieval (Fun (LPCUser f) (map Var xs)) rho)] d m) cs @
        LPCBarrier m#es))\<in>lp_cut_mgu_source P"
proof -
  let ?a = "lp_ieval (Fun (LPCUser f) (map Var xs)) rho"
  let ?s = "LPCGoals [LPCAtom ?a]#es"
  obtain m where allocated: "lp_cut_fresh m ?s" using lpc_uniform_fresh by blast
  let ?saved = "map (\<lambda>d. LPCClause [LPCAtom ?a] d m) cs @ LPCBarrier m#es"
  have selected: "(?s,LPCClause [LPCAtom ?a] c m#?saved)\<in>lp_cut_mgu_source P"
    using lp_cut_mgu_source.case_call[of m f "map rho xs" "[]" es P] allocated
    by (simp add: first o_def)
  have mgu: "lpc_mgu_resolve ?a [] (fst (P!c)) (snd (P!c)) LPIVar rho"
    using lpc_ground_head_fresh_body_mgu[where f="LPCUser f" and bs=bs, OF ground fresh]
    by (simp add: clause)
  have resolved: "(LPCClause [LPCAtom ?a] c m#?saved,
    LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) bs)#?saved)\<in>lp_cut_mgu_source P"
    using lp_cut_mgu_source.resolve[OF index mgu, of m ?saved] by (simp add: clause)
  show ?thesis using selected resolved by blast
qed

lemma lpc_ground_first_clause_steps:
  assumes first: "lp_cut_slice P (LPCUser f) (length xs)=c#cs"
    and index: "c<length P"
    and clause: "P!c=(Fun (LPCUser f) (map Var xs),bs)"
    and ground: "\<And>x. x\<in>set xs \<Longrightarrow> lp_seg_ground (rho x)"
    and fresh: "\<And>x. x\<notin>set xs \<Longrightarrow> rho x=LPIVar x"
  shows "\<exists>m. (LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) (map Var xs)) rho)]#es,
    LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) bs)#
      (map (\<lambda>d. LPCClause [LPCAtom (lp_ieval (Fun (LPCUser f) (map Var xs)) rho)] d m) cs @
        LPCBarrier m#es))\<in>(lp_cut_mgu_source P)\<^sup>+"
  using lpc_ground_first_clause_transition_pair[OF assms]
  by (meson r_into_trancl trancl_trans)

end
