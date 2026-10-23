theory LP_Cut_MGU_Scopes
  imports LP_Cut_MGU_Coverage LP_Cut_Scope_Source
begin

lemma lpc_mgu_resolve_scope:
  fixes a :: "('f,string) lp_iterm"
  assumes mgu: "lpc_mgu_resolve a gs h bs \<sigma> \<rho>"
  shows "lpc_mgu_resolve a (map (lp_cut_scope_goal r) gs) h bs \<sigma> \<rho>"
proof (unfold lpc_mgu_resolve_def, intro conjI allI impI)
  show "lp_isubst a \<sigma> = lp_ieval h \<rho>" using mgu by (simp add: lpc_mgu_resolve_def)
next
  fix \<tau> \<nu> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assume eq: "lp_isubst a \<tau> = lp_ieval h \<nu>"
  from mgu eq obtain \<delta> :: "string \<Rightarrow> ('f,string) lp_iterm" where atom: "lp_isubst (lp_isubst a \<sigma>) \<delta> = lp_isubst a \<tau>"
    and goals: "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t \<sigma>) \<delta>)) gs =
      map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>)) gs"
    and body: "map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t \<rho>) \<delta>)) bs =
      map (lp_cut_map (\<lambda>t. lp_ieval t \<nu>)) bs"
    unfolding lpc_mgu_resolve_def by blast
  have scoped: "map (lp_cut_scope_goal r)
    (map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t \<sigma>) \<delta>)) gs) =
    map (lp_cut_scope_goal r) (map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>)) gs)"
    by (rule arg_cong[OF goals])
  show "\<exists>\<delta>. lp_isubst (lp_isubst a \<sigma>) \<delta> = lp_isubst a \<tau> \<and>
    map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t \<sigma>) \<delta>)) (map (lp_cut_scope_goal r) gs) =
      map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>)) (map (lp_cut_scope_goal r) gs) \<and>
    map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t \<rho>) \<delta>)) bs =
      map (lp_cut_map (\<lambda>t. lp_ieval t \<nu>)) bs"
    by (rule exI[of _ \<delta>])
      (use atom body scoped in \<open>simp add: map_map o_def lp_cut_scope_goal_map\<close>)
qed

lemma lpc_mgu_unify_scope:
  fixes a :: "('f,string) lp_iterm"
  assumes mgu: "lpc_mgu_unify a b gs \<sigma>"
  shows "lpc_mgu_unify a b (map (lp_cut_scope_goal r) gs) \<sigma>"
proof (unfold lpc_mgu_unify_def, intro conjI allI impI)
  show "lp_isubst a \<sigma> = lp_isubst b \<sigma>" using mgu by (simp add: lpc_mgu_unify_def)
next
  fix \<tau> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assume eq: "lp_isubst a \<tau> = lp_isubst b \<tau>"
  from mgu eq obtain \<delta> :: "string \<Rightarrow> ('f,string) lp_iterm" where atom: "lp_isubst (lp_isubst a \<sigma>) \<delta> = lp_isubst a \<tau>"
    and goals: "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t \<sigma>) \<delta>)) gs =
      map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>)) gs"
    unfolding lpc_mgu_unify_def by blast
  have scoped: "map (lp_cut_scope_goal r)
    (map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t \<sigma>) \<delta>)) gs) =
    map (lp_cut_scope_goal r) (map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>)) gs)"
    by (rule arg_cong[OF goals])
  show "\<exists>\<delta>. lp_isubst (lp_isubst a \<sigma>) \<delta> = lp_isubst a \<tau> \<and>
    map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t \<sigma>) \<delta>)) (map (lp_cut_scope_goal r) gs) =
      map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>)) (map (lp_cut_scope_goal r) gs)"
    by (rule exI[of _ \<delta>])
      (use atom scoped in \<open>simp add: map_map o_def lp_cut_scope_goal_map\<close>)
qed

lemma lpc_mgu_scope_source:
  assumes step: "(s,t)\<in>lp_cut_mgu_source P"
    and injective: "inj r" and program: "lp_cut_source_program P"
  shows "(map (lp_cut_scope_entry r) s,map (lp_cut_scope_entry r) t)\<in>lp_cut_mgu_source P"
  using step
proof (induct rule: lp_cut_mgu_source.induct)
  case (admin s t)
  show ?case by (rule lp_cut_mgu_source.admin)
    (simp add: lp_cut_scope_admin[OF injective] admin)
next
  case (case_call m f ts gs es)
  have fresh: "lp_cut_fresh (r m)
    (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#map (lp_cut_scope_goal r) gs)#map (lp_cut_scope_entry r) es)"
    using case_call(1) lp_cut_scope_fresh[OF injective, of m
      "LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#es"] by simp
  show ?case using lp_cut_mgu_source.case_call[OF fresh]
    by (simp add: case_call map_map o_def)
next
  case (resolve c a gs \<sigma> \<rho> m es)
  have body: "map (lp_cut_scope_goal r)
    (map (lp_cut_bind m (\<lambda>t. lp_ieval t \<rho>)) (snd (P!c))) =
    map (lp_cut_bind (r m) (\<lambda>t. lp_ieval t \<rho>)) (snd (P!c))"
    using program resolve(1)
    by (auto simp: lp_cut_source_program_def list_all_iff map_map o_def
      intro!: map_cong lp_cut_scope_bind)
  have mgu: "lpc_mgu_resolve a (map (lp_cut_scope_goal r) gs) (fst (P!c)) (snd (P!c)) \<sigma> \<rho>"
    by (rule lpc_mgu_resolve_scope[OF resolve(2)])
  show ?case using lp_cut_mgu_source.resolve[OF resolve(1) mgu, of "r m" "map (lp_cut_scope_entry r) es"]
    by (simp add: resolve body[unfolded map_map o_def] map_map o_def lp_cut_scope_goal_map)
next
  case (backtrack c a gs m es)
  show ?case using lp_cut_mgu_source.backtrack[OF backtrack(1,2),
    of "map (lp_cut_scope_goal r) gs" "r m" "map (lp_cut_scope_entry r) es"]
    by (simp add: backtrack)
next
  case (unify a b gs \<sigma> es)
  have mgu: "lpc_mgu_unify a b (map (lp_cut_scope_goal r) gs) \<sigma>"
    by (rule lpc_mgu_unify_scope[OF unify(1)])
  show ?case using lp_cut_mgu_source.unify[OF mgu, of "map (lp_cut_scope_entry r) es"]
    by (simp add: unify map_map o_def lp_cut_scope_goal_map)
next
  case (unify_fail a b gs es)
  show ?case using lp_cut_mgu_source.unify_fail[OF unify_fail(1), of "map (lp_cut_scope_goal r) gs"
      "map (lp_cut_scope_entry r) es"]
    by (simp add: unify_fail)
next
  case (meta m a gs es body)
  have fresh: "lp_cut_fresh (r m)
    (LPCGoals (LPCMeta a#map (lp_cut_scope_goal r) gs)#map (lp_cut_scope_entry r) es)"
    using meta(1) lp_cut_scope_fresh[OF injective, of m "LPCGoals (LPCMeta a#gs)#es"] by simp
  show ?case using lp_cut_mgu_source.meta[OF fresh lp_cut_scope_lower[OF meta(2), of r]]
    by (simp add: meta)
next
  case (meta_unlowerable a gs es)
  show ?case using lp_cut_mgu_source.meta_unlowerable[OF meta_unlowerable(1),
    of "map (lp_cut_scope_goal r) gs" "map (lp_cut_scope_entry r) es"]
    by (simp add: meta_unlowerable)
qed

lemma lpc_mgu_scope_reflects_SN:
  assumes injective: "inj r" and program: "lp_cut_source_program P"
    and sn: "SN_on (lp_cut_mgu_source P) {map (lp_cut_scope_entry r) s}"
  shows "SN_on (lp_cut_mgu_source P) {s}"
proof -
  have all: "\<forall>s. xs=map (lp_cut_scope_entry r) s \<longrightarrow> SN_on (lp_cut_mgu_source P) {s}"
    if "SN_on (lp_cut_mgu_source P) {xs}" for xs
  proof (rule SN_on_induct[OF that singletonI], intro allI impI)
    fix xs s
    assume ih: "\<And>ys. (xs,ys)\<in>lp_cut_mgu_source P \<Longrightarrow>
      \<forall>s. ys=map (lp_cut_scope_entry r) s \<longrightarrow> SN_on (lp_cut_mgu_source P) {s}"
      and represented: "xs=map (lp_cut_scope_entry r) s"
    show "SN_on (lp_cut_mgu_source P) {s}"
    proof (rule step_reflects_SN_on)
      fix t assume step: "(s,t)\<in>lp_cut_mgu_source P"
      show "SN_on (lp_cut_mgu_source P) {t}"
        using ih[OF lpc_mgu_scope_source[OF step injective program, folded represented]] by blast
    qed
  qed
  show ?thesis using all[OF sn] by blast
qed

lemma lpc_mgu_scope_swap_preserves_SN:
  assumes "lp_cut_source_program P" "SN_on (lp_cut_mgu_source P) {s}"
  shows "SN_on (lp_cut_mgu_source P) {map (lp_cut_scope_entry (lp_cut_scope_swap a b)) s}"
proof -
  have twice: "map (lp_cut_scope_entry (lp_cut_scope_swap a b))
    (map (lp_cut_scope_entry (lp_cut_scope_swap a b)) s)=s"
    by (simp add: map_map o_def lp_cut_scope_entry_comp lp_cut_scope_swap_inverse
      lp_cut_scope_identity[unfolded id_def])
  show ?thesis by (rule lpc_mgu_scope_reflects_SN[OF lp_cut_scope_swap_injective[of a b] assms(1)])
    (use assms(2) twice in simp)
qed

end
