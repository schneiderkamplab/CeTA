theory LP_Cut_Domain_Precise_Canonical
  imports LP_Cut_Domain_Precise_MGU
begin

context cut_runtime_domain
begin

lemma precise_canonical_step:
  fixes P :: "'f logic_cut_program"
  assumes "logic_cut_step (\<lambda>t. D (cut_tree t)) P s t"
  shows "(cut_state s,cut_state t) \<in> precise_source (cut_program P)"
  using assms
proof (cases rule: logic_cut_step.cases)
  case admin
  then show ?thesis by (auto intro: precise_source.admin simp: cut_admin)
next
  case (case_call m f ts gs es)
  then show ?thesis
    using precise_source.case_call[of m f "map cut_tree ts" "map (cut_goal cut_tree) gs"
      "cut_state es" "cut_program P"]
    by (simp add: cut_slice map_map o_def lp_cut_fresh_def logic_fresh_mark_def image_image)
next
  case (resolve c a gs sigma rho m es)
  have index: "c<length (cut_program P)" using resolve by simp
  have mgu: "mgu_resolve (cut_tree a) (map (cut_goal cut_tree) gs)
    (fst (cut_program P!c)) (snd (cut_program P!c)) (cut_tree \<circ> sigma) (cut_tree \<circ> rho)"
    using precise_mgu_resolve[OF resolve(4)] index by (simp add: cut_program_nth)
  show ?thesis using precise_source.resolve[OF index mgu, where m=m and es="cut_state es"] resolve
    by (simp add: cut_program_nth map_map o_def cut_goal_subst cut_goal_eval_bind)
next
  case (backtrack c a gs m)
  have head: "fst (cut_program P!c) = cut_term (fst (P!c))"
    using backtrack by (simp add: cut_program_nth)
  have index: "c<length (cut_program P)" using backtrack by simp
  have failure: "\<not>(\<exists>sigma :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm. \<exists>rho.
    (\<forall>x. D (sigma x)) \<and> (\<forall>x. D (rho x)) \<and>
    lp_isubst (cut_tree a) sigma = lp_ieval (fst (cut_program P!c)) rho)"
    unfolding head using backtrack unifiable_iff[of a "fst (P!c)"] by blast
  show ?thesis using precise_source.backtrack[OF index failure,
    where gs="map (cut_goal cut_tree) gs" and m=m and es="cut_state t"] backtrack by simp
next
  case (unify a b gs sigma es)
  have mgu: "mgu_unify (cut_tree a) (cut_tree b) (map (cut_goal cut_tree) gs) (cut_tree \<circ> sigma)"
    by (rule precise_mgu_unify[OF unify(3)])
  show ?thesis using precise_source.unify[OF mgu, where es="cut_state es"] unify
    by (simp add: map_map o_def cut_goal_subst)
next
  case (unify_fail a b gs)
  have failure: "\<not>(\<exists>sigma :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm.
    (\<forall>x. D (sigma x)) \<and> lp_isubst (cut_tree a) sigma = lp_isubst (cut_tree b) sigma)"
    using unify_fail by (simp add: equalizable_iff logic_substitution_def)
  show ?thesis using precise_source.unify_fail[OF failure,
    where gs="map (cut_goal cut_tree) gs" and es="cut_state t"] unify_fail by simp
next
  case (meta m f ts gs es body)
  have fresh: "lp_cut_fresh m (cut_state (LogicGoals (LogicMeta (LFun f ts)#gs)#es))"
    using meta by (simp add: lp_cut_fresh_def logic_fresh_mark_def image_image)
  have lower: "lp_cut_lower m (cut_tree (LFun f ts)) (map (cut_goal cut_tree) body)"
    by (rule cut_lower) (use meta in blast)
  show ?thesis using precise_source.meta[OF _ lower,
    where gs="map (cut_goal cut_tree) gs" and es="cut_state es"] meta fresh by simp
next
  case (meta_diverges a gs es)
  have failure: "\<not>(\<exists>m body. lp_cut_lower m (cut_tree a) body)"
    by (rule cut_diverges_unlowerable) (use meta_diverges in blast)
  show ?thesis using precise_source.meta_unlowerable[OF failure,
    where gs="map (cut_goal cut_tree) gs" and es="cut_state es"] meta_diverges
    by simp
qed

theorem precise_canonical_termination:
  assumes native: "\<And>ts. logic_query (LogicUser p) modes (LogicUser p,ts) \<Longrightarrow>
    SN_on (precise_source (cut_program P))
      {cut_state [LogicGoals [LogicAtom (LFun (LogicUser p) (map logic_embed ts))]]}"
  shows "logic_cut_terminates_in (\<lambda>t. D (cut_tree t)) P p modes"
proof (unfold logic_cut_terminates_in_def, clarify)
  fix ts s assume query: "logic_query (LogicUser p) modes (LogicUser p,ts)"
    and init: "s 0 = [LogicGoals [LogicAtom (LFun (LogicUser p) (map logic_embed ts))]]"
    and steps: "\<forall>n. logic_cut_step (\<lambda>t. D (cut_tree t)) P (s n) (s (Suc n))"
  have chain: "\<forall>n. ((cut_state \<circ> s) n,(cut_state \<circ> s) (Suc n))
    \<in> precise_source (cut_program P)"
    by (simp only: o_apply; intro allI; rule precise_canonical_step; rule spec[OF steps])
  have bad: "\<exists>f. f 0 \<in> {cut_state [LogicGoals [LogicAtom (LFun (LogicUser p) (map logic_embed ts))]]}
    \<and> (\<forall>n. (f n,f (Suc n)) \<in> precise_source (cut_program P))"
    by (rule exI[of _ "cut_state \<circ> s"], rule conjI)
      (simp add: init, rule chain)
  show False using native[OF query] bad unfolding SN_on_def by blast
qed

end
end
