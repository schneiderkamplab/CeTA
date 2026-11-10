theory LP_Cut_Domain_Success
  imports LP_Cut_Domain_Resolution
begin

context cut_runtime_domain
begin

lemma erase_resolution_guards:
  "lp_cut_check_resolution P fuel k l G A guards a gs c m es next anchors \<Longrightarrow>
    lp_cut_check_resolution P fuel k l G A [] a gs c m es next anchors"
  by (simp add: lp_cut_check_resolution_def)
lemma erase_unify_guards:
  "lp_cut_check_unify fuel k l G guards a b gs es next \<Longrightarrow>
    lp_cut_check_unify fuel k l G [] a b gs es next"
  by (simp add: lp_cut_check_unify_def)
lemma erase_knowledge_guards:
  "knowledge G guards eta \<Longrightarrow> lp_cut_knowledge G [] eta"
  by (simp add: knowledge_def lp_cut_knowledge_def)

lemma resolution_equations:
  "lp_cut_check_resolution P fuel k l G A guards a gs c m es next anchors \<Longrightarrow>
    knowledge (set G) guards eta \<Longrightarrow>
    lp_isubst (lp_ieval a eta) sigma = lp_ieval (fst (P!c)) rho \<Longrightarrow>
    lp_equations (lp_cut_resolution_equations k l G a (fst (P!c)))
      (lp_cut_resolution_env k l eta sigma rho)"
  by (rule lp_cut_checked_resolution_equations[OF erase_resolution_guards erase_knowledge_guards]) assumption+
lemma unify_equations:
  "lp_cut_check_unify fuel k l G guards a b gs es next \<Longrightarrow>
    knowledge (set G) guards eta \<Longrightarrow>
    lp_isubst (lp_ieval a eta) sigma = lp_isubst (lp_ieval b eta) sigma \<Longrightarrow>
    lp_equations [(a\<cdot>lp_cut_refresh k (set G),b\<cdot>lp_cut_refresh k (set G))]
      (lp_cut_resolution_env k l eta sigma eta)"
  by (rule lp_cut_checked_unify_equations[OF erase_unify_guards erase_knowledge_guards]) assumption+

lemma resolution_success:
  assumes checked: "lp_cut_check_resolution P fuel k l G A guards a gs c m es next anchors"
    and known: "knowledge (set G) guards eta"
    and eq: "lp_isubst (lp_ieval a eta) sigma = lp_ieval (fst (P!c)) rho"
    and ds: "\<And>x. D (sigma x)" and dr: "\<And>x. D (rho x)"
  defines "eta' \<equiv> lp_cut_resolution_env k l eta sigma rho"
  shows "lp_cut_state_eval (LPCGoals next#es) eta' =
    LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) (snd (P!c)) @
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma)) gs)#lp_cut_state_eval es eta"
    and "knowledge (set G \<union> lp_cut_anchor_vars anchors)
      (guards@[LPCHeadGuard a (fst (P!c)) True]) eta'"
proof -
  note native = lp_cut_check_resolution_success[OF erase_resolution_guards[OF checked]
    erase_knowledge_guards[OF known] eq]
  show "lp_cut_state_eval (LPCGoals next#es) eta' =
    LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) (snd (P!c)) @
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma)) gs)#lp_cut_state_eval es eta"
    unfolding eta'_def by (rule native(1))
  have kl: "k\<le>l" using checked by (auto simp: lp_cut_check_resolution_def)
  have old: "knowledge (set G) guards eta'"
    unfolding eta'_def
    by (rule resolution_knowledge_preserved[OF known _ _ kl ds dr])
      (use checked in \<open>auto simp: lp_cut_check_resolution_def\<close>)
  have possible: "cut_domain_head D a (fst (P!c)) eta"
    unfolding cut_domain_head_def
    by (rule exI[of _ sigma], rule exI[of _ rho]) (simp only: ds dr eq simp_thms)
  have short: "lp_cut_short_guard k (LPCHeadGuard a (fst (P!c)) True)"
    using checked by (simp add: lp_cut_check_resolution_def)
  have positive: "guard_holds (LPCHeadGuard a (fst (P!c)) True) eta'"
    using resolution_guard_preserved[OF short kl, of eta sigma rho] possible
    by (simp add: eta'_def)
  show "knowledge (set G \<union> lp_cut_anchor_vars anchors)
      (guards@[LPCHeadGuard a (fst (P!c)) True]) eta'"
    using old positive native(2)
    by (auto simp: knowledge_def lp_cut_knowledge_def eta'_def)
qed

lemma unify_success:
  assumes checked: "lp_cut_check_unify fuel k l G guards a b gs es next"
    and known: "knowledge (set G) guards eta"
    and eq: "lp_isubst (lp_ieval a eta) sigma = lp_isubst (lp_ieval b eta) sigma"
    and ds: "\<And>x. D (sigma x)"
  defines "eta' \<equiv> lp_cut_resolution_env k l eta sigma eta"
  shows "lp_cut_state_eval (LPCGoals next#es) eta' =
      LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma)) gs)#lp_cut_state_eval es eta"
    and "knowledge (set G) (guards@[LPCEqGuard a b True]) eta'"
proof -
  show "lp_cut_state_eval (LPCGoals next#es) eta' =
      LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma)) gs)#lp_cut_state_eval es eta"
    unfolding eta'_def
    by (rule lp_cut_checked_unify_success(1)[OF erase_unify_guards[OF checked] erase_knowledge_guards[OF known] eq])
  have kl: "k\<le>l" using checked by (auto simp: lp_cut_check_unify_def)
  have old: "knowledge (set G) guards eta'"
    unfolding eta'_def
    by (rule resolution_knowledge_preserved[OF known _ _ kl ds knowledge_domain[OF known]])
      (use checked in \<open>auto simp: lp_cut_check_unify_def\<close>)
  have possible: "cut_domain_equality D a b eta"
    unfolding cut_domain_equality_def
    by (rule exI[of _ sigma]) (simp only: ds eq simp_thms)
  have short: "lp_cut_short_guard k (LPCEqGuard a b True)"
    using checked by (auto simp: lp_cut_check_unify_def)
  have positive: "guard_holds (LPCEqGuard a b True) eta'"
    using resolution_guard_preserved[OF short kl, of eta sigma eta] possible
    by (simp add: eta'_def)
  show "knowledge (set G) (guards@[LPCEqGuard a b True]) eta'"
    using old positive by (simp add: knowledge_def)
qed

end
end
