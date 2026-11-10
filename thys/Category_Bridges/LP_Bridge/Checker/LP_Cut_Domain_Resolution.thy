theory LP_Cut_Domain_Resolution
  imports Category_LP_Cut_Domain_Bridge.LP_Cut_Domain_Structural
    Category_LP_Cut_Domain_Bridge.LP_Cut_Domain_Instances
begin

text \<open>Normalization and groundness use the existing native proofs.
Only unifiability, negative guards and the valuation domain need a separate
interpretation. Erasing guard annotations for those normalization lemmas does
not erase any obligation from the executable certificate check.\<close>

context cut_runtime_domain
begin

lemma resolution_domain:
  assumes "\<And>x. D (eta x)" "\<And>x. D (sigma x)" "\<And>x. D (rho x)"
  shows "D (lp_cut_resolution_env k l eta sigma rho x)"
  using assms substitute by (auto simp: lp_cut_resolution_env_def)

lemma resolution_guard_preserved:
  "lp_cut_short_guard k g \<Longrightarrow> k\<le>l \<Longrightarrow>
    guard_holds g (lp_cut_resolution_env k l eta sigma rho) = guard_holds g eta"
  by (cases g) (auto simp: cut_domain_head_def cut_domain_equality_def lp_cut_resolution_old)

lemma resolution_knowledge_preserved:
  assumes known: "knowledge G guards eta"
    and short: "\<forall>x\<in>G. length x<k" "\<forall>g\<in>set guards. lp_cut_short_guard k g" "k\<le>l"
    and ds: "\<And>x. D (sigma x)" and dr: "\<And>x. D (rho x)"
  shows "knowledge G guards (lp_cut_resolution_env k l eta sigma rho)"
proof -
  have domain: "\<forall>x. D (lp_cut_resolution_env k l eta sigma rho x)"
    by (intro allI; rule resolution_domain[OF knowledge_domain[OF known] ds dr])
  show ?thesis using known short domain resolution_guard_preserved[of k _ l eta sigma rho]
    by (auto simp: knowledge_def lp_cut_resolution_env_def list_all_iff)
qed

lemma head_negative:
  assumes no: "\<not>(\<exists>tau rho. (\<forall>x. D (tau x)) \<and> (\<forall>x. D (rho x)) \<and>
    lp_isubst a tau = lp_ieval h rho)"
    and ds: "\<And>x. D (sigma x)"
  shows "\<not>(\<exists>tau rho. (\<forall>x. D (tau x)) \<and> (\<forall>x. D (rho x)) \<and>
    lp_isubst (lp_isubst a sigma) tau = lp_ieval h rho)"
proof
  assume "\<exists>tau rho. (\<forall>x. D (tau x)) \<and> (\<forall>x. D (rho x)) \<and>
    lp_isubst (lp_isubst a sigma) tau = lp_ieval h rho"
  then obtain tau rho where dt: "\<And>x. D (tau x)" and dr: "\<forall>x. D (rho x)"
    and eq: "lp_isubst (lp_isubst a sigma) tau = lp_ieval h rho" by blast
  have dc: "\<forall>x. D (lp_isubst (sigma x) tau)"
    by (intro allI; rule substitute[OF ds dt])
  have "\<exists>tau rho. (\<forall>x. D (tau x)) \<and> (\<forall>x. D (rho x)) \<and>
    lp_isubst a tau = lp_ieval h rho"
    by (rule exI[of _ "\<lambda>x. lp_isubst (sigma x) tau"], rule exI[of _ rho])
      (use dc dr eq in \<open>simp add: lpc_isubst_comp\<close>)
  then show False using no by contradiction
qed

lemma equality_negative:
  assumes no: "\<not>(\<exists>tau. (\<forall>x. D (tau x)) \<and> lp_isubst a tau = lp_isubst b tau)"
    and ds: "\<And>x. D (sigma x)"
  shows "\<not>(\<exists>tau. (\<forall>x. D (tau x)) \<and>
    lp_isubst (lp_isubst a sigma) tau = lp_isubst (lp_isubst b sigma) tau)"
proof
  assume "\<exists>tau. (\<forall>x. D (tau x)) \<and>
    lp_isubst (lp_isubst a sigma) tau = lp_isubst (lp_isubst b sigma) tau"
  then obtain tau where dt: "\<And>x. D (tau x)"
    and eq: "lp_isubst (lp_isubst a sigma) tau = lp_isubst (lp_isubst b sigma) tau" by blast
  have dc: "\<forall>x. D (lp_isubst (sigma x) tau)"
    by (intro allI; rule substitute[OF ds dt])
  have "\<exists>tau. (\<forall>x. D (tau x)) \<and> lp_isubst a tau = lp_isubst b tau"
    by (rule exI[of _ "\<lambda>x. lp_isubst (sigma x) tau"])
      (use dc eq in \<open>simp add: lpc_isubst_comp\<close>)
  then show False using no by contradiction
qed

lemma negative_refresh:
  assumes short: "lp_cut_short_guard k g" and bounds: "2 * k \<le> l"
    and ground: "\<forall>x\<in>G. lp_seg_ground (\<eta> x)"
    and known: "guard_holds g \<eta>"
    and ds: "\<And>x. D (\<sigma> x)"
  shows "list_all (\<lambda>h. guard_holds h (lp_cut_resolution_env k l \<eta> \<sigma> \<rho>))
    (lpc_negative_refresh k G g)"
proof (cases g)
  case (LPCHeadGuard a h b)
  show ?thesis
  proof (cases b)
    case True then show ?thesis by (simp add: LPCHeadGuard)
  next
    case False
    have active: "lp_ieval (a\<cdot>lp_cut_refresh k G) (lp_cut_resolution_env k l \<eta> \<sigma> \<rho>) = lp_isubst (lp_ieval a \<eta>) \<sigma>"
      by (rule lp_cut_resolution_active[OF _ bounds ground]) (use short LPCHeadGuard in simp)
    show ?thesis using head_negative[OF _ ds, where a="lp_ieval a \<eta>" and h=h] known
      by (simp add: cut_domain_head_def LPCHeadGuard False active)
  qed
next
  case (LPCEqGuard a b c)
  show ?thesis
  proof (cases c)
    case True then show ?thesis by (simp add: LPCEqGuard)
  next
    case False
    have active_a: "lp_ieval (a\<cdot>lp_cut_refresh k G) (lp_cut_resolution_env k l \<eta> \<sigma> \<rho>) = lp_isubst (lp_ieval a \<eta>) \<sigma>"
      by (rule lp_cut_resolution_active[OF _ bounds ground]) (use short LPCEqGuard in auto)
    have active_b: "lp_ieval (b\<cdot>lp_cut_refresh k G) (lp_cut_resolution_env k l \<eta> \<sigma> \<rho>) = lp_isubst (lp_ieval b \<eta>) \<sigma>"
      by (rule lp_cut_resolution_active[OF _ bounds ground]) (use short LPCEqGuard in auto)
    show ?thesis using equality_negative[OF _ ds, where a="lp_ieval a \<eta>" and b="lp_ieval b \<eta>"] known
      by (simp add: cut_domain_equality_def LPCEqGuard False active_a active_b)
  qed
qed

lemma negative_guards:
  assumes "\<forall>g\<in>set K. lp_cut_short_guard k g" "2 * k \<le> l"
    "knowledge G K \<eta>" "\<And>x. D (\<sigma> x)"
  shows "list_all (\<lambda>g. guard_holds g (lp_cut_resolution_env k l \<eta> \<sigma> \<rho>))
    (lpc_negative_guards k G K)"
  using assms negative_refresh[where k=k and l=l and G=G and \<eta>=\<eta> and \<sigma>=\<sigma> and \<rho>=\<rho>]
  by (auto simp: lpc_negative_guards_def knowledge_def list_all_iff)

end
end
