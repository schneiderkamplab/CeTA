theory LP_Cut_Negative_Guards
  imports LP_Cut_Knowledge
begin

text \<open>Failed unification remains impossible after instantiation. Positive
unifiability does not have this property and is deliberately excluded.\<close>

lemma lpc_isubst_comp:
  "lp_isubst (lp_isubst t \<sigma>) \<tau> =
    lp_isubst t (\<lambda>x. lp_isubst (\<sigma> x) \<tau>)"
  by (coinduction arbitrary: t rule: lp_iterm.coinduct_strong)
    (auto simp: list_all2_map1 list_all2_map2 list_all2_conv_all_nth split: lp_iterm.splits)

lemma lpc_negative_head_instantiation:
  fixes a :: "('f,string) lp_iterm" and h :: "('f,string) term"
    and \<sigma> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes "\<not>(\<exists>\<tau>::string \<Rightarrow> ('f,string) lp_iterm. \<exists>\<rho>. lp_isubst a \<tau> = lp_ieval h \<rho>)"
  shows "\<not>(\<exists>\<tau>::string \<Rightarrow> ('f,string) lp_iterm. \<exists>\<rho>. lp_isubst (lp_isubst a \<sigma>) \<tau> = lp_ieval h \<rho>)"
proof
  assume "\<exists>\<tau>::string \<Rightarrow> ('f,string) lp_iterm. \<exists>\<rho>. lp_isubst (lp_isubst a \<sigma>) \<tau> = lp_ieval h \<rho>"
  then obtain \<tau> \<rho> :: "string \<Rightarrow> ('f,string) lp_iterm"
    where eq: "lp_isubst (lp_isubst a \<sigma>) \<tau> = lp_ieval h \<rho>" by blast
  have "\<exists>\<tau>::string \<Rightarrow> ('f,string) lp_iterm. \<exists>\<rho>. lp_isubst a \<tau> = lp_ieval h \<rho>"
    by (rule exI[of _ "\<lambda>x. lp_isubst (\<sigma> x) \<tau>"], rule exI[of _ \<rho>])
      (use eq in \<open>simp add: lpc_isubst_comp\<close>)
  then show False using assms by blast
qed

lemma lpc_negative_equality_instantiation:
  fixes a b :: "('f,string) lp_iterm" and \<sigma> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes "\<not>(\<exists>\<tau>::string \<Rightarrow> ('f,string) lp_iterm. lp_isubst a \<tau> = lp_isubst b \<tau>)"
  shows "\<not>(\<exists>\<tau>::string \<Rightarrow> ('f,string) lp_iterm. lp_isubst (lp_isubst a \<sigma>) \<tau> =
    lp_isubst (lp_isubst b \<sigma>) \<tau>)"
proof
  assume "\<exists>\<tau>::string \<Rightarrow> ('f,string) lp_iterm. lp_isubst (lp_isubst a \<sigma>) \<tau> = lp_isubst (lp_isubst b \<sigma>) \<tau>"
  then obtain \<tau> :: "string \<Rightarrow> ('f,string) lp_iterm"
    where eq: "lp_isubst (lp_isubst a \<sigma>) \<tau> = lp_isubst (lp_isubst b \<sigma>) \<tau>" by blast
  have "\<exists>\<tau>::string \<Rightarrow> ('f,string) lp_iterm. lp_isubst a \<tau> = lp_isubst b \<tau>"
    by (rule exI[of _ "\<lambda>x. lp_isubst (\<sigma> x) \<tau>"])
      (use eq in \<open>simp add: lpc_isubst_comp\<close>)
  then show False using assms by blast
qed

fun lpc_negative_refresh where
  "lpc_negative_refresh k G (LPCHeadGuard a h False) =
    [LPCHeadGuard (a\<cdot>lp_cut_refresh k G) h False]"
| "lpc_negative_refresh k G (LPCEqGuard a b False) =
    [LPCEqGuard (a\<cdot>lp_cut_refresh k G) (b\<cdot>lp_cut_refresh k G) False]"
| "lpc_negative_refresh k G g = []"

definition lpc_negative_guards where
  "lpc_negative_guards k G K = concat (map (lpc_negative_refresh k G) K)"

lemma lpc_negative_refresh_sound:
  assumes short: "lp_cut_short_guard k g" and bounds: "2 * k \<le> l"
    and ground: "\<forall>x\<in>G. lp_seg_ground (\<eta> x)"
    and known: "lp_cut_guard_holds g \<eta>"
  shows "list_all (\<lambda>h. lp_cut_guard_holds h (lp_cut_resolution_env k l \<eta> \<sigma> \<rho>))
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
    show ?thesis using lpc_negative_head_instantiation[of "lp_ieval a \<eta>" h \<sigma>] known
      by (simp add: LPCHeadGuard False active)
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
    show ?thesis using lpc_negative_equality_instantiation[of "lp_ieval a \<eta>" "lp_ieval b \<eta>" \<sigma>] known
      by (simp add: LPCEqGuard False active_a active_b)
  qed
qed

lemma lpc_negative_guards_sound:
  assumes "\<forall>g\<in>set K. lp_cut_short_guard k g" "2 * k \<le> l"
    "lp_cut_knowledge G K \<eta>"
  shows "list_all (\<lambda>g. lp_cut_guard_holds g (lp_cut_resolution_env k l \<eta> \<sigma> \<rho>))
    (lpc_negative_guards k G K)"
  using assms lpc_negative_refresh_sound[of k _ l G \<eta> \<sigma> \<rho>]
  by (auto simp: lpc_negative_guards_def lp_cut_knowledge_def list_all_iff)

end
