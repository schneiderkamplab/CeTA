theory LP_Cut_Answer_Knowledge
  imports LP_Cut_Answer_Control
begin

fun lpc_answer_negative_guard where
  "lpc_answer_negative_guard (LPCHeadGuard a h b) = (\<not>b)"
| "lpc_answer_negative_guard (LPCEqGuard a c b) = (\<not>b)"

lemma lpc_answer_negative_guard_subst:
  fixes \<eta> \<sigma> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes negative: "lpc_answer_negative_guard g"
    and known: "lp_cut_guard_holds g \<eta>"
  shows "lp_cut_guard_holds g (\<lambda>x. lp_isubst (\<eta> x) \<sigma>)"
proof (cases g)
  case (LPCHeadGuard a h b)
  have b: "b=False" using negative LPCHeadGuard by simp
  have absent: "\<not>(\<exists>\<tau>::string\<Rightarrow>('f,string) lp_iterm. \<exists>\<rho>.
    lp_isubst (lp_ieval a \<eta>) \<tau> = lp_ieval h \<rho>)"
    using known by (simp add: LPCHeadGuard b)
  show ?thesis
  proof (unfold LPCHeadGuard b, simp only: lp_cut_guard_holds.simps, intro iffI)
    assume "\<exists>\<tau>::string\<Rightarrow>('f,string) lp_iterm. \<exists>\<rho>.
      lp_isubst (lp_ieval a (\<lambda>x. lp_isubst (\<eta> x) \<sigma>)) \<tau> = lp_ieval h \<rho>"
    then obtain \<tau> \<rho> :: "string \<Rightarrow> ('f,string) lp_iterm" where raw:
      "lp_isubst (lp_ieval a (\<lambda>x. lp_isubst (\<eta> x) \<sigma>)) \<tau> = lp_ieval h \<rho>"
      by blast
    have eq:
      "lp_isubst (lp_ieval a \<eta>) (\<lambda>x. lp_isubst (\<sigma> x) \<tau>) = lp_ieval h \<rho>"
      using raw by (simp add: lp_ieval_subst lp_seg_isubst_comp)
    show False using absent eq by blast
  qed simp
next
  case (LPCEqGuard a c b)
  have b: "b=False" using negative LPCEqGuard by simp
  have absent: "\<not>(\<exists>\<tau>::string\<Rightarrow>('f,string) lp_iterm.
    lp_isubst (lp_ieval a \<eta>) \<tau> = lp_isubst (lp_ieval c \<eta>) \<tau>)"
    using known by (simp add: LPCEqGuard b)
  show ?thesis
  proof (unfold LPCEqGuard b, simp only: lp_cut_guard_holds.simps, intro iffI)
    assume "\<exists>\<tau>::string\<Rightarrow>('f,string) lp_iterm.
      lp_isubst (lp_ieval a (\<lambda>x. lp_isubst (\<eta> x) \<sigma>)) \<tau> =
      lp_isubst (lp_ieval c (\<lambda>x. lp_isubst (\<eta> x) \<sigma>)) \<tau>"
    then obtain \<tau> :: "string \<Rightarrow> ('f,string) lp_iterm" where raw:
      "lp_isubst (lp_ieval a (\<lambda>x. lp_isubst (\<eta> x) \<sigma>)) \<tau> =
       lp_isubst (lp_ieval c (\<lambda>x. lp_isubst (\<eta> x) \<sigma>)) \<tau>"
      by blast
    have eq:
      "lp_isubst (lp_ieval a \<eta>) (\<lambda>x. lp_isubst (\<sigma> x) \<tau>) =
       lp_isubst (lp_ieval c \<eta>) (\<lambda>x. lp_isubst (\<sigma> x) \<tau>)"
      using raw by (simp add: lp_ieval_subst lp_seg_isubst_comp)
    show False using absent eq by blast
  qed simp
qed

theorem lpc_answer_knowledge_preserved:
  fixes \<eta> \<rho> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes path: "((gs,\<eta>),(hs,\<rho>))\<in>(lp_seg_answer_step Q)\<^sup>*"
    and known: "lp_cut_knowledge G K \<eta>"
    and grounds: "G' \<subseteq> G"
    and guards: "set K' \<subseteq> set (filter lpc_answer_negative_guard K)"
  shows "lp_cut_knowledge G' K' \<rho>"
proof -
  obtain \<sigma> where env: "\<rho>=(\<lambda>x. lp_isubst (\<eta> x) \<sigma>)"
    using lp_seg_answer_steps_environment[OF path] by blast
  have ground: "lp_seg_ground (\<rho> x)" if "x\<in>G'" for x
    using lp_seg_answer_steps_preserve_ground[OF path] known grounds that
    by (auto simp: lp_cut_knowledge_def)
  have guard: "lp_cut_guard_holds g \<rho>" if "g\<in>set K'" for g
    using guards that known lpc_answer_negative_guard_subst[of g \<eta> \<sigma>]
    by (auto simp: env lp_cut_knowledge_def list_all_iff)
  show ?thesis using ground guard by (simp add: lp_cut_knowledge_def list_all_iff)
qed

end
