theory Higher_Order_Finite_Branching
  imports Higher_Order_Delegation_Foundation
begin

fun ho_free_support where
  "ho_free_support (HFree n) = {n}"
| "ho_free_support (HApp f x) = ho_free_support f \<union> ho_free_support x"
| "ho_free_support (HAbs A t) = ho_free_support t"
| "ho_free_support t = {}"

lemma ho_lift_injective:
  "ho_lift d k t=ho_lift d k u \<Longrightarrow> t=u"
  by (induction t arbitrary: u k; case_tac u; auto; arith)

lemma ho_subst_support_agreement:
  "(\<And>n. n\<in>ho_free_support t \<Longrightarrow> s n=q n) \<Longrightarrow>
    ho_subst s d t=ho_subst q d t"
  by (induction t arbitrary: d) auto

lemma ho_subst_support_recovery:
  "ho_subst s d t=ho_subst q d t \<Longrightarrow>
    n\<in>ho_free_support t \<Longrightarrow> s n=q n"
  by (induction t arbitrary: d) (auto dest: ho_lift_injective)

definition ho_finitely_matching_rules where
  "ho_finitely_matching_rules R \<longleftrightarrow>
    (\<forall>G l r. (G,l,r)\<in>set R \<longrightarrow>
      ho_zero_arity_pattern l \<and> ho_zero_arity_pattern r \<and>
      ho_free_support (ho_erase_pattern r) \<subseteq> ho_free_support (ho_erase_pattern l))"

lemma ho_zero_arity_unique_reduct:
  assumes zl: "ho_zero_arity_pattern l" and zr: "ho_zero_arity_pattern r"
    and support: "ho_free_support (ho_erase_pattern r) \<subseteq> ho_free_support (ho_erase_pattern l)"
    and l1: "ho_instantiate s 0 l=Some t" and l2: "ho_instantiate q 0 l=Some t"
    and r1: "ho_instantiate s 0 r=Some u" and r2: "ho_instantiate q 0 r=Some v"
  shows "u=v"
proof -
  have lhs: "ho_subst s 0 (ho_erase_pattern l)=ho_subst q 0 (ho_erase_pattern l)"
    using l1 l2 ho_zero_arity_instantiate[OF zl] by simp
  have rhs: "ho_subst s 0 (ho_erase_pattern r)=ho_subst q 0 (ho_erase_pattern r)"
    by (rule ho_subst_support_agreement)
       (use support ho_subst_support_recovery[OF lhs] in blast)
  show ?thesis using r1 r2 rhs ho_zero_arity_instantiate[OF zr] by simp
qed

lemma ho_finite_rule_instances:
  assumes zl: "ho_zero_arity_pattern l" and zr: "ho_zero_arity_pattern r"
    and support: "ho_free_support (ho_erase_pattern r) \<subseteq> ho_free_support (ho_erase_pattern l)"
  shows "finite {u. \<exists>s. ho_instantiate s 0 l=Some t \<and> ho_instantiate s 0 r=Some u}"
proof (cases "\<exists>s u. ho_instantiate s 0 l=Some t \<and> ho_instantiate s 0 r=Some u")
  case False
  have empty: "{u. \<exists>s. ho_instantiate s 0 l=Some t \<and> ho_instantiate s 0 r=Some u} = {}"
    using False by blast
  show ?thesis by (subst empty) simp
next
  case True
  then obtain s u where ls: "ho_instantiate s 0 l=Some t"
    and rs: "ho_instantiate s 0 r=Some u" by blast
  have subset: "{v. \<exists>q. ho_instantiate q 0 l=Some t \<and> ho_instantiate q 0 r=Some v} \<subseteq> {u}"
    using ho_zero_arity_unique_reduct[OF zl zr support ls _ rs] by blast
  show ?thesis by (rule finite_subset[OF subset]) simp
qed

lemma ho_finite_root_reducts:
  assumes rules: "ho_finitely_matching_rules R"
  shows "finite {u. ho_root_step S V R B t u}"
proof -
  let ?all = "\<Union>(G,l,r)\<in>set R. {u. \<exists>s. ho_instantiate s 0 l=Some t \<and> ho_instantiate s 0 r=Some u}"
  have fin: "finite ?all"
    by (rule finite_UN_I) (use rules ho_finite_rule_instances in \<open>auto simp: ho_finitely_matching_rules_def\<close>)
  have sub: "{u. ho_root_step S V R B t u} \<subseteq> ?all"
    by (auto simp: ho_root_step_def)
  show ?thesis by (rule finite_subset[OF sub fin])
qed

fun ho_context_reducts where
  "ho_context_reducts S V R B (HApp f x) =
    (HApp f ` {y. ho_step S V R B x y}) \<union>
    ((\<lambda>g. HApp g x) ` {g. ho_step S V R B f g}) \<union>
    (case f of HAbs A t \<Rightarrow> {ho_beta_subst x 0 t} | _ \<Rightarrow> {})"
| "ho_context_reducts S V R B (HAbs A t) = HAbs A ` {u. ho_step S V R (A#B) t u}"
| "ho_context_reducts S V R B t = {}"

lemma ho_step_root_or_context:
  "ho_step S V R B t u \<Longrightarrow>
    ho_root_step S V R B t u \<or> u\<in>ho_context_reducts S V R B t"
  by (cases rule: ho_step.cases) (auto simp: ho_root_step_def)

theorem ho_zero_arity_finite_branching:
  assumes rules: "ho_finitely_matching_rules R"
  shows "finite {u. ho_step S V R B t u}"
proof (induction t arbitrary: B)
  case (HBound n)
  then show ?case using ho_step_root_or_context ho_finite_root_reducts[OF rules]
    by (metis ho_context_reducts.simps(3) Un_empty_right finite_subset subsetI mem_Collect_eq empty_iff)
next
  case (HFree n)
  then show ?case using ho_step_root_or_context ho_finite_root_reducts[OF rules]
    by (metis ho_context_reducts.simps(4) Un_empty_right finite_subset subsetI mem_Collect_eq empty_iff)
next
  case (HConst n)
  then show ?case using ho_step_root_or_context ho_finite_root_reducts[OF rules]
    by (metis ho_context_reducts.simps(5) Un_empty_right finite_subset subsetI mem_Collect_eq empty_iff)
next
  case (HApp f x)
  have fin: "finite ({u. ho_root_step S V R B (HApp f x) u} \<union> ho_context_reducts S V R B (HApp f x))"
    using ho_finite_root_reducts[OF rules] HApp.IH by (simp split: ho_term.splits)
  show ?case by (rule finite_subset[OF _ fin]) (use ho_step_root_or_context in blast)
next
  case (HAbs A t)
  have fin: "finite ({u. ho_root_step S V R B (HAbs A t) u} \<union> ho_context_reducts S V R B (HAbs A t))"
    using ho_finite_root_reducts[OF rules] HAbs.IH by simp
  show ?case by (rule finite_subset[OF _ fin]) (use ho_step_root_or_context in blast)
qed

corollary ho_zero_arity_finite_reducts:
  "ho_finitely_matching_rules R \<Longrightarrow>
    Wellfounded.accp (\<lambda>u t. ho_step S V R B t u) t \<Longrightarrow>
    finite {u. (ho_step S V R B)\<^sup>*\<^sup>* t u}"
  by (rule ho_finite_SN_reducts) (assumption, rule ho_zero_arity_finite_branching, assumption)

end
