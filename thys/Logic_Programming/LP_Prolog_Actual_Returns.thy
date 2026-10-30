theory LP_Prolog_Actual_Returns
 imports LP_Prolog_Domain_Composition LP_Prolog_Numeric_Observations
begin

abbreviation lpp_actual_return where
  "lpp_actual_return P ss eta \<equiv> lp_actual_answer
    (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) ss eta"

lemma lpp_domain_answer_substitution_property:
  assumes stable: "\<And>eta sigma. F eta \<Longrightarrow> F (\<lambda>x. lp_isubst (eta x) sigma)"
    and step: "lpp_domain_answers P B U D ss event us"
    and known: "list_all (\<lambda>e. F (snd e)) ss"
  shows "list_all (\<lambda>e. F (snd e)) us \<and> (\<forall>eta. event=Some eta \<longrightarrow> F eta)"
proof (cases "lpp_answer_transition P B U ss event us")
  case True
  show ?thesis by (rule lpp_answer_substitution_property[OF stable True known])
next
  case False
  show ?thesis using step False known by (simp add: lpp_domain_answers_def)
qed

lemma lpp_actual_return_substitution_property:
  assumes stable: "\<And>eta sigma. F eta \<Longrightarrow> F (\<lambda>x. lp_isubst (eta x) sigma)"
    and actual: "lp_actual_answer (lpp_domain_answers P B U D) ss eta"
    and known: "list_all (\<lambda>e. F (snd e)) ss"
  shows "F eta"
proof -
  obtain us tail where path: "(ss,us)\<in>(lp_answer_steps (lpp_domain_answers P B U D))\<^sup>*"
    and event: "lpp_domain_answers P B U D us (Some eta) tail"
    using actual by (auto simp: lp_actual_answer_def)
  have preserved: "list_all (\<lambda>e. F (snd e)) us"
    using path
  proof (induct rule: rtrancl_induct)
    case base show ?case by (rule known)
  next
    case (step ys zs)
    obtain ev where local: "lpp_domain_answers P B U D ys ev zs"
      using step.hyps(2) by (auto simp: lp_answer_steps_def)
    show ?case using lpp_domain_answer_substitution_property[where F=F, OF stable local step.hyps(3)] by blast
  qed
  show ?thesis using lpp_domain_answer_substitution_property[where F=F, OF stable event preserved] by simp
qed

lemma lpp_actual_return_preserves_finite_value:
  assumes finite: "lp_seg_ground value"
    and actual: "lp_actual_answer (lpp_domain_answers P B U D) ss eta"
    and initialized: "list_all (\<lambda>e. snd e slot = value) ss"
  shows "eta slot = value"
  by (rule lpp_actual_return_substitution_property[OF _ actual initialized])
    (use finite in \<open>auto simp: lp_seg_ground_subst\<close>)

text \<open>A finite observed spine permits arbitrary, including rational,
heads. Its inductive witness counts source constructors, never heap encoding
nodes. No finite-spine fact is inferred from a finite representation.\<close>
inductive lpp_finite_spine :: "'f \<Rightarrow> 'f \<Rightarrow> ('f,'v) lp_iterm \<Rightarrow> nat \<Rightarrow> bool"
  for cons nil where
  empty: "lpp_finite_spine cons nil (LPIFun nil []) 0"
| cell: "lpp_finite_spine cons nil tail n \<Longrightarrow>
    lpp_finite_spine cons nil (LPIFun cons [head,tail]) (Suc n)"

lemma lpp_finite_spine_subst:
  assumes spine: "lpp_finite_spine cons nil t n"
  shows "lpp_finite_spine cons nil (lp_isubst t sigma) n"
  using spine by induct (auto intro: lpp_finite_spine.intros)

lemma lpp_actual_return_preserves_spine:
  assumes actual: "lp_actual_answer (lpp_domain_answers P B U D) ss eta"
    and initialized: "list_all (\<lambda>e. lpp_finite_spine cons nil (snd e slot) n) ss"
  shows "lpp_finite_spine cons nil (eta slot) n"
  by (rule lpp_actual_return_substitution_property[OF _ actual initialized])
    (auto intro: lpp_finite_spine_subst)

lemma lpp_cyclic_spine_not_finite:
  assumes cycle: "t = LPIFun cons [head,t]"
  shows "\<not>lpp_finite_spine cons nil t n"
proof
  assume finite: "lpp_finite_spine cons nil t n"
  have impossible: "lpp_finite_spine cons nil u k \<Longrightarrow>
      u = LPIFun cons [h,u] \<Longrightarrow> False" for k u h
  proof (induction k arbitrary: u h)
    case 0
    then have "u = LPIFun nil []" by (cases rule: lpp_finite_spine.cases) auto
    then show False using 0 by simp
  next
    case (Suc k)
    from Suc.prems(1) obtain x tail where shape: "u = LPIFun cons [x,tail]"
      and spine: "lpp_finite_spine cons nil tail k"
      by (cases rule: lpp_finite_spine.cases) auto
    have eq: "LPIFun cons [x,tail] = LPIFun cons [h,u]"
      using shape Suc.prems(2) by metis
    have "tail=u" using eq by simp
    then show False using Suc.IH[OF spine] Suc.prems(2) by blast
  qed
  show False by (rule impossible[OF finite cycle])
qed

end
