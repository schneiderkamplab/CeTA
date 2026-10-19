theory Higher_Order_Source_Computability
  imports Higher_Order_Computability
begin

text \<open>The basic reducibility locale applies directly to the original
typed union-beta rewrite relation for zero-arity rules. The separate neutral
and beta-expansion locales still require their operational side conditions;
they are not asserted here for arbitrary rules or binder contexts.\<close>

locale ho_source_reducibility =
  fixes S V :: "ho_type list" and R :: "ho_rule list" and B :: "ho_type list"
  assumes zero: "ho_zero_arity_rules R"
begin

sublocale source: ho_reducibility "ho_step S V R B" HApp "\<lambda>A t. ho_typeof S V B t=Some A"
proof
  fix A t u assume ty: "ho_typeof S V B t=Some A" and step: "ho_step S V R B t u"
  show "ho_typeof S V B u=Some A" by (rule ho_zero_arity_step_type[OF step zero ty])
next
  fix A C f x assume "ho_typeof S V B f=Some (HArrow A C)" and "ho_typeof S V B x=Some A"
  then show "ho_typeof S V B (HApp f x)=Some C" by simp
next
  fix f g x assume "ho_step S V R B f g"
  then show "ho_step S V R B (HApp f x) (HApp g x)" by (rule ho_step.app_left)
next
  fix x y f assume "ho_step S V R B x y"
  then show "ho_step S V R B (HApp f x) (HApp f y)" by (rule ho_step.app_right)
qed

theorem source_computability_termination:
  assumes empty_context: "B=[]"
    and all_terms: "\<And>t. ho_typeof S V B t=Some A \<Longrightarrow> source.computable A t"
  shows "wf ((ho_relation S V R A)\<inverse>)"
proof -
  have wf_source: "wf {(u,t). ho_typeof S V B t=Some A \<and> ho_step S V R B t u}"
    using source.computability_implies_termination[OF all_terms] by (simp add: wfp_def)
  have subset: "(ho_relation S V R A)\<inverse> \<subseteq>
    {(u,t). ho_typeof S V B t=Some A \<and> ho_step S V R B t u}"
    by (auto simp: ho_relation_def empty_context)
  show ?thesis by (rule wf_subset[OF wf_source subset])
qed

end

fun ho_application_head where
  "ho_application_head (HApp f x) = ho_application_head f"
| "ho_application_head t = t"

definition ho_source_neutral where
  "ho_source_neutral t = ((\<forall>c. ho_application_head t \<noteq> HConst c) \<and>
    (\<forall>A b. t \<noteq> HAbs A b))"

lemma ho_constant_head_substitution:
  "ho_application_head t=HConst c \<Longrightarrow>
    ho_application_head (ho_subst s d t)=HConst c"
  by (induction t arbitrary: d) auto

locale ho_source_neutral_reducibility = ho_source_reducibility S V R B
  for S V :: "ho_type list" and R :: "ho_rule list" and B :: "ho_type list" +
  assumes constant_heads: "(G,l,r)\<in>set R \<Longrightarrow>
    \<exists>c. ho_application_head (ho_erase_pattern l)=HConst c"
begin

lemma rule_instance_constant_head:
  assumes member: "(G,l,r)\<in>set R" and inst: "ho_instantiate s 0 l=Some t"
  shows "\<exists>c. ho_application_head t=HConst c"
proof -
  have zl: "ho_zero_arity_pattern l" using zero member unfolding ho_zero_arity_rules_def by auto
  have t: "t=ho_subst s 0 (ho_erase_pattern l)"
    using inst ho_zero_arity_instantiate[OF zl, of s 0] by simp
  obtain c where head: "ho_application_head (ho_erase_pattern l)=HConst c"
    using constant_heads[OF member] by blast
  show ?thesis unfolding t using ho_constant_head_substitution[OF head, of s 0] by blast
qed

lemma neutral_source_application:
  "ho_source_neutral f \<Longrightarrow> ho_source_neutral (HApp f x)"
  by (auto simp: ho_source_neutral_def)

lemma neutral_source_reduct:
  assumes neutral: "ho_source_neutral f" and step: "ho_step S V R B (HApp f x) u"
  shows "(\<exists>g. ho_step S V R B f g \<and> u=HApp g x) \<or>
    (\<exists>y. ho_step S V R B x y \<and> u=HApp f y)"
  using step neutral
  by (cases rule: ho_step.cases)
     (auto simp: ho_source_neutral_def dest: rule_instance_constant_head)

sublocale source_neutral: ho_neutral_reducibility "ho_step S V R B" HApp
  "\<lambda>A t. ho_typeof S V B t=Some A" ho_source_neutral
proof unfold_locales
  fix f x assume "ho_source_neutral f"
  then show "ho_source_neutral (HApp f x)" by (rule neutral_source_application)
next
  fix f x u assume nf: "ho_source_neutral f" and st: "ho_step S V R B (HApp f x) u"
  show "(\<exists>g. ho_step S V R B f g \<and> u=HApp g x) \<or>
    (\<exists>y. ho_step S V R B x y \<and> u=HApp f y)"
    by (rule neutral_source_reduct[OF nf st])
qed

lemma source_free_irreducible: "\<not> ho_step S V R B (HFree n) u"
proof
  assume "ho_step S V R B (HFree n) u"
  then show False by (cases rule: ho_step.cases) (auto dest: rule_instance_constant_head)
qed

lemma source_bound_irreducible: "\<not> ho_step S V R B (HBound n) u"
proof
  assume "ho_step S V R B (HBound n) u"
  then show False by (cases rule: ho_step.cases) (auto dest: rule_instance_constant_head)
qed

lemma source_free_computable:
  "ho_lookup V n=Some A \<Longrightarrow> source.computable A (HFree n)"
  by (rule source_neutral.neutral_computable)
     (auto simp: ho_source_neutral_def source_free_irreducible)

lemma source_bound_computable:
  "ho_lookup B n=Some A \<Longrightarrow> source.computable A (HBound n)"
  by (rule source_neutral.neutral_computable)
     (auto simp: ho_source_neutral_def source_bound_irreducible)

end

end
