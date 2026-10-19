theory Higher_Order_Saturated_Neutral
  imports Higher_Order_Source_Substitution
begin

fun ho_spine_length where
  "ho_spine_length (HApp f x) = Suc (ho_spine_length f)"
| "ho_spine_length t = 0"

lemma ho_constant_spine_substitution:
  "ho_application_head t=HConst c \<Longrightarrow>
    ho_spine_length (ho_subst s d t)=ho_spine_length t"
  by (induction t arbitrary: d) auto

definition ho_saturated_neutral where
  "ho_saturated_neutral R t = ((\<forall>A b. t\<noteq>HAbs A b) \<and>
    (\<forall>G l r. (G,l,r)\<in>set R \<longrightarrow>
      ho_application_head (ho_erase_pattern l)=ho_application_head t \<longrightarrow>
      ho_spine_length (ho_erase_pattern l)\<le>ho_spine_length t))"

context ho_source_neutral_reducibility
begin

lemma rule_instance_head_spine:
  assumes member: "(G,l,r)\<in>set R" and inst: "ho_instantiate s 0 l=Some t"
  shows "ho_application_head t=ho_application_head (ho_erase_pattern l)"
    and "ho_spine_length t=ho_spine_length (ho_erase_pattern l)"
proof -
  have zl: "ho_zero_arity_pattern l" using zero member unfolding ho_zero_arity_rules_def by auto
  have t: "t=ho_subst s 0 (ho_erase_pattern l)"
    using inst ho_zero_arity_instantiate[OF zl, of s 0] by simp
  obtain c where head: "ho_application_head (ho_erase_pattern l)=HConst c"
    using constant_heads[OF member] by blast
  show "ho_application_head t=ho_application_head (ho_erase_pattern l)"
    unfolding t using ho_constant_head_substitution[OF head, of s 0] head by simp
  show "ho_spine_length t=ho_spine_length (ho_erase_pattern l)"
    unfolding t by (rule ho_constant_spine_substitution[OF head])
qed

lemma saturated_neutral_application:
  "ho_saturated_neutral R f \<Longrightarrow> ho_saturated_neutral R (HApp f x)"
  by (auto simp: ho_saturated_neutral_def; meson le_SucI)

lemma saturated_no_root:
  assumes neutral: "ho_saturated_neutral R f" and member: "(G,l,r)\<in>set R"
    and inst: "ho_instantiate s 0 l=Some (HApp f x)"
  shows False
proof -
  have head: "ho_application_head (ho_erase_pattern l)=ho_application_head f"
    using rule_instance_head_spine(1)[OF member inst] by simp
  have length: "ho_spine_length (ho_erase_pattern l)=Suc (ho_spine_length f)"
    using rule_instance_head_spine(2)[OF member inst] by simp
  have "ho_spine_length (ho_erase_pattern l)\<le>ho_spine_length f"
    using neutral member head unfolding ho_saturated_neutral_def by blast
  then show False using length by simp
qed

lemma saturated_neutral_reduct:
  assumes neutral: "ho_saturated_neutral R f" and step: "ho_step S V R B (HApp f x) u"
  shows "(\<exists>g. ho_step S V R B f g \<and> u=HApp g x) \<or>
    (\<exists>y. ho_step S V R B x y \<and> u=HApp f y)"
  using step neutral
  by (cases rule: ho_step.cases)
     (auto simp: ho_saturated_neutral_def dest: saturated_no_root[OF neutral])

sublocale saturated: ho_neutral_reducibility "ho_step S V R B" HApp
  "\<lambda>A t. ho_typeof S V B t=Some A" "ho_saturated_neutral R"
proof unfold_locales
  fix f x assume "ho_saturated_neutral R f"
  then show "ho_saturated_neutral R (HApp f x)" by (rule saturated_neutral_application)
next
  fix f x u assume nf: "ho_saturated_neutral R f" and st: "ho_step S V R B (HApp f x) u"
  show "(\<exists>g. ho_step S V R B f g \<and> u=HApp g x) \<or>
    (\<exists>y. ho_step S V R B x y \<and> u=HApp f y)"
    by (rule saturated_neutral_reduct[OF nf st])
qed

lemma constructor_computable:
  assumes ty: "ho_lookup S c=Some A"
    and constructor: "\<And>G l r. (G,l,r)\<in>set R \<Longrightarrow>
      ho_application_head (ho_erase_pattern l)\<noteq>HConst c"
  shows "source.computable A (HConst c)"
proof (rule saturated.neutral_computable)
  show "ho_typeof S V B (HConst c)=Some A" using ty by simp
  show "ho_saturated_neutral R (HConst c)" using constructor by (auto simp: ho_saturated_neutral_def)
  fix u assume "ho_step S V R B (HConst c) u"
  moreover have no_inst: False if member: "(G,l,r)\<in>set R"
    and inst: "ho_instantiate s 0 l=Some (HConst c)" for G l r s
    using rule_instance_head_spine(1)[OF member inst] constructor[OF member] by simp
  ultimately have False by (cases rule: ho_step.cases) (auto dest: no_inst)
  then show "source.computable A u" by simp
qed

end

end
