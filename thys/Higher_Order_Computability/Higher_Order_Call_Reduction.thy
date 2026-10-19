theory Higher_Order_Call_Reduction
  imports Higher_Order_Full_Application Higher_Order_Application_Descent
begin

lemma ho_apply_terms_head [simp]:
  "ho_application_head (ho_apply_terms f xs)=ho_application_head f"
  by (induction xs arbitrary: f) auto

lemma ho_apply_terms_spine [simp]:
  "ho_spine_length (ho_apply_terms f xs)=length xs+ho_spine_length f"
  by (induction xs arbitrary: f) auto

definition ho_root_step where
  "ho_root_step S V R B t u \<longleftrightarrow>
    (\<exists>G l r s. (G,l,r)\<in>set R \<and> ho_rule_welltyped S (G,l,r) \<and>
      ho_typed_subst S V B G s \<and> ho_instantiate s 0 l=Some t \<and> ho_instantiate s 0 r=Some u)"

definition ho_arguments_step where
  "ho_arguments_step S V R B xs ys \<longleftrightarrow>
    (\<exists>us v vs w. xs=us@v#vs \<and> ys=us@w#vs \<and> ho_step S V R B v w)"

context ho_source_neutral_reducibility
begin

lemma root_call_arity:
  assumes arities: "\<And>G l r c. (G,l,r)\<in>set R \<Longrightarrow>
      ho_application_head (ho_erase_pattern l)=HConst c \<Longrightarrow>
      ho_spine_length (ho_erase_pattern l)=a c"
    and root: "ho_root_step S V R B (ho_apply_terms (HConst c) xs) u"
  shows "length xs=a c"
proof -
  obtain G l r s where member: "(G,l,r)\<in>set R"
    and inst: "ho_instantiate s 0 l=Some (ho_apply_terms (HConst c) xs)"
    using root unfolding ho_root_step_def by blast
  have head: "ho_application_head (ho_erase_pattern l)=HConst c"
    using rule_instance_head_spine(1)[OF member inst] by simp
  show ?thesis using rule_instance_head_spine(2)[OF member inst] arities[OF member head] by simp
qed

theorem source_call_reduct:
  assumes arities: "\<And>G l r c. (G,l,r)\<in>set R \<Longrightarrow>
      ho_application_head (ho_erase_pattern l)=HConst c \<Longrightarrow>
      ho_spine_length (ho_erase_pattern l)=a c"
    and bound: "length xs\<le>a c"
    and step: "ho_step S V R B (ho_apply_terms (HConst c) xs) u"
  shows "ho_root_step S V R B (ho_apply_terms (HConst c) xs) u \<or>
    (\<exists>ys. ho_arguments_step S V R B xs ys \<and> u=ho_apply_terms (HConst c) ys)"
  using bound step
proof (induction xs arbitrary: u rule: rev_induct)
  case Nil
  have st: "ho_step S V R B (HConst c) u" using Nil.prems(2) by simp
  have "ho_root_step S V R B (HConst c) u"
    using st by (cases rule: ho_step.cases) (auto simp: ho_root_step_def)
  then show ?case by simp
next
  case (snoc x xs)
  let ?f = "ho_apply_terms (HConst c) xs"
  have noabs: "?f\<noteq>HAbs A t" for A t
  proof
    assume eq: "?f=HAbs A t"
    have "ho_application_head ?f=HConst c" by simp
    then show False by (simp add: eq)
  qed
  have st: "ho_step S V R B (HApp ?f x) u" using snoc.prems(2) by simp
  have split: "ho_root_step S V R B (HApp ?f x) u \<or>
      (\<exists>g. ho_step S V R B ?f g \<and> u=HApp g x) \<or>
      (\<exists>y. ho_step S V R B x y \<and> u=HApp ?f y)"
    using st by (cases rule: ho_step.cases) (auto simp: ho_root_step_def noabs)
  from split show ?case
  proof (elim disjE exE conjE)
    assume "ho_root_step S V R B (HApp ?f x) u"
    then show ?thesis by simp
  next
    fix g assume fg: "ho_step S V R B ?f g" and eq: "u=HApp g x"
    have len: "length xs\<le>a c" using snoc.prems(1) by simp
    have notroot: "\<not>ho_root_step S V R B ?f g"
      using root_call_arity[OF arities] snoc.prems(1) by fastforce
    obtain ys where args: "ho_arguments_step S V R B xs ys" and g: "g=ho_apply_terms (HConst c) ys"
      using snoc.IH[OF len fg] notroot by blast
    have "ho_arguments_step S V R B (xs@[x]) (ys@[x])"
      using args unfolding ho_arguments_step_def by fastforce
    then show ?thesis using eq g by auto
  next
    fix y assume xy: "ho_step S V R B x y" and eq: "u=HApp ?f y"
    have "ho_arguments_step S V R B (xs@[x]) (xs@[y])"
      unfolding ho_arguments_step_def using xy by blast
    then show ?thesis using eq by auto
  qed
qed

end

end
