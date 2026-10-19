theory Higher_Order_Candidate_Delegation
  imports Higher_Order_Context_Property
begin

lemma ho_spine_argument_typed:
  "ho_typeof S V B t=Some T \<Longrightarrow> x\<in>set (ho_spine_arguments t) \<Longrightarrow>
    \<exists>U. ho_typeof S V B x=Some U"
  by (induction t arbitrary: T)
     (auto split: option.splits ho_type.splits if_splits)

lemma ho_apply_terms_type_inverse:
  "ho_typeof S V B (ho_apply_terms f xs)=Some T \<Longrightarrow>
    \<exists>U. ho_typeof S V B f=Some U \<and> length xs\<le>length (ho_argument_types U) \<and>
      T=ho_drop_type (length xs) U \<and>
      list_all2 (\<lambda>A x. ho_typeof S V B x=Some A) (take (length xs) (ho_argument_types U)) xs"
proof (induction xs arbitrary: f T)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  have ty: "ho_typeof S V B (ho_apply_terms (HApp f x) xs)=Some T"
    using Cons.prems by simp
  obtain U where app: "ho_typeof S V B (HApp f x)=Some U"
    and len: "length xs\<le>length (ho_argument_types U)"
    and result: "T=ho_drop_type (length xs) U"
    and args: "list_all2 (\<lambda>A x. ho_typeof S V B x=Some A) (take (length xs) (ho_argument_types U)) xs"
    using Cons.IH[OF ty] by blast
  obtain A where ft: "ho_typeof S V B f=Some (HArrow A U)"
    and xt: "ho_typeof S V B x=Some A"
    using app by (auto split: option.splits ho_type.splits if_splits)
  show ?case by (rule exI[of _ "HArrow A U"])
    (use ft xt len result args in simp)
qed

lemma ho_fo_signature_accessible:
  assumes signature: "\<And>c U. c\<in>F \<Longrightarrow> ho_lookup S c=Some U \<Longrightarrow>
      arity c=length (ho_argument_types U) \<and>
      list_all (ho_positive_type rank (rank (ho_result_sort U))) (ho_argument_types U)"
    and node: "ho_fo_node F arity t=Some c" and typed: "ho_typeof S V B t=Some T"
    and member: "x\<in>set (ho_spine_arguments t)"
  shows "\<exists>b A. T=HBase b \<and> (A,x)\<in>ho_accessible_arguments rank S V B t"
proof -
  let ?xs = "ho_spine_arguments t"
  have fc: "c\<in>F" and len: "length ?xs=arity c"
    and shape: "t=ho_apply_terms (HConst c) ?xs"
    using ho_fo_node_parts[OF node] by auto
  have ty_call: "ho_typeof S V B (ho_apply_terms (HConst c) ?xs)=Some T"
    by (subst shape[symmetric]) (rule typed)
  obtain U where lookup: "ho_lookup S c=Some U"
    and result: "T=ho_drop_type (length ?xs) U"
    and args: "list_all2 (\<lambda>A x. ho_typeof S V B x=Some A) (take (length ?xs) (ho_argument_types U)) ?xs"
    using ho_apply_terms_type_inverse[OF ty_call] by auto
  have full: "length ?xs=length (ho_argument_types U)"
    and positive: "list_all (ho_positive_type rank (rank (ho_result_sort U))) (ho_argument_types U)"
    using signature[OF fc lookup] len by auto
  have T: "T=HBase (ho_result_sort U)" using result full by simp
  obtain i where i: "i<length ?xs" and x: "x=?xs!i" using member by (auto simp: in_set_conv_nth)
  have typed_x: "ho_typeof S V B x=Some (ho_argument_types U!i)"
    using list_all2_nthD2[OF args i] full x by simp
  have pos_x: "ho_positive_type rank (rank (ho_result_sort U)) (ho_argument_types U!i)"
    using positive full i by (simp add: list_all_iff)
  have head: "ho_application_head t=HConst c"
    using node unfolding ho_fo_node_def by (auto split: ho_term.splits if_splits)
  have av: "(ho_argument_types U!i,x)\<in>ho_accessible_arguments rank S V B t"
    using typed_x pos_x member typed T head by (simp add: ho_accessible_arguments_def)
  show ?thesis using T av by blast
qed

lemma ho_fo_node_saturated:
  assumes node: "ho_fo_node F arity t=Some c"
    and arities: "\<And>G l r d. (G,l,r)\<in>set R \<Longrightarrow>
      ho_application_head (ho_erase_pattern l)=HConst d \<Longrightarrow>
      ho_spine_length (ho_erase_pattern l)=arity d"
  shows "ho_saturated_neutral R t"
proof -
  have head: "ho_application_head t=HConst c"
    using node unfolding ho_fo_node_def by (auto split: ho_term.splits if_splits)
  have len: "ho_spine_length t=arity c" using ho_fo_node_parts(2)[OF node] by simp
  have not_abs: "t\<noteq>HAbs A b" for A b
  proof
    assume eq: "t=HAbs A b"
    show False using head by (simp add: eq)
  qed
  show ?thesis unfolding ho_saturated_neutral_def
    using head len arities not_abs by auto
qed

context ho_source_accessible_reducibility
begin

abbreviation ho_candidate_context where
  "ho_candidate_context F arity t \<equiv>
    ho_fo_context_property F arity (\<lambda>t. \<exists>T. source_candidate T t) t"

lemma ho_candidate_context_of_candidate:
  assumes access: "\<And>t c T x. ho_fo_node F arity t=Some c \<Longrightarrow>
      ho_typeof S V B t=Some T \<Longrightarrow> x\<in>set (ho_spine_arguments t) \<Longrightarrow>
      \<exists>b U. T=HBase b \<and> (U,x)\<in>ho_accessible_arguments rank S V B t"
    and ct: "source_candidate T t"
  shows "ho_candidate_context F arity t"
  using ct
proof (induction t arbitrary: T rule: measure_induct_rule[where f=size])
  case (less t)
  show ?case
  proof (cases "ho_fo_node F arity t")
    case None
    show ?thesis using less.prems
      by (subst ho_fo_context_property.simps) (auto simp: None)
  next
    case (Some c)
    have ty: "ho_typeof S V B t=Some T" by (rule source.candidate_typed[OF less.prems])
    have args: "list_all (ho_candidate_context F arity) (ho_spine_arguments t)"
    proof (unfold list_all_iff, intro ballI)
      fix x assume mem: "x\<in>set (ho_spine_arguments t)"
      obtain b U where T: "T=HBase b" and av: "(U,x)\<in>ho_accessible_arguments rank S V B t"
        using access[OF Some ty mem] by blast
      have cx: "source_candidate U x"
        by (rule source_candidate_accessible[OF less.prems[unfolded T] av])
      show "ho_candidate_context F arity x"
        by (rule less.IH[OF ho_spine_argument_size[OF mem] cx])
    qed
    show ?thesis by (subst ho_fo_context_property.simps) (simp add: Some args)
  qed
qed

theorem ho_candidate_context_stable:
  assumes arities: "\<And>G l r c. (G,l,r)\<in>set R \<Longrightarrow>
      ho_application_head (ho_erase_pattern l)=HConst c \<Longrightarrow>
      ho_spine_length (ho_erase_pattern l)=arity c"
    and access: "\<And>t c T x. ho_fo_node F arity t=Some c \<Longrightarrow>
      ho_typeof S V B t=Some T \<Longrightarrow> x\<in>set (ho_spine_arguments t) \<Longrightarrow>
      \<exists>b U. T=HBase b \<and> (U,x)\<in>ho_accessible_arguments rank S V B t"
    and coverage: "\<And>G l r d. (G,l,r)\<in>set R \<Longrightarrow>
      ho_application_head (ho_erase_pattern l)=HConst d \<Longrightarrow> d\<in>F \<Longrightarrow>
      \<exists>p q. l=ho_fo_pattern p \<and> r=ho_fo_pattern q \<and>
        ho_fo_wellformed F arity p \<and> ho_fo_wellformed F arity q \<and>
        ho_fo_variables q\<subseteq>ho_fo_variables p"
    and has_prop: "ho_candidate_context F arity t" and step: "ho_step S V R B t u"
  shows "ho_candidate_context F arity u"
proof (rule ho_fo_context_property_step[OF arities _ _ _ has_prop step])
  fix x assume "\<exists>T. source_candidate T x"
  then obtain T where cx: "source_candidate T x" by blast
  show "ho_candidate_context F arity x"
    by (rule ho_candidate_context_of_candidate[where F=F and arity=arity, OF access cx])
next
  fix x y assume "\<exists>T. source_candidate T x" and "ho_step S V R B x y"
  then show "\<exists>T. source_candidate T y" using source_candidate_reduction by blast
next
  fix x y c
  assume px: "ho_candidate_context F arity x" and node: "ho_fo_node F arity x=Some c"
    and root: "ho_root_step S V R B x y"
  show "ho_candidate_context F arity y"
    by (rule ho_fo_context_property_root[OF px node root coverage])
qed

lemma ho_candidate_context_safe:
  assumes has_prop: "ho_candidate_context F arity t"
  shows "ho_projection_safe F arity t"
  unfolding ho_projection_safe_context_property
proof (rule ho_fo_context_property_mono[OF _ has_prop])
  fix x assume "\<exists>T. source_candidate T x"
  then obtain T where ct: "source_candidate T x" by blast
  show "Wellfounded.accp application_descent x"
    by (rule source_SN_application_descent[OF source.candidate_SN[OF ct]])
qed

theorem ho_SN_candidate_context:
  assumes arities: "\<And>G l r c. (G,l,r)\<in>set R \<Longrightarrow>
      ho_application_head (ho_erase_pattern l)=HConst c \<Longrightarrow>
      ho_spine_length (ho_erase_pattern l)=arity c"
    and stable: "\<And>t u. ho_candidate_context F arity t \<Longrightarrow>
      ho_step S V R B t u \<Longrightarrow> ho_candidate_context F arity u"
    and sn: "Wellfounded.accp application_descent t"
    and has_prop: "ho_candidate_context F arity t"
    and typed: "ho_typeof S V B t=Some T"
  shows "source_candidate T t"
proof -
  have all: "\<forall>T. Wellfounded.accp application_descent x \<longrightarrow>
      ho_candidate_context F arity x \<longrightarrow> ho_typeof S V B x=Some T \<longrightarrow>
      source_candidate T x" for x
  proof (induction x rule: wf_induct[OF wf_trancl[OF wf_terminating_descent]])
    case (1 x)
    note ih = "1.IH"
    show ?case
    proof (intro allI impI)
      fix T assume ax: "Wellfounded.accp application_descent x"
        and px: "ho_candidate_context F arity x" and tx: "ho_typeof S V B x=Some T"
      show "source_candidate T x"
      proof (cases "ho_fo_node F arity x")
        case None
        obtain U where cu: "source_candidate U x" using px
          by (subst (asm) ho_fo_context_property.simps) (auto simp: None)
        show ?thesis by (rule source_candidate_retype[OF cu tx])
      next
        case (Some c)
        have neu: "ho_saturated_neutral R x" by (rule ho_fo_node_saturated[OF Some arities])
        have args: "list_all (ho_candidate_context F arity) (ho_spine_arguments x)"
          using px ho_fo_context_property.simps[of F arity "\<lambda>t. \<exists>T. source_candidate T t" x]
          by (simp only: Some option.simps)
        have children: "\<exists>U. source_candidate U y" if mem: "y\<in>set (ho_spine_arguments x)" for y
        proof -
          obtain U where ty: "ho_typeof S V B y=Some U"
            using ho_spine_argument_typed[OF tx mem] by blast
          have ay: "Wellfounded.accp application_descent y"
            by (rule application_subterm_accessible[OF ax])
               (rule tranclp_into_rtranclp[OF ho_spine_argument_descent[OF mem]])
          have py: "ho_candidate_context F arity y" using args mem by (simp add: list_all_iff)
          have small: "(y,x)\<in>terminating_descent\<^sup>+"
            by (rule ho_projection_argument_decreases[OF ax mem])
          show ?thesis using ih small ay py ty by blast
        qed
        have reducts: "source_candidate T y" if step: "ho_step S V R B x y" for y
        proof -
          have ay: "Wellfounded.accp application_descent y"
            by (rule accp_downward[OF ax]) (use step in \<open>simp add: application_descent_def\<close>)
          have py: "ho_candidate_context F arity y" by (rule stable[OF px step])
          have ty: "ho_typeof S V B y=Some T" by (rule ho_zero_arity_step_type[OF step zero tx])
          have small: "(y,x)\<in>terminating_descent\<^sup>+"
            by (rule r_into_trancl) (use ax step in \<open>simp add: terminating_descent_def application_descent_def\<close>)
          show ?thesis using ih small ay py ty by blast
        qed
        show ?thesis by (rule source_candidate_saturated[OF tx neu children reducts])
      qed
    qed
  qed
  show ?thesis using all[of t] sn has_prop typed by blast
qed

theorem ho_first_order_delegation_computable:
  fixes rel :: "ho_fo_tree \<Rightarrow> ho_fo_tree \<Rightarrow> bool" and ce :: nat
  assumes arities: "\<And>G l r c. (G,l,r)\<in>set R \<Longrightarrow>
      ho_application_head (ho_erase_pattern l)=HConst c \<Longrightarrow>
      ho_spine_length (ho_erase_pattern l)=arity c"
    and signature: "\<And>c U. c\<in>F \<Longrightarrow> ho_lookup S c=Some U \<Longrightarrow>
      arity c=length (ho_argument_types U) \<and>
      list_all (ho_positive_type rank (rank (ho_result_sort U))) (ho_argument_types U)"
    and branching: "\<And>t. finite {u. ho_step S V R B t u}"
    and ce_left: "\<And>x y. rel (HFOFun ce [x,y]) x"
    and ce_right: "\<And>x y. rel (HFOFun ce [x,y]) y"
    and fo_context: "\<And>c xs ys x y. rel x y \<Longrightarrow>
      rel (HFOFun c (xs@x#ys)) (HFOFun c (xs@y#ys))"
    and coverage: "\<And>G l r d. (G,l,r)\<in>set R \<Longrightarrow>
      ho_application_head (ho_erase_pattern l)=HConst d \<Longrightarrow> d\<in>F \<Longrightarrow>
      \<exists>p q. l=ho_fo_pattern p \<and> r=ho_fo_pattern q \<and>
        ho_fo_wellformed F arity p \<and> ho_fo_wellformed F arity q \<and>
        ho_fo_variables q\<subseteq>ho_fo_variables p \<and> (p,q)\<in>P"
    and instances: "\<And>p q s. (p,q)\<in>P \<Longrightarrow>
      rel (ho_fo_substitution s p) (ho_fo_substitution s q)"
    and fo_wf: "wf {(u,t). rel\<^sup>+\<^sup>+ t u}"
    and has_prop: "ho_candidate_context F arity t"
    and typed: "ho_typeof S V B t=Some T"
  shows "source_candidate T t"
proof -
  have safe: "ho_projection_safe F arity t" by (rule ho_candidate_context_safe[OF has_prop])
  have sn: "Wellfounded.accp (\<lambda>u t. ho_step S V R B t u) t"
    by (rule ho_first_order_delegation_SN[where rel=rel and ce=ce and P=P,
          OF arities branching ce_left ce_right fo_context coverage instances fo_wf safe])
  have acc: "Wellfounded.accp application_descent t" by (rule source_SN_application_descent[OF sn])
  have access: "\<exists>b U. A=HBase b \<and> (U,x)\<in>ho_accessible_arguments rank S V B v"
    if "ho_fo_node F arity v=Some c" and "ho_typeof S V B v=Some A"
      and "x\<in>set (ho_spine_arguments v)" for v c A x
    by (rule ho_fo_signature_accessible[where F=F and arity=arity, OF signature that])
  have closed: "ho_candidate_context F arity v"
    if ctx: "ho_candidate_context F arity u" and st: "ho_step S V R B u v" for u v
  proof (rule ho_candidate_context_stable[where F=F and arity=arity, OF arities access _ ctx st])
    fix G l r d
    assume mem: "(G,l,r)\<in>set R" and head: "ho_application_head (ho_erase_pattern l)=HConst d"
      and fd: "d\<in>F"
    show "\<exists>p q. l=ho_fo_pattern p \<and> r=ho_fo_pattern q \<and>
        ho_fo_wellformed F arity p \<and> ho_fo_wellformed F arity q \<and>
        ho_fo_variables q\<subseteq>ho_fo_variables p"
      using coverage[OF mem head fd] by blast
  qed
  show ?thesis by (rule ho_SN_candidate_context[OF arities closed acc has_prop typed])
qed

end
end
