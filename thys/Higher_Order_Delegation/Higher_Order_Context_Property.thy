theory Higher_Order_Context_Property
  imports Higher_Order_First_Order_Delegation
begin

function ho_fo_context_property where
  "ho_fo_context_property F arity P t = (case ho_fo_node F arity t of
    Some c \<Rightarrow> list_all (ho_fo_context_property F arity P) (ho_spine_arguments t)
    | None \<Rightarrow> P t)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(F,arity,P,t). size t)")
     (auto intro: ho_spine_argument_size)

lemma ho_fo_context_property_mono:
  assumes mono: "\<And>x. P x \<Longrightarrow> Q x"
  shows "ho_fo_context_property F arity P t \<Longrightarrow> ho_fo_context_property F arity Q t"
proof (induction t rule: measure_induct_rule[where f=size])
  case (less t)
  show ?case
  proof (cases "ho_fo_node F arity t")
    case None
    show ?thesis using less.prems mono
      by (subst ho_fo_context_property.simps, subst (asm) ho_fo_context_property.simps)
         (simp add: None)
  next
    case (Some c)
    have args: "list_all (ho_fo_context_property F arity P) (ho_spine_arguments t)"
      using less.prems by (subst (asm) ho_fo_context_property.simps) (simp add: Some)
    have target: "list_all (ho_fo_context_property F arity Q) (ho_spine_arguments t)"
      using args less.IH ho_spine_argument_size by (auto simp: list_all_iff)
    show ?thesis by (subst ho_fo_context_property.simps) (simp add: Some target)
  qed
qed

lemma ho_fo_context_property_instance:
  "ho_fo_wellformed F arity p \<Longrightarrow>
    ho_fo_context_property F arity P (ho_fo_instance s p) \<longleftrightarrow>
      (\<forall>n\<in>ho_fo_variables p. ho_fo_context_property F arity P (s n))"
proof (induction p)
  case (HFOVar n)
  then show ?case by simp
next
  case (HFOFun c ps)
  have node: "ho_fo_node F arity (ho_fo_instance s (HFOFun c ps))=Some c"
    using HFOFun.prems by (auto intro: ho_fo_node_call)
  have eq: "ho_fo_context_property F arity P (ho_fo_instance s (HFOFun c ps)) =
      list_all (ho_fo_context_property F arity P) (ho_spine_arguments (ho_fo_instance s (HFOFun c ps)))"
    using ho_fo_context_property.simps[of F arity P "ho_fo_instance s (HFOFun c ps)"]
    by (simp only: node option.simps)
  show ?case using eq HFOFun.IH HFOFun.prems by (auto simp: list_all_iff)
qed

context ho_source_neutral_reducibility
begin

lemma ho_projection_safe_context_property:
  "ho_projection_safe F arity t =
    ho_fo_context_property F arity (Wellfounded.accp application_descent) t"
proof (induction t rule: measure_induct_rule[where f=size])
  case (less t)
  have children: "list_all (ho_projection_safe F arity) (ho_spine_arguments t) =
      list_all (ho_fo_context_property F arity (Wellfounded.accp application_descent)) (ho_spine_arguments t)"
    using less.IH ho_spine_argument_size by (auto simp: list_all_iff)
  show ?case
    using ho_projection_safe.simps[of F arity t]
      ho_fo_context_property.simps[of F arity "Wellfounded.accp application_descent" t]
    by (simp only: children)
qed

lemma ho_fo_context_property_root:
  assumes has_prop: "ho_fo_context_property F arity P t"
    and node: "ho_fo_node F arity t=Some c" and step: "ho_root_step S V R B t u"
    and coverage: "\<And>G l r d. (G,l,r)\<in>set R \<Longrightarrow>
      ho_application_head (ho_erase_pattern l)=HConst d \<Longrightarrow> d\<in>F \<Longrightarrow>
      \<exists>p q. l=ho_fo_pattern p \<and> r=ho_fo_pattern q \<and>
        ho_fo_wellformed F arity p \<and> ho_fo_wellformed F arity q \<and>
        ho_fo_variables q\<subseteq>ho_fo_variables p"
  shows "ho_fo_context_property F arity P u"
proof -
  obtain G l r s where member: "(G,l,r)\<in>set R"
    and li: "ho_instantiate s 0 l=Some t" and ri: "ho_instantiate s 0 r=Some u"
    using step unfolding ho_root_step_def by blast
  have head_t: "ho_application_head t=HConst c"
    using node unfolding ho_fo_node_def by (auto split: ho_term.splits if_splits)
  have head_l: "ho_application_head (ho_erase_pattern l)=HConst c"
    using rule_instance_head_spine(1)[OF member li] head_t by simp
  obtain p q where l: "l=ho_fo_pattern p" and r: "r=ho_fo_pattern q"
    and wp: "ho_fo_wellformed F arity p" and wq: "ho_fo_wellformed F arity q"
    and vars: "ho_fo_variables q\<subseteq>ho_fo_variables p"
    using coverage[OF member head_l ho_fo_node_parts(1)[OF node]] by blast
  have t: "t=ho_fo_instance s p" and u: "u=ho_fo_instance s q"
    using li ri by (simp_all add: l r ho_fo_pattern_instantiate)
  have variables: "\<forall>n\<in>ho_fo_variables p. ho_fo_context_property F arity P (s n)"
    using has_prop ho_fo_context_property_instance[OF wp, of P s] t by simp
  show ?thesis using variables vars ho_fo_context_property_instance[OF wq, of P s] u by blast
qed

theorem ho_fo_context_property_step:
  assumes rule_arities: "\<And>G l r c. (G,l,r)\<in>set R \<Longrightarrow>
      ho_application_head (ho_erase_pattern l)=HConst c \<Longrightarrow>
      ho_spine_length (ho_erase_pattern l)=arity c"
    and leaf: "\<And>t. P t \<Longrightarrow> ho_fo_context_property F arity P t"
    and leaf_step: "\<And>t u. P t \<Longrightarrow> ho_step S V R B t u \<Longrightarrow> P u"
    and root: "\<And>t u c. ho_fo_context_property F arity P t \<Longrightarrow>
      ho_fo_node F arity t=Some c \<Longrightarrow> ho_root_step S V R B t u \<Longrightarrow>
      ho_fo_context_property F arity P u"
    and has_prop: "ho_fo_context_property F arity P t" and step: "ho_step S V R B t u"
  shows "ho_fo_context_property F arity P u"
  using has_prop step
proof (induction t arbitrary: u rule: measure_induct_rule[where f=size])
  case (less t)
  show ?case
  proof (cases "ho_fo_node F arity t")
    case None
    have pt: "P t" using less.prems(1)
      by (subst (asm) ho_fo_context_property.simps) (simp add: None)
    show ?thesis by (rule leaf[OF leaf_step[OF pt less.prems(2)]])
  next
    case (Some c)
    let ?xs = "ho_spine_arguments t"
    have mem: "c\<in>F" and len: "length ?xs=arity c"
      and shape: "t=ho_apply_terms (HConst c) ?xs"
      using ho_fo_node_parts[OF Some] by auto
    have args: "list_all (ho_fo_context_property F arity P) ?xs"
      using less.prems(1) by (subst (asm) ho_fo_context_property.simps) (simp add: Some)
    have st_call: "ho_step S V R B (ho_apply_terms (HConst c) ?xs) u"
      by (subst shape[symmetric]) (rule less.prems(2))
    have bound: "length ?xs\<le>arity c" using len by simp
    have split: "ho_root_step S V R B t u \<or>
        (\<exists>ys. ho_arguments_step S V R B ?xs ys \<and> u=ho_apply_terms (HConst c) ys)"
      using source_call_reduct[where a=arity, OF rule_arities bound st_call]
      by (simp only: shape[symmetric])
    from split show ?thesis
    proof
      assume "ho_root_step S V R B t u"
      then show ?thesis by (rule root[OF less.prems(1) Some])
    next
      assume "\<exists>ys. ho_arguments_step S V R B ?xs ys \<and> u=ho_apply_terms (HConst c) ys"
      then obtain us v vs w where xs: "?xs=us@v#vs"
        and target: "u=ho_apply_terms (HConst c) (us@w#vs)"
        and step: "ho_step S V R B v w"
        unfolding ho_arguments_step_def by blast
      have member: "v\<in>set ?xs" using xs by simp
      have pv: "ho_fo_context_property F arity P v" using args member by (simp add: list_all_iff)
      have pw: "ho_fo_context_property F arity P w"
        by (rule less.IH[OF ho_spine_argument_size[OF member] pv step])
      have node_u: "ho_fo_node F arity u=Some c"
        unfolding target by (rule ho_fo_node_call[OF mem]) (use len xs in simp)
      have args_u: "list_all (ho_fo_context_property F arity P) (ho_spine_arguments u)"
        using args pw xs by (simp add: target)
      show ?thesis by (subst ho_fo_context_property.simps) (simp add: node_u args_u)
    qed
  qed
qed

end
end
