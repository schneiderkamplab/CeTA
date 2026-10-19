theory Higher_Order_Finite_Projection
  imports Higher_Order_Algebraic_Embedding
begin

lemma ho_spine_argument_descent:
  "u\<in>set (ho_spine_arguments t) \<Longrightarrow>
    ho_direct_application_subterm\<^sup>+\<^sup>+ u t"
proof (induction t)
  case (HApp f x)
  have left: "ho_direct_application_subterm f (HApp f x)"
    and right: "ho_direct_application_subterm x (HApp f x)" by simp_all
  show ?case using HApp left right
    by (auto intro: tranclp.r_into_trancl tranclp.trancl_into_trancl)
qed auto

definition ho_fo_node where
  "ho_fo_node F arity t = (case ho_application_head t of HConst c \<Rightarrow>
    if c\<in>F \<and> length (ho_spine_arguments t)=arity c then Some c else None
    | _ \<Rightarrow> None)"

lemma ho_fo_node_call:
  "c\<in>F \<Longrightarrow> length xs=arity c \<Longrightarrow>
    ho_fo_node F arity (ho_apply_terms (HConst c) xs)=Some c"
  by (simp add: ho_fo_node_def)

lemma ho_fo_node_parts:
  assumes node: "ho_fo_node F arity t=Some c"
  shows "c\<in>F" "length (ho_spine_arguments t)=arity c"
    "t=ho_apply_terms (HConst c) (ho_spine_arguments t)"
proof -
  have head: "ho_application_head t=HConst c" and member: "c\<in>F"
    and len: "length (ho_spine_arguments t)=arity c"
    using node unfolding ho_fo_node_def
    by (auto split: ho_term.splits if_splits)
  show "c\<in>F" by (rule member)
  show "length (ho_spine_arguments t)=arity c" by (rule len)
  show "t=ho_apply_terms (HConst c) (ho_spine_arguments t)"
    using ho_spine_reconstruct[of t] head by simp
qed

lemma ho_spine_argument_size:
  "u\<in>set (ho_spine_arguments t) \<Longrightarrow> size u<size t"
  by (induction t) auto

context ho_source_neutral_reducibility
begin

definition ho_source_reduct_list where
  "ho_source_reduct_list t = (if finite {u. ho_step S V R B t u}
    then SOME xs. set xs={u. ho_step S V R B t u} else [])"

lemma ho_source_reduct_list_set:
  "finite {u. ho_step S V R B t u} \<Longrightarrow>
    set (ho_source_reduct_list t)={u. ho_step S V R B t u}"
  unfolding ho_source_reduct_list_def
  by (simp add: someI_ex[OF finite_list])

lemma ho_source_reduct_list_member:
  assumes member: "u\<in>set (ho_source_reduct_list t)"
  shows "ho_step S V R B t u"
proof (cases "finite {u. ho_step S V R B t u}")
  case True
  show ?thesis using member ho_source_reduct_list_set[OF True] by blast
next
  case False
  show ?thesis using member False by (simp add: ho_source_reduct_list_def)
qed

lemma ho_projection_argument_decreases:
  "Wellfounded.accp application_descent t \<Longrightarrow>
    u\<in>set (ho_spine_arguments t) \<Longrightarrow> (u,t)\<in>terminating_descent\<^sup>+"
  by (rule application_path_terminating_descent[OF ho_spine_argument_descent]) assumption+

lemma ho_projection_reduct_decreases:
  "Wellfounded.accp application_descent t \<Longrightarrow>
    u\<in>set (ho_source_reduct_list t) \<Longrightarrow> (u,t)\<in>terminating_descent\<^sup>+"
  by (rule r_into_trancl)
     (auto simp: terminating_descent_def application_descent_def dest: ho_source_reduct_list_member)

context
  fixes F :: "nat set" and arity :: "nat \<Rightarrow> nat" and ce :: nat
begin

text \<open>This semantic projection is used only in the soundness proof.
It is deliberately not an executable certificate checker: deciding source
normalization is not an implementation step. Non-normalizing inputs receive
an irrelevant default; the bridge must prove the accessibility guards.\<close>

function ho_SN_projection where
  "ho_SN_projection t = (if Wellfounded.accp application_descent t then
    (case ho_fo_node F arity t of Some c \<Rightarrow>
      HFOFun c (map ho_SN_projection (ho_spine_arguments t))
     | None \<Rightarrow> ho_finite_choice (\<lambda>x y. HFOFun ce [x,y]) (HFOVar 0)
         (map ho_SN_projection (ho_source_reduct_list t)))
    else HFOVar 0)"
  by pat_completeness auto
termination
  by (relation "terminating_descent\<^sup>+")
     (auto intro: wf_trancl wf_terminating_descent ho_projection_argument_decreases ho_projection_reduct_decreases)

lemma ho_SN_projection_fo:
  "Wellfounded.accp application_descent t \<Longrightarrow>
    ho_fo_node F arity t=Some c \<Longrightarrow>
    ho_SN_projection t=HFOFun c (map ho_SN_projection (ho_spine_arguments t))"
  by (subst ho_SN_projection.simps) simp

theorem ho_SN_projection_alien_step:
  assumes sn: "Wellfounded.accp application_descent t"
    and alien: "ho_fo_node F arity t=None"
    and branching: "finite {u. ho_step S V R B t u}"
    and step: "ho_step S V R B t u"
    and left: "\<And>x y. rel (HFOFun ce [x,y]) x"
    and right: "\<And>x y. rel (HFOFun ce [x,y]) y"
  shows "rel\<^sup>+\<^sup>+ (ho_SN_projection t) (ho_SN_projection u)"
proof -
  have member: "ho_SN_projection u\<in>set (map ho_SN_projection (ho_source_reduct_list t))"
    using step ho_source_reduct_list_set[OF branching] by auto
  have path: "rel\<^sup>+\<^sup>+
      (ho_finite_choice (\<lambda>x y. HFOFun ce [x,y]) (HFOVar 0)
        (map ho_SN_projection (ho_source_reduct_list t))) (ho_SN_projection u)"
    apply (rule ho_finite_choice_projects)
      apply (rule left)
     apply (rule right)
    apply (rule member)
    done
  show ?thesis by (subst ho_SN_projection.simps) (use sn alien path in simp)
qed

text \<open>Unlike the SN projection, this extension does not assume that
the entire first-order context terminates. Only its alien leaves will need
that premise. This distinction prevents circular use of the desired bridge.\<close>

function ho_context_projection where
  "ho_context_projection t = (case ho_fo_node F arity t of
    Some c \<Rightarrow> HFOFun c (map ho_context_projection (ho_spine_arguments t))
    | None \<Rightarrow> ho_SN_projection t)"
  by pat_completeness auto
termination
  by (relation "measure size") (auto intro: ho_spine_argument_size)

lemma ho_context_projection_SN:
  assumes sn: "Wellfounded.accp application_descent t"
  shows "ho_context_projection t=ho_SN_projection t"
  using sn
proof (induction t rule: ho_context_projection.induct)
  case (1 t)
  note ih = "1.IH" and acc_t = "1.prems"
  show ?case
  proof (cases "ho_fo_node F arity t")
    case None
    then show ?thesis by (subst ho_context_projection.simps) simp
  next
    case (Some c)
    have children: "map ho_context_projection (ho_spine_arguments t) =
        map ho_SN_projection (ho_spine_arguments t)"
    proof (rule map_cong)
      show "ho_spine_arguments t=ho_spine_arguments t" by rule
      fix u assume member: "u\<in>set (ho_spine_arguments t)"
      have acc: "Wellfounded.accp application_descent u"
        by (rule application_subterm_accessible[OF acc_t])
           (rule tranclp_into_rtranclp[OF ho_spine_argument_descent[OF member]])
      show "ho_context_projection u=ho_SN_projection u"
        by (rule ih[OF Some member acc])
    qed
    show ?thesis
      by (subst ho_context_projection.simps)
         (simp add: acc_t Some children ho_SN_projection_fo[OF acc_t Some])
  qed
qed

function ho_projection_safe where
  "ho_projection_safe t = (case ho_fo_node F arity t of
    Some c \<Rightarrow> list_all ho_projection_safe (ho_spine_arguments t)
    | None \<Rightarrow> Wellfounded.accp application_descent t)"
  by pat_completeness auto
termination
  by (relation "measure size") (auto intro: ho_spine_argument_size)

lemma ho_projection_safe_SN:
  "Wellfounded.accp application_descent t \<Longrightarrow> ho_projection_safe t"
proof (induction t rule: ho_projection_safe.induct)
  case (1 t)
  note ih = "1.IH" and acc_t = "1.prems"
  have children: "list_all ho_projection_safe (ho_spine_arguments t)"
    if node: "ho_fo_node F arity t=Some c" for c
  proof (unfold list_all_iff, intro ballI)
    fix u assume member: "u\<in>set (ho_spine_arguments t)"
    have acc: "Wellfounded.accp application_descent u"
      by (rule application_subterm_accessible[OF acc_t])
         (rule tranclp_into_rtranclp[OF ho_spine_argument_descent[OF member]])
    show "ho_projection_safe u" by (rule ih[OF node member acc])
  qed
  show ?case by (subst ho_projection_safe.simps)
     (use acc_t children in \<open>auto split: option.splits\<close>)
qed

lemma ho_context_projection_alien_step:
  assumes safe: "ho_projection_safe t" and alien: "ho_fo_node F arity t=None"
    and branching: "finite {u. ho_step S V R B t u}"
    and step: "ho_step S V R B t u"
    and left: "\<And>x y. rel (HFOFun ce [x,y]) x"
    and right: "\<And>x y. rel (HFOFun ce [x,y]) y"
  shows "ho_projection_safe u \<and>
    rel\<^sup>+\<^sup>+ (ho_context_projection t) (ho_context_projection u)"
proof -
  have sn: "Wellfounded.accp application_descent t"
    using safe by (subst (asm) ho_projection_safe.simps) (simp add: alien)
  have sn_u: "Wellfounded.accp application_descent u"
    by (rule accp_downward[OF sn]) (use step in \<open>simp add: application_descent_def\<close>)
  have path: "rel\<^sup>+\<^sup>+ (ho_SN_projection t) (ho_SN_projection u)"
    by (rule ho_SN_projection_alien_step[where rel=rel, OF sn alien branching step])
       (rule left, rule right)
  show ?thesis
    using ho_projection_safe_SN[OF sn_u] path
      ho_context_projection_SN[OF sn] ho_context_projection_SN[OF sn_u] by simp
qed

lemma ho_context_projection_instance:
  "ho_fo_wellformed F arity p \<Longrightarrow>
    ho_context_projection (ho_fo_instance s p) =
      ho_fo_substitution (\<lambda>n. ho_context_projection (s n)) p"
proof (induction p)
  case (HFOVar n)
  then show ?case by simp
next
  case (HFOFun c ps)
  have node: "ho_fo_node F arity (ho_fo_instance s (HFOFun c ps))=Some c"
    using HFOFun.prems by (auto intro: ho_fo_node_call)
  have children: "map (\<lambda>p. ho_context_projection (ho_fo_instance s p)) ps =
      map (ho_fo_substitution (\<lambda>n. ho_context_projection (s n))) ps"
    using HFOFun.IH HFOFun.prems by (auto simp: list_all_iff intro!: map_cong)
  have eq: "ho_context_projection (ho_fo_instance s (HFOFun c ps)) =
      HFOFun c (map ho_context_projection (ho_spine_arguments (ho_fo_instance s (HFOFun c ps))))"
    using ho_context_projection.simps[of "ho_fo_instance s (HFOFun c ps)"]
    by (simp only: node option.simps)
  show ?case using eq
    by (simp only: ho_fo_instance.simps ho_apply_terms_arguments ho_spine_arguments.simps
        append.simps map_map o_def children ho_fo_substitution.simps)
qed

lemma ho_projection_safe_instance:
  "ho_fo_wellformed F arity p \<Longrightarrow>
    ho_projection_safe (ho_fo_instance s p) \<longleftrightarrow>
      (\<forall>n\<in>ho_fo_variables p. ho_projection_safe (s n))"
proof (induction p)
  case (HFOVar n)
  then show ?case by simp
next
  case (HFOFun c ps)
  have node: "ho_fo_node F arity (ho_fo_instance s (HFOFun c ps))=Some c"
    using HFOFun.prems by (auto intro: ho_fo_node_call)
  have eq: "ho_projection_safe (ho_fo_instance s (HFOFun c ps)) =
      list_all ho_projection_safe (ho_spine_arguments (ho_fo_instance s (HFOFun c ps)))"
    using ho_projection_safe.simps[of "ho_fo_instance s (HFOFun c ps)"]
    by (simp only: node option.simps)
  show ?case using eq HFOFun.IH HFOFun.prems
    by (auto simp: list_all_iff)
qed

end
end

end
