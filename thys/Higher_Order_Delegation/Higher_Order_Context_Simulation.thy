theory Higher_Order_Context_Simulation
  imports Higher_Order_Finite_Projection
begin

lemma ho_fo_context_trancl:
  assumes ctx: "\<And>x y. rel x y \<Longrightarrow>
      rel (HFOFun c (xs@x#ys)) (HFOFun c (xs@y#ys))"
    and path: "rel\<^sup>+\<^sup>+ x y"
  shows "rel\<^sup>+\<^sup>+ (HFOFun c (xs@x#ys)) (HFOFun c (xs@y#ys))"
  using path by (induction rule: tranclp_induct)
    (auto intro: ctx tranclp.r_into_trancl tranclp.trancl_into_trancl)

context ho_source_neutral_reducibility
begin

context
  fixes F :: "nat set" and arity :: "nat \<Rightarrow> nat" and ce :: nat
    and rel :: "ho_fo_tree \<Rightarrow> ho_fo_tree \<Rightarrow> bool"
  assumes rule_arities: "\<And>G l r c. (G,l,r)\<in>set R \<Longrightarrow>
      ho_application_head (ho_erase_pattern l)=HConst c \<Longrightarrow>
      ho_spine_length (ho_erase_pattern l)=arity c"
    and branching: "\<And>t. finite {u. ho_step S V R B t u}"
    and ce_left: "\<And>x y. rel (HFOFun ce [x,y]) x"
    and ce_right: "\<And>x y. rel (HFOFun ce [x,y]) y"
    and fo_context: "\<And>c xs ys x y. rel x y \<Longrightarrow>
      rel (HFOFun c (xs@x#ys)) (HFOFun c (xs@y#ys))"
    and root_simulation: "\<And>t u c. ho_projection_safe F arity t \<Longrightarrow>
      ho_fo_node F arity t=Some c \<Longrightarrow> ho_root_step S V R B t u \<Longrightarrow>
      ho_projection_safe F arity u \<and>
      rel\<^sup>+\<^sup>+ (ho_context_projection F arity ce t) (ho_context_projection F arity ce u)"
begin

text \<open>Only root simulation remains a premise here. Argument and alien
reductions, including beta reductions inside alien terms, are discharged by
the source relation itself. No first-order certificate is accepted by this
theory or used as an unchecked oracle for that root premise.\<close>

theorem ho_safe_context_step:
  "ho_projection_safe F arity t \<Longrightarrow> ho_step S V R B t u \<Longrightarrow>
    ho_projection_safe F arity u \<and>
    rel\<^sup>+\<^sup>+ (ho_context_projection F arity ce t) (ho_context_projection F arity ce u)"
proof (induction t arbitrary: u rule: measure_induct_rule[where f=size])
  case (less t)
  show ?case
  proof (cases "ho_fo_node F arity t")
    case None
    show ?thesis
      by (rule ho_context_projection_alien_step[where rel=rel,
            OF less.prems(1) None branching less.prems(2)])
         (rule ce_left, rule ce_right)
  next
    case (Some c)
    let ?xs = "ho_spine_arguments t"
    have mem: "c\<in>F" and len: "length ?xs=arity c"
      and shape: "t=ho_apply_terms (HConst c) ?xs"
      using ho_fo_node_parts[OF Some] by auto
    have args: "list_all (ho_projection_safe F arity) ?xs"
      using less.prems(1) by (subst (asm) ho_projection_safe.simps) (simp add: Some)
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
      then show ?thesis by (rule root_simulation[OF less.prems(1) Some])
    next
      assume "\<exists>ys. ho_arguments_step S V R B ?xs ys \<and> u=ho_apply_terms (HConst c) ys"
      then obtain us v vs w where xs: "?xs=us@v#vs"
        and target: "u=ho_apply_terms (HConst c) (us@w#vs)"
        and step: "ho_step S V R B v w"
        unfolding ho_arguments_step_def by blast
      have member: "v\<in>set ?xs" using xs by simp
      have safe_v: "ho_projection_safe F arity v" using args member by (simp add: list_all_iff)
      have ih: "ho_projection_safe F arity w \<and>
        rel\<^sup>+\<^sup>+ (ho_context_projection F arity ce v) (ho_context_projection F arity ce w)"
        by (rule less.IH[OF ho_spine_argument_size[OF member] safe_v step])
      have node_u: "ho_fo_node F arity u=Some c"
        unfolding target by (rule ho_fo_node_call[OF mem]) (use len xs in simp)
      have args_u: "list_all (ho_projection_safe F arity) (ho_spine_arguments u)"
        using args ih xs by (simp add: target)
      have safe_u: "ho_projection_safe F arity u"
        by (subst ho_projection_safe.simps) (simp add: node_u args_u)
      have path: "rel\<^sup>+\<^sup>+
          (HFOFun c (map (ho_context_projection F arity ce) us @
            ho_context_projection F arity ce v # map (ho_context_projection F arity ce) vs))
          (HFOFun c (map (ho_context_projection F arity ce) us @
            ho_context_projection F arity ce w # map (ho_context_projection F arity ce) vs))"
        by (rule ho_fo_context_trancl[where rel=rel]) (rule fo_context, assumption, rule conjunct2[OF ih])
      have simulation: "rel\<^sup>+\<^sup>+ (ho_context_projection F arity ce t)
          (ho_context_projection F arity ce u)"
      proof -
        have pt: "ho_context_projection F arity ce t =
            HFOFun c (map (ho_context_projection F arity ce) (us@v#vs))"
          using ho_context_projection.simps[of F arity ce t]
          by (simp only: Some option.simps xs)
        have pu0: "ho_context_projection F arity ce u =
            HFOFun c (map (ho_context_projection F arity ce) (ho_spine_arguments u))"
          using ho_context_projection.simps[of F arity ce u]
          by (simp only: node_u option.simps)
        have pu: "ho_context_projection F arity ce u =
            HFOFun c (map (ho_context_projection F arity ce) (us@w#vs))"
          using pu0 by (simp only: target ho_apply_terms_arguments
              ho_spine_arguments.simps append.simps)
        show ?thesis using path by (simp only: pt pu map_append list.map)
      qed
      show ?thesis using safe_u simulation by blast
    qed
  qed
qed

theorem ho_safe_context_SN:
  assumes fo_wf: "wf {(u,t). rel\<^sup>+\<^sup>+ t u}"
    and safe: "ho_projection_safe F arity t"
  shows "Wellfounded.accp (\<lambda>u t. ho_step S V R B t u) t"
proof -
  let ?Q = "inv_image {(u,t). rel\<^sup>+\<^sup>+ t u} (ho_context_projection F arity ce)"
  have wfQ: "wf ?Q" by (rule wf_inv_image[OF fo_wf])
  have all: "ho_projection_safe F arity x \<Longrightarrow>
      Wellfounded.accp (\<lambda>u t. ho_step S V R B t u) x" for x
  proof (induction x rule: wf_induct[OF wfQ])
    case (1 x)
    note ih = "1.IH" and sx = "1.prems"
    show ?case
    proof (rule accp.accI)
      fix y assume step: "ho_step S V R B x y"
      have result: "ho_projection_safe F arity y \<and>
        rel\<^sup>+\<^sup>+ (ho_context_projection F arity ce x) (ho_context_projection F arity ce y)"
        by (rule ho_safe_context_step[OF sx step])
      have small: "(y,x)\<in>?Q" using result by (simp add: inv_image_def)
      show "Wellfounded.accp (\<lambda>u t. ho_step S V R B t u) y"
        using ih small result by blast
    qed
  qed
  show ?thesis by (rule all[OF safe])
qed

end
end
end
