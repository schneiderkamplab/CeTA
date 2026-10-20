theory Higher_Order_Spine_Expansion
  imports Higher_Order_Call_Expansion
begin

lemma ho_expansion_apply_step:
  "ho_step S V R B t u \<Longrightarrow>
    ho_step S V R B (ho_apply_terms t xs) (ho_apply_terms u xs)"
  by (induction xs arbitrary: t u) (auto intro: ho_step.app_left)

lemma ho_expansion_apply_steps:
  "(ho_step S V R B)\<^sup>*\<^sup>* t u \<Longrightarrow>
    (ho_step S V R B)\<^sup>*\<^sup>* (ho_apply_terms t xs) (ho_apply_terms u xs)"
  by (induction rule: rtranclp_induct)
    (auto intro: rtranclp.rtrancl_into_rtrancl ho_expansion_apply_step)

lemma ho_expansion_argument_step:
  "ho_arguments_step S V R B xs ys \<Longrightarrow>
    ho_step S V R B (ho_apply_terms t xs) (ho_apply_terms t ys)"
proof -
  assume st: "ho_arguments_step S V R B xs ys"
  obtain us v vs w where xs: "xs=us@v#vs" and ys: "ys=us@w#vs"
    and vw: "ho_step S V R B v w"
    using st unfolding ho_arguments_step_def by blast
  show ?thesis unfolding xs ys
    by (simp add: ho_apply_terms_append
      ho_expansion_apply_step[OF ho_step.app_right[OF vw]])
qed

lemma ho_expansion_apply_head_type:
  "ho_typeof S V B (ho_apply_terms f xs)=Some T \<Longrightarrow>
    \<exists>U. ho_typeof S V B f=Some U"
proof (induction xs arbitrary: f)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  have app: "ho_typeof S V B (ho_apply_terms (HApp f x) xs)=Some T"
    using Cons.prems by simp
  obtain U where "ho_typeof S V B (HApp f x)=Some U"
    using Cons.IH[OF app] by blast
  then show ?case by (auto split: option.splits ho_type.splits if_splits)
qed

lemma ho_expansion_apply_subterm:
  "ho_direct_application_subterm\<^sup>*\<^sup>* f (ho_apply_terms f xs)"
proof (induction xs arbitrary: f)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  have first: "ho_direct_application_subterm\<^sup>*\<^sup>* f (HApp f x)" by auto
  show ?case using rtranclp_trans[OF first Cons.IH] by simp
qed

context ho_source_neutral_reducibility
begin

lemma sn_arguments_step:
  assumes args: "\<And>x. x\<in>set xs \<Longrightarrow> source.strongly_normalizing x"
    and step: "ho_arguments_step S V R B xs ys"
    and member: "y\<in>set ys"
  shows "source.strongly_normalizing y"
proof -
  obtain us v vs w where xs: "xs=us@v#vs" and ys: "ys=us@w#vs"
    and vw: "ho_step S V R B v w"
    using step unfolding ho_arguments_step_def by blast
  have sn: "source.strongly_normalizing v" using args xs by simp
  have sw: "source.strongly_normalizing w"
    by (rule accp_downward[OF sn]) (rule vw)
  show ?thesis using member args sw unfolding xs ys by auto
qed

lemma beta_contractum_argument_steps:
  assumes step: "ho_arguments_step S V R B (x#xs) (y#ys)"
  shows "(ho_step S V R B)\<^sup>*\<^sup>*
    (ho_apply_terms (ho_beta_subst x 0 t) xs)
    (ho_apply_terms (ho_beta_subst y 0 t) ys)"
proof -
  obtain us v vs w where left: "x#xs=us@v#vs" and right: "y#ys=us@w#vs"
    and vw: "ho_step S V R B v w"
    using step unfolding ho_arguments_step_def by blast
  show ?thesis
  proof (cases us)
    case Nil
    have xy: "ho_step S V R B x y" and eq: "ys=xs" using left right vw Nil by auto
    have st: "(ho_step S V R B)\<^sup>*\<^sup>* (ho_beta_subst x 0 t) (ho_beta_subst y 0 t)"
      using ho_source_beta_argument_steps[OF xy zero, where B="[]" and t=t] by simp
    show ?thesis unfolding eq by (rule ho_expansion_apply_steps[OF st])
  next
    case (Cons a rest)
    have eq: "y=x" and xs: "xs=rest@v#vs" and ys: "ys=rest@w#vs"
      using left right Cons by auto
    have arg: "ho_arguments_step S V R B xs ys"
      unfolding ho_arguments_step_def using xs ys vw by blast
    show ?thesis unfolding eq by (rule r_into_rtranclp, rule ho_expansion_argument_step[OF arg])
  qed
qed

lemma sn_argument_step_order:
  assumes args: "\<And>x. x\<in>set xs \<Longrightarrow> source.strongly_normalizing x"
    and step: "ho_arguments_step S V R B xs ys"
  shows "((c,ys),(c,xs))\<in>call_order prec"
proof -
  obtain us v vs w where xs: "xs=us@v#vs" and ys: "ys=us@w#vs"
    and vw: "ho_step S V R B v w"
    using step unfolding ho_arguments_step_def by blast
  have sn: "source.strongly_normalizing v" using args xs by simp
  have small: "(w,v)\<in>terminating_descent"
    using source_SN_application_descent[OF sn] vw
    by (simp add: terminating_descent_def application_descent_def)
  have lex: "(ys,xs)\<in>lex (terminating_descent\<^sup>+)"
    using r_into_trancl[OF small] unfolding xs ys lex_conv by auto
  show ?thesis using lex by (simp add: call_order_def inv_image_def lex_prod_def)
qed

lemma source_lambda_spine_reduct:
  assumes step: "ho_step S V R B (ho_apply_terms (HAbs A t) (x#xs)) u"
  shows "u=ho_apply_terms (ho_beta_subst x 0 t) xs \<or>
    (\<exists>v. ho_step S V R (A#B) t v \<and>
       u=ho_apply_terms (HAbs A v) (x#xs)) \<or>
    (\<exists>ys. ho_arguments_step S V R B (x#xs) ys \<and>
       u=ho_apply_terms (HAbs A t) ys)"
  using step
proof (induction xs arbitrary: u rule: rev_induct)
  case Nil
  have st: "ho_step S V R B (HApp (HAbs A t) x) u" using Nil.prems by simp
  have arg: "ho_arguments_step S V R B [x] [y]" if "ho_step S V R B x y" for y
    unfolding ho_arguments_step_def
    by (rule exI[of _ "[]"], rule exI[of _ x], rule exI[of _ "[]"],
        rule exI[of _ y]) (use that in simp)
  from source_beta_reduct[OF st] show ?case
    using arg by fastforce
next
  case (snoc y xs)
  let ?f = "ho_apply_terms (HAbs A t) (x#xs)"
  have head: "ho_application_head ?f=HAbs A t" by simp
  have noabs: "?f\<noteq>HAbs C v" for C v
  proof
    assume eq: "?f=HAbs C v"
    have "ho_spine_length ?f=ho_spine_length (HAbs C v)" by (rule arg_cong[OF eq])
    then show False by simp
  qed
  have noabs': "ho_apply_terms (HApp (HAbs A t) x) xs\<noteq>HAbs C v" for C v
    using noabs[of C v] by simp
  have st: "ho_step S V R B (HApp ?f y) u" using snoc.prems by simp
  have cases: "(\<exists>g. ho_step S V R B ?f g \<and> u=HApp g y) \<or>
      (\<exists>z. ho_step S V R B y z \<and> u=HApp ?f z)"
    using st by (cases rule: ho_step.cases)
      (auto dest: rule_instance_constant_head simp: head noabs')
  from cases show ?case
  proof (elim disjE exE conjE)
    fix g assume fg: "ho_step S V R B ?f g" and eq: "u=HApp g y"
    from snoc.IH[OF fg] show ?thesis
    proof (elim disjE exE conjE)
      assume "g=ho_apply_terms (ho_beta_subst x 0 t) xs"
      then show ?thesis using eq by simp
    next
      fix v assume tv: "ho_step S V R (A#B) t v"
        and g: "g=ho_apply_terms (HAbs A v) (x#xs)"
      show ?thesis using tv eq g by auto
    next
      fix ys assume args: "ho_arguments_step S V R B (x#xs) ys"
        and g: "g=ho_apply_terms (HAbs A t) ys"
      have "ho_arguments_step S V R B ((x#xs)@[y]) (ys@[y])"
        using args unfolding ho_arguments_step_def by fastforce
      then show ?thesis using eq g by auto
    qed
  next
    fix z assume yz: "ho_step S V R B y z" and eq: "u=HApp ?f z"
    have "ho_arguments_step S V R B ((x#xs)@[y]) ((x#xs)@[z])"
      unfolding ho_arguments_step_def using yz by blast
    then show ?thesis using eq by auto
  qed
qed

end

context ho_source_accessible_reducibility
begin

lemma source_candidate_beta_spine_aux:
  assumes body_sn: "Wellfounded.accp (\<lambda>v t. ho_step S V R (A#B) t v) t"
    and args: "\<And>v. v\<in>set (x#xs) \<Longrightarrow> source.strongly_normalizing v"
    and ty: "ho_typeof S V B (ho_apply_terms (HAbs A t) (x#xs))=Some (HBase b)"
    and contractum: "source_candidate (HBase b) (ho_apply_terms (ho_beta_subst x 0 t) xs)"
  shows "source_candidate (HBase b) (ho_apply_terms (HAbs A t) (x#xs))"
  using body_sn args ty contractum
proof (induction t arbitrary: x xs rule: accp.induct)
  case (accI t)
  note body_ih = accI.IH
  have all: "\<forall>x xs. zs=x#xs \<longrightarrow>
      (\<forall>v\<in>set zs. source.strongly_normalizing v) \<longrightarrow>
      ho_typeof S V B (ho_apply_terms (HAbs A t) zs)=Some (HBase b) \<longrightarrow>
      source_candidate (HBase b) (ho_apply_terms (ho_beta_subst x 0 t) xs) \<longrightarrow>
      source_candidate (HBase b) (ho_apply_terms (HAbs A t) zs)" for zs
  proof (induction zs rule: wf_induct[OF wf_lex[OF wf_trancl[OF wf_terminating_descent]]])
    case (1 zs)
    show ?case
    proof (intro allI impI)
      fix x xs
      assume zs: "zs=x#xs" and sn: "\<forall>v\<in>set zs. source.strongly_normalizing v"
        and typed: "ho_typeof S V B (ho_apply_terms (HAbs A t) zs)=Some (HBase b)"
        and comp: "source_candidate (HBase b) (ho_apply_terms (ho_beta_subst x 0 t) xs)"
      have typed': "ho_typeof S V B (ho_apply_terms (HAbs A t) (x#xs))=Some (HBase b)"
        using typed zs by simp
      obtain U where ht: "ho_typeof S V B (HApp (HAbs A t) x)=Some U"
        using ho_expansion_apply_head_type[of S V B "HApp (HAbs A t) x" xs "HBase b"] typed'
        by fastforce
      have xt: "ho_typeof S V B x=Some A"
        using ht by (auto split: option.splits ho_type.splits if_splits)
      have reducts: "source_candidate (HBase b) u"
        if st: "ho_step S V R B (ho_apply_terms (HAbs A t) zs) u" for u
      proof -
        have st': "ho_step S V R B (ho_apply_terms (HAbs A t) (x#xs)) u" using st zs by simp
        from source_lambda_spine_reduct[OF st'] show ?thesis
        proof (elim disjE exE conjE)
          assume "u=ho_apply_terms (ho_beta_subst x 0 t) xs"
          then show ?thesis using comp by simp
        next
          fix v assume tv: "ho_step S V R (A#B) t v"
            and eq: "u=ho_apply_terms (HAbs A v) (x#xs)"
          have sub: "ho_step S V R B (ho_beta_subst x 0 t) (ho_beta_subst x 0 v)"
            using ho_source_step_beta_substitution[OF tv zero, where D="[]" and T=A and C=B and x=x] xt by simp
          have cc: "source_candidate (HBase b) (ho_apply_terms (ho_beta_subst x 0 v) xs)"
            by (rule source_candidate_reduction[OF comp ho_expansion_apply_step[OF sub]])
          have ty': "ho_typeof S V B (ho_apply_terms (HAbs A v) (x#xs))=Some (HBase b)"
            by (rule ho_zero_arity_step_type[OF
              ho_expansion_apply_step[OF ho_step.abs[OF tv]] zero typed'])
          show ?thesis unfolding eq
            by (rule body_ih[OF tv _ ty' cc]) (use sn zs in auto)
        next
          fix ys assume step: "ho_arguments_step S V R B (x#xs) ys"
            and eq: "u=ho_apply_terms (HAbs A t) ys"
          have length: "length ys=length (x#xs)"
            using step unfolding ho_arguments_step_def
            by (metis length_append length_Cons)
          then obtain y rest where ys: "ys=y#rest" by (cases ys) auto
          have order: "((0,ys),(0,zs))\<in>call_order (\<lambda>_. 0)"
            using sn_argument_step_order[OF _ step, where c=0 and prec="\<lambda>_. 0"] sn zs by auto
          have small: "(ys,zs)\<in>lex (terminating_descent\<^sup>+)"
            using order by (simp add: call_order_def inv_image_def lex_prod_def)
          have sn': "\<forall>v\<in>set ys. source.strongly_normalizing v"
            using sn_arguments_step[OF _ step] sn zs by auto
          have ty': "ho_typeof S V B (ho_apply_terms (HAbs A t) ys)=Some (HBase b)"
            by (rule ho_zero_arity_step_type[OF ho_expansion_argument_step[OF step] zero typed'])
          have steps: "(ho_step S V R B)\<^sup>*\<^sup>*
              (ho_apply_terms (ho_beta_subst x 0 t) xs)
              (ho_apply_terms (ho_beta_subst y 0 t) rest)"
            by (rule beta_contractum_argument_steps) (use step ys in simp)
          have cc: "source_candidate (HBase b) (ho_apply_terms (ho_beta_subst y 0 t) rest)"
            by (rule source_candidate_reductions[OF steps comp])
          show ?thesis using 1 small ys sn' ty' cc unfolding eq by blast
        qed
      qed
      have empty: "ho_accessible_arguments rank S V B (ho_apply_terms (HAbs A t) zs)={}"
        unfolding ho_accessible_arguments_def
        by (simp only: typed option.case ho_type.case ho_apply_terms_head
          ho_application_head.simps ho_term.case)
      show "source_candidate (HBase b) (ho_apply_terms (HAbs A t) zs)"
      proof (rule source_candidate_base_intro[OF typed reducts])
        fix T v
        assume av: "(T,v)\<in>ho_accessible_arguments rank S V B (ho_apply_terms (HAbs A t) zs)"
        have False using av empty by blast
        then show "source_candidate T v" by blast
      qed
    qed
  qed
  show ?case using all[of "x#xs"] accI.prems by blast
qed

theorem source_candidate_beta_spine:
  assumes args: "\<And>v. v\<in>set (x#xs) \<Longrightarrow> source.strongly_normalizing v"
    and ty: "ho_typeof S V B (ho_apply_terms (HAbs A t) (x#xs))=Some (HBase b)"
    and contractum: "source_candidate (HBase b) (ho_apply_terms (ho_beta_subst x 0 t) xs)"
  shows "source_candidate (HBase b) (ho_apply_terms (HAbs A t) (x#xs))"
proof -
  obtain U where ht: "ho_typeof S V B (HApp (HAbs A t) x)=Some U"
    using ho_expansion_apply_head_type[of S V B "HApp (HAbs A t) x" xs "HBase b"] ty by fastforce
  have xt: "ho_typeof S V B x=Some A"
    using ht by (auto split: option.splits ho_type.splits if_splits)
  have root: "Wellfounded.accp application_descent (ho_apply_terms (ho_beta_subst x 0 t) xs)"
    by (rule source_SN_application_descent[OF source.candidate_SN[OF contractum]])
  have sn: "source.strongly_normalizing (ho_beta_subst x 0 t)"
    by (rule application_descent_SN, rule application_subterm_accessible[OF root ho_expansion_apply_subterm])
  have body: "Wellfounded.accp (\<lambda>v t. ho_step S V R (A#B) t v) t"
    by (rule source_body_SN_from_instance[OF xt sn])
  show ?thesis by (rule source_candidate_beta_spine_aux[OF body args ty contractum])
qed

end
end
