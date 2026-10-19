theory Higher_Order_Candidate_Recursion
  imports Higher_Order_Candidate_Symbols
begin

context ho_source_accessible_reducibility
begin

lemma candidate_arguments_step:
  assumes args: "list_all2 source_candidate Ts xs" and step: "ho_arguments_step S V R B xs ys"
  shows "list_all2 source_candidate Ts ys"
proof -
  obtain us v vs w where xs: "xs=us@v#vs" and ys: "ys=us@w#vs" and vw: "ho_step S V R B v w"
    using step unfolding ho_arguments_step_def by blast
  obtain As A Bs where ts: "Ts=As@A#Bs" and pre: "list_all2 source_candidate As us"
    and cv: "source_candidate A v" and post: "list_all2 source_candidate Bs vs"
    using args unfolding xs by (auto simp: list_all2_append2 list_all2_Cons2)
  have cw: "source_candidate A w" by (rule source_candidate_reduction[OF cv vw])
  show ?thesis unfolding ts ys using pre cw post by (auto intro: list_all2_appendI)
qed

lemma candidate_argument_step_order:
  assumes args: "list_all2 source_candidate Ts xs" and step: "ho_arguments_step S V R B xs ys"
  shows "((c,ys),(c,xs))\<in>priority_call_order prec priority"
proof -
  obtain us v vs w where xs: "xs=us@v#vs" and ys: "ys=us@w#vs" and vw: "ho_step S V R B v w"
    using step unfolding ho_arguments_step_def by blast
  obtain A where cv: "source_candidate A v"
    using args unfolding xs by (auto simp: list_all2_append2 list_all2_Cons2)
  have small: "(w,v)\<in>terminating_descent"
    using source_SN_application_descent[OF source.candidate_SN[OF cv]] vw
    by (simp add: terminating_descent_def application_descent_def)
  have index: "length us<length xs" and at: "xs!length us=v" and update: "ys=xs[length us:=w]"
    by (simp_all add: xs ys list_update_append)
  have lex: "(ho_priority_arguments priority ys,ho_priority_arguments priority xs)\<in>lex (terminating_descent\<^sup>+)"
    unfolding update by (rule ho_priority_arguments_update[OF index]) (use r_into_trancl[OF small] at in simp)
  show ?thesis using lex by (simp add: priority_call_order_def inv_image_def lex_prod_def)
qed

theorem candidate_recursive_calls_computable:
  assumes arities: "\<And>G l r c. (G,l,r)\<in>set R \<Longrightarrow>
      ho_application_head (ho_erase_pattern l)=HConst c \<Longrightarrow>
      ho_spine_length (ho_erase_pattern l)=arity c"
    and bounds: "\<And>c T. ho_lookup S c=Some T \<Longrightarrow> arity c\<le>length (ho_argument_types T)"
    and closed: "\<And>c xs T u. ho_lookup S c=Some T \<Longrightarrow>
      list_all2 source_candidate (take (arity c) (ho_argument_types T)) xs \<Longrightarrow>
      ho_root_step S V R B (ho_apply_terms (HConst c) xs) u \<Longrightarrow>
      (\<And>d ys U. ((d,ys),(c,xs))\<in>priority_call_order prec priority \<Longrightarrow>
        ho_lookup S d=Some U \<Longrightarrow>
        list_all2 source_candidate (take (arity d) (ho_argument_types U)) ys \<Longrightarrow>
        source_candidate (ho_drop_type (arity d) U) (ho_apply_terms (HConst d) ys)) \<Longrightarrow>
      source_candidate (ho_drop_type (arity c) T) u"
    and symbol: "ho_lookup S c=Some T"
    and args: "list_all2 source_candidate (take (arity c) (ho_argument_types T)) xs"
  shows "source_candidate (ho_drop_type (arity c) T) (ho_apply_terms (HConst c) xs)"
proof -
  have all: "\<forall>T. ho_lookup S (fst p)=Some T \<longrightarrow>
      list_all2 source_candidate (take (arity (fst p)) (ho_argument_types T)) (snd p) \<longrightarrow>
      source_candidate (ho_drop_type (arity (fst p)) T) (ho_apply_terms (HConst (fst p)) (snd p))" for p
  proof (induction p rule: wf_induct[OF wf_priority_call_order[of prec priority]])
    case (1 p)
    obtain c xs where p: "p=(c,xs)" by (cases p) auto
    show ?case
    proof (intro allI impI)
      fix T assume sy: "ho_lookup S (fst p)=Some T"
        and aa: "list_all2 source_candidate (take (arity (fst p)) (ho_argument_types T)) (snd p)"
      have syc: "ho_lookup S c=Some T" and aac: "list_all2 source_candidate (take (arity c) (ho_argument_types T)) xs"
        using sy aa p by simp_all
      have ih: "source_candidate (ho_drop_type (arity d) U) (ho_apply_terms (HConst d) ys)"
        if small: "((d,ys),(c,xs))\<in>priority_call_order prec priority" and ds: "ho_lookup S d=Some U"
          and da: "list_all2 source_candidate (take (arity d) (ho_argument_types U)) ys" for d ys U
        using 1 small ds da p by fastforce
      have typed_args: "list_all2 (\<lambda>A x. ho_typeof S V B x=Some A) (take (arity c) (ho_argument_types T)) xs"
        by (rule list_all2_mono[OF aac]) (rule source.candidate_typed)
      have ty: "ho_typeof S V B (ho_apply_terms (HConst c) xs)=Some (ho_drop_type (arity c) T)"
        by (rule ho_apply_prefix_type[OF _ bounds[OF syc] typed_args]) (use syc in simp)
      have len: "length xs=arity c"
        using list_all2_lengthD[OF aac] bounds[OF syc] by simp
      have bound_xs: "length xs\<le>arity c" using len by arith
      have reducts: "source_candidate (ho_drop_type (arity c) T) u"
        if st: "ho_step S V R B (ho_apply_terms (HConst c) xs) u" for u
      proof -
          have split: "ho_root_step S V R B (ho_apply_terms (HConst c) xs) u \<or>
            (\<exists>ys. ho_arguments_step S V R B xs ys \<and> u=ho_apply_terms (HConst c) ys)"
            by (rule source_call_reduct[where a=arity, OF arities bound_xs st])
          from split show ?thesis
        proof
          assume root: "ho_root_step S V R B (ho_apply_terms (HConst c) xs) u"
          show ?thesis by (rule closed[OF syc aac root ih])
        next
          assume "\<exists>ys. ho_arguments_step S V R B xs ys \<and> u=ho_apply_terms (HConst c) ys"
          then obtain ys where step: "ho_arguments_step S V R B xs ys" and eq: "u=ho_apply_terms (HConst c) ys" by blast
          have small: "((c,ys),(c,xs))\<in>priority_call_order prec priority" by (rule candidate_argument_step_order[OF aac step])
          have ay: "list_all2 source_candidate (take (arity c) (ho_argument_types T)) ys" by (rule candidate_arguments_step[OF aac step])
          show ?thesis unfolding eq by (rule ih[OF small syc ay])
        qed
      qed
      have neu: "ho_saturated_neutral R (ho_apply_terms (HConst c) xs)"
      proof (unfold ho_saturated_neutral_def, intro conjI allI impI)
        fix A t
        show "ho_apply_terms (HConst c) xs\<noteq>HAbs A t"
        proof
          assume eq: "ho_apply_terms (HConst c) xs=HAbs A t"
          have "ho_application_head (ho_apply_terms (HConst c) xs)=HConst c" by simp
          then show False by (simp add: eq)
        qed
      next
        fix G l r assume member: "(G,l,r)\<in>set R"
          and head: "ho_application_head (ho_erase_pattern l)=ho_application_head (ho_apply_terms (HConst c) xs)"
        have hc: "ho_application_head (ho_erase_pattern l)=HConst c" using head by simp
        show "ho_spine_length (ho_erase_pattern l)\<le>ho_spine_length (ho_apply_terms (HConst c) xs)"
          using arities[OF member hc] len by simp
      qed
      have comp: "source_candidate (ho_drop_type (arity c) T) (ho_apply_terms (HConst c) xs)"
        proof (rule source_candidate_saturated[OF ty neu _ reducts])
          fix x assume member: "x\<in>set (ho_spine_arguments (ho_apply_terms (HConst c) xs))"
          have "x\<in>set xs" using member by simp
          then show "\<exists>T. source_candidate T x"
            using aac by (metis list_all2_nthD2 in_set_conv_nth)
        qed
      show "source_candidate (ho_drop_type (arity (fst p)) T) (ho_apply_terms (HConst (fst p)) (snd p))"
        using comp by (simp add: p)
    qed
  qed
  show ?thesis using all[of "(c,xs)"] symbol args by simp
qed

end

end
