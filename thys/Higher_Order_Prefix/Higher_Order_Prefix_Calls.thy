theory Higher_Order_Prefix_Calls
  imports "Higher_Order_Blocked.Higher_Order_Blocked_Schema"
begin

text \<open>Unlike uniform-arity call inversion, this accounts for a source rule
firing at any prefix of a fully applied call. No rewriting obligation is
discarded by padding a rule with arguments.\<close>

context ho_source_neutral_reducibility
begin

lemma source_call_prefix_reduct:
  assumes step: "ho_step S V R B (ho_apply_terms (HConst c) xs) u"
  shows "(\<exists>ps qs v. xs=ps@qs \<and>
      ho_root_step S V R B (ho_apply_terms (HConst c) ps) v \<and>
      u=ho_apply_terms v qs) \<or>
    (\<exists>ys. ho_arguments_step S V R B xs ys \<and>
      u=ho_apply_terms (HConst c) ys)"
  using step
proof (induction xs arbitrary: u rule: rev_induct)
  case Nil
  have st: "ho_step S V R B (HConst c) u" using Nil.prems by simp
  have root: "ho_root_step S V R B (HConst c) u"
    using st by (cases rule: ho_step.cases) (auto simp: ho_root_step_def)
  show ?case using root by auto
next
  case (snoc x xs)
  let ?f = "ho_apply_terms (HConst c) xs"
  have noabs: "?f\<noteq>HAbs A t" for A t
  proof
    assume eq: "?f=HAbs A t"
    have "ho_application_head ?f=HConst c" by simp
    then show False by (simp add: eq)
  qed
  have st: "ho_step S V R B (HApp ?f x) u" using snoc.prems by simp
  have split: "ho_root_step S V R B (HApp ?f x) u \<or>
      (\<exists>g. ho_step S V R B ?f g \<and> u=HApp g x) \<or>
      (\<exists>y. ho_step S V R B x y \<and> u=HApp ?f y)"
    using st by (cases rule: ho_step.cases) (auto simp: ho_root_step_def noabs)
  from split show ?case
  proof (elim disjE exE conjE)
    assume root: "ho_root_step S V R B (HApp ?f x) u"
    have "ho_root_step S V R B (ho_apply_terms (HConst c) (xs@[x])) u"
      using root by simp
    then show ?thesis by (metis append_Nil2 ho_apply_terms_Nil)
  next
    fix g assume fg: "ho_step S V R B ?f g" and eq: "u=HApp g x"
    from snoc.IH[OF fg] show ?thesis
    proof
      assume "\<exists>ps qs v. xs=ps@qs \<and>
        ho_root_step S V R B (ho_apply_terms (HConst c) ps) v \<and>
        g=ho_apply_terms v qs"
      then obtain ps qs v where ps: "xs=ps@qs"
        and root: "ho_root_step S V R B (ho_apply_terms (HConst c) ps) v"
        and g: "g=ho_apply_terms v qs" by blast
      have "xs@[x]=ps@(qs@[x])" using ps by simp
      moreover have "u=ho_apply_terms v (qs@[x])" using eq g by simp
      ultimately show ?thesis using root by blast
    next
      assume "\<exists>ys. ho_arguments_step S V R B xs ys \<and>
        g=ho_apply_terms (HConst c) ys"
      then obtain ys where args: "ho_arguments_step S V R B xs ys"
        and g: "g=ho_apply_terms (HConst c) ys" by blast
      have "ho_arguments_step S V R B (xs@[x]) (ys@[x])"
        using args unfolding ho_arguments_step_def by fastforce
      then show ?thesis using eq g by auto
    qed
  next
    fix y assume xy: "ho_step S V R B x y" and eq: "u=HApp ?f y"
    have "ho_arguments_step S V R B (xs@[x]) (xs@[y])"
      unfolding ho_arguments_step_def using xy by blast
    then show ?thesis using eq by auto
  qed
qed

end

context ho_source_accessible_reducibility
begin

theorem candidate_prefix_recursive_calls_computable:
  assumes arities: "\<And>G l r c. (G,l,r)\<in>set R \<Longrightarrow>
      ho_application_head (ho_erase_pattern l)=HConst c \<Longrightarrow>
      ho_spine_length (ho_erase_pattern l)\<le>arity c"
    and bounds: "\<And>c T. ho_lookup S c=Some T \<Longrightarrow> arity c\<le>length (ho_argument_types T)"
    and closed: "\<And>c xs T ps qs v. ho_lookup S c=Some T \<Longrightarrow>
      list_all2 source_candidate (take (arity c) (ho_argument_types T)) xs \<Longrightarrow>
      xs=ps@qs \<Longrightarrow>
      ho_root_step S V R B (ho_apply_terms (HConst c) ps) v \<Longrightarrow>
      (\<And>d ys U. ((d,ys),(c,xs))\<in>priority_call_order prec priority \<Longrightarrow>
        ho_lookup S d=Some U \<Longrightarrow>
        list_all2 source_candidate (take (arity d) (ho_argument_types U)) ys \<Longrightarrow>
        source_candidate (ho_drop_type (arity d) U) (ho_apply_terms (HConst d) ys)) \<Longrightarrow>
      source_candidate (ho_drop_type (arity c) T) (ho_apply_terms v qs)"
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
      have syc: "ho_lookup S c=Some T"
        and aac: "list_all2 source_candidate (take (arity c) (ho_argument_types T)) xs"
        using sy aa p by simp_all
      have ih: "source_candidate (ho_drop_type (arity d) U) (ho_apply_terms (HConst d) ys)"
        if small: "((d,ys),(c,xs))\<in>priority_call_order prec priority"
          and ds: "ho_lookup S d=Some U"
          and da: "list_all2 source_candidate (take (arity d) (ho_argument_types U)) ys" for d ys U
        using 1 small ds da p by fastforce
      have typed_args: "list_all2 (\<lambda>A x. ho_typeof S V B x=Some A)
          (take (arity c) (ho_argument_types T)) xs"
        by (rule list_all2_mono[OF aac]) (rule source.candidate_typed)
      have ty: "ho_typeof S V B (ho_apply_terms (HConst c) xs)=Some (ho_drop_type (arity c) T)"
        by (rule ho_apply_prefix_type[OF _ bounds[OF syc] typed_args]) (use syc in simp)
      have len: "length xs=arity c"
        using list_all2_lengthD[OF aac] bounds[OF syc] by simp
      have reducts: "source_candidate (ho_drop_type (arity c) T) u"
        if st: "ho_step S V R B (ho_apply_terms (HConst c) xs) u" for u
      proof -
        from source_call_prefix_reduct[OF st] show ?thesis
        proof
          assume "\<exists>ps qs v. xs=ps@qs \<and>
            ho_root_step S V R B (ho_apply_terms (HConst c) ps) v \<and> u=ho_apply_terms v qs"
          then obtain ps qs v where xs: "xs=ps@qs"
            and root: "ho_root_step S V R B (ho_apply_terms (HConst c) ps) v"
            and u: "u=ho_apply_terms v qs" by blast
          show ?thesis unfolding u by (rule closed[OF syc aac xs root ih])
        next
          assume "\<exists>ys. ho_arguments_step S V R B xs ys \<and> u=ho_apply_terms (HConst c) ys"
          then obtain ys where step: "ho_arguments_step S V R B xs ys"
            and eq: "u=ho_apply_terms (HConst c) ys" by blast
          have small: "((c,ys),(c,xs))\<in>priority_call_order prec priority"
            by (rule candidate_argument_step_order[OF aac step])
          have ay: "list_all2 source_candidate (take (arity c) (ho_argument_types T)) ys"
            by (rule candidate_arguments_step[OF aac step])
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
