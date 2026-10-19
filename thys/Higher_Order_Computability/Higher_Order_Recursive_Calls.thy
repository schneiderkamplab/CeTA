theory Higher_Order_Recursive_Calls
  imports Higher_Order_Call_Order
begin

context ho_source_neutral_reducibility
begin

theorem recursive_calls_computable:
  assumes arities: "\<And>G l r c. (G,l,r)\<in>set R \<Longrightarrow>
      ho_application_head (ho_erase_pattern l)=HConst c \<Longrightarrow>
      ho_spine_length (ho_erase_pattern l)=length (ho_argument_types (S!c))"
    and closed: "\<And>c xs T u. ho_lookup S c=Some T \<Longrightarrow>
      list_all2 source.computable (ho_argument_types T) xs \<Longrightarrow>
      ho_root_step S V R B (ho_apply_terms (HConst c) xs) u \<Longrightarrow>
      (\<And>d ys U. ((d,ys),(c,xs))\<in>call_order rank \<Longrightarrow>
        ho_lookup S d=Some U \<Longrightarrow>
        list_all2 source.computable (ho_argument_types U) ys \<Longrightarrow>
        source.computable (HBase (ho_result_sort U)) (ho_apply_terms (HConst d) ys)) \<Longrightarrow>
      source.computable (HBase (ho_result_sort T)) u"
    and symbol: "ho_lookup S c=Some T"
    and args: "list_all2 source.computable (ho_argument_types T) xs"
  shows "source.computable (HBase (ho_result_sort T)) (ho_apply_terms (HConst c) xs)"
proof -
  have all: "\<forall>T. ho_lookup S (fst p)=Some T \<longrightarrow>
      list_all2 source.computable (ho_argument_types T) (snd p) \<longrightarrow>
      source.computable (HBase (ho_result_sort T)) (ho_apply_terms (HConst (fst p)) (snd p))" for p
  proof (induction p rule: wf_induct[OF wf_call_order[of rank]])
    case (1 p)
    obtain c xs where p: "p=(c,xs)" by (cases p) auto
    show ?case
    proof (intro allI impI)
      fix T assume sy: "ho_lookup S (fst p)=Some T"
        and aa: "list_all2 source.computable (ho_argument_types T) (snd p)"
      have syc: "ho_lookup S c=Some T" and aac: "list_all2 source.computable (ho_argument_types T) xs"
        using sy aa p by simp_all
      have ih: "source.computable (HBase (ho_result_sort U)) (ho_apply_terms (HConst d) ys)"
        if small: "((d,ys),(c,xs))\<in>call_order rank" and ds: "ho_lookup S d=Some U"
          and da: "list_all2 source.computable (ho_argument_types U) ys" for d ys U
        using 1 small ds da p by fastforce
      have typed_args: "list_all2 (\<lambda>A x. ho_typeof S V B x=Some A) (ho_argument_types T) xs"
        by (rule list_all2_mono[OF aac]) (rule source.computable_typed)
      have ty: "ho_typeof S V B (ho_apply_terms (HConst c) xs)=Some (HBase (ho_result_sort T))"
        by (rule ho_apply_terms_type[OF _ typed_args]) (use syc in simp)
      have len: "length xs\<le>length (ho_argument_types (S!c))"
        using list_all2_lengthD[OF aac] syc by (auto split: if_splits)
      have reducts: "source.computable (HBase (ho_result_sort T)) u"
        if st: "ho_step S V R B (ho_apply_terms (HConst c) xs) u" for u
      proof -
        from source_call_reduct[where a="\<lambda>c. length (ho_argument_types (S!c))", OF arities len st] show ?thesis
        proof
          assume root: "ho_root_step S V R B (ho_apply_terms (HConst c) xs) u"
          show ?thesis by (rule closed[OF syc aac root ih])
        next
          assume "\<exists>ys. ho_arguments_step S V R B xs ys \<and> u=ho_apply_terms (HConst c) ys"
          then obtain ys where step: "ho_arguments_step S V R B xs ys" and eq: "u=ho_apply_terms (HConst c) ys" by blast
          have small: "((c,ys),(c,xs))\<in>call_order rank" by (rule argument_step_call_order[OF aac step])
          have ay: "list_all2 source.computable (ho_argument_types T) ys" by (rule computable_arguments_step[OF aac step])
          show ?thesis unfolding eq by (rule ih[OF small syc ay])
        qed
      qed
      have sn: "source.strongly_normalizing (ho_apply_terms (HConst c) xs)"
        by (rule accp.accI) (rule source.computable_SN[OF reducts])
      show "source.computable (HBase (ho_result_sort T)) (ho_apply_terms (HConst (fst p)) (snd p))"
        using ty sn by (simp add: p)
    qed
  qed
  show ?thesis using all[of "(c,xs)"] symbol args by simp
qed

end

end
