theory Higher_Order_Delegated_Schema
  imports Higher_Order_Delegation_Partition
begin

text \<open>The closure checker is unchanged. Only rules headed by a
separately established computable symbol are exempted from its rule checks.
The original source relation and all binder/type contexts remain in scope.\<close>

context ho_source_accessible_reducibility
begin

theorem functional_access_schema_symbols_with_known:
  assumes checked: "\<And>G l r d. (G,l,r)\<in>set R \<Longrightarrow>
      ho_application_head (ho_erase_pattern l)=HConst d \<Longrightarrow> d\<notin>K \<Longrightarrow>
      ho_check_functional_access_schema_rule S R rank prec priority arity fuel (G,l,r)"
    and arities: "\<And>G l r d. (G,l,r)\<in>set R \<Longrightarrow>
      ho_application_head (ho_erase_pattern l)=HConst d \<Longrightarrow>
      ho_spine_length (ho_erase_pattern l)=arity d"
    and known_calls: "\<And>d xs U. d\<in>K \<Longrightarrow> ho_lookup S d=Some U \<Longrightarrow>
      list_all2 source_candidate (take (arity d) (ho_argument_types U)) xs \<Longrightarrow>
      source_candidate (ho_drop_type (arity d) U) (ho_apply_terms (HConst d) xs)"
    and bounds: "\<And>c T. ho_lookup S c=Some T \<Longrightarrow> arity c\<le>length (ho_argument_types T)"
    and inhabited: "\<And>d U b. ho_lookup S d=Some U \<Longrightarrow> b\<in>ho_type_bases U \<Longrightarrow>
      \<exists>x. source_candidate (HBase b) x"
    and rhs_inhabited: "\<And>G l r T. (G,l,r)\<in>set R \<Longrightarrow>
      T\<in>ho_binder_types (ho_erase_pattern r) \<Longrightarrow> \<exists>x. source_candidate T x"
    and lhs_inhabited: "\<And>G l r T. (G,l,r)\<in>set R \<Longrightarrow>
      T\<in>ho_binder_types (ho_erase_pattern l) \<Longrightarrow> \<exists>x. source_candidate T x"
    and symbol: "ho_lookup S c=Some T"
  shows "source_candidate T (HConst c)"
proof -
  have root_closed: "source_candidate (ho_drop_type (arity d) U) u"
    if not_known: "d\<notin>K" and sy: "ho_lookup S d=Some U"
      and args: "list_all2 source_candidate (take (arity d) (ho_argument_types U)) xs"
      and root: "ho_root_step S V R B (ho_apply_terms (HConst d) xs) u"
      and smaller: "\<And>e ys Z. ((e,ys),(d,xs))\<in>priority_call_order prec priority \<Longrightarrow>
        ho_lookup S e=Some Z \<Longrightarrow> list_all2 source_candidate (take (arity e) (ho_argument_types Z)) ys \<Longrightarrow>
        source_candidate (ho_drop_type (arity e) Z) (ho_apply_terms (HConst e) ys)"
    for d xs U u
  proof -
    obtain G l r s where member: "(G,l,r)\<in>set R" and wt: "ho_rule_welltyped S (G,l,r)"
      and subst: "ho_typed_subst S V B G s"
      and li: "ho_instantiate s 0 l=Some (ho_apply_terms (HConst d) xs)"
      and ri: "ho_instantiate s 0 r=Some u"
      using root unfolding ho_root_step_def by blast
    have lhs_head: "ho_application_head (ho_erase_pattern l)=HConst d"
      using rule_instance_head_spine(1)[OF member li] by simp
    have rule_checked: "ho_check_functional_access_schema_rule S R rank prec priority arity fuel (G,l,r)"
      by (rule checked[OF member lhs_head not_known])
    obtain e Z where head: "ho_application_head (ho_erase_pattern l)=HConst e"
      and es: "ho_lookup S e=Some Z"
      and types: "list_all2 (\<lambda>A x. ho_typeof S G [] x=Some A) (take (arity e) (ho_argument_types Z)) (ho_spine_arguments (ho_erase_pattern l))"
      and closure: "ho_check_functional_access_closure S G R rank prec priority arity e (ho_spine_arguments (ho_erase_pattern l)) fuel [] (ho_erase_pattern r)"
      using functional_access_schema_rule_data[OF rule_checked] by blast
    have ed: "e=d" using rule_instance_head_spine(1)[OF member li] head by simp
    have zu: "Z=U" using es sy ed by simp
    let ?ls = "ho_spine_arguments (ho_erase_pattern l)"
    have zl: "ho_zero_arity_pattern l" and zr: "ho_zero_arity_pattern r"
      using zero member unfolding ho_zero_arity_rules_def by auto
    have leq: "ho_subst s 0 (ho_erase_pattern l)=ho_apply_terms (HConst d) xs"
      using li ho_zero_arity_instantiate[OF zl, of s 0] by simp
    have req: "ho_subst s 0 (ho_erase_pattern r)=u"
      using ri ho_zero_arity_instantiate[OF zr, of s 0] by simp
    have reconstruct: "ho_apply_terms (HConst d) ?ls=ho_erase_pattern l"
      using ho_spine_reconstruct[of "ho_erase_pattern l"] head ed by simp
    have mapped: "map (ho_subst s 0) ?ls=xs"
    proof -
      have "ho_apply_terms (HConst d) (map (ho_subst s 0) ?ls)=ho_apply_terms (HConst d) xs"
        using ho_subst_apply_terms[of s 0 "HConst d" ?ls] reconstruct leq by simp
      then show ?thesis by (metis ho_apply_terms_arguments ho_spine_arguments.simps(4) append_Nil)
    qed
    have known: "\<exists>A. source_candidate A (ho_subst s 0 q)" if "q\<in>set ?ls" for q
    proof -
      have mem: "ho_subst s 0 q\<in>set xs" using that mapped by force
      show ?thesis using args mem by (metis list_all2_nthD2 in_set_conv_nth)
    qed
    have lt: "ho_typeof S G [] (ho_erase_pattern l)=Some (ho_drop_type (arity d) U)"
      using ho_apply_prefix_type[where S=S and V=G and B="[]" and f="HConst d" and A=U and xs="?ls" and n="arity d"]
        types sy bounds[OF sy] reconstruct ed zu by simp
    have rt: "ho_typeof S G [] (ho_erase_pattern r)=Some (ho_drop_type (arity d) U)"
      using wt lt by (simp add: ho_rule_welltyped_def)
    have rec: "source_candidate (ho_drop_type (arity e) Z) (ho_apply_terms (HConst e) ys)"
      if small: "((e,ys),(d,map (ho_subst s 0) ?ls))\<in>priority_call_order prec priority"
        and sym: "ho_lookup S e=Some Z" and aa: "list_all2 source_candidate (take (arity e) (ho_argument_types Z)) ys" for e ys Z
      using smaller[of e ys Z] small sym aa mapped by simp
    have cl: "ho_check_functional_access_closure S G R rank prec priority arity d ?ls fuel [] (ho_erase_pattern r)" using closure ed by simp
    have closed: "ho_bound_closed 0 q" if "q\<in>set ?ls" for q
    proof -
      have "list_all (ho_bound_closed 0) ?ls" using types
        by (induction rule: list_all2_induct) (auto dest: ho_typeof_bound_closed)
      then show ?thesis using that by (simp add: list_all_iff)
    qed
    have lhs_typed: "\<exists>T. ho_typeof S G [] q=Some T" if "q\<in>set ?ls" for q
    proof -
      have "list_all (\<lambda>x. \<exists>T. ho_typeof S G [] x=Some T) ?ls"
        using types by (induction rule: list_all2_induct) auto
      then show ?thesis using that by (simp add: list_all_iff)
    qed
    have lhsi: "\<exists>x. source_candidate T x" if "q\<in>set ?ls" "T\<in>ho_binder_types q" for q T
      using lhs_inhabited[OF member] ho_spine_binder_types[OF that(1)] that(2) by blast
    have result: "source_candidate (ho_drop_type (arity d) U) (ho_open s HBound 0 (ho_erase_pattern r))"
      by (rule ho_check_functional_access_closure_sound[where b=HBound and prec=prec and priority=priority and arity=arity,
        OF cl rt subst _ closed rhs_inhabited[OF member] bounds lhs_typed lhsi known inhabited rec]) simp
    have closed_rhs: "ho_bound_closed 0 (ho_erase_pattern r)"
      using ho_typeof_bound_closed[OF rt] by simp
    show ?thesis using result ho_open_closed[OF closed_rhs, of s HBound] req by simp
  qed
  show ?thesis
  proof (rule candidate_from_prefix_calls)
    show "ho_typeof S V B (HConst c)=Some T" using symbol by simp
    show "arity c\<le>length (ho_argument_types T)" by (rule bounds[OF symbol])
    show "\<exists>x. source_candidate (HBase b) x" if "b\<in>ho_type_bases T" for b
      by (rule inhabited[OF symbol that])
    fix xs assume args: "list_all2 source_candidate (take (arity c) (ho_argument_types T)) xs"
    show "source_candidate (ho_drop_type (arity c) T) (ho_apply_terms (HConst c) xs)"
      by (rule ordered_recursive_calls_with_known[where Q="priority_call_order prec priority"
            and arity=arity and K=K,
            OF wf_priority_call_order candidate_argument_step_order arities bounds
               known_calls root_closed symbol args])
  qed
qed

end
end

