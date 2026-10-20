theory Higher_Order_Guarded_Schema
  imports Higher_Order_Guarded_Closure
begin

definition ho_check_guarded_schema_rule where
  "ho_check_guarded_schema_rule F S R sorts prec priority arity fuel rule=(case rule of (G,l,r) \<Rightarrow>
    ho_rule_welltyped S (G,l,r) \<and>
    (case ho_application_head (ho_erase_pattern l) of HConst c \<Rightarrow>
      (case ho_lookup S c of None \<Rightarrow> False | Some T \<Rightarrow>
        list_all2 (\<lambda>A x. ho_typeof S G [] x=Some A)
          (take (arity c) (ho_argument_types T)) (ho_spine_arguments (ho_erase_pattern l)) \<and>
        ho_check_guarded_closure F S G R sorts prec priority arity c (ho_spine_arguments (ho_erase_pattern l)) fuel [] (ho_erase_pattern r))
     | _ \<Rightarrow> False))"

definition ho_check_guarded_schema where
  "ho_check_guarded_schema F S R ranks arities priorities sorts fuel=(ho_guard_rules F R \<and> length ranks=length S \<and> length arities=length S \<and>
    list_all (\<lambda>n. n\<le>length priorities) arities \<and>
    (\<forall>i<length S. arities!i\<le>length (ho_argument_types (S!i))) \<and>
    ho_zero_arity_rules R \<and> list_all (ho_check_guarded_schema_rule F S R (\<lambda>b. if b<length sorts then sorts!b else 0) ((!) ranks) ((!) priorities) ((!) arities) fuel) R)"

lemma guarded_schema_rule_data:
  assumes "ho_check_guarded_schema_rule F S R sorts prec priority arity fuel (G,l,r)"
  obtains c T where "ho_rule_welltyped S (G,l,r)"
    "ho_application_head (ho_erase_pattern l)=HConst c" "ho_lookup S c=Some T"
    "list_all2 (\<lambda>A x. ho_typeof S G [] x=Some A) (take (arity c) (ho_argument_types T)) (ho_spine_arguments (ho_erase_pattern l))"
    "ho_check_guarded_closure F S G R sorts prec priority arity c (ho_spine_arguments (ho_erase_pattern l)) fuel [] (ho_erase_pattern r)"
  using assms unfolding ho_check_guarded_schema_rule_def by (auto split: ho_term.splits option.splits)

context ho_source_accessible_reducibility
begin

theorem guarded_schema_symbols:
  assumes checked: "list_all (ho_check_guarded_schema_rule F S R rank prec priority arity fuel) R"
    and bounds: "\<And>c T. ho_lookup S c=Some T \<Longrightarrow> arity c\<le>length (ho_argument_types T)"
    and inhabited: "\<And>d U b. ho_lookup S d=Some U \<Longrightarrow> b\<in>ho_type_bases U \<Longrightarrow>
      \<exists>x. source_candidate (HBase b) x"
    and rhs_inhabited: "\<And>G l r T. (G,l,r)\<in>set R \<Longrightarrow>
      T\<in>ho_binder_types (ho_erase_pattern r) \<Longrightarrow> \<exists>x. source_candidate T x"
    and lhs_inhabited: "\<And>G l r T. (G,l,r)\<in>set R \<Longrightarrow>
      T\<in>ho_binder_types (ho_erase_pattern l) \<Longrightarrow> \<exists>x. source_candidate T x"
    and symbol: "ho_lookup S c=Some T"
    and guard_rules: "ho_guard_rules F R"
  shows "source_candidate T (HConst c)"
proof -
  have rule_checked: "ho_check_guarded_schema_rule F S R rank prec priority arity fuel (G,l,r)" if "(G,l,r)\<in>set R" for G l r
    using checked that by (simp add: list_all_iff)
  have arities: "ho_spine_length (ho_erase_pattern l)=arity d"
    if member: "(G,l,r)\<in>set R" and head: "ho_application_head (ho_erase_pattern l)=HConst d" for G l r d
  proof -
    obtain e U where he: "ho_application_head (ho_erase_pattern l)=HConst e" and sy: "ho_lookup S e=Some U"
      and args: "list_all2 (\<lambda>A x. ho_typeof S G [] x=Some A) (take (arity e) (ho_argument_types U)) (ho_spine_arguments (ho_erase_pattern l))"
      using guarded_schema_rule_data[OF rule_checked[OF member]] by blast
    show ?thesis using list_all2_lengthD[OF args] he head bounds[OF sy] by simp
  qed
  have root_closed: "source_candidate (ho_drop_type (arity d) U) u"
    if sy: "ho_lookup S d=Some U"
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
    obtain e Z where head: "ho_application_head (ho_erase_pattern l)=HConst e"
      and es: "ho_lookup S e=Some Z"
      and types: "list_all2 (\<lambda>A x. ho_typeof S G [] x=Some A) (take (arity e) (ho_argument_types Z)) (ho_spine_arguments (ho_erase_pattern l))"
      and closure: "ho_check_guarded_closure F S G R rank prec priority arity e (ho_spine_arguments (ho_erase_pattern l)) fuel [] (ho_erase_pattern r)"
      using guarded_schema_rule_data[OF rule_checked[OF member]] by blast
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
    have cl: "ho_check_guarded_closure F S G R rank prec priority arity d ?ls fuel [] (ho_erase_pattern r)" using closure ed by simp
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
      by (rule ho_check_guarded_closure_sound[where b=HBound and prec=prec and priority=priority and arity=arity,
        OF cl rt subst _ closed rhs_inhabited[OF member] bounds lhs_typed lhsi known inhabited rec arities guard_rules]) simp
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
      by (rule candidate_recursive_calls_computable[where prec=prec and priority=priority and arity=arity, OF arities bounds root_closed symbol args])
  qed
qed

end
theorem ho_check_guarded_schema_sound:
  assumes checked: "ho_check_guarded_schema F S R ranks arities priorities sorts fuel"
  shows "wf ((ho_relation S V R A)\<inverse>)"
proof -
  have guard_rules: "ho_guard_rules F R" and zero: "ho_zero_arity_rules R" and rules: "list_all (ho_check_guarded_schema_rule F S R (\<lambda>b. if b<length sorts then sorts!b else 0) ((!) ranks) ((!) priorities) ((!) arities) fuel) R"
    and bound: "\<And>c T. ho_lookup S c=Some T \<Longrightarrow> arities!c\<le>length (ho_argument_types T)"
    using checked unfolding ho_check_guarded_schema_def by (auto split: if_splits)
  have heads: "\<exists>c. ho_application_head (ho_erase_pattern l)=HConst c" if "(G,l,r)\<in>set R" for G l r
    using guarded_schema_rule_data[of F S R "(\<lambda>b. if b<length sorts then sorts!b else 0)" "(!) ranks" "(!) priorities" "(!) arities" fuel G l r] rules that by (auto simp: list_all_iff)
  let ?K = "(\<Union>T\<in>set S. ho_type_bases T) \<union>
    (\<Union>(G,l,r)\<in>set R. \<Union>T\<in>ho_binder_types (ho_erase_pattern r). ho_type_bases T) \<union>
    (\<Union>(G,l,r)\<in>set R. \<Union>T\<in>ho_binder_types (ho_erase_pattern l). ho_type_bases T)"
  show ?thesis
  proof (rule ho_candidate_symbol_termination[where K="?K" and rank="\<lambda>b. if b<length sorts then sorts!b else 0", OF zero heads])
    show "finite ?K" by (auto split: prod.splits)
    fix W c T assume available: "\<And>b. b\<in>?K \<Longrightarrow> HBase b\<in>set W"
      and symbol: "ho_lookup S c=Some T"
    interpret src: ho_source_accessible_reducibility S W R "[]" "(\<lambda>b. if b<length sorts then sorts!b else 0)"
      by unfold_locales (rule zero, rule heads, assumption)
    have inhabited: "\<exists>x. src.source_candidate (HBase b) x"
      if sy: "ho_lookup S d=Some U" and base: "b\<in>ho_type_bases U" for d U b
    proof -
      have "U\<in>set S" using sy by (auto split: if_splits)
      then have "b\<in>?K" using base by blast
      then obtain n where n: "n<length W" and eq: "W!n=HBase b"
        using available by (metis in_set_conv_nth)
      have "src.source_candidate (HBase b) (HFree n)"
        by (rule src.source_candidate_free) (use n eq in auto)
      then show ?thesis by blast
    qed
    have rhs_inhabited: "\<exists>x. src.source_candidate Z x"
      if member: "(G,l,r)\<in>set R" and bt: "Z\<in>ho_binder_types (ho_erase_pattern r)" for G l r Z
    proof (rule src.source_candidate_type_inhabited)
      fix b assume base: "b\<in>ho_type_bases Z"
      have entry: "b\<in>(\<Union>T\<in>ho_binder_types (ho_erase_pattern r). ho_type_bases T)"
        using bt base by blast
      have rhs: "b\<in>(\<Union>(G,l,r)\<in>set R. \<Union>T\<in>ho_binder_types (ho_erase_pattern r). ho_type_bases T)"
        by (rule UN_I[OF member]) (use entry in simp)
      have "b\<in>?K" using rhs by blast
      then obtain n where n: "n<length W" and eq: "W!n=HBase b"
        using available by (metis in_set_conv_nth)
      have "src.source_candidate (HBase b) (HFree n)"
        by (rule src.source_candidate_free) (use n eq in auto)
      then show "\<exists>x. src.source_candidate (HBase b) x" by blast
    qed
    have lhs_inhabited: "\<exists>x. src.source_candidate Z x"
      if member: "(G,l,r)\<in>set R" and bt: "Z\<in>ho_binder_types (ho_erase_pattern l)" for G l r Z
    proof (rule src.source_candidate_type_inhabited)
      fix b assume base: "b\<in>ho_type_bases Z"
      have entry: "b\<in>(\<Union>T\<in>ho_binder_types (ho_erase_pattern l). ho_type_bases T)"
        using bt base by blast
      have rhs: "b\<in>(\<Union>(G,l,r)\<in>set R. \<Union>T\<in>ho_binder_types (ho_erase_pattern l). ho_type_bases T)"
        by (rule UN_I[OF member]) (use entry in simp)
      have "b\<in>?K" using rhs by blast
      then obtain n where n: "n<length W" and eq: "W!n=HBase b"
        using available by (metis in_set_conv_nth)
      have "src.source_candidate (HBase b) (HFree n)"
        by (rule src.source_candidate_free) (use n eq in auto)
      then show "\<exists>x. src.source_candidate (HBase b) x" by blast
    qed
    show "ho_source_candidate_computable S W R [] (\<lambda>b. if b<length sorts then sorts!b else 0) T (HConst c)"
      by (rule src.guarded_schema_symbols[OF rules bound inhabited rhs_inhabited lhs_inhabited symbol guard_rules])
  qed
qed

end
