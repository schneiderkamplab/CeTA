theory Higher_Order_General_Schema
  imports Higher_Order_Closure_Check
begin

lemma ho_apply_terms_arguments [simp]:
  "ho_spine_arguments (ho_apply_terms f xs)=ho_spine_arguments f@xs"
  by (induction xs arbitrary: f) auto

definition ho_check_schema_rule where
  "ho_check_schema_rule S rank arity fuel rule=(case rule of (G,l,r) \<Rightarrow>
    ho_rule_welltyped S (G,l,r) \<and>
    (case ho_application_head (ho_erase_pattern l) of HConst c \<Rightarrow>
      (case ho_lookup S c of None \<Rightarrow> False | Some T \<Rightarrow>
        list_all2 (\<lambda>A x. ho_typeof S G [] x=Some A)
          (take (arity c) (ho_argument_types T)) (ho_spine_arguments (ho_erase_pattern l)) \<and>
        ho_check_closure S G rank arity c (ho_spine_arguments (ho_erase_pattern l)) fuel (ho_erase_pattern r))
     | _ \<Rightarrow> False))"

definition ho_check_schema_with_arities where
  "ho_check_schema_with_arities S R ranks arities fuel=(length ranks=length S \<and> length arities=length S \<and>
    (\<forall>i<length S. arities!i\<le>length (ho_argument_types (S!i))) \<and>
    ho_zero_arity_rules R \<and> list_all (ho_check_schema_rule S ((!) ranks) ((!) arities) fuel) R)"

definition ho_check_general_schema where
  "ho_check_general_schema S R ranks fuel=ho_check_schema_with_arities S R ranks (map (length \<circ> ho_argument_types) S) fuel"

lemma schema_rule_data:
  assumes "ho_check_schema_rule S rank arity fuel (G,l,r)"
  obtains c T where "ho_rule_welltyped S (G,l,r)"
    "ho_application_head (ho_erase_pattern l)=HConst c" "ho_lookup S c=Some T"
    "list_all2 (\<lambda>A x. ho_typeof S G [] x=Some A) (take (arity c) (ho_argument_types T)) (ho_spine_arguments (ho_erase_pattern l))"
    "ho_check_closure S G rank arity c (ho_spine_arguments (ho_erase_pattern l)) fuel (ho_erase_pattern r)"
  using assms unfolding ho_check_schema_rule_def by (auto split: ho_term.splits option.splits)

context ho_source_neutral_reducibility
begin

theorem general_schema_symbols:
  assumes checked: "list_all (ho_check_schema_rule S rank arity fuel) R"
    and bounds: "\<And>c T. ho_lookup S c=Some T \<Longrightarrow> arity c\<le>length (ho_argument_types T)"
    and inhabited: "\<And>d U b. ho_lookup S d=Some U \<Longrightarrow> b\<in>ho_type_bases U \<Longrightarrow>
      \<exists>x. source.computable (HBase b) x"
    and symbol: "ho_lookup S c=Some T"
  shows "source.computable T (HConst c)"
proof -
  have rule_checked: "ho_check_schema_rule S rank arity fuel (G,l,r)" if "(G,l,r)\<in>set R" for G l r
    using checked that by (simp add: list_all_iff)
  have arities: "ho_spine_length (ho_erase_pattern l)=arity d"
    if member: "(G,l,r)\<in>set R" and head: "ho_application_head (ho_erase_pattern l)=HConst d" for G l r d
  proof -
    obtain e U where he: "ho_application_head (ho_erase_pattern l)=HConst e" and sy: "ho_lookup S e=Some U"
      and args: "list_all2 (\<lambda>A x. ho_typeof S G [] x=Some A) (take (arity e) (ho_argument_types U)) (ho_spine_arguments (ho_erase_pattern l))"
      using schema_rule_data[OF rule_checked[OF member]] by blast
    show ?thesis using list_all2_lengthD[OF args] he head bounds[OF sy] by simp
  qed
  have root_closed: "source.computable (ho_drop_type (arity d) U) u"
    if sy: "ho_lookup S d=Some U"
      and args: "list_all2 source.computable (take (arity d) (ho_argument_types U)) xs"
      and root: "ho_root_step S V R B (ho_apply_terms (HConst d) xs) u"
      and smaller: "\<And>e ys Z. ((e,ys),(d,xs))\<in>call_order rank \<Longrightarrow>
        ho_lookup S e=Some Z \<Longrightarrow> list_all2 source.computable (take (arity e) (ho_argument_types Z)) ys \<Longrightarrow>
        source.computable (ho_drop_type (arity e) Z) (ho_apply_terms (HConst e) ys)"
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
      and closure: "ho_check_closure S G rank arity e (ho_spine_arguments (ho_erase_pattern l)) fuel (ho_erase_pattern r)"
      using schema_rule_data[OF rule_checked[OF member]] by blast
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
    have known: "\<exists>A. source.computable A (ho_subst s 0 q)" if "q\<in>set ?ls" for q
    proof -
      have mem: "ho_subst s 0 q\<in>set xs" using that mapped by force
      show ?thesis using args mem by (metis list_all2_nthD2 in_set_conv_nth)
    qed
    have lt: "ho_typeof S G [] (ho_erase_pattern l)=Some (ho_drop_type (arity d) U)"
      using ho_apply_prefix_type[where S=S and V=G and B="[]" and f="HConst d" and A=U and xs="?ls" and n="arity d"]
        types sy bounds[OF sy] reconstruct ed zu by simp
    have rt: "ho_typeof S G [] (ho_erase_pattern r)=Some (ho_drop_type (arity d) U)"
      using wt lt by (simp add: ho_rule_welltyped_def)
    have rec: "source.computable (ho_drop_type (arity e) Z) (ho_apply_terms (HConst e) ys)"
      if small: "((e,ys),(d,map (ho_subst s 0) ?ls))\<in>call_order rank"
        and sym: "ho_lookup S e=Some Z" and aa: "list_all2 source.computable (take (arity e) (ho_argument_types Z)) ys" for e ys Z
      using smaller[of e ys Z] small sym aa mapped by simp
    have cl: "ho_check_closure S G rank arity d ?ls fuel (ho_erase_pattern r)" using closure ed by simp
    show ?thesis using ho_check_closure_sound[OF cl rt subst bounds known inhabited rec] req by simp
  qed
  show ?thesis
  proof (rule computable_from_prefix_calls)
    show "ho_typeof S V B (HConst c)=Some T" using symbol by simp
    show "arity c\<le>length (ho_argument_types T)" by (rule bounds[OF symbol])
    show "\<exists>x. source.computable (HBase b) x" if "b\<in>ho_type_bases T" for b
      by (rule inhabited[OF symbol that])
    fix xs assume args: "list_all2 source.computable (take (arity c) (ho_argument_types T)) xs"
    show "source.computable (ho_drop_type (arity c) T) (ho_apply_terms (HConst c) xs)"
      by (rule recursive_calls_computable[where rank=rank and arity=arity, OF arities bounds root_closed symbol args])
  qed
qed

end

theorem ho_check_schema_with_arities_sound:
  assumes checked: "ho_check_schema_with_arities S R ranks arities fuel"
  shows "wf ((ho_relation S V R A)\<inverse>)"
proof -
  have zero: "ho_zero_arity_rules R" and rules: "list_all (ho_check_schema_rule S ((!) ranks) ((!) arities) fuel) R"
    and bound: "\<And>c T. ho_lookup S c=Some T \<Longrightarrow> arities!c\<le>length (ho_argument_types T)"
    using checked unfolding ho_check_schema_with_arities_def by (auto split: if_splits)
  have heads: "\<exists>c. ho_application_head (ho_erase_pattern l)=HConst c" if "(G,l,r)\<in>set R" for G l r
    using schema_rule_data[of S "(!) ranks" "(!) arities" fuel G l r] rules that by (auto simp: list_all_iff)
  let ?K = "\<Union>T\<in>set S. ho_type_bases T"
  show ?thesis
  proof (rule ho_symbol_termination[where K="?K", OF zero heads])
    show "finite ?K" by simp
    fix W c T assume available: "\<And>b. b\<in>?K \<Longrightarrow> HBase b\<in>set W"
      and symbol: "ho_lookup S c=Some T"
    interpret src: ho_source_neutral_reducibility S W R "[]"
      by unfold_locales (rule zero, rule heads, assumption)
    have inhabited: "\<exists>x. src.source.computable (HBase b) x"
      if sy: "ho_lookup S d=Some U" and base: "b\<in>ho_type_bases U" for d U b
    proof -
      have "U\<in>set S" using sy by (auto split: if_splits)
      then have "b\<in>?K" using base by blast
      then obtain n where n: "n<length W" and eq: "W!n=HBase b"
        using available by (metis in_set_conv_nth)
      have "src.source.computable (HBase b) (HFree n)"
        by (rule src.source_free_computable) (use n eq in auto)
      then show ?thesis by blast
    qed
    show "ho_source_computable S W R [] T (HConst c)"
      by (rule src.general_schema_symbols[OF rules bound inhabited symbol])
  qed
qed

corollary ho_check_general_schema_sound:
  "ho_check_general_schema S R ranks fuel \<Longrightarrow> wf ((ho_relation S V R A)\<inverse>)"
  unfolding ho_check_general_schema_def by (rule ho_check_schema_with_arities_sound)

end
