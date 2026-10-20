theory Higher_Order_Prefix_Schema
  imports Higher_Order_Prefix_Substitution
begin

definition ho_check_prefix_schema_rule where
  "ho_check_prefix_schema_rule S R sorts prec priority arity fuel rule =
    (case rule of (G,l,r) \<Rightarrow>
      ho_rule_welltyped S (G,l,r) \<and>
      (case ho_application_head (ho_erase_pattern l) of HConst c \<Rightarrow>
        (case ho_lookup S c of None \<Rightarrow> False | Some T \<Rightarrow>
          (let ls=ho_spine_arguments (ho_erase_pattern l);
               Ds=drop (length ls) (take (arity c) (ho_argument_types T));
               vs=ho_prefix_variables G Ds;
               H=G@Ds;
               rs=ho_apply_terms (ho_erase_pattern r) vs
           in length ls\<le>arity c \<and>
              list_all2 (\<lambda>A x. ho_typeof S H [] x=Some A)
                (take (arity c) (ho_argument_types T)) (ls@vs) \<and>
              ho_typeof S H [] rs=Some (ho_drop_type (arity c) T) \<and>
              ho_check_functional_access_closure S H R sorts prec priority arity c
                (ls@vs) fuel [] rs))
       | _ \<Rightarrow> False))"

definition ho_check_prefix_schema where
  "ho_check_prefix_schema S R ranks arities priorities sorts fuel =
    (length ranks=length S \<and> length arities=length S \<and>
     list_all (\<lambda>n. n\<le>length priorities) arities \<and>
     (\<forall>i<length S. arities!i\<le>length (ho_argument_types (S!i))) \<and>
     ho_zero_arity_rules R \<and>
     list_all (ho_check_prefix_schema_rule S R
       (\<lambda>b. if b<length sorts then sorts!b else 0)
       ((!) ranks) ((!) priorities) ((!) arities) fuel) R)"

lemma prefix_schema_rule_data:
  assumes "ho_check_prefix_schema_rule S R sorts prec priority arity fuel (G,l,r)"
  obtains c T where
    "ho_rule_welltyped S (G,l,r)"
    "ho_application_head (ho_erase_pattern l)=HConst c"
    "ho_lookup S c=Some T"
    "length (ho_spine_arguments (ho_erase_pattern l))\<le>arity c"
    "let ls=ho_spine_arguments (ho_erase_pattern l);
         Ds=drop (length ls) (take (arity c) (ho_argument_types T));
         vs=ho_prefix_variables G Ds in
       list_all2 (\<lambda>A x. ho_typeof S (G@Ds) [] x=Some A)
         (take (arity c) (ho_argument_types T)) (ls@vs) \<and>
       ho_typeof S (G@Ds) [] (ho_apply_terms (ho_erase_pattern r) vs)=Some (ho_drop_type (arity c) T) \<and>
       ho_check_functional_access_closure S (G@Ds) R sorts prec priority arity c
         (ls@vs) fuel [] (ho_apply_terms (ho_erase_pattern r) vs)"
  using assms unfolding ho_check_prefix_schema_rule_def
  by (auto simp: Let_def split: ho_term.splits option.splits)

lemma ho_prefix_variables_binders:
  assumes "v\<in>set (ho_prefix_variables G Ds)"
  shows "ho_binder_types v={}"
  using assms by (auto simp: ho_prefix_variables_def)

lemma ho_binders_apply_terms:
  "ho_binder_types (ho_apply_terms t xs)=ho_binder_types t \<union> (\<Union>x\<in>set xs. ho_binder_types x)"
  by (induction xs arbitrary: t) auto

context ho_source_accessible_reducibility
begin

lemma prefix_schema_root_closed:
  assumes checked: "list_all (ho_check_prefix_schema_rule S R rank prec priority arity fuel) R"
    and bounds: "\<And>c T. ho_lookup S c=Some T \<Longrightarrow> arity c\<le>length (ho_argument_types T)"
    and inhabited: "\<And>d U b. ho_lookup S d=Some U \<Longrightarrow> b\<in>ho_type_bases U \<Longrightarrow>
      \<exists>x. source_candidate (HBase b) x"
    and rhs_inhabited: "\<And>G l r T. (G,l,r)\<in>set R \<Longrightarrow>
      T\<in>ho_binder_types (ho_erase_pattern r) \<Longrightarrow> \<exists>x. source_candidate T x"
    and lhs_inhabited: "\<And>G l r T. (G,l,r)\<in>set R \<Longrightarrow>
      T\<in>ho_binder_types (ho_erase_pattern l) \<Longrightarrow> \<exists>x. source_candidate T x"
    and sy: "ho_lookup S d=Some U"
    and args: "list_all2 source_candidate (take (arity d) (ho_argument_types U)) xs"
    and split: "xs=ps@qs"
    and root: "ho_root_step S V R B (ho_apply_terms (HConst d) ps) v"
    and smaller: "\<And>e ys Z. ((e,ys),(d,xs))\<in>priority_call_order prec priority \<Longrightarrow>
      ho_lookup S e=Some Z \<Longrightarrow>
      list_all2 source_candidate (take (arity e) (ho_argument_types Z)) ys \<Longrightarrow>
      source_candidate (ho_drop_type (arity e) Z) (ho_apply_terms (HConst e) ys)"
  shows "source_candidate (ho_drop_type (arity d) U) (ho_apply_terms v qs)"
proof -
  obtain G l r s where member: "(G,l,r)\<in>set R"
    and wt: "ho_rule_welltyped S (G,l,r)"
    and subst: "ho_typed_subst S V B G s"
    and li: "ho_instantiate s 0 l=Some (ho_apply_terms (HConst d) ps)"
    and ri: "ho_instantiate s 0 r=Some v"
    using root unfolding ho_root_step_def by blast
  have rule_checked: "ho_check_prefix_schema_rule S R rank prec priority arity fuel (G,l,r)"
    using checked member by (simp add: list_all_iff)
  obtain e Z where head: "ho_application_head (ho_erase_pattern l)=HConst e"
    and es: "ho_lookup S e=Some Z"
    and data: "let ls=ho_spine_arguments (ho_erase_pattern l);
         Ds=drop (length ls) (take (arity e) (ho_argument_types Z));
         vs=ho_prefix_variables G Ds in
       list_all2 (\<lambda>A x. ho_typeof S (G@Ds) [] x=Some A)
         (take (arity e) (ho_argument_types Z)) (ls@vs) \<and>
       ho_typeof S (G@Ds) [] (ho_apply_terms (ho_erase_pattern r) vs)=Some (ho_drop_type (arity e) Z) \<and>
       ho_check_functional_access_closure S (G@Ds) R rank prec priority arity e
         (ls@vs) fuel [] (ho_apply_terms (ho_erase_pattern r) vs)"
    using prefix_schema_rule_data[OF rule_checked] by blast
  have ed: "e=d" using rule_instance_head_spine(1)[OF member li] head by simp
  have zu: "Z=U" using es sy ed by simp
  let ?ls = "ho_spine_arguments (ho_erase_pattern l)"
  let ?Ds = "drop (length ?ls) (take (arity d) (ho_argument_types U))"
  let ?vs = "ho_prefix_variables G ?Ds"
  let ?s = "ho_prefix_subst G s qs"
  let ?lhs = "?ls@?vs"
  let ?rhs = "ho_apply_terms (ho_erase_pattern r) ?vs"
  have types: "list_all2 (\<lambda>A x. ho_typeof S (G@?Ds) [] x=Some A)
      (take (arity d) (ho_argument_types U)) ?lhs"
    and rt: "ho_typeof S (G@?Ds) [] ?rhs=Some (ho_drop_type (arity d) U)"
    and cl: "ho_check_functional_access_closure S (G@?Ds) R rank prec priority arity d ?lhs fuel [] ?rhs"
    using data ed zu by (simp_all add: Let_def)
  obtain A where lt0: "ho_typeof S G [] (ho_erase_pattern l)=Some A"
    and rt0: "ho_typeof S G [] (ho_erase_pattern r)=Some A"
    using wt by (auto simp: ho_rule_welltyped_def split: option.splits)
  have zl: "ho_zero_arity_pattern l" and zr: "ho_zero_arity_pattern r"
    using zero member unfolding ho_zero_arity_rules_def by auto
  have leq: "ho_subst s 0 (ho_erase_pattern l)=ho_apply_terms (HConst d) ps"
    using li ho_zero_arity_instantiate[OF zl, of s 0] by simp
  have req: "ho_subst s 0 (ho_erase_pattern r)=v"
    using ri ho_zero_arity_instantiate[OF zr, of s 0] by simp
  have head_d: "ho_application_head (ho_erase_pattern l)=HConst d" using head ed by simp
  have mapped_old: "map (ho_subst s 0) ?ls=ps"
    using ho_constant_arguments_subst[OF head_d, of s 0] leq by simp
  have lp: "length ?ls=length ps" using mapped_old by (metis length_map)
  have qa: "list_all2 source_candidate ?Ds qs"
    using list_all2_dropI[OF args, of "length ps"] split lp by simp
  have qt: "list_all2 (\<lambda>A x. ho_typeof S V B x=Some A) ?Ds qs"
    by (rule list_all2_mono[OF qa]) (rule source.candidate_typed)
  have sub: "ho_typed_subst S V B (G@?Ds) ?s"
    by (rule ho_prefix_subst_typed[OF subst qt])
  have lnew: "ho_subst ?s 0 (ho_erase_pattern l)=ho_apply_terms (HConst d) ps"
    using ho_prefix_subst_old[OF lt0, of s qs 0] leq by simp
  have mapped_prefix: "map (ho_subst ?s 0) ?ls=ps"
    using ho_constant_arguments_subst[OF head_d, of ?s 0] lnew by simp
  have mapped: "map (ho_subst ?s 0) ?lhs=xs"
    using mapped_prefix ho_prefix_subst_variables[OF list_all2_lengthD[OF qa, symmetric], of G s]
      split by simp
  have rnew: "ho_subst ?s 0 ?rhs=ho_apply_terms v qs"
    using ho_prefix_subst_old[OF rt0, of s qs 0] req
      ho_prefix_subst_variables[OF list_all2_lengthD[OF qa, symmetric], of G s]
    by (simp add: ho_subst_apply_terms)
  have known: "\<exists>A. source_candidate A (ho_subst ?s 0 q)" if "q\<in>set ?lhs" for q
  proof -
    have mem: "ho_subst ?s 0 q\<in>set xs" using that mapped by force
    show ?thesis using args mem by (metis list_all2_nthD2 in_set_conv_nth)
  qed
  have closed: "ho_bound_closed 0 q" if "q\<in>set ?lhs" for q
  proof -
    have "list_all (ho_bound_closed 0) ?lhs" using types
      by (induction rule: list_all2_induct) (auto dest: ho_typeof_bound_closed)
    then show ?thesis using that by (simp add: list_all_iff)
  qed
  have lhs_typed: "\<exists>T. ho_typeof S (G@?Ds) [] q=Some T" if "q\<in>set ?lhs" for q
  proof -
    have mem: "q\<in>set ?lhs" by (rule that)
    obtain i where idx: "i<length ?lhs" and qi: "?lhs!i=q"
      using in_set_conv_nth[THEN iffD1, OF mem] by blast
    have tyq: "ho_typeof S (G@?Ds) [] (?lhs!i)=Some ((take (arity d) (ho_argument_types U))!i)"
      by (rule list_all2_nthD2[OF types idx])
    show ?thesis using tyq qi by blast
  qed
  have lhsi: "\<exists>x. source_candidate T x" if "q\<in>set ?lhs" "T\<in>ho_binder_types q" for q T
  proof -
    have old: "q\<in>set ?ls" using that ho_prefix_variables_binders by auto
    show ?thesis by (rule lhs_inhabited[OF member]) (use ho_spine_binder_types[OF old] that(2) in blast)
  qed
  have rhsi: "\<exists>x. source_candidate T x" if "T\<in>ho_binder_types ?rhs" for T
    by (rule rhs_inhabited[OF member])
       (use that ho_prefix_variables_binders in \<open>auto simp: ho_binders_apply_terms\<close>)
  have rec: "source_candidate (ho_drop_type (arity e) Z) (ho_apply_terms (HConst e) ys)"
    if small: "((e,ys),(d,map (ho_subst ?s 0) ?lhs))\<in>priority_call_order prec priority"
      and sym: "ho_lookup S e=Some Z"
      and aa: "list_all2 source_candidate (take (arity e) (ho_argument_types Z)) ys" for e ys Z
    using smaller[of e ys Z] small sym aa mapped by simp
  have result: "source_candidate (ho_drop_type (arity d) U) (ho_open ?s HBound 0 ?rhs)"
    by (rule ho_check_functional_access_closure_sound[where b=HBound and prec=prec and priority=priority and arity=arity,
      OF cl rt sub _ closed rhsi bounds lhs_typed lhsi known inhabited rec]) simp
  have closed_rhs: "ho_bound_closed 0 ?rhs"
    using ho_typeof_bound_closed[OF rt] by simp
  show ?thesis using result ho_open_closed[OF closed_rhs, of ?s HBound] rnew by simp
qed

theorem prefix_schema_symbols:
  assumes checked: "list_all (ho_check_prefix_schema_rule S R rank prec priority arity fuel) R"
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
  have arities: "ho_spine_length (ho_erase_pattern l)\<le>arity d"
    if member: "(G,l,r)\<in>set R" and head: "ho_application_head (ho_erase_pattern l)=HConst d"
    for G l r d
  proof -
    have rc: "ho_check_prefix_schema_rule S R rank prec priority arity fuel (G,l,r)"
      using checked member by (simp add: list_all_iff)
    show ?thesis using prefix_schema_rule_data[OF rc] head by auto
  qed
  show ?thesis
  proof (rule candidate_from_prefix_calls)
    show "ho_typeof S V B (HConst c)=Some T" using symbol by simp
    show "arity c\<le>length (ho_argument_types T)" by (rule bounds[OF symbol])
    show "\<exists>x. source_candidate (HBase b) x" if "b\<in>ho_type_bases T" for b
      by (rule inhabited[OF symbol that])
    fix xs assume args: "list_all2 source_candidate (take (arity c) (ho_argument_types T)) xs"
    show "source_candidate (ho_drop_type (arity c) T) (ho_apply_terms (HConst c) xs)"
    proof (rule candidate_prefix_recursive_calls_computable[where prec=prec and priority=priority and arity=arity])
      fix G l r d
      assume "(G,l,r)\<in>set R" "ho_application_head (ho_erase_pattern l)=HConst d"
      then show "ho_spine_length (ho_erase_pattern l)\<le>arity d" by (rule arities)
    next
      fix d U assume "ho_lookup S d=Some U"
      then show "arity d\<le>length (ho_argument_types U)" by (rule bounds)
    next
      fix d ys U ps qs v
      assume sy: "ho_lookup S d=Some U"
        and aa: "list_all2 source_candidate (take (arity d) (ho_argument_types U)) ys"
        and split: "ys=ps@qs"
        and root: "ho_root_step S V R B (ho_apply_terms (HConst d) ps) v"
        and ih: "\<And>e zs Z. ((e,zs),(d,ys))\<in>priority_call_order prec priority \<Longrightarrow>
          ho_lookup S e=Some Z \<Longrightarrow>
          list_all2 source_candidate (take (arity e) (ho_argument_types Z)) zs \<Longrightarrow>
          source_candidate (ho_drop_type (arity e) Z) (ho_apply_terms (HConst e) zs)"
      show "source_candidate (ho_drop_type (arity d) U) (ho_apply_terms v qs)"
        by (rule prefix_schema_root_closed[OF checked bounds inhabited rhs_inhabited lhs_inhabited sy aa split root ih])
    next
      show "ho_lookup S c=Some T" by (rule symbol)
      show "list_all2 source_candidate (take (arity c) (ho_argument_types T)) xs" by (rule args)
    qed
  qed
qed

end

theorem ho_check_prefix_schema_sound:
  assumes checked: "ho_check_prefix_schema S R ranks arities priorities sorts fuel"
  shows "wf ((ho_relation S V R A)\<inverse>)"
proof -
  have zero: "ho_zero_arity_rules R"
    and rules: "list_all (ho_check_prefix_schema_rule S R
      (\<lambda>b. if b<length sorts then sorts!b else 0) ((!) ranks) ((!) priorities) ((!) arities) fuel) R"
    and bound: "\<And>c T. ho_lookup S c=Some T \<Longrightarrow> arities!c\<le>length (ho_argument_types T)"
    using checked unfolding ho_check_prefix_schema_def by (auto split: if_splits)
  have heads: "\<exists>c. ho_application_head (ho_erase_pattern l)=HConst c"
    if "(G,l,r)\<in>set R" for G l r
    using prefix_schema_rule_data[of S R "(\<lambda>b. if b<length sorts then sorts!b else 0)"
      "(!) ranks" "(!) priorities" "(!) arities" fuel G l r] rules that
    by (auto simp: list_all_iff)
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
    have base_inhabited: "\<exists>x. src.source_candidate (HBase b) x" if "b\<in>?K" for b
    proof -
      have mem: "HBase b\<in>set W" by (rule available[OF that])
      obtain n where n: "n<length W" and eq: "W!n=HBase b"
        using mem by (metis in_set_conv_nth)
      have "src.source_candidate (HBase b) (HFree n)"
        by (rule src.source_candidate_free) (use n eq in auto)
      then show ?thesis by blast
    qed
    have inhabited: "\<exists>x. src.source_candidate (HBase b) x"
      if sy: "ho_lookup S d=Some U" and base: "b\<in>ho_type_bases U" for d U b
    proof -
      have "U\<in>set S" using sy by (auto split: if_splits)
      then have "b\<in>?K" using base by blast
      then show ?thesis by (rule base_inhabited)
    qed
    have rhs_inhabited: "\<exists>x. src.source_candidate Z x"
      if member: "(G,l,r)\<in>set R" and bt: "Z\<in>ho_binder_types (ho_erase_pattern r)" for G l r Z
    proof (rule src.source_candidate_type_inhabited)
      fix b assume base: "b\<in>ho_type_bases Z"
      have entry: "b\<in>(\<Union>T\<in>ho_binder_types (ho_erase_pattern r). ho_type_bases T)" using bt base by blast
      have rhs: "b\<in>(\<Union>(G,l,r)\<in>set R. \<Union>T\<in>ho_binder_types (ho_erase_pattern r). ho_type_bases T)"
        by (rule UN_I[OF member]) (use entry in simp)
      show "\<exists>x. src.source_candidate (HBase b) x" by (rule base_inhabited) (use rhs in blast)
    qed
    have lhs_inhabited: "\<exists>x. src.source_candidate Z x"
      if member: "(G,l,r)\<in>set R" and bt: "Z\<in>ho_binder_types (ho_erase_pattern l)" for G l r Z
    proof (rule src.source_candidate_type_inhabited)
      fix b assume base: "b\<in>ho_type_bases Z"
      have entry: "b\<in>(\<Union>T\<in>ho_binder_types (ho_erase_pattern l). ho_type_bases T)" using bt base by blast
      have lhs: "b\<in>(\<Union>(G,l,r)\<in>set R. \<Union>T\<in>ho_binder_types (ho_erase_pattern l). ho_type_bases T)"
        by (rule UN_I[OF member]) (use entry in simp)
      show "\<exists>x. src.source_candidate (HBase b) x" by (rule base_inhabited) (use lhs in blast)
    qed
    show "ho_source_candidate_computable S W R [] (\<lambda>b. if b<length sorts then sorts!b else 0) T (HConst c)"
      by (rule src.prefix_schema_symbols[OF rules bound inhabited rhs_inhabited lhs_inhabited symbol])
  qed
qed

end
