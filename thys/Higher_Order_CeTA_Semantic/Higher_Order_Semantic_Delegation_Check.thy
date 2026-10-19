theory Higher_Order_Semantic_Delegation_Check
  imports Higher_Order_Semantic_Delegated
begin

definition ho_check_semantic_delegation_side where
  "ho_check_semantic_delegation_side S R F P ps ms ofuel ranks arities priorities sorts fuel =
    (ho_check_polynomial_signature S ps \<and> ho_check_polynomial_signature S ms \<and>
     list_all (\<lambda>(G,l,r). ho_check_weak_polynomial_rule S ps ofuel G l r) R \<and>
     length ranks=length S \<and> length arities=length S \<and>
     list_all (\<lambda>n. n\<le>length priorities) arities \<and>
     (\<forall>i<length S. arities!i\<le>length (ho_argument_types (S!i))) \<and>
     (\<forall>c\<in>set F. c<length S \<and> arities!c=length (ho_argument_types (S!c)) \<and>
       list_all (ho_positive_type (\<lambda>b. if b<length sorts then sorts!b else 0)
         (if ho_result_sort (S!c)<length sorts then sorts!ho_result_sort (S!c) else 0))
         (ho_argument_types (S!c))) \<and>
     ho_zero_arity_rules R \<and> ho_finitely_matching_rules R \<and>
     list_all (ho_rule_welltyped S) R \<and>
     list_all (ho_partition_rule (set F) ((!) arities) (set P)) R \<and>
     list_all (\<lambda>(G,l,r). case ho_application_head (ho_erase_pattern l) of HConst c \<Rightarrow>
       c\<in>set F \<or> ho_check_semantic_schema_rule S
         (\<lambda>b. if b<length sorts then sorts!b else 0) ps ms ofuel ((!) ranks) ((!) priorities) ((!) arities) fuel (G,l,r)
       | _ \<Rightarrow> False) R)"

lemma ho_semantic_delegation_side_data:
  assumes checked: "ho_check_semantic_delegation_side S R F P ps ms ofuel ranks arities priorities sorts fuel"
  shows "ho_zero_arity_rules R"
    "ho_finitely_matching_rules R"
    "ho_lookup S c=Some T \<Longrightarrow> arities!c\<le>length (ho_argument_types T)"
    "c\<in>set F \<Longrightarrow> ho_lookup S c=Some T \<Longrightarrow>
      arities!c=length (ho_argument_types T) \<and>
      list_all (ho_positive_type (\<lambda>b. if b<length sorts then sorts!b else 0)
        (if ho_result_sort T<length sorts then sorts!ho_result_sort T else 0)) (ho_argument_types T)"
    "(G,l,r)\<in>set R \<Longrightarrow> ho_partition_rule (set F) ((!) arities) (set P) (G,l,r)"
    "(G,l,r)\<in>set R \<Longrightarrow> ho_application_head (ho_erase_pattern l)=HConst c \<Longrightarrow>
      c\<notin>set F \<Longrightarrow> ho_check_semantic_schema_rule S
        (\<lambda>b. if b<length sorts then sorts!b else 0) ps ms ofuel ((!) ranks) ((!) priorities) ((!) arities) fuel (G,l,r)"
proof -
  have zero: "ho_zero_arity_rules R" and matching: "ho_finitely_matching_rules R"
    and bounds: "\<forall>i<length S. arities!i\<le>length (ho_argument_types (S!i))"
    and signatures: "\<forall>c\<in>set F. c<length S \<and> arities!c=length (ho_argument_types (S!c)) \<and>
       list_all (ho_positive_type (\<lambda>b. if b<length sorts then sorts!b else 0)
         (if ho_result_sort (S!c)<length sorts then sorts!ho_result_sort (S!c) else 0))
         (ho_argument_types (S!c))"
    and partition: "list_all (ho_partition_rule (set F) ((!) arities) (set P)) R"
    and rules: "list_all (\<lambda>(G,l,r). case ho_application_head (ho_erase_pattern l) of HConst c \<Rightarrow>
       c\<in>set F \<or> ho_check_semantic_schema_rule S
         (\<lambda>b. if b<length sorts then sorts!b else 0) ps ms ofuel ((!) ranks) ((!) priorities) ((!) arities) fuel (G,l,r)
       | _ \<Rightarrow> False) R"
    using checked[unfolded ho_check_semantic_delegation_side_def] by blast+
  show "ho_zero_arity_rules R" by (rule zero)
  show "ho_finitely_matching_rules R" by (rule matching)
  show "ho_lookup S c=Some T \<Longrightarrow> arities!c\<le>length (ho_argument_types T)"
  proof -
    assume lookup: "ho_lookup S c=Some T"
    have idx: "c<length S" and eq: "S!c=T" using lookup by (auto split: if_splits)
    show "arities!c\<le>length (ho_argument_types T)" using bounds idx eq by blast
  qed
  show "c\<in>set F \<Longrightarrow> ho_lookup S c=Some T \<Longrightarrow>
      arities!c=length (ho_argument_types T) \<and>
      list_all (ho_positive_type (\<lambda>b. if b<length sorts then sorts!b else 0)
        (if ho_result_sort T<length sorts then sorts!ho_result_sort T else 0)) (ho_argument_types T)"
  proof -
    assume member: "c\<in>set F" and lookup: "ho_lookup S c=Some T"
    have eq: "S!c=T" using lookup by (auto split: if_splits)
    show "arities!c=length (ho_argument_types T) \<and>
      list_all (ho_positive_type (\<lambda>b. if b<length sorts then sorts!b else 0)
        (if ho_result_sort T<length sorts then sorts!ho_result_sort T else 0)) (ho_argument_types T)"
      using signatures member eq by blast
  qed
  show "(G,l,r)\<in>set R \<Longrightarrow> ho_partition_rule (set F) ((!) arities) (set P) (G,l,r)"
    using partition[unfolded list_all_iff] by blast
  show "(G,l,r)\<in>set R \<Longrightarrow> ho_application_head (ho_erase_pattern l)=HConst c \<Longrightarrow>
      c\<notin>set F \<Longrightarrow> ho_check_semantic_schema_rule S
        (\<lambda>b. if b<length sorts then sorts!b else 0) ps ms ofuel ((!) ranks) ((!) priorities) ((!) arities) fuel (G,l,r)"
  proof -
    assume member: "(G,l,r)\<in>set R" and head: "ho_application_head (ho_erase_pattern l)=HConst c"
      and absent: "c\<notin>set F"
    have local_rule: "(case ho_application_head (ho_erase_pattern l) of HConst d \<Rightarrow>
       d\<in>set F \<or> ho_check_semantic_schema_rule S
         (\<lambda>b. if b<length sorts then sorts!b else 0) ps ms ofuel ((!) ranks) ((!) priorities) ((!) arities) fuel (G,l,r)
       | _ \<Rightarrow> False)"
      using rules[unfolded list_all_iff] member by blast
    show "ho_check_semantic_schema_rule S
        (\<lambda>b. if b<length sorts then sorts!b else 0) ps ms ofuel ((!) ranks) ((!) priorities) ((!) arities) fuel (G,l,r)"
      using local_rule absent by (simp only: head ho_term.case) blast
  qed
qed


theorem ho_check_semantic_delegation_side_sound:
  fixes rel :: "ho_fo_tree \<Rightarrow> ho_fo_tree \<Rightarrow> bool" and ce :: nat
  assumes checked: "ho_check_semantic_delegation_side S R F P ps ms ofuel ranks arities priorities sorts fuel"
    and ce_left: "\<And>x y. rel (HFOFun ce [x,y]) x"
    and ce_right: "\<And>x y. rel (HFOFun ce [x,y]) y"
    and fo_context: "\<And>c xs ys x y. rel x y \<Longrightarrow>
      rel (HFOFun c (xs@x#ys)) (HFOFun c (xs@y#ys))"
    and instances: "\<And>p q s. (p,q)\<in>set P \<Longrightarrow>
      rel (ho_fo_substitution s p) (ho_fo_substitution s q)"
    and fo_wf: "wf {(u,t). rel\<^sup>+\<^sup>+ t u}"
  shows "wf ((ho_relation S V R A)\<inverse>)"
proof -
  have ps: "ho_check_polynomial_signature S ps"
    by (rule conjunct1[OF checked[unfolded ho_check_semantic_delegation_side_def]])
  have ms: "ho_check_polynomial_signature S ms"
    by (rule conjunct1[OF conjunct2[OF checked[unfolded ho_check_semantic_delegation_side_def]]])
  have wc: "list_all (\<lambda>(G,l,r). ho_check_weak_polynomial_rule S ps ofuel G l r) R"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF checked[unfolded ho_check_semantic_delegation_side_def]]]])
  have weak: "ho_weak_rule S (ho_polynomial_interpretation ps) G l r"
    if "(G,l,r)\<in>set R" for G l r
    by (rule ho_check_weak_polynomial_rule_sound[where fuel=ofuel, OF ps])
      (use wc that in \<open>auto simp: list_all_iff\<close>)
  have zero: "ho_zero_arity_rules R" and matching: "ho_finitely_matching_rules R"
    using ho_semantic_delegation_side_data(1,2)[OF checked] by auto
  have partition: "ho_partition_rule (set F) ((!) arities) (set P) (G,l,r)"
    if "(G,l,r)\<in>set R" for G l r
    by (rule ho_semantic_delegation_side_data(5)[OF checked that])
  have heads: "\<exists>c. ho_application_head (ho_erase_pattern l)=HConst c"
    if "(G,l,r)\<in>set R" for G l r
    by (rule ho_partition_rule_data(1)[OF partition[OF that]])
  have arities: "ho_spine_length (ho_erase_pattern l)=arities!d"
    if "(G,l,r)\<in>set R" and "ho_application_head (ho_erase_pattern l)=HConst d" for G l r d
    by (rule ho_partition_rule_data(2)[OF partition[OF that(1)] that(2)])
  have coverage: "\<exists>p q. l=ho_fo_pattern p \<and> r=ho_fo_pattern q \<and>
      ho_fo_wellformed (set F) ((!) arities) p \<and> ho_fo_wellformed (set F) ((!) arities) q \<and>
      ho_fo_variables q\<subseteq>ho_fo_variables p \<and> (p,q)\<in>set P"
    if "(G,l,r)\<in>set R" and "ho_application_head (ho_erase_pattern l)=HConst d" and "d\<in>set F"
    for G l r d
    by (rule ho_partition_rule_data(3)[OF partition[OF that(1)] that(2,3)])
  have bound: "arities!c\<le>length (ho_argument_types T)"
    if "ho_lookup S c=Some T" for c T
    by (rule ho_semantic_delegation_side_data(3)[OF checked that])
  have signature: "arities!c=length (ho_argument_types T) \<and>
      list_all (ho_positive_type (\<lambda>b. if b<length sorts then sorts!b else 0)
        (if ho_result_sort T<length sorts then sorts!ho_result_sort T else 0)) (ho_argument_types T)"
    if "c\<in>set F" and "ho_lookup S c=Some T" for c T
    by (rule ho_semantic_delegation_side_data(4)[OF checked that])
  have rules: "ho_check_semantic_schema_rule S
      (\<lambda>b. if b<length sorts then sorts!b else 0) ps ms ofuel ((!) ranks) ((!) priorities) ((!) arities) fuel (G,l,r)"
    if "(G,l,r)\<in>set R" and "ho_application_head (ho_erase_pattern l)=HConst c" and "c\<notin>set F"
    for G l r c
    by (rule ho_semantic_delegation_side_data(6)[OF checked that])
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
    have branching: "finite {u. ho_step S W R [] t u}" for t
      by (rule ho_zero_arity_finite_branching[OF matching])
    have delegated: "src.source_candidate Z t"
      if ctx: "src.ho_candidate_context (set F) ((!) arities) t"
        and ty: "ho_typeof S W [] t=Some Z" for t Z
      by (rule src.ho_first_order_delegation_computable[
          where rel=rel and ce=ce and P="set P",
          OF arities signature branching ce_left ce_right fo_context coverage instances fo_wf ctx ty])
    have known: "src.source_candidate (ho_drop_type (arities!d) U) (ho_apply_terms (HConst d) xs)"
      if fd: "d\<in>set F" and sy: "ho_lookup S d=Some U"
        and args: "list_all2 src.source_candidate (take (arities!d) (ho_argument_types U)) xs"
      for d xs U
      by (rule src.ho_delegation_known_call[where F="set F" and arity="(!) arities",
            OF signature delegated fd sy args])
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
    have ev: "ho_env_value ([]@W) (\<lambda>n. ho_zero (W!n))"
      by (simp add: ho_env_value_def ho_zero_value)
    show "ho_source_candidate_computable S W R [] (\<lambda>b. if b<length sorts then sorts!b else 0) T (HConst c)"
      by (rule src.semantic_schema_symbols_with_known[OF ps ms ev weak refl rules arities known bound inhabited rhs_inhabited symbol])
  qed
qed

end
