theory Higher_Order_Delegation_Partition
  imports Higher_Order_Candidate_Delegation
begin

fun ho_decode_fo_pattern where
  "ho_decode_fo_pattern (PMeta n xs) = (if xs=[] then Some (HFOVar n) else None)"
| "ho_decode_fo_pattern (PConst c) = Some (HFOFun c [])"
| "ho_decode_fo_pattern (PApp p q) = (case ho_decode_fo_pattern p of
    Some (HFOFun c xs) \<Rightarrow> map_option (\<lambda>y. HFOFun c (xs@[y])) (ho_decode_fo_pattern q)
    | _ \<Rightarrow> None)"
| "ho_decode_fo_pattern _ = None"

lemma ho_decode_fo_pattern_sound:
  "ho_decode_fo_pattern p=Some t \<Longrightarrow> p=ho_fo_pattern t"
  by (induction p arbitrary: t)
     (auto simp: foldl_append split: option.splits ho_fo_tree.splits if_splits)

definition ho_check_fo_rule where
  "ho_check_fo_rule F arity rule = (case rule of (G,l,r) \<Rightarrow>
    (case (ho_decode_fo_pattern l,ho_decode_fo_pattern r) of (Some p,Some q) \<Rightarrow>
      if ho_fo_wellformed F arity p \<and> ho_fo_wellformed F arity q \<and>
        ho_fo_variables q\<subseteq>ho_fo_variables p then Some (p,q) else None
      | _ \<Rightarrow> None))"

lemma ho_check_fo_rule_sound:
  "ho_check_fo_rule F arity (G,l,r)=Some (p,q) \<Longrightarrow>
    l=ho_fo_pattern p \<and> r=ho_fo_pattern q \<and>
    ho_fo_wellformed F arity p \<and> ho_fo_wellformed F arity q \<and>
    ho_fo_variables q\<subseteq>ho_fo_variables p"
  unfolding ho_check_fo_rule_def
  by (auto dest: ho_decode_fo_pattern_sound split: option.splits if_splits)

definition ho_partition_rule where
  "ho_partition_rule F arity P rule = (case rule of (G,l,r) \<Rightarrow>
    case ho_application_head (ho_erase_pattern l) of HConst c \<Rightarrow>
      ho_spine_length (ho_erase_pattern l)=arity c \<and>
      (c\<in>F \<longrightarrow> (case ho_check_fo_rule F arity rule of Some pq \<Rightarrow> pq\<in>P | None \<Rightarrow> False))
      | _ \<Rightarrow> False)"

lemma ho_partition_rule_data:
  assumes checked: "ho_partition_rule F arity P (G,l,r)"
  shows "\<exists>c. ho_application_head (ho_erase_pattern l)=HConst c"
    "ho_application_head (ho_erase_pattern l)=HConst c \<Longrightarrow>
      ho_spine_length (ho_erase_pattern l)=arity c"
    "ho_application_head (ho_erase_pattern l)=HConst c \<Longrightarrow> c\<in>F \<Longrightarrow>
      \<exists>p q. l=ho_fo_pattern p \<and> r=ho_fo_pattern q \<and>
        ho_fo_wellformed F arity p \<and> ho_fo_wellformed F arity q \<and>
        ho_fo_variables q\<subseteq>ho_fo_variables p \<and> (p,q)\<in>P"
  using checked unfolding ho_partition_rule_def
  by (auto dest: ho_check_fo_rule_sound split: ho_term.splits option.splits)

text \<open>The partition does not infer a strategy from filenames, and
does not accept an omitted source rule merely because a first-order proof
exists. Every rule whose head belongs to the delegated signature must decode
exactly and occur in the certified first-order rule set.\<close>

lemma ho_partition_rejects_missing_rule:
  "\<not> ho_partition_rule {0} (\<lambda>_. 1) {}
    ([], PApp (PConst 0) (PMeta 0 []), PMeta 0 [])"
  by eval

lemma ho_partition_accepts_exact_rule:
  "ho_partition_rule {0} (\<lambda>_. 1) {(HFOFun 0 [HFOVar 0],HFOVar 0)}
    ([], PApp (PConst 0) (PMeta 0 []), PMeta 0 [])"
  by eval

lemma ho_partition_rejects_extra_variable:
  "ho_check_fo_rule {0} (\<lambda>_. 1)
    ([], PApp (PConst 0) (PMeta 0 []), PMeta 1 [])=None"
  by eval

lemma ho_partition_rejects_unsaturated_and_functional_patterns:
  "ho_check_fo_rule {0} (\<lambda>_. 2)
    ([], PApp (PConst 0) (PMeta 0 []), PMeta 0 [])=None"
  "ho_decode_fo_pattern (PApp (PMeta 0 []) (PMeta 1 []))=None"
  "ho_decode_fo_pattern (PMeta 0 [PBound 0])=None"
  by eval+

end
