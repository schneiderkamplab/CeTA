theory Higher_Order_Expansion_Observations
  imports Higher_Order_Expansion_Semantic
begin

text \<open>Type-directed observations are search proposals only. Their types
and computability are checked by the expansion closure; no completeness or
inhabitation assertion is assumed for this generator.\<close>

fun ho_expansion_witness where
  "ho_expansion_witness S G (HBase b)=
    (case List.find (\<lambda>i. G!i=HBase b) [0..<length G] of
      Some i \<Rightarrow> Some (HFree i) | None \<Rightarrow>
        map_option HConst (List.find (\<lambda>i. S!i=HBase b) [0..<length S]))"
| "ho_expansion_witness S G (HArrow A C)=
    (case List.find (\<lambda>i. G!i=HArrow A C) [0..<length G] of
      Some i \<Rightarrow> Some (HFree i) | None \<Rightarrow>
        if A=C then Some (HAbs A (HBound 0))
        else map_option (\<lambda>t. HAbs A (ho_lift 1 0 t)) (ho_expansion_witness S G C))"

definition ho_expansion_observations where
  "ho_expansion_observations S G T=
    (case those (map (ho_expansion_witness S G) (ho_argument_types T)) of
      None \<Rightarrow> [] | Some ts \<Rightarrow> ts)"

definition ho_expansion_sorts where
  "ho_expansion_sorts S R=(\<Union>T\<in>set S. ho_type_bases T) \<union>
    (\<Union>(G,l,r)\<in>set R. \<Union>T\<in>ho_binder_types (ho_erase_pattern r). ho_type_bases T)"

lemma finite_expansion_sorts: "finite (ho_expansion_sorts S R)"
  by (auto simp: ho_expansion_sorts_def split: prod.splits)

end
