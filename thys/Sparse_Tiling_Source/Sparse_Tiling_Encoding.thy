theory Sparse_Tiling_Encoding
  imports Sparse_Tiling_Extraction
begin

fun sparse_encode_word :: "('a \<times> 'b) list \<Rightarrow> 'a list \<Rightarrow> 'b list option" where
  "sparse_encode_word table [] = Some []"
| "sparse_encode_word table (a # w) = (case map_of table a of None \<Rightarrow> None
    | Some b \<Rightarrow> map_option (Cons b) (sparse_encode_word table w))"

lemma sparse_encode_word_sound:
  "sparse_encode_word table w = Some v \<Longrightarrow> v = map (\<lambda>a. the (map_of table a)) w"
  by (induction w arbitrary: v) (auto split: option.splits)

definition sparse_check_encoding where
  "sparse_check_encoding table rs ss \<longleftrightarrow> list_all (\<lambda>(l,r).
    case (sparse_encode_word table l,sparse_encode_word table r) of
      (Some u,Some v) \<Rightarrow> (u,v) \<in> set ss | _ \<Rightarrow> False) rs"

lemma sparse_check_encoding_sound:
  assumes checked: "sparse_check_encoding table rs ss" and member: "(l,r) \<in> set rs"
  shows "(map (\<lambda>a. the (map_of table a)) l,map (\<lambda>a. the (map_of table a)) r) \<in> set ss"
proof -
  have selected: "(case (sparse_encode_word table l,sparse_encode_word table r) of
    (Some u,Some v) \<Rightarrow> (u,v) \<in> set ss | _ \<Rightarrow> False)"
    using checked member unfolding sparse_check_encoding_def list_all_iff
    by (auto split: prod.splits)
  obtain u v where left: "sparse_encode_word table l = Some u"
    and right: "sparse_encode_word table r = Some v" and target: "(u,v) \<in> set ss"
    using selected by (auto split: option.splits)
  show ?thesis using target sparse_encode_word_sound[OF left] sparse_encode_word_sound[OF right] by simp
qed

lemma sparse_word_map_step:
  assumes rules: "\<And>l r. (l,r) \<in> R \<Longrightarrow> (map f l,map f r) \<in> S"
    and step: "(s,t) \<in> sparse_word_step R"
  shows "(map f s,map f t) \<in> sparse_word_step S"
proof -
  obtain p q l r where rule: "(l,r) \<in> R" and s: "s = p @ l @ q" and t: "t = p @ r @ q"
    using step unfolding sparse_word_step_def by blast
  have "(map f p @ map f l @ map f q,map f p @ map f r @ map f q) \<in> sparse_word_step S"
    by (rule sparse_word_stepI[OF rules[OF rule]])
  then show ?thesis by (simp add: s t)
qed

lemma sparse_encoding_SN:
  assumes checked: "sparse_check_encoding table rs ss"
    and sn: "SN (sparse_word_step (set ss))"
  shows "SN (sparse_word_step (set rs))"
proof (rule sparse_local_simulation_SN[where L=UNIV and
    label="map (\<lambda>a. the (map_of table a))" and S="sparse_word_step (set ss)"])
  fix x y
  assume "x \<in> UNIV" "(x,y) \<in> sparse_word_step (set rs)"
  show "y \<in> UNIV" by simp
next
  fix x y
  assume "x \<in> UNIV" and step: "(x,y) \<in> sparse_word_step (set rs)"
  show "(map (\<lambda>a. the (map_of table a)) x,map (\<lambda>a. the (map_of table a)) y)
    \<in> sparse_word_step (set ss)"
    by (rule sparse_word_map_step[OF _ step]) (rule sparse_check_encoding_sound[OF checked], assumption)
next
  show "SN_on (sparse_word_step (set ss)) (map (\<lambda>a. the (map_of table a)) ` UNIV)"
    using sn unfolding SN_on_def by blast
qed

definition sparse_check_encoded_tiling where
  "sparse_check_encoded_tiling q z tiles tiled_rules table source residual =
    (case (sparse_rules_of_terms source,sparse_rules_of_terms residual) of
      (Some rs,Some ss) \<Rightarrow> sparse_check_coverage q z tiles rs tiled_rules \<and>
        sparse_check_encoding table tiled_rules ss | _ \<Rightarrow> False)"

lemma sparse_check_encoded_tiling_sound:
  assumes checked: "sparse_check_encoded_tiling q z tiles tiled_rules table source residual"
    and target: "SN (rstep (set residual))"
  shows "SN (rstep (set source))"
proof -
  obtain rs ss where source: "sparse_rules_of_terms source = Some rs"
    and residual: "sparse_rules_of_terms residual = Some ss"
    and coverage: "sparse_check_coverage q z tiles rs tiled_rules"
    and encoding: "sparse_check_encoding table tiled_rules ss"
    using checked unfolding sparse_check_encoded_tiling_def by (auto split: option.splits)
  have target_words: "SN (sparse_word_step (set ss))" by (rule sparse_extracted_word_SN[OF residual target])
  have tiled: "SN (sparse_word_step (set tiled_rules))" by (rule sparse_encoding_SN[OF encoding target_words])
  have source_words: "SN (sparse_word_step (set rs))" by (rule sparse_check_termination_sound[OF coverage tiled])
  show ?thesis by (rule sparse_extracted_term_SN[OF source source_words])
qed

lemma sparse_encoding_example:
  "sparse_check_encoding [([0::nat,0],7::nat)]
    [([[0,0],[0,0]],[[0,0]])] [([7,7],[7])]"
  by eval

lemma sparse_encoding_missing_symbol:
  "\<not> sparse_check_encoding ([] :: (nat list \<times> nat) list)
    [([[0,0],[0,0]],[[0,0]])] [([7,7],[7])]"
  by eval

lemma sparse_encoding_wrong_residual:
  "\<not> sparse_check_encoding [([0::nat,0],7::nat)]
    [([[0,0],[0,0]],[[0,0]])] [([8,8],[8])]"
  by eval

lemma sparse_encoding_duplicate_table_is_deterministic:
  "\<not> sparse_check_encoding [([0::nat,0],8::nat),([0,0],7)]
    [([[0,0],[0,0]],[[0,0]])] [([7,7],[7])]"
  by eval

lemma sparse_encoded_term_example:
  "sparse_check_encoded_tiling [0::nat] [0] [[0,0]]
    [([[0,0],[0,0]],[[0,0]])] [([0,0],7::nat)]
    [(sparse_term [0] (Var (0::nat)),Var 0)]
    [(sparse_term [7,7] (Var (1::nat)),sparse_term [7] (Var 1))]"
  by eval

export_code sparse_check_encoded_tiling checking SML

end
