theory Sparse_Tiling_Removal_Source
  imports "Sparse_Tiling_Source.Sparse_Tiling_Extraction"
    "Sparse_Tiling_Removal.Sparse_Tiling_Removal"
begin

definition sparse_check_term_removal where
  "sparse_check_term_removal q z ts tiled source residual =
    (case (sparse_rules_of_terms source,sparse_rules_of_terms residual) of
      (Some rs,Some kept) \<Rightarrow> sparse_check_removal q z ts rs tiled kept
    | _ \<Rightarrow> False)"

lemma sparse_check_term_removal_sound:
  assumes checked: "sparse_check_term_removal q z ts tiled source residual"
    and target: "SN (rstep (set residual))"
  shows "SN (rstep (set source))"
proof -
  obtain rs kept where source: "sparse_rules_of_terms source = Some rs"
    and residual: "sparse_rules_of_terms residual = Some kept"
    and coverage: "sparse_check_removal q z ts rs tiled kept"
    using checked unfolding sparse_check_term_removal_def by (auto split: option.splits)
  have word_target: "SN (sparse_word_step (set kept))"
    by (rule sparse_extracted_word_SN[OF residual target])
  have word_source: "SN (sparse_word_step (set rs))"
    by (rule sparse_check_removal_sound[OF coverage word_target])
  show ?thesis by (rule sparse_extracted_term_SN[OF source word_source])
qed

lemma sparse_term_removal_empty_residual:
  "sparse_check_term_removal [0::nat] [4]
    [[1,2],[1,3],[2,2],[2,3],[0,1],[0,2],[3,4]] []
    [(sparse_term [3,3] (Var (0::nat)),sparse_term [2,3] (Var 0)),
     (sparse_term [2,1] (Var 1),sparse_term [1,3] (Var 1))] ([] :: (nat,nat) rule list)"
  by eval

lemma sparse_term_removal_kept_rule:
  "sparse_check_term_removal [0::nat] [0] [[0,0]]
    [([[0,0],[0,0]],[[0,0]])]
    [(sparse_term [0] (Var (0::nat)),Var 0)]
    [(sparse_term [0] (Var (1::nat)),Var 1)]"
  by eval

lemma sparse_term_removal_false_empty_rejected:
  "\<not> sparse_check_term_removal [0::nat] [0] [[0,0]]
    [([[0,0],[0,0]],[[0,0]])]
    [(sparse_term [0] (Var (0::nat)),Var 0)] ([] :: (nat,nat) rule list)"
  by eval

lemma sparse_term_removal_wrong_source_tail_rejected:
  "\<not> sparse_check_term_removal [0::nat] [0] [[0,0]]
    [([[0,0],[0,0]],[[0,0]])]
    [(sparse_term [0] (Var (0::nat)),Var 1)]
    [(sparse_term [0] (Var (0::nat)),Var 0)]"
  by eval

lemma sparse_term_removal_empty_lhs_rejected:
  "\<not> sparse_check_term_removal [0::nat] [0] [[0,0]] []
    [(Var (0::nat),sparse_term [0] (Var 0))] ([] :: (nat,nat) rule list)"
  by eval

export_code sparse_check_term_removal checking SML
end
