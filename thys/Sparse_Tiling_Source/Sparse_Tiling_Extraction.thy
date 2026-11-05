theory Sparse_Tiling_Extraction
  imports Sparse_Tiling_Source
begin

fun sparse_word_of_term :: "('a,'v) term \<Rightarrow> ('a list \<times> 'v) option" where
  "sparse_word_of_term (Var x) = Some ([],x)"
| "sparse_word_of_term (Fun f [t]) = map_option (\<lambda>(w,x). (f # w,x)) (sparse_word_of_term t)"
| "sparse_word_of_term (Fun f ts) = None"

lemma sparse_word_of_term_sound:
  "sparse_word_of_term t = Some (w,x) \<Longrightarrow> t = sparse_term w (Var x)"
  by (induction t arbitrary: w x rule: sparse_word_of_term.induct)
    (auto split: option.splits prod.splits)

lemma sparse_word_of_term_complete [simp]:
  "sparse_word_of_term (sparse_term w (Var x)) = Some (w,x)"
  by (induction w) auto

definition sparse_rule_of_terms where
  "sparse_rule_of_terms lr = (case (sparse_word_of_term (fst lr),sparse_word_of_term (snd lr)) of
    (Some (l,x),Some (r,y)) \<Rightarrow> if x = y then Some (l,r) else None | _ \<Rightarrow> None)"

lemma sparse_rule_of_terms_sound:
  assumes "sparse_rule_of_terms (l,r) = Some (u,v)"
  shows "\<exists>x. l = sparse_term u (Var x) \<and> r = sparse_term v (Var x)"
proof -
  obtain x where left: "sparse_word_of_term l = Some (u,x)"
    and right: "sparse_word_of_term r = Some (v,x)"
    using assms unfolding sparse_rule_of_terms_def by (auto split: option.splits prod.splits if_splits)
  show ?thesis using sparse_word_of_term_sound[OF left] sparse_word_of_term_sound[OF right] by blast
qed

lemma sparse_rule_of_terms_complete [simp]:
  "sparse_rule_of_terms (sparse_term u (Var x),sparse_term v (Var x)) = Some (u,v)"
  by (simp add: sparse_rule_of_terms_def)

fun sparse_rules_of_terms :: "('a,'v) rule list \<Rightarrow> ('a list \<times> 'a list) list option" where
  "sparse_rules_of_terms [] = Some []"
| "sparse_rules_of_terms (lr # trs) = (case sparse_rule_of_terms lr of None \<Rightarrow> None
    | Some uv \<Rightarrow> map_option (Cons uv) (sparse_rules_of_terms trs))"

lemma sparse_rules_of_terms_pairs:
  assumes "sparse_rules_of_terms trs = Some rs"
  shows "(\<forall>lr\<in>set trs. \<exists>uv\<in>set rs. sparse_rule_of_terms lr = Some uv) \<and>
    (\<forall>uv\<in>set rs. \<exists>lr\<in>set trs. sparse_rule_of_terms lr = Some uv)"
  using assms
proof (induction trs arbitrary: rs)
  case Nil
  then show ?case by simp
next
  case (Cons lr trs)
  obtain uv rest where head: "sparse_rule_of_terms lr = Some uv"
    and tail: "sparse_rules_of_terms trs = Some rest" and rs: "rs = uv # rest"
    using Cons.prems by (auto split: option.splits)
  show ?case using Cons.IH[OF tail] head
    by (simp only: rs list.set; blast)
qed

lemma sparse_extracted_term_SN:
  assumes extracted: "sparse_rules_of_terms trs = Some rs"
    and sn: "SN (sparse_word_step (set rs))"
  shows "SN (rstep (set trs))"
proof (rule sparse_word_SN_imp_term_SN[OF _ sn])
  fix l r
  assume member: "(l,r) \<in> set trs"
  obtain u v where uv: "(u,v) \<in> set rs" and rule: "sparse_rule_of_terms (l,r) = Some (u,v)"
    using sparse_rules_of_terms_pairs[OF extracted] member by auto
  show "\<exists>u v x. (u,v) \<in> set rs \<and> l = sparse_term u (Var x) \<and> r = sparse_term v (Var x)"
    using uv sparse_rule_of_terms_sound[OF rule] by blast
qed

lemma sparse_extracted_word_SN:
  assumes extracted: "sparse_rules_of_terms trs = Some rs"
    and sn: "SN (rstep (set trs))"
  shows "SN (sparse_word_step (set rs))"
proof (rule sparse_term_SN_imp_word_SN[OF _ sn])
  fix u v
  assume member: "(u,v) \<in> set rs"
  obtain l r where lr: "(l,r) \<in> set trs" and rule: "sparse_rule_of_terms (l,r) = Some (u,v)"
    using sparse_rules_of_terms_pairs[OF extracted] member by auto
  show "\<exists>x. (sparse_term u (Var x),sparse_term v (Var x)) \<in> set trs"
    using lr sparse_rule_of_terms_sound[OF rule] by blast
qed

definition sparse_check_term_tiling where
  "sparse_check_term_tiling q z ts source residual =
    (case (sparse_rules_of_terms source,sparse_rules_of_terms residual) of
      (Some rs,Some ss) \<Rightarrow> sparse_check_coverage q z ts rs ss | _ \<Rightarrow> False)"

lemma sparse_check_term_tiling_sound:
  assumes checked: "sparse_check_term_tiling q z ts source residual"
    and target: "SN (rstep (set residual))"
  shows "SN (rstep (set source))"
proof -
  obtain rs ss where source: "sparse_rules_of_terms source = Some rs"
    and residual: "sparse_rules_of_terms residual = Some ss"
    and coverage: "sparse_check_coverage q z ts rs ss"
    using checked unfolding sparse_check_term_tiling_def by (auto split: option.splits)
  have word_target: "SN (sparse_word_step (set ss))"
    by (rule sparse_extracted_word_SN[OF residual target])
  have word_source: "SN (sparse_word_step (set rs))"
    by (rule sparse_check_termination_sound[OF coverage word_target])
  show ?thesis by (rule sparse_extracted_term_SN[OF source word_source])
qed

lemma sparse_extraction_rejects_mismatched_tail:
  "sparse_rules_of_terms [(Fun (0::nat) [Var (0::nat)],Fun 1 [Var 1])] = None"
  by eval

lemma sparse_extraction_rejects_branching:
  "sparse_rules_of_terms [(Fun (0::nat) [Var (0::nat),Var 0],Var 0)] = None"
  by eval

lemma sparse_extraction_rejects_constants:
  "sparse_rules_of_terms [(Fun (0::nat) [],Var (0::nat))] = None"
  by eval

lemma sparse_term_check_example:
  "sparse_check_term_tiling [0::nat] [4]
    [[1,2],[1,3],[2,2],[2,3],[0,1],[0,2],[3,4]]
    [(sparse_term [3,3] (Var (0::nat)),sparse_term [2,3] (Var 0)),
     (sparse_term [2,1] (Var 1),sparse_term [1,3] (Var 1))]
    ([] :: (nat list,nat) rule list)"
  by eval

lemma sparse_term_example_terminates:
  "SN (rstep (set
    [(sparse_term [3::nat,3] (Var (0::nat)),sparse_term [2,3] (Var 0)),
     (sparse_term [2,1] (Var 1),sparse_term [1,3] (Var 1))]))"
  by (rule sparse_check_term_tiling_sound[OF sparse_term_check_example]) simp

export_code sparse_check_term_tiling checking SML

end
