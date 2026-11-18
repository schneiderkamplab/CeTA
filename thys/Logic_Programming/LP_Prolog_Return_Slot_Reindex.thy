theory LP_Prolog_Return_Slot_Reindex
 imports LP_Prolog_Attached_Return_Leaf
begin

text \<open>A proof-only change of template coordinates. Evaluated runtime terms,
MGUs, clause variables and source states are unchanged. Numeric return slots
can therefore use the existing string-template continuation lemmas.\<close>

definition lpp_return_slot_name :: "nat \<Rightarrow> string" where
 "lpp_return_slot_name n = replicate n (CHR ''r'')"

definition lpp_named_return_goals where
 "lpp_named_return_goals gs = map (lp_cut_map (map_term id lpp_return_slot_name)) gs"

lemma lpp_return_slot_name_length[simp]:
 "length (lpp_return_slot_name n)=n"
 by (simp add: lpp_return_slot_name_def)

lemma lpp_return_slot_term_eval:
 "lp_ieval (map_term id lpp_return_slot_name t) (\<lambda>name. eta (length name))=lp_ieval t eta"
 by (induct t) (auto simp: map_map o_def intro: map_cong)

lemma lpp_return_slot_term_support:
 "vars_term (map_term id lpp_return_slot_name t)=lpp_return_slot_name ` vars_term t"
 by (induct t) auto

lemma lpp_named_return_goals_eval:
 "map (lp_cut_map (\<lambda>t. lp_ieval t (\<lambda>name. eta (length name)))) (lpp_named_return_goals gs) =
  map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs"
proof -
 have each: "lp_cut_map (\<lambda>t. lp_ieval t (\<lambda>name. eta (length name)))
    (lp_cut_map (map_term id lpp_return_slot_name) g) = lp_cut_map (\<lambda>t. lp_ieval t eta) g" for g
  by (cases g) (auto simp: lpp_return_slot_term_eval)
 show ?thesis by (simp add: lpp_named_return_goals_def map_map each)
qed

lemma lpp_named_return_goals_support:
 "(\<Union>g\<in>set (lpp_named_return_goals gs). \<Union>t\<in>set (lp_cut_terms g). vars_term t) =
  lpp_return_slot_name ` (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
proof -
 have each: "(\<Union>t\<in>set (lp_cut_terms (lp_cut_map (map_term id lpp_return_slot_name) g)). vars_term t) =
    lpp_return_slot_name ` (\<Union>t\<in>set (lp_cut_terms g). vars_term t)" for g
  by (cases g) (auto simp: lpp_return_slot_term_support)
 show ?thesis by (auto simp: lpp_named_return_goals_def each)
qed

ML \<open>
val checked = @{thms lpp_return_slot_name_length lpp_return_slot_term_eval lpp_return_slot_term_support
 lpp_named_return_goals_eval lpp_named_return_goals_support};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted return-slot reindexing" else ();
\<close>
end
