theory LP_Dependency_Triple_Translation
  imports LP_Dependency_Triple_Chains LP_PiDP_Checker
begin

text \<open>Only triple control edges are strict. The successful-prefix
  program is translated independently and supplies weak rewrite rules. In
  particular, recursive helper clauses do not add strict dependency pairs.
  The definitions below specify obligations; they are not an accepting
  source checker until the chain simulation theorem is connected.\<close>

definition lp_dt_clause where
  "lp_dt_clause t = (case t of (h,ps,b) \<Rightarrow> (h,ps@[b]))"

locale lp_triple_translation =
  fixes D :: "('f,'v) lp_dependency_triple list"
    and P :: "('f,'v) lp_clause list"
    and inp out sharp :: "'f \<Rightarrow> 'f"
    and du pu :: "nat \<Rightarrow> nat \<Rightarrow> 'f"
begin

definition dt_saved where
  "dt_saved c i = lp_saved_vars (lp_dt_clause (D!c)) i"

definition dt_frame where
  "dt_frame c i t = Fun (du c i) (t # map Var (dt_saved c i))"

definition dt_entry where
  "dt_entry c = (case D!c of (h,ps,b) \<Rightarrow>
    (lp_tag inp h, if ps=[] then lp_tag inp b
      else dt_frame c 0 (lp_tag inp (ps!0))))"

definition dt_return where
  "dt_return c i = (case D!c of (h,ps,b) \<Rightarrow>
    (dt_frame c i (lp_tag out (ps!i)),
      if Suc i < length ps then dt_frame c (Suc i) (lp_tag inp (ps!Suc i))
      else lp_tag inp b))"

definition dt_control where
  "dt_control = concat (map (\<lambda>c. dt_entry c #
      map (dt_return c) [0..<length (fst (snd (D!c)))]) [0..<length D])"

definition dt_pairs where
  "dt_pairs = map (\<lambda>(l,r). (lp_mark sharp l,
    lp_mark sharp r)) dt_control"

definition dt_support where
  "dt_support = lp_translation.translated P inp out pu"

lemma dt_entry_member:
  "c < length D \<Longrightarrow> dt_entry c \<in> set dt_control"
  by (auto simp: dt_control_def)

lemma dt_return_member:
  "c < length D \<Longrightarrow> i < length (fst (snd (D!c))) \<Longrightarrow>
    dt_return c i \<in> set dt_control"
  unfolding dt_control_def by force

lemma dt_control_length:
  "length dt_control = sum_list (map (\<lambda>t. Suc (length (fst (snd t)))) D)"
  by (simp add: dt_control_def length_concat sum_list_sum_nth)

lemma dt_support_independent:
  "dt_support = lp_translation.translated P inp out pu"
  by (rule dt_support_def)

end

declare lp_triple_translation.dt_saved_def[code]
declare lp_triple_translation.dt_frame_def[code]
declare lp_triple_translation.dt_entry_def[code]
declare lp_triple_translation.dt_return_def[code]
declare lp_triple_translation.dt_control_def[code]
declare lp_triple_translation.dt_pairs_def[code]
declare lp_triple_translation.dt_support_def[code]

end
