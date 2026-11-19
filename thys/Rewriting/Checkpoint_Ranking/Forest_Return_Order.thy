theory Forest_Return_Order
 imports "First_Order_Rewriting.Trs"
begin

text \<open>Shared finite-tree mathematics for source observations and residual
checkpoint ranking. These definitions and proofs are extracted unchanged from
the LP structural-return theories; no execution semantics is imported here.\<close>

fun lpp_structure_template :: "('f,'v) term \<Rightarrow> ('f + unit,unit) term" where
 "lpp_structure_template (Var x)=Fun (Inr ()) []"
| "lpp_structure_template (Fun f ts)=Fun (Inl f) (map lpp_structure_template ts)"

inductive lpp_leaf_effect :: "('f,'v) term set \<Rightarrow>
 ('f+unit,unit) term \<Rightarrow> ('f+unit,unit) term \<Rightarrow> bool" for A where
 unchanged: "lpp_leaf_effect A (Fun (Inr ()) []) (Fun (Inr ()) [])"
| replace: "u\<in>A \<Longrightarrow> lpp_leaf_effect A (Fun (Inr ()) []) (lpp_structure_template u)"
| constructor: "list_all2 (lpp_leaf_effect A) xs ys \<Longrightarrow>
 lpp_leaf_effect A (Fun (Inl f) xs) (Fun (Inl f) ys)"

fun lpp_leaf_budget :: "nat \<Rightarrow> ('f+unit,unit) term \<Rightarrow> nat" where
 "lpp_leaf_budget k (Var x)=0"
| "lpp_leaf_budget k (Fun f ts)=
   (case f of Inl g \<Rightarrow> Suc (sum_list (map (lpp_leaf_budget k) ts))
    | Inr u \<Rightarrow> k)"

fun lpp_variable_leaf_count :: "('f+unit,'v) term \<Rightarrow> nat" where
 "lpp_variable_leaf_count (Var x) = 0"
| "lpp_variable_leaf_count (Fun (Inr u) ts) = 1"
| "lpp_variable_leaf_count (Fun (Inl f) ts) = sum_list (map lpp_variable_leaf_count ts)"

lemma lpp_ground_template_zero_leaves:
 "vars_term u = {} \<Longrightarrow> lpp_variable_leaf_count (lpp_structure_template u) = 0"
 by (induct u) (auto simp: sum_list_eq_0_iff)

lemma lpp_leaf_count_list_rigidity:
 assumes pairs: "list_all2 (\<lambda>x y. lpp_variable_leaf_count y \<le> lpp_variable_leaf_count x \<and>
  (lpp_variable_leaf_count y = lpp_variable_leaf_count x \<longrightarrow> x=y)) xs ys"
 shows "sum_list (map lpp_variable_leaf_count ys) \<le> sum_list (map lpp_variable_leaf_count xs) \<and>
  (sum_list (map lpp_variable_leaf_count ys) = sum_list (map lpp_variable_leaf_count xs) \<longrightarrow> xs=ys)"
 using pairs
proof (induct rule: list_all2_induct)
 case Nil then show ?case by simp
next
 case (Cons x xs y ys)
 have decrease: "lpp_variable_leaf_count y \<le> lpp_variable_leaf_count x"
  and tail_decrease: "sum_list (map lpp_variable_leaf_count ys) \<le> sum_list (map lpp_variable_leaf_count xs)"
  using Cons by auto
 have rigid: "x=y \<and> xs=ys" if equal:
  "lpp_variable_leaf_count y + sum_list (map lpp_variable_leaf_count ys) =
   lpp_variable_leaf_count x + sum_list (map lpp_variable_leaf_count xs)"
 proof -
  have "lpp_variable_leaf_count y = lpp_variable_leaf_count x"
   and "sum_list (map lpp_variable_leaf_count ys) = sum_list (map lpp_variable_leaf_count xs)"
   using decrease tail_decrease equal by linarith+
  then show ?thesis using Cons by auto
 qed
 show ?case using decrease tail_decrease rigid by auto
qed

lemma lpp_ground_leaf_effect_rigidity:
 assumes effect: "lpp_leaf_effect A s t"
 and ground: "\<And>u. u\<in>A \<Longrightarrow> vars_term u = {}"
 shows "lpp_variable_leaf_count t \<le> lpp_variable_leaf_count s \<and>
   (lpp_variable_leaf_count t = lpp_variable_leaf_count s \<longrightarrow> s=t)"
 using effect
proof (induct rule: lpp_leaf_effect.induct)
 case unchanged then show ?case by simp
next
 case (replace u)
 show ?case using lpp_ground_template_zero_leaves[OF ground[OF replace.hyps]] by simp
next
 case (constructor xs ys f)
 have children: "list_all2 (\<lambda>x y. lpp_variable_leaf_count y \<le> lpp_variable_leaf_count x \<and>
  (lpp_variable_leaf_count y = lpp_variable_leaf_count x \<longrightarrow> x=y)) xs ys"
  using constructor.hyps by (auto elim: list_all2_mono)
 show ?case using lpp_leaf_count_list_rigidity[OF children] by simp
qed

lemma lpp_leaf_effect_constructor_iff:
 "lpp_leaf_effect A (Fun (Inl f) xs) t \<longleftrightarrow>
   (\<exists>ys. t=Fun (Inl f) ys \<and> list_all2 (lpp_leaf_effect A) xs ys)"
 by (auto elim: lpp_leaf_effect.cases intro: lpp_leaf_effect.constructor)

fun lpp_forest_call_rank where
 "lpp_forest_call_rank (Inl s) = (lpp_variable_leaf_count s,2 * lpp_leaf_budget 1 s)"
| "lpp_forest_call_rank (Inr ts) =
   (sum_list (map lpp_variable_leaf_count ts),Suc (2 * sum_list (map (lpp_leaf_budget 1) ts)))"

definition lpp_forest_call_order where
 "lpp_forest_call_order = inv_image (lex_prod less_than less_than) lpp_forest_call_rank"

lemma lpp_forest_call_order_wf:
 "wf lpp_forest_call_order"
 unfolding lpp_forest_call_order_def
 by (rule wf_inv_image) (rule wf_lex_prod; rule wf_less_than)

lemma lpp_constructor_to_argument_forest_decreases:
 "(Inr ts,Inl (Fun (Inl f) ts))\<in>lpp_forest_call_order"
 by (simp add: lpp_forest_call_order_def inv_image_def in_lex_prod)

lemma lpp_argument_forest_to_head_decreases:
 "(Inl s,Inr (s#ss))\<in>lpp_forest_call_order"
 by (auto simp: lpp_forest_call_order_def inv_image_def in_lex_prod)

lemma lpp_template_size_positive:
 "0<lpp_leaf_budget 1 (lpp_structure_template u)"
 by (cases u) auto

lemma lpp_returned_argument_tail_decreases:
 assumes effect: "list_all2 (lpp_leaf_effect A) xs ys"
 and ground: "\<And>u. u\<in>A \<Longrightarrow> vars_term u = {}"
 and positive_head: "0<lpp_leaf_budget 1 s"
 shows "(Inr ys,Inr (s#xs))\<in>lpp_forest_call_order"
proof -
 have pairwise: "list_all2 (\<lambda>x y. lpp_variable_leaf_count y \<le> lpp_variable_leaf_count x \<and>
  (lpp_variable_leaf_count y = lpp_variable_leaf_count x \<longrightarrow> x=y)) xs ys"
  by (rule list_all2_mono[OF effect]) (use lpp_ground_leaf_effect_rigidity[OF _ ground] in auto)
 have decreased: "sum_list (map lpp_variable_leaf_count ys) \<le> sum_list (map lpp_variable_leaf_count xs)"
  and rigid: "sum_list (map lpp_variable_leaf_count ys) = sum_list (map lpp_variable_leaf_count xs) \<Longrightarrow> xs=ys"
  using lpp_leaf_count_list_rigidity[OF pairwise] by auto
 show ?thesis
 proof (cases "sum_list (map lpp_variable_leaf_count ys) < lpp_variable_leaf_count s + sum_list (map lpp_variable_leaf_count xs)")
  case True then show ?thesis by (simp add: lpp_forest_call_order_def inv_image_def in_lex_prod)
 next
  case False
  have same: "sum_list (map lpp_variable_leaf_count ys) = sum_list (map lpp_variable_leaf_count xs)"
   and no_head_leaves: "lpp_variable_leaf_count s=0" using False decreased by linarith+
  show ?thesis using rigid[OF same] positive_head no_head_leaves
   by (simp add: lpp_forest_call_order_def inv_image_def in_lex_prod)
 qed
qed

ML \<open>
val thms = @{thms lpp_ground_template_zero_leaves lpp_leaf_count_list_rigidity lpp_ground_leaf_effect_rigidity lpp_leaf_effect_constructor_iff lpp_forest_call_order_wf lpp_constructor_to_argument_forest_decreases lpp_argument_forest_to_head_decreases lpp_template_size_positive lpp_returned_argument_tail_decreases};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted shared forest mathematics" else ();
\<close>
end
