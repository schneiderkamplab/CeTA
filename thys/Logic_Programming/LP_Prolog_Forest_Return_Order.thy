theory LP_Prolog_Forest_Return_Order
 imports LP_Prolog_List_Leaf_Effect LP_Prolog_Runtime_Leaf_Invariant
begin

text \<open>A constructor call and an argument-list traversal have different
size measures. This order connects constructor decomposition, element calls and
actual tail returns without charging list encoding nodes as source work.\<close>

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

lemma lpp_runtime_observation_size_positive:
 assumes observed: "lpp_runtime_structure runtime_value observed_tree"
 shows "0<lpp_leaf_budget 1 observed_tree"
 using observed lpp_template_size_positive unfolding lpp_runtime_structure_def by blast

lemma lpp_runtime_returned_argument_tail_decreases:
 assumes returned: "lpp_runtime_leaf_effect A (lpp_structural_argument_list xs) returned_tail"
 and ground: "\<And>u. u\<in>A \<Longrightarrow> vars_term u = {}"
 and observed_head: "lpp_runtime_structure head_value head_shape"
 shows "\<exists>ys. lpp_runtime_structure returned_tail (lpp_structural_argument_list ys) \<and>
   (Inr ys,Inr (head_shape#xs))\<in>lpp_forest_call_order"
proof -
 obtain observed_tail where runtime: "lpp_runtime_structure returned_tail observed_tail"
  and effect: "lpp_leaf_effect A (lpp_structural_argument_list xs) observed_tail"
  using returned unfolding lpp_runtime_leaf_effect_def by blast
 obtain ys where shape: "observed_tail=lpp_structural_argument_list ys"
  and elements: "list_all2 (lpp_leaf_effect A) xs ys"
  using effect by (auto simp: lpp_list_leaf_effect_exact)
 have ordered: "(Inr ys,Inr (head_shape#xs))\<in>lpp_forest_call_order"
  by (rule lpp_returned_argument_tail_decreases[OF elements ground lpp_runtime_observation_size_positive[OF observed_head]])
 show ?thesis by (rule exI[of _ ys]) (use runtime shape ordered in simp)
qed

ML \<open>
val checked = @{thms lpp_forest_call_order_wf lpp_constructor_to_argument_forest_decreases
 lpp_argument_forest_to_head_decreases lpp_template_size_positive lpp_returned_argument_tail_decreases
 lpp_runtime_observation_size_positive lpp_runtime_returned_argument_tail_decreases};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted forest return order" else ();
\<close>
end
