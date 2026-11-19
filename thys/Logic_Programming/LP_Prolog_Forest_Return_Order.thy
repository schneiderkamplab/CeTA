theory LP_Prolog_Forest_Return_Order
 imports LP_Prolog_List_Leaf_Effect LP_Prolog_Runtime_Leaf_Invariant
begin

text \<open>A constructor call and an argument-list traversal have different
size measures. This order connects constructor decomposition, element calls and
actual tail returns without charging list encoding nodes as source work.\<close>

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
