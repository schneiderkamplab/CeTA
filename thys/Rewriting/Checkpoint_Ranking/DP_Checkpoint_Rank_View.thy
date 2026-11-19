theory DP_Checkpoint_Rank_View
 imports DP_Checkpoint_Leaf_Effect
begin

text \<open>Every residual forest element has positive size, including an opaque
atom. A constructor wrapper supplies that unit while retaining exactly the
existing variable-leaf count and the established forest return order.\<close>

definition checkpoint_rank_view where
 "checkpoint_rank_view L t = Fun (Inl L) [checkpoint_leaf_view L t]"

lemma checkpoint_rank_view_positive:
 "0<lpp_leaf_budget 1 (checkpoint_rank_view L t)"
 by (simp add: checkpoint_rank_view_def)

lemma checkpoint_rank_view_leaves:
 "lpp_variable_leaf_count (checkpoint_rank_view L t)=lpp_variable_leaf_count (checkpoint_leaf_view L t)"
 by (simp add: checkpoint_rank_view_def)

lemma checkpoint_rank_view_effect:
 "checkpoint_leaf_relation L s t \<Longrightarrow>
 lpp_leaf_effect (checkpoint_leaf_replacements L) (checkpoint_rank_view L s) (checkpoint_rank_view L t)"
 unfolding checkpoint_rank_view_def checkpoint_leaf_relation_def
 by (rule lpp_leaf_effect.constructor) simp

lemma checkpoint_rank_forest_return:
 assumes related: "list_all2 (checkpoint_leaf_relation L) xs ys"
 shows "(Inr (map (checkpoint_rank_view L) ys),Inr (checkpoint_rank_view L h#map (checkpoint_rank_view L) xs))\<in>lpp_forest_call_order"
proof -
 have effect: "list_all2 (lpp_leaf_effect (checkpoint_leaf_replacements L))
   (map (checkpoint_rank_view L) xs) (map (checkpoint_rank_view L) ys)"
  unfolding list_all2_map1 list_all2_map2
  by (rule list_all2_mono[OF related]) (rule checkpoint_rank_view_effect)
 show ?thesis
  by (rule lpp_returned_argument_tail_decreases[OF effect _ checkpoint_rank_view_positive])
   (simp add: checkpoint_leaf_replacements_def)
qed

ML \<open>
val thms = @{thms checkpoint_rank_view_positive checkpoint_rank_view_leaves checkpoint_rank_view_effect checkpoint_rank_forest_return};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms))
 then error "Untrusted total residual rank" else ();
\<close>
end
