theory DP_Checkpoint_Forest_Rank
 imports DP_Checkpoint_Argument_Rank DP_Checkpoint_Composed_Summary
begin

text \<open>A rank must be total even on malformed residual list endpoints.
This decoder truncates at the first endpoint that is not an encoded cons.\<close>
fun checkpoint_forest where
 "checkpoint_forest N Z S (Fun n [Fun s [h,Fun s' [t,Fun z []]]]) =
   (if n=N \<and> s=S \<and> s'=S \<and> z=Z then h#checkpoint_forest N Z S t else [])"
| "checkpoint_forest N Z S _ = []"

lemma checkpoint_forest_cons[simp]:
 "checkpoint_forest N Z S (checkpoint_list_cons N Z S h t)=h#checkpoint_forest N Z S t"
 by (simp add: checkpoint_list_cons_def)

lemma checkpoint_forest_encoded[simp]:
 "checkpoint_forest N Z S (checkpoint_encoded_list N Z S xs)=xs"
 by (induct xs) simp_all

lemma checkpoint_forest_head_descent:
 assumes children: "checkpoint_raw_children Z S children=Some xs"
 and distinct: "N\<noteq>L" "Z\<noteq>L" "S\<noteq>L"
 shows "(Inr (map (checkpoint_rank_view L) xs),
 Inr (map (checkpoint_rank_view L) (checkpoint_forest N Z S (checkpoint_list_cons N Z S (Fun N [children]) tail))))\<in>lpp_forest_call_order"
 using checkpoint_raw_children_rank[OF children distinct(2,3)] distinct
 by (auto simp: lpp_forest_call_order_def inv_image_def in_lex_prod checkpoint_rank_view_def map_map)

lemma checkpoint_forest_tail_descent:
 fixes input result :: "('f,unit) term"
 assumes before: "input=checkpoint_encoded_list N Z S xs"
 and after: "result=checkpoint_encoded_list N Z S ys"
 and effect: "list_all2 (checkpoint_leaf_relation L) xs ys"
 shows "(Inr (map (checkpoint_rank_view L) (checkpoint_forest N Z S result)),
 Inr (map (checkpoint_rank_view L) (checkpoint_forest N Z S (checkpoint_list_cons N Z S head input))))\<in>lpp_forest_call_order"
 using checkpoint_rank_forest_return[OF effect, of head] by (simp add: before after)

ML \<open>
val thms = @{thms checkpoint_forest_cons checkpoint_forest_encoded checkpoint_forest_head_descent checkpoint_forest_tail_descent};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted forest rank" else ();
\<close>
end
