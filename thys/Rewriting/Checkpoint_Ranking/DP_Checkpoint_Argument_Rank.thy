theory DP_Checkpoint_Argument_Rank
 imports DP_Checkpoint_Rank_View
begin

text \<open>The raw child spine pays for one rank wrapper per child. No premise
requires children to be constructor values; opaque residual atoms are allowed.\<close>

lemma checkpoint_raw_children_rank:
 assumes "checkpoint_raw_children Z S t = Some xs" "Z\<noteq>L" "S\<noteq>L"
 shows "lpp_variable_leaf_count (checkpoint_leaf_view L t) = sum_list (map (lpp_variable_leaf_count \<circ> checkpoint_rank_view L) xs)"
 and "lpp_leaf_budget 1 (checkpoint_leaf_view L t) = Suc (sum_list (map (lpp_leaf_budget 1 \<circ> checkpoint_rank_view L) xs))"
 using assms
 by (induct Z S t arbitrary: xs rule: checkpoint_raw_children.induct)
    (auto simp: checkpoint_rank_view_def split: if_splits option.splits)

lemma checkpoint_constructor_arguments_decrease:
 assumes children: "checkpoint_raw_children Z S t = Some xs"
 and distinct: "N\<noteq>L" "Z\<noteq>L" "S\<noteq>L"
 shows "(Inr (map (checkpoint_rank_view L) xs),Inl (checkpoint_rank_view L (Fun N [t])))\<in>lpp_forest_call_order"
 using checkpoint_raw_children_rank[OF children distinct(2,3)] distinct
 by (simp add: lpp_forest_call_order_def inv_image_def in_lex_prod checkpoint_rank_view_def map_map)

lemma checked_checkpoint_argument_rank:
 fixes support :: "('f,'v) rule list" and input copied result :: "('f,'v) term"
 assumes checked: "check_checkpoint_argument_summary C N Z S ain aout resume support witnesses"
 and success: "(Fun ain [input],Fun aout [copied,result])\<in>(Trs.rstep (set support))\<^sup>*"
 and distinct: "N\<noteq>L" "Z\<noteq>L" "S\<noteq>L"
 shows "\<exists>xs. checkpoint_skeleton C result=checkpoint_encoded_list N Z S xs \<and>
 (Inr (map (checkpoint_rank_view L) xs),Inl (checkpoint_rank_view L (Fun N [checkpoint_skeleton C input])))\<in>lpp_forest_call_order"
proof -
 obtain xs where children: "checkpoint_raw_children Z S (checkpoint_skeleton C input)=Some xs"
 and result: "checkpoint_skeleton C result=checkpoint_encoded_list N Z S xs"
  using checked_checkpoint_argument_success[OF checked success] by blast
 show ?thesis
  apply (rule exI[of _ xs], rule conjI)
  apply (rule result)
  apply (rule checkpoint_constructor_arguments_decrease[OF children distinct])
  done
qed

lemma checkpoint_argument_rank_opaque_child:
 "(Inr [checkpoint_rank_view (0::nat) (Var ())],
   Inl (checkpoint_rank_view 0 (Fun 1 [Fun 3 [Var (),Fun 2 []]])))\<in>lpp_forest_call_order"
 by (simp add: lpp_forest_call_order_def inv_image_def in_lex_prod checkpoint_rank_view_def)

ML \<open>
val thms = @{thms checkpoint_raw_children_rank checkpoint_constructor_arguments_decrease checked_checkpoint_argument_rank checkpoint_argument_rank_opaque_child};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted argument rank" else ();
\<close>
end
