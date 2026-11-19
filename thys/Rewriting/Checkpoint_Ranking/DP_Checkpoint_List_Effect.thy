theory DP_Checkpoint_List_Effect
 imports DP_Checkpoint_Leaf_Effect
begin

lemma checkpoint_leaf_constructor_iff:
 assumes "f\<noteq>L"
 shows "checkpoint_leaf_relation L (Fun f xs) t \<longleftrightarrow>
 (\<exists>ys. t=Fun f ys \<and> list_all2 (checkpoint_leaf_relation L) xs ys)"
 using assms
 by (cases t) (auto simp: checkpoint_leaf_relation_def[abs_def] lpp_leaf_effect_constructor_iff
   list_all2_map1 list_all2_map2 split: if_splits)

lemma checkpoint_list_cons_effect:
 assumes "distinct [L,N,Z,S]"
 shows "checkpoint_leaf_relation L (checkpoint_list_cons N Z S x xs) t \<longleftrightarrow>
 (\<exists>y ys. t=checkpoint_list_cons N Z S y ys \<and> checkpoint_leaf_relation L x y \<and> checkpoint_leaf_relation L xs ys)"
 using assms
 by (auto simp: checkpoint_list_cons_def checkpoint_leaf_constructor_iff list_all2_Cons1 split: list.splits)

lemma checkpoint_encoded_list_effect_exact:
 assumes distinct: "distinct [L,N,Z,S]"
 shows "checkpoint_leaf_relation L (checkpoint_encoded_list N Z S xs) t \<longleftrightarrow>
 (\<exists>ys. t=checkpoint_encoded_list N Z S ys \<and> list_all2 (checkpoint_leaf_relation L) xs ys)"
 using distinct
proof (induct xs arbitrary: t)
 case Nil
 then show ?case by (auto simp: checkpoint_leaf_constructor_iff list_all2_Cons1 split: list.splits)
next
 case (Cons x xs)
 have step: "checkpoint_leaf_relation L (checkpoint_encoded_list N Z S (x#xs)) t \<longleftrightarrow>
 (\<exists>y zs. t=checkpoint_list_cons N Z S y (checkpoint_encoded_list N Z S zs) \<and>
 checkpoint_leaf_relation L x y \<and> list_all2 (checkpoint_leaf_relation L) xs zs)"
  using checkpoint_list_cons_effect[OF Cons.prems, of x "checkpoint_encoded_list N Z S xs" t] Cons.hyps[OF Cons.prems]
  by auto
 show ?case unfolding step
  apply auto
  subgoal for y zs by (rule exI[of _ "y#zs"]) simp
  subgoal for ys by (cases ys) auto
  done
qed

lemma checkpoint_encoded_list_return:
 assumes distinct: "distinct [L,N,Z,S]"
 and effect: "checkpoint_leaf_relation L (checkpoint_encoded_list N Z S xs) t"
 and head: "0<lpp_leaf_budget 1 (checkpoint_leaf_view L h)"
 shows "\<exists>ys. t=checkpoint_encoded_list N Z S ys \<and> length ys=length xs \<and>
 (Inr (map (checkpoint_leaf_view L) ys),Inr (checkpoint_leaf_view L h#map (checkpoint_leaf_view L) xs))\<in>lpp_forest_call_order"
proof -
 obtain ys where shape: "t=checkpoint_encoded_list N Z S ys"
 and related: "list_all2 (checkpoint_leaf_relation L) xs ys"
  using effect checkpoint_encoded_list_effect_exact[OF distinct] by blast
 show ?thesis
  apply (rule exI[of _ ys])
  apply (intro conjI)
  apply (rule shape)
  using list_all2_lengthD[OF related] apply simp
  apply (rule checkpoint_leaf_forest_return[OF related head])
  done
qed

ML \<open>
val thms = @{thms checkpoint_leaf_constructor_iff checkpoint_encoded_list_effect_exact checkpoint_encoded_list_return};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms))
 then error "Untrusted residual list effect" else ();
\<close>
end
