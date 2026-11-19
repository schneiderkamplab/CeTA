theory LP_Prolog_Leaf_Lexicographic_Return
 imports LP_Prolog_Leaf_Effect_Composition
begin

text \<open>A successful ground replacement can increase constructor size but
removes a variable leaf. If the leaf count is unchanged, the whole observation
is unchanged. This gives a return order without a uniform replacement-size bound.\<close>

lemma lpp_returned_child_lexicographic_decrease:
 assumes member: "s\<in>set ts" and effect: "lpp_leaf_effect A s t"
 and ground: "\<And>u. u\<in>A \<Longrightarrow> vars_term u = {}"
 shows "lpp_variable_leaf_count t < lpp_variable_leaf_count (Fun (Inl f) ts) \<or>
  (lpp_variable_leaf_count t = lpp_variable_leaf_count (Fun (Inl f) ts) \<and>
   lpp_leaf_budget 1 t < lpp_leaf_budget 1 (Fun (Inl f) ts))"
proof -
 have child_count: "lpp_variable_leaf_count s \<le> sum_list (map lpp_variable_leaf_count ts)"
  using member by (induct ts) auto
 have returned: "lpp_variable_leaf_count t \<le> lpp_variable_leaf_count s"
  and rigid: "lpp_variable_leaf_count t = lpp_variable_leaf_count s \<Longrightarrow> s=t"
  using lpp_ground_leaf_effect_rigidity[OF effect ground] by auto
 have child_size: "lpp_leaf_budget 1 s < lpp_leaf_budget 1 (Fun (Inl f) ts)"
  by (rule lpp_leaf_budget_child_strict[OF member])
 show ?thesis using child_count returned rigid child_size by auto
qed

definition lpp_leaf_lexicographic_order where
 "lpp_leaf_lexicographic_order = inv_image (lex_prod less_than less_than)
   (\<lambda>s. (lpp_variable_leaf_count s,lpp_leaf_budget 1 s))"

lemma lpp_leaf_lexicographic_order_wf:
 "wf lpp_leaf_lexicographic_order"
 unfolding lpp_leaf_lexicographic_order_def
 by (rule wf_inv_image) (rule wf_lex_prod; rule wf_less_than)

lemma lpp_returned_child_in_lexicographic_order:
 assumes member: "s\<in>set ts" and effect: "lpp_leaf_effect A s t"
 and ground: "\<And>u. u\<in>A \<Longrightarrow> vars_term u = {}"
 shows "(t,Fun (Inl f) ts)\<in>lpp_leaf_lexicographic_order"
 using lpp_returned_child_lexicographic_decrease[OF member effect ground]
 by (simp add: lpp_leaf_lexicographic_order_def inv_image_def in_lex_prod)

lemma lpp_nonground_leaf_rigidity_counterexample:
 "lpp_leaf_effect {Fun f [Var ()]} (Fun (Inr ()) []) (Fun (Inl f) [Fun (Inr ()) []]) \<and>
  lpp_variable_leaf_count (Fun (Inr ()) []) = lpp_variable_leaf_count (Fun (Inl f) [Fun (Inr ()) []]) \<and>
  Fun (Inr ()) [] \<noteq> Fun (Inl f) [Fun (Inr ()) []]"
 using lpp_leaf_effect.replace[of "Fun f [Var ()]" "{Fun f [Var ()]}"] by simp

ML \<open>
val checked = @{thms lpp_ground_template_zero_leaves lpp_leaf_count_list_rigidity
 lpp_ground_leaf_effect_rigidity lpp_returned_child_lexicographic_decrease
 lpp_leaf_lexicographic_order_wf lpp_returned_child_in_lexicographic_order
 lpp_nonground_leaf_rigidity_counterexample};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted lexicographic leaf return" else ();
\<close>
end
