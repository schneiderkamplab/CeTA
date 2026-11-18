theory LP_Prolog_Leaf_Lexicographic_Return
 imports LP_Prolog_Leaf_Effect_Composition
begin

text \<open>A successful ground replacement can increase constructor size but
removes a variable leaf. If the leaf count is unchanged, the whole observation
is unchanged. This gives a return order without a uniform replacement-size bound.\<close>

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
 case (Cons x y xs ys)
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
