theory DP_Checkpoint_Leaf_Effect
 imports DP_Checkpoint_Arguments Forest_Return_Order
begin

text \<open>The residual leaf symbol is interpreted by the established structural
leaf relation. All other symbols retain their identities. This interpretation
is defined on arbitrary skeletons, including malformed terms and opaque atoms.\<close>

fun checkpoint_leaf_view :: "'f \<Rightarrow> ('f,unit) term \<Rightarrow> ('f+unit,unit) term" where
 "checkpoint_leaf_view L (Var x) = Var x"
| "checkpoint_leaf_view L (Fun f ts) =
   Fun (if f=L then Inr () else Inl f) (map (checkpoint_leaf_view L) ts)"

fun checkpoint_leaf_unview :: "'f \<Rightarrow> ('f+unit,unit) term \<Rightarrow> ('f,unit) term" where
 "checkpoint_leaf_unview L (Var x) = Var x"
| "checkpoint_leaf_unview L (Fun f ts) =
   Fun (case f of Inl g \<Rightarrow> g | Inr _ \<Rightarrow> L) (map (checkpoint_leaf_unview L) ts)"

lemma checkpoint_leaf_view_left_inverse[simp]:
 "checkpoint_leaf_unview L (checkpoint_leaf_view L t) = t"
 by (induct t) (auto simp: map_idI)

lemma checkpoint_leaf_view_injective:
 "checkpoint_leaf_view L s = checkpoint_leaf_view L t \<Longrightarrow> s=t"
 by (metis checkpoint_leaf_view_left_inverse)

lemma checkpoint_leaf_free_template:
 "vars_term t={} \<Longrightarrow> L\<notin>funs_term t \<Longrightarrow>
   checkpoint_leaf_view L t = lpp_structure_template t"
 by (induct t) (auto simp: map_eq_conv)

definition checkpoint_leaf_replacements :: "'f \<Rightarrow> ('f,unit) term set" where
 "checkpoint_leaf_replacements L = {u. vars_term u={} \<and> L\<notin>funs_term u}"

definition checkpoint_leaf_relation where
 "checkpoint_leaf_relation L s t = lpp_leaf_effect (checkpoint_leaf_replacements L)
    (checkpoint_leaf_view L s) (checkpoint_leaf_view L t)"

lemma checkpoint_leaf_relation_identity_leaf:
 "checkpoint_leaf_relation L (Fun L []) (Fun L [])"
 unfolding checkpoint_leaf_relation_def by (simp add: lpp_leaf_effect.unchanged)

lemma checkpoint_leaf_relation_replace:
 "vars_term u={} \<Longrightarrow> L\<notin>funs_term u \<Longrightarrow>
   checkpoint_leaf_relation L (Fun L []) u"
 unfolding checkpoint_leaf_relation_def
 using lpp_leaf_effect.replace[of u "checkpoint_leaf_replacements L"]
 by (simp add: checkpoint_leaf_replacements_def checkpoint_leaf_free_template)

lemma checkpoint_leaf_relation_constructor:
 "f\<noteq>L \<Longrightarrow> list_all2 (checkpoint_leaf_relation L) xs ys \<Longrightarrow>
   checkpoint_leaf_relation L (Fun f xs) (Fun f ys)"
 unfolding checkpoint_leaf_relation_def
 by (auto simp: list_all2_map1 list_all2_map2 intro: lpp_leaf_effect.constructor)

lemma checkpoint_leaf_relation_rigidity:
 assumes "checkpoint_leaf_relation L s t"
 shows "lpp_variable_leaf_count (checkpoint_leaf_view L t) \<le> lpp_variable_leaf_count (checkpoint_leaf_view L s) \<and>
   (lpp_variable_leaf_count (checkpoint_leaf_view L t) = lpp_variable_leaf_count (checkpoint_leaf_view L s) \<longrightarrow> s=t)"
 using lpp_ground_leaf_effect_rigidity[OF assms[unfolded checkpoint_leaf_relation_def]]
 by (auto simp: checkpoint_leaf_replacements_def dest: checkpoint_leaf_view_injective)

lemma checkpoint_leaf_forest_return:
 assumes "list_all2 (checkpoint_leaf_relation L) xs ys"
 and "0<lpp_leaf_budget 1 (checkpoint_leaf_view L h)"
 shows "(Inr (map (checkpoint_leaf_view L) ys),Inr (checkpoint_leaf_view L h # map (checkpoint_leaf_view L) xs))
   \<in>lpp_forest_call_order"
proof -
 have related: "list_all2 (lpp_leaf_effect (checkpoint_leaf_replacements L))
  (map (checkpoint_leaf_view L) xs) (map (checkpoint_leaf_view L) ys)"
  unfolding list_all2_map1 list_all2_map2
  by (rule list_all2_mono[OF assms(1)]) (simp add: checkpoint_leaf_relation_def)
 show ?thesis
  by (rule lpp_returned_argument_tail_decreases[OF related _ assms(2)])
   (simp add: checkpoint_leaf_replacements_def)
qed

ML \<open>
val thms = @{thms checkpoint_leaf_view_injective checkpoint_leaf_free_template
 checkpoint_leaf_relation_identity_leaf checkpoint_leaf_relation_replace checkpoint_leaf_relation_constructor
 checkpoint_leaf_relation_rigidity checkpoint_leaf_forest_return};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms))
 then error "Untrusted residual leaf relation" else ();
\<close>
end
