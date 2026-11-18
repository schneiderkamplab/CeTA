theory LP_Prolog_Leaf_Effect_Composition
 imports LP_Prolog_Bounded_Instantiation
begin

fun lpp_no_variable_leaf where
 "lpp_no_variable_leaf (Var x) = False"
| "lpp_no_variable_leaf (Fun (Inr u) ts) = False"
| "lpp_no_variable_leaf (Fun (Inl f) ts) = list_all lpp_no_variable_leaf ts"

lemma lpp_ground_template_no_variable_leaf:
 "vars_term u = {} \<Longrightarrow> lpp_no_variable_leaf (lpp_structure_template u)"
 by (induct u) (auto simp: list_all_iff)

lemma lpp_leaf_free_effect_identity:
 assumes effect: "lpp_leaf_effect A s t"
 and leaf_free: "lpp_no_variable_leaf s"
 shows "s = t"
 using effect leaf_free
proof (induct rule: lpp_leaf_effect.induct)
 case unchanged then show ?case by simp
next
 case (replace u) then show ?case by simp
next
 case (constructor xs ys f)
 have "list_all2 (=) xs ys"
  using constructor by (induct rule: list_all2_induct) auto
 then show ?case by (simp add: list_all2_eq)
qed

lemma lpp_ground_template_effect_identity:
 assumes ground_template: "vars_term u = {}"
 and effect: "lpp_leaf_effect A (lpp_structure_template u) t"
 shows "lpp_structure_template u = t"
 by (rule lpp_leaf_free_effect_identity[OF effect lpp_ground_template_no_variable_leaf[OF ground_template]])

lemma lpp_list_effect_compose:
 assumes first_effect: "list_all2 (\<lambda>x y. \<forall>z. R y z \<longrightarrow> R x z) xs ys"
 and second_effect: "list_all2 R ys zs"
 shows "list_all2 R xs zs"
 using first_effect second_effect
 by (induct arbitrary: zs rule: list_all2_induct) (case_tac zs; auto)+

lemma lpp_leaf_effect_transitive:
 assumes first_effect: "lpp_leaf_effect A s t"
 and second_effect: "lpp_leaf_effect A t v"
 and ground_templates: "\<And>u. u\<in>A \<Longrightarrow> vars_term u = {}"
 shows "lpp_leaf_effect A s v"
 using first_effect second_effect
proof (induct arbitrary: v rule: lpp_leaf_effect.induct)
 case unchanged then show ?case .
next
 case (replace u)
 have "lpp_structure_template u = v"
  by (rule lpp_ground_template_effect_identity[OF ground_templates[OF replace.hyps] replace.prems])
 then show ?case using replace.hyps by (auto intro: lpp_leaf_effect.replace)
next
 case (constructor xs ys f)
 obtain zs where shape: "v = Fun (Inl f) zs" and latter: "list_all2 (lpp_leaf_effect A) ys zs"
  using constructor.prems by (cases rule: lpp_leaf_effect.cases) auto
 have earlier: "list_all2 (\<lambda>x y. \<forall>z. lpp_leaf_effect A y z \<longrightarrow> lpp_leaf_effect A x z) xs ys"
  using constructor.hyps by (auto elim: list_all2_mono)
 have children: "list_all2 (lpp_leaf_effect A) xs zs"
  by (rule lpp_list_effect_compose[OF earlier latter])
 show ?case using lpp_leaf_effect.constructor[OF children, where f = f] by (simp add: shape)
qed


lemma lpp_non_ground_leaf_effect_not_transitive:
 "lpp_leaf_effect {Fun f [Var ()]} (Fun (Inr ()) []) (Fun (Inl f) [Fun (Inr ()) []]) \<and>
  lpp_leaf_effect {Fun f [Var ()]} (Fun (Inl f) [Fun (Inr ()) []])
    (Fun (Inl f) [Fun (Inl f) [Fun (Inr ()) []]]) \<and>
  \<not>lpp_leaf_effect {Fun f [Var ()]} (Fun (Inr ()) [])
    (Fun (Inl f) [Fun (Inl f) [Fun (Inr ()) []]])"
proof -
 let ?A = "{Fun f [Var ()]}"
 let ?leaf = "Fun (Inr ()) []"
 let ?node = "Fun (Inl f) [?leaf]"
 have single: "lpp_leaf_effect ?A ?leaf ?node"
  using lpp_leaf_effect.replace[of "Fun f [Var ()]" ?A] by simp
 have children: "list_all2 (lpp_leaf_effect ?A) [?leaf] [?node]"
  using single by simp
 have doubled: "lpp_leaf_effect ?A ?node (Fun (Inl f) [?node])"
  by (rule lpp_leaf_effect.constructor[OF children])
 have excluded: "\<not>lpp_leaf_effect ?A ?leaf (Fun (Inl f) [?node])"
  by (auto elim: lpp_leaf_effect.cases)
 show ?thesis using single doubled excluded by blast
qed

ML \<open>
val checked = @{thms lpp_ground_template_no_variable_leaf lpp_leaf_free_effect_identity
 lpp_ground_template_effect_identity lpp_list_effect_compose lpp_leaf_effect_transitive
 lpp_non_ground_leaf_effect_not_transitive};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted leaf effect composition" else ();
\<close>
end
