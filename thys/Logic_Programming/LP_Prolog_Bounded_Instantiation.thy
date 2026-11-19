theory LP_Prolog_Bounded_Instantiation
 imports LP_Prolog_Structural_Projection
begin

text \<open>A candidate return effect permits finite replacements only at free
variable leaves. The allowed templates are parameters to be justified from
actual source execution, never inferred from termination. Runtime sharing is
not erased by the source semantics; this relation only observes tree shape.\<close>

definition lpp_bounded_images where
 "lpp_bounded_images A sigma V = (\<forall>x\<in>V.
   (\<exists>y. sigma x=LPIVar y) \<or> (\<exists>u\<in>A. sigma x=lp_ieval u LPIVar))"

lemma lpp_bounded_image_finite:
 fixes sigma :: "'v \<Rightarrow> ('f,'w) lp_iterm"
 assumes bounded: "lpp_bounded_images A sigma V" and member: "x\<in>V"
 shows "lpp_finite_term (sigma x)"
proof -
 have image: "(\<exists>y. sigma x=LPIVar y) \<or> (\<exists>u\<in>A. sigma x=lp_ieval u LPIVar)"
  using bounded member unfolding lpp_bounded_images_def by blast
 show ?thesis using image by (auto intro: lpp_finite_term_initial)
qed

lemma lpp_leaf_effect_template_substitution:
 assumes images: "\<And>x. x\<in>vars_term t \<Longrightarrow> (\<exists>y. theta x=Var y) \<or> theta x\<in>A"
 shows "lpp_leaf_effect A (lpp_structure_template t) (lpp_structure_template (t\<cdot>theta))"
 using images
proof (induct t)
 case (Var x)
 then show ?case by (auto intro: lpp_leaf_effect.unchanged lpp_leaf_effect.replace)
next
 case (Fun f ts)
 have children: "list_all2 (lpp_leaf_effect A) (map lpp_structure_template ts)
   (map (\<lambda>t. lpp_structure_template (t\<cdot>theta)) ts)"
  using Fun by (auto simp: list_all2_map1 list_all2_map2 list_all2_same)
 show ?case using lpp_leaf_effect.constructor[OF children, where f=f] by (simp add: o_def)
qed

lemma lpp_bounded_runtime_structural_effect:
 fixes sigma :: "'v \<Rightarrow> ('f,'v) lp_iterm"
 and t :: "('f,'v) term" and A :: "('f,'v) term set"
 assumes bounded: "lpp_bounded_images A sigma (vars_term t)"
 shows "\<exists>u. lp_isubst (lp_ieval t LPIVar) sigma=lp_ieval u LPIVar \<and>
   lpp_leaf_effect A (lpp_structure_template t) (lpp_structure_template u)"
proof -
 have choices: "\<exists>u. sigma x=lp_ieval u LPIVar \<and> ((\<exists>y. u=Var y) \<or> u\<in>A)"
  if "x\<in>vars_term t" for x
 proof -
  have image: "(\<exists>y. sigma x=LPIVar y) \<or> (\<exists>u\<in>A. sigma x=lp_ieval u LPIVar)"
   using bounded that unfolding lpp_bounded_images_def by blast
  then show ?thesis
  proof
   assume "\<exists>y. sigma x=LPIVar y"
   then obtain y where image: "sigma x=LPIVar y" by blast
   show ?thesis by (rule exI[of _ "Var y"]) (simp add: image)
  next
   assume "\<exists>u\<in>A. sigma x=lp_ieval u LPIVar"
   then show ?thesis by blast
  qed
 qed
 define theta where "theta x=(SOME u. sigma x=lp_ieval u LPIVar \<and>
   ((\<exists>y. u=Var y) \<or> u\<in>A))" for x
 have selected: "sigma x=lp_ieval (theta x) LPIVar \<and> ((\<exists>y. theta x=Var y) \<or> theta x\<in>A)"
  if "x\<in>vars_term t" for x
  unfolding theta_def by (rule someI_ex[OF choices[OF that]])
 have evaluated: "lp_ieval t sigma=lp_ieval (t\<cdot>theta) LPIVar"
  unfolding lp_ieval_finite_subst using selected
  by (induct t) (auto intro!: map_cong)
 have effect: "lpp_leaf_effect A (lpp_structure_template t) (lpp_structure_template (t\<cdot>theta))"
  by (rule lpp_leaf_effect_template_substitution) (use selected in blast)
 show ?thesis by (rule exI[of _ "t\<cdot>theta"]) (simp add: lp_ieval_subst evaluated effect)
qed


lemma lpp_bounded_images_compose:
 fixes sigma delta :: "'v \<Rightarrow> ('f,'v) lp_iterm"
 assumes first_images: "lpp_bounded_images A sigma V"
 and later_images: "lpp_bounded_images A delta (\<Union>x\<in>V. set2_lp_iterm (sigma x))"
 and ground_templates: "\<And>u. u\<in>A \<Longrightarrow> vars_term u={}"
 shows "lpp_bounded_images A (\<lambda>x. lp_isubst (sigma x) delta) V"
proof (unfold lpp_bounded_images_def, intro ballI)
 fix x assume member: "x\<in>V"
 have image: "(\<exists>y. sigma x=LPIVar y) \<or> (\<exists>u\<in>A. sigma x=lp_ieval u LPIVar)"
  using first_images member unfolding lpp_bounded_images_def by blast
 show "(\<exists>y. lp_isubst (sigma x) delta=LPIVar y) \<or>
   (\<exists>u\<in>A. lp_isubst (sigma x) delta=lp_ieval u LPIVar)"
 proof (rule disjE[OF image])
  assume "\<exists>y. sigma x=LPIVar y"
  then obtain y where image: "sigma x=LPIVar y" by blast
  have covered: "y\<in>(\<Union>x\<in>V. set2_lp_iterm (sigma x))"
   by (rule UN_I[OF member]) (simp add: image)
  show ?thesis using later_images covered unfolding lpp_bounded_images_def
   by (auto simp: image)
 next
  assume "\<exists>u\<in>A. sigma x=lp_ieval u LPIVar"
  then obtain u where allowed: "u\<in>A" and image: "sigma x=lp_ieval u LPIVar" by blast
  have grounded: "lp_seg_ground (lp_ieval u LPIVar)"
   using ground_templates[OF allowed] by (simp add: lp_seg_ground_eval)
  have unchanged: "lp_isubst (sigma x) delta=lp_ieval u LPIVar"
   using lp_seg_ground_subst[OF grounded, of delta] by (simp add: image)
  show ?thesis using allowed unchanged by blast
 qed
qed

lemma lpp_leaf_effect_preserves_constructor:
 "lpp_leaf_effect A (Fun (Inl f) xs) (Fun (Inl g) ys) \<Longrightarrow> f=g"
 by (cases rule: lpp_leaf_effect.cases) auto

lemma lpp_empty_leaf_effect_rejects_constructor:
 "\<not>lpp_leaf_effect {} (Fun (Inr ()) []) (Fun (Inl f) ts)"
 by (auto elim: lpp_leaf_effect.cases)

lemma lpp_bounded_images_reject_cycle:
 assumes bounded: "lpp_bounded_images A sigma V" and member: "x\<in>V"
 and cycle: "sigma x=LPIFun f [sigma x]"
 shows False
 using lpp_finite_constructor_not_self_child[OF lpp_bounded_image_finite[OF bounded member]] cycle by blast


text \<open>The bound is an additional premise: finite replacements alone do not
provide a uniform measure. Give each uninstantiated leaf enough weight to pay
for any permitted replacement. Constructor descent is then strict even when
other leaves have been instantiated by a successful helper.\<close>

lemma lpp_leaf_budget_list_mono:
 "list_all2 (\<lambda>x y. lpp_leaf_budget k y \<le> lpp_leaf_budget k x) xs ys \<Longrightarrow>
 sum_list (map (lpp_leaf_budget k) ys) \<le> sum_list (map (lpp_leaf_budget k) xs)"
 by (induct rule: list_all2_induct) auto

lemma lpp_leaf_effect_budget:
 assumes effect: "lpp_leaf_effect A s t"
 and budget: "\<And>u. u\<in>A \<Longrightarrow> lpp_leaf_budget k (lpp_structure_template u) \<le> k"
 shows "lpp_leaf_budget k t \<le> lpp_leaf_budget k s"
 using effect
proof (induct rule: lpp_leaf_effect.induct)
 case unchanged
 then show ?case by simp
next
 case (replace u)
 then show ?case using budget by simp
next
 case (constructor xs ys f)
 have children: "list_all2 (\<lambda>x y. lpp_leaf_budget k y \<le> lpp_leaf_budget k x) xs ys"
  using constructor by (auto elim: list_all2_mono)
 show ?case using lpp_leaf_budget_list_mono[OF children] by simp
qed

lemma lpp_leaf_budget_child_strict:
 assumes member: "t\<in>set ts"
 shows "lpp_leaf_budget k t < lpp_leaf_budget k (Fun (Inl f) ts)"
proof -
 have "lpp_leaf_budget k t \<le> sum_list (map (lpp_leaf_budget k) ts)"
  using member by (induct ts) auto
 then show ?thesis by simp
qed


lemma lpp_returned_child_budget_strict:
 assumes member: "s\<in>set ts" and effect: "lpp_leaf_effect A s t"
 and budget: "\<And>u. u\<in>A \<Longrightarrow> lpp_leaf_budget k (lpp_structure_template u) \<le> k"
 shows "lpp_leaf_budget k t < lpp_leaf_budget k (Fun (Inl f) ts)"
proof -
 have nonincrease: "lpp_leaf_budget k t \<le> lpp_leaf_budget k s"
  by (rule lpp_leaf_effect_budget[OF effect]) (rule budget)
 have decrease: "lpp_leaf_budget k s < lpp_leaf_budget k (Fun (Inl f) ts)"
  by (rule lpp_leaf_budget_child_strict[OF member])
 show ?thesis using nonincrease decrease by arith
qed

lemma lpp_binary_atomic_template_budget:
 "lpp_leaf_budget k (lpp_structure_template (Fun f [Fun g [], Fun h []]))=3"
 by simp

lemma lpp_insufficient_leaf_budget:
 assumes oversized: "k < lpp_leaf_budget k (lpp_structure_template u)"
 shows "lpp_leaf_effect {u} (Fun (Inr ()) []) (lpp_structure_template u) \<and>
   \<not>lpp_leaf_budget k (lpp_structure_template u) \<le> lpp_leaf_budget k (Fun (Inr ()) [])"
 using oversized by (auto intro: lpp_leaf_effect.replace)

ML \<open>
val checked = @{thms lpp_bounded_image_finite lpp_leaf_effect_template_substitution
 lpp_bounded_runtime_structural_effect lpp_bounded_images_compose
 lpp_leaf_effect_preserves_constructor lpp_empty_leaf_effect_rejects_constructor
 lpp_bounded_images_reject_cycle lpp_leaf_budget_list_mono
 lpp_leaf_effect_budget lpp_leaf_budget_child_strict
 lpp_returned_child_budget_strict lpp_binary_atomic_template_budget
 lpp_insufficient_leaf_budget};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted bounded instantiation" else ();
\<close>
end
