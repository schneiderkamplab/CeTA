theory Higher_Order_Sort_Extension
  imports Higher_Order_Equivalence Category_Specifications.Higher_Order_Sorts_Spec
begin
fun hs_type where
  "hs_type N (SpecHBase n) = SpecHBase (if n < N then n else 0)"
| "hs_type N (SpecHArrow A B) = SpecHArrow (hs_type N A) (hs_type N B)"
fun hs_term where
  "hs_term N (SpecHBound n) = SpecHBound n"
| "hs_term N (SpecHFree n) = SpecHFree n"
| "hs_term N (SpecHConst n) = SpecHConst n"
| "hs_term N (SpecHApp t u) = SpecHApp (hs_term N t) (hs_term N u)"
| "hs_term N (SpecHAbs A t) = SpecHAbs (hs_type N A) (hs_term N t)"
fun hs_pattern where
  "hs_pattern N (SpecPBound n) = SpecPBound n"
| "hs_pattern N (SpecPConst n) = SpecPConst n"
| "hs_pattern N (SpecPApp t u) = SpecPApp (hs_pattern N t) (hs_pattern N u)"
| "hs_pattern N (SpecPAbs A t) = SpecPAbs (hs_type N A) (hs_pattern N t)"
| "hs_pattern N (SpecPMeta n ps) = SpecPMeta n (map (hs_pattern N) ps)"
definition hs_rule where
  "hs_rule N r = (case r of (G,l,u) \<Rightarrow> (map (hs_type N) G,hs_pattern N l,hs_pattern N u))"
lemma hs_type_fixed: "higher_sort_type N A \<Longrightarrow> hs_type N A = A"
  by (induct A) auto
lemma hs_types_fixed: "list_all (higher_sort_type N) G \<Longrightarrow> map (hs_type N) G = G"
  by (induct G) (auto intro: hs_type_fixed)
lemma hs_pattern_fixed: "higher_sort_pattern N p \<Longrightarrow> hs_pattern N p = p"
  by (induct p) (auto simp: list_all_iff intro: hs_type_fixed map_idI)
lemma hs_rule_fixed: "higher_sort_rule N r \<Longrightarrow> hs_rule N r = r"
  by (cases r) (auto simp: higher_sort_rule_def hs_rule_def hs_types_fixed hs_pattern_fixed)
lemma hs_term_fixed: "higher_sort_term N t \<Longrightarrow> hs_term N t = t"
  by (induct t) (auto intro: hs_type_fixed)
lemma hs_type_range: "0 < N \<Longrightarrow> higher_sort_type N (hs_type N A)"
  by (induct A) auto
lemma hs_term_range: "0 < N \<Longrightarrow> higher_sort_term N (hs_term N t)"
  by (induct t) (auto intro: hs_type_range)
lemma hs_typeof:
  "higher_typeof S V B t = Some A \<Longrightarrow>
   higher_typeof (map (hs_type N) S) (map (hs_type N) V) (map (hs_type N) B)
     (hs_term N t) = Some (hs_type N A)"
proof (induct t arbitrary: B A)
  case (SpecHAbs T t)
  show ?case using SpecHAbs.hyps[of "T # B"] SpecHAbs.prems
    by (auto split: option.splits)
qed (auto split: option.splits higher_type.splits if_splits)
lemma hs_typeof_empty:
  "higher_typeof S V [] t = Some A \<Longrightarrow>
    higher_typeof (map (hs_type N) S) (map (hs_type N) V) [] (hs_term N t) = Some (hs_type N A)"
  using hs_typeof[where B="[]" and N=N] by simp
lemma hs_lift [simp]: "hs_term N (higher_lift d k t) = higher_lift d k (hs_term N t)"
  by (induct t arbitrary: k) auto
lemma hs_beta [simp]:
  "hs_term N (higher_beta_subst u k t) = higher_beta_subst (hs_term N u) k (hs_term N t)"
  by (induct t arbitrary: k) auto
lemma hs_meta:
  "higher_meta_apply (hs_term N t) (map (hs_term N) us) = map_option (hs_term N) (higher_meta_apply t us)"
proof (induct us arbitrary: t)
  case Nil then show ?case by simp
next
  case (Cons u us)
  then show ?case by (cases t)
    (simp_all only: higher_meta_apply.simps hs_term.simps hs_beta[symmetric]
      Cons.hyps higher_term.case list.map option.map)
qed
lemma hs_instantiate:
  "higher_instantiate (hs_term N \<circ> sigma) d (hs_pattern N p) =
    map_option (hs_term N) (higher_instantiate sigma d p)"
proof (induct p arbitrary: d)
  case (SpecPMeta n ps)
  have mapped: "map (\<lambda>p. higher_instantiate (hs_term N \<circ> sigma) d (hs_pattern N p)) ps =
      map (map_option (hs_term N)) (map (higher_instantiate sigma d) ps)"
    using SpecPMeta by (auto simp: comp_def intro!: map_cong)
  show ?case
    by (cases "those (map (higher_instantiate sigma d) ps)")
      (simp_all add: map_map comp_def mapped[unfolded comp_def] those_map_comp
        hs_meta hs_lift[symmetric] del: hs_lift)
qed (auto simp: map_option.compositionality comp_def split: option.splits)
text \<open>Restricting rule instances to declared endpoint terms does not
admit hidden extra-sort substitutions: projection supplies declared-sort
images and leaves each such instance unchanged. The same projected substitution
works for both sides of a rule.\<close>
lemma hs_declared_instance:
  assumes "0 < N" "higher_sort_pattern N p" "higher_sort_term N t"
    "higher_instantiate sigma d p = Some t"
  shows "higher_instantiate (hs_term N \<circ> sigma) d p = Some t"
    "\<And>n. higher_sort_term N ((hs_term N \<circ> sigma) n)"
  using hs_instantiate[of N sigma d p] assms hs_term_range[OF assms(1)]
  by (simp_all add: hs_pattern_fixed hs_term_fixed comp_def)
lemma hs_apps:
  "foldl SpecHApp (hs_term N t) (map (hs_term N) ts) = hs_term N (foldl SpecHApp t ts)"
proof (induct ts arbitrary: t)
  case Nil then show ?case by simp
next
  case (Cons a ts) show ?case using Cons.hyps[of "SpecHApp t a"] by simp
qed
lemma hs_erase [simp]:
  "higher_erase_pattern (hs_pattern N p) = hs_term N (higher_erase_pattern p)"
proof (induct p)
  case (SpecPMeta n ps)
  have mapped: "map (\<lambda>p. higher_erase_pattern (hs_pattern N p)) ps =
    map (hs_term N) (map higher_erase_pattern ps)"
    using SpecPMeta by (auto intro!: map_cong)
  show ?case using hs_apps[of N "SpecHFree n" "map higher_erase_pattern ps"]
    by (simp only: hs_pattern.simps higher_erase_pattern.simps map_map comp_def mapped hs_term.simps)
qed auto
lemma hs_rule_typed:
  "higher_rule_welltyped S r \<Longrightarrow> higher_rule_welltyped (map (hs_type N) S) (hs_rule N r)"
proof -
  assume typed: "higher_rule_welltyped S r"
  obtain G l u where r: "r = (G,l,u)" by (cases r) auto
  obtain A where l: "higher_typeof S G [] (higher_erase_pattern l) = Some A"
    and u: "higher_typeof S G [] (higher_erase_pattern u) = Some A"
    using typed unfolding r higher_rule_welltyped_def by (auto split: option.splits)
  show ?thesis using hs_typeof_empty[OF l, of N] hs_typeof_empty[OF u, of N]
    by (simp add: r hs_rule_def higher_rule_welltyped_def)
qed
lemma hs_subst:
  "higher_typed_subst S V B G sigma \<Longrightarrow>
   higher_typed_subst (map (hs_type N) S) (map (hs_type N) V) (map (hs_type N) B)
     (map (hs_type N) G) (hs_term N \<circ> sigma)"
  by (auto simp: higher_typed_subst_def comp_def nth_map intro: hs_typeof)
lemma hs_step:
  "higher_step S V R B t u \<Longrightarrow>
   higher_step (map (hs_type N) S) (map (hs_type N) V) (map (hs_rule N) R) (map (hs_type N) B)
     (hs_term N t) (hs_term N u)"
proof (induct rule: higher_step.induct)
  case (rule G l r B sigma t u)
  have mem: "(map (hs_type N) G, hs_pattern N l, hs_pattern N r) \<in> set (map (hs_rule N) R)"
    using rule.hyps(1) by (force simp: hs_rule_def)
  have typed: "higher_rule_welltyped (map (hs_type N) S)
    (map (hs_type N) G, hs_pattern N l, hs_pattern N r)"
    using hs_rule_typed[OF rule.hyps(2), of N] by (simp add: hs_rule_def)
  show ?case
    by (rule higher_step.rule[OF mem typed, where s="hs_term N \<circ> sigma"])
      (use rule.hyps in \<open>auto simp: hs_instantiate intro: hs_subst\<close>)
qed (auto intro: higher_step.intros)
lemma hs_typed_step:
  "higher_order_step S V R A t u \<Longrightarrow>
   higher_order_step (map (hs_type N) S) (map (hs_type N) V) (map (hs_rule N) R) (hs_type N A)
     (hs_term N t) (hs_term N u)"
  unfolding higher_order_step_def
  using hs_step[where B="[]" and N=N] hs_typeof[where B="[]" and N=N] by auto

lemma higher_order_sorts_extension:
  assumes "0 < N" "list_all (higher_sort_type N) S" "list_all (higher_sort_rule N) R"
  shows "higher_order_terminates_over_sorts N S R \<longleftrightarrow> higher_order_terminates S R"
proof
  assume finite: "higher_order_terminates_over_sorts N S R"
  have sig: "map (hs_type N) S = S" using assms(2) by (rule hs_types_fixed)
  have rules: "map (hs_rule N) R = R"
    using assms(3) by (induct R) (auto intro: hs_rule_fixed)
  show "higher_order_terminates S R"
  proof (rule ccontr)
    assume "\<not> higher_order_terminates S R"
    then obtain V A ts where seq: "\<And>i. higher_order_step S V R A (ts i) (ts (Suc i))"
      by (auto simp: higher_order_nontermination_iff)
    have steps: "\<And>i. higher_order_step S (map (hs_type N) V) R (hs_type N A)
        (hs_term N (ts i)) (hs_term N (ts (Suc i)))"
      using hs_typed_step[OF seq, of N] by (simp add: sig rules)
    have V: "list_all (higher_sort_type N) (map (hs_type N) V)"
      using assms(1) by (simp add: list_all_iff hs_type_range)
    have seq': "\<exists>us. \<forall>i. higher_sort_term N (us i) \<and> higher_sort_term N (us (Suc i)) \<and>
      higher_order_step S (map (hs_type N) V) R (hs_type N A) (us i) (us (Suc i))"
      by (intro exI[of _ "\<lambda>i. hs_term N (ts i)"] allI conjI)
        (use steps hs_term_range[OF assms(1)] in auto)
    show False using finite V hs_type_range[OF assms(1), of A] seq'
      unfolding higher_order_terminates_over_sorts_def no_infinite_steps_def by blast
  qed
next
  assume "higher_order_terminates S R"
  then show "higher_order_terminates_over_sorts N S R"
    unfolding higher_order_terminates_def higher_order_terminates_over_sorts_def no_infinite_steps_def
    by blast
qed
end
