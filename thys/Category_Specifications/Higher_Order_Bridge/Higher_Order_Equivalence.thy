theory Higher_Order_Equivalence
  imports Category_Specifications.Higher_Order_Spec
    Higher_Order_Checker.Higher_Order_Core
begin

fun to_ho_type :: "higher_type \<Rightarrow> ho_type" where
  "to_ho_type (SpecHBase n) = HBase n"
| "to_ho_type (SpecHArrow a b) = HArrow (to_ho_type a) (to_ho_type b)"

fun to_ho_term :: "higher_term \<Rightarrow> ho_term" where
  "to_ho_term (SpecHBound n) = HBound n"
| "to_ho_term (SpecHFree n) = HFree n"
| "to_ho_term (SpecHConst n) = HConst n"
| "to_ho_term (SpecHApp t u) = HApp (to_ho_term t) (to_ho_term u)"
| "to_ho_term (SpecHAbs a t) = HAbs (to_ho_type a) (to_ho_term t)"

fun to_ho_pattern :: "higher_pattern \<Rightarrow> ho_pattern" where
  "to_ho_pattern (SpecPBound n) = PBound n"
| "to_ho_pattern (SpecPConst n) = PConst n"
| "to_ho_pattern (SpecPApp p q) = PApp (to_ho_pattern p) (to_ho_pattern q)"
| "to_ho_pattern (SpecPAbs a p) = PAbs (to_ho_type a) (to_ho_pattern p)"
| "to_ho_pattern (SpecPMeta n ps) = PMeta n (map to_ho_pattern ps)"

fun from_ho_type :: "ho_type \<Rightarrow> higher_type" where
  "from_ho_type (HBase n) = SpecHBase n"
| "from_ho_type (HArrow a b) = SpecHArrow (from_ho_type a) (from_ho_type b)"

fun from_ho_term :: "ho_term \<Rightarrow> higher_term" where
  "from_ho_term (HBound n) = SpecHBound n"
| "from_ho_term (HFree n) = SpecHFree n"
| "from_ho_term (HConst n) = SpecHConst n"
| "from_ho_term (HApp t u) = SpecHApp (from_ho_term t) (from_ho_term u)"
| "from_ho_term (HAbs a t) = SpecHAbs (from_ho_type a) (from_ho_term t)"

fun from_ho_pattern :: "ho_pattern \<Rightarrow> higher_pattern" where
  "from_ho_pattern (PBound n) = SpecPBound n"
| "from_ho_pattern (PConst n) = SpecPConst n"
| "from_ho_pattern (PApp p q) = SpecPApp (from_ho_pattern p) (from_ho_pattern q)"
| "from_ho_pattern (PAbs a p) = SpecPAbs (from_ho_type a) (from_ho_pattern p)"
| "from_ho_pattern (PMeta n ps) = SpecPMeta n (map from_ho_pattern ps)"

lemma from_to_ho_type [simp]: "from_ho_type (to_ho_type t) = t"
  by (induct t) (auto simp: comp_def intro: map_idI)
lemma to_from_ho_type [simp]: "to_ho_type (from_ho_type t) = t"
  by (induct t) (auto simp: comp_def intro: map_idI)
lemma to_ho_type_inj [simp]: "to_ho_type s = to_ho_type t \<longleftrightarrow> s = t"
  by (metis from_to_ho_type)

lemma from_to_ho_term [simp]: "from_ho_term (to_ho_term t) = t"
  by (induct t) (auto simp: comp_def intro: map_idI)
lemma to_from_ho_term [simp]: "to_ho_term (from_ho_term t) = t"
  by (induct t) (auto simp: comp_def intro: map_idI)
lemma to_ho_term_inj [simp]: "to_ho_term s = to_ho_term t \<longleftrightarrow> s = t"
  by (metis from_to_ho_term)

lemma from_to_ho_pattern [simp]: "from_ho_pattern (to_ho_pattern t) = t"
  by (induct t) (auto simp: comp_def intro: map_idI)
lemma to_from_ho_pattern [simp]: "to_ho_pattern (from_ho_pattern t) = t"
  by (induct t) (auto simp: comp_def intro: map_idI)
lemma to_ho_pattern_inj [simp]: "to_ho_pattern s = to_ho_pattern t \<longleftrightarrow> s = t"
  by (metis from_to_ho_pattern)

definition to_ho_rule where
  "to_ho_rule r = (case r of (G,l,u) \<Rightarrow> (map to_ho_type G,to_ho_pattern l,to_ho_pattern u))"
definition from_ho_rule where
  "from_ho_rule r = (case r of (G,l,u) \<Rightarrow> (map from_ho_type G,from_ho_pattern l,from_ho_pattern u))"
lemma from_to_ho_rule [simp]: "from_ho_rule (to_ho_rule r) = r"
  by (cases r) (auto simp: to_ho_rule_def from_ho_rule_def comp_def)
lemma to_from_ho_rule [simp]: "to_ho_rule (from_ho_rule r) = r"
  by (cases r) (auto simp: to_ho_rule_def from_ho_rule_def comp_def)
lemma translate_typeof:
  "ho_typeof (map to_ho_type S) (map to_ho_type V) (map to_ho_type B) (to_ho_term t) =
    map_option to_ho_type (higher_typeof S V B t)"
proof (induct t arbitrary: B)
  case (SpecHAbs A t)
  show ?case using SpecHAbs[of "A # B"]
    by (simp add: map_option.compositionality comp_def option.map_id)
qed (auto split: option.splits higher_type.splits)
lemma translate_typeof_empty:
  "ho_typeof (map to_ho_type S) (map to_ho_type V) [] (to_ho_term t) =
    map_option to_ho_type (higher_typeof S V [] t)"
  using translate_typeof[of S V "[]" t] by simp
lemma translate_lift [simp]:
  "to_ho_term (higher_lift d k t) = ho_lift d k (to_ho_term t)"
  by (induct t arbitrary: k) auto
lemma translate_beta_subst [simp]:
  "to_ho_term (higher_beta_subst u k t) = ho_beta_subst (to_ho_term u) k (to_ho_term t)"
  by (induct t arbitrary: k) auto
lemma translate_meta_apply:
  "ho_meta_apply (to_ho_term t) (map to_ho_term us) = map_option to_ho_term (higher_meta_apply t us)"
  proof (induct us arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons u us)
  then show ?case
    by (cases t) (simp_all only: higher_meta_apply.simps to_ho_term.simps ho_meta_apply.simps
      translate_beta_subst[symmetric] Cons.hyps higher_term.case ho_term.case list.map option.map)
qed
lemma those_map_option:
  "those (map (map_option f) xs) = map_option (map f) (those xs)"
  by (induct xs) (auto simp: map_option.compositionality comp_def split: option.splits)
lemma those_map_comp:
  "those (map (\<lambda>x. map_option f (g x)) xs) = map_option (map f) (those (map g xs))"
  using those_map_option[of f "map g xs"] by (simp only: map_map comp_def)
lemma translate_instantiate:
  "ho_instantiate (to_ho_term \<circ> sigma) d (to_ho_pattern p) =
    map_option to_ho_term (higher_instantiate sigma d p)"
proof (induct p arbitrary: d)
  case (SpecPMeta n ps)
  have mapped: "map (\<lambda>p. ho_instantiate (to_ho_term \<circ> sigma) d (to_ho_pattern p)) ps =
      map (map_option to_ho_term) (map (higher_instantiate sigma d) ps)"
    using SpecPMeta by (auto simp: comp_def intro!: map_cong)
  show ?case
    by (cases "those (map (higher_instantiate sigma d) ps)")
      (simp_all add: map_map comp_def mapped[unfolded comp_def] those_map_comp
        translate_meta_apply translate_lift[symmetric] del: translate_lift)
qed (auto simp: map_option.compositionality comp_def split: option.splits)
lemma translate_apps:
  "foldl HApp (to_ho_term t) (map to_ho_term ts) = to_ho_term (foldl SpecHApp t ts)"
proof (induct ts arbitrary: t)
  case Nil then show ?case by simp
next
  case (Cons a ts)
  show ?case using Cons.hyps[of "SpecHApp t a"] by simp
qed
lemma translate_erase [simp]:
  "ho_erase_pattern (to_ho_pattern p) = to_ho_term (higher_erase_pattern p)"
proof (induct p)
  case (SpecPMeta n ps)
  have mapped: "map (\<lambda>p. ho_erase_pattern (to_ho_pattern p)) ps =
    map to_ho_term (map higher_erase_pattern ps)"
    using SpecPMeta by (auto intro!: map_cong)
  show ?case
    using translate_apps[of "SpecHFree n" "map higher_erase_pattern ps"]
    by (simp only: to_ho_pattern.simps ho_erase_pattern.simps higher_erase_pattern.simps
      map_map comp_def mapped to_ho_term.simps)
qed auto
lemma translate_rule_welltyped [simp]:
  "ho_rule_welltyped (map to_ho_type S) (to_ho_rule r) = higher_rule_welltyped S r"
  by (cases r) (auto simp: to_ho_rule_def ho_rule_welltyped_def higher_rule_welltyped_def
      translate_typeof_empty split: option.splits)
lemma translate_typed_subst:
  "ho_typed_subst (map to_ho_type S) (map to_ho_type V) (map to_ho_type B)
    (map to_ho_type G) (to_ho_term \<circ> sigma) = higher_typed_subst S V B G sigma"
  by (auto simp: ho_typed_subst_def higher_typed_subst_def translate_typeof comp_def nth_map)

lemma higher_option_identity [simp]: "map_option (\<lambda>x. x) u = u"
  by (cases u) auto
lemma inverse_typeof:
  "higher_typeof (map from_ho_type S) (map from_ho_type V) (map from_ho_type B) (from_ho_term t) =
    map_option from_ho_type (ho_typeof S V B t)"
proof -
  note h = translate_typeof[of "map from_ho_type S" "map from_ho_type V" "map from_ho_type B" "from_ho_term t"]
  show ?thesis using arg_cong[OF h, of "map_option from_ho_type"]
    by (simp add: map_option.compositionality comp_def option.map_id)
qed
lemma inverse_instantiate:
  "higher_instantiate (from_ho_term \<circ> sigma) d (from_ho_pattern p) =
    map_option from_ho_term (ho_instantiate sigma d p)"
proof -
  have inv: "to_ho_term \<circ> (from_ho_term \<circ> sigma) = sigma" by auto
  note h = translate_instantiate[of "from_ho_term \<circ> sigma" d "from_ho_pattern p"]
  show ?thesis using arg_cong[OF h, of "map_option from_ho_term"]
    by (simp add: inv map_option.compositionality comp_def option.map_id)
qed
lemma inverse_rule_welltyped [simp]:
  "higher_rule_welltyped (map from_ho_type S) (from_ho_rule r) = ho_rule_welltyped S r"
  using translate_rule_welltyped[of "map from_ho_type S" "from_ho_rule r"]
  by (simp add: comp_def)
lemma inverse_typed_subst:
  "higher_typed_subst (map from_ho_type S) (map from_ho_type V) (map from_ho_type B)
    (map from_ho_type G) (from_ho_term \<circ> sigma) = ho_typed_subst S V B G sigma"
  using translate_typed_subst[of "map from_ho_type S" "map from_ho_type V" "map from_ho_type B"
      "map from_ho_type G" "from_ho_term \<circ> sigma"]
  by (simp add: comp_def)
lemma inverse_beta_subst [simp]:
  "from_ho_term (ho_beta_subst u k t) = higher_beta_subst (from_ho_term u) k (from_ho_term t)"
  by (metis translate_beta_subst from_to_ho_term to_from_ho_term)

lemma translate_step:
  "higher_step S V R B t u \<Longrightarrow>
   ho_step (map to_ho_type S) (map to_ho_type V) (map to_ho_rule R) (map to_ho_type B)
     (to_ho_term t) (to_ho_term u)"
proof (induct rule: higher_step.induct)
  case (rule G l r B sigma t u)
  have mem: "(map to_ho_type G, to_ho_pattern l, to_ho_pattern r) \<in> set (map to_ho_rule R)"
    using rule.hyps(1) by (force simp: to_ho_rule_def)
  have typed: "ho_rule_welltyped (map to_ho_type S) (map to_ho_type G, to_ho_pattern l, to_ho_pattern r)"
    using translate_rule_welltyped[of S "(G,l,r)"] rule.hyps(2) by (simp add: to_ho_rule_def)
  show ?case
    by (rule ho_step.rule[OF mem typed, where s="to_ho_term \<circ> sigma"])
      (use rule.hyps in \<open>auto simp: to_ho_rule_def[symmetric] translate_typed_subst translate_instantiate\<close>)
qed (auto intro: ho_step.intros)

lemma inverse_step:
  "ho_step S V R B t u \<Longrightarrow>
   higher_step (map from_ho_type S) (map from_ho_type V) (map from_ho_rule R) (map from_ho_type B)
     (from_ho_term t) (from_ho_term u)"
proof (induct rule: ho_step.induct)
  case (rule G l r B sigma t u)
  have mem: "(map from_ho_type G, from_ho_pattern l, from_ho_pattern r) \<in> set (map from_ho_rule R)"
    using rule.hyps(1) by (force simp: from_ho_rule_def)
  have typed: "higher_rule_welltyped (map from_ho_type S) (map from_ho_type G, from_ho_pattern l, from_ho_pattern r)"
    using inverse_rule_welltyped[of S "(G,l,r)"] rule.hyps(2) by (simp add: from_ho_rule_def)
  show ?case
    by (rule higher_step.rule[OF mem typed, where s="from_ho_term \<circ> sigma"])
      (use rule.hyps in \<open>auto simp: from_ho_rule_def[symmetric] inverse_typed_subst inverse_instantiate\<close>)
qed (auto intro: higher_step.intros)

lemma higher_step_iff:
  "higher_step S V R B t u \<longleftrightarrow>
   ho_step (map to_ho_type S) (map to_ho_type V) (map to_ho_rule R) (map to_ho_type B)
     (to_ho_term t) (to_ho_term u)"
  using translate_step inverse_step by (fastforce simp: comp_def)

lemma higher_order_step_iff:
  "higher_order_step S V R A t u \<longleftrightarrow>
    (to_ho_term t, to_ho_term u) \<in>
      ho_relation (map to_ho_type S) (map to_ho_type V) (map to_ho_rule R) (to_ho_type A)"
  by (auto simp: higher_order_step_def ho_relation_def translate_typeof_empty higher_step_iff)

lemma higher_order_typed_termination_iff:
  "no_infinite_steps (higher_order_step S V R A) \<longleftrightarrow>
    wf ((ho_relation (map to_ho_type S) (map to_ho_type V) (map to_ho_rule R) (to_ho_type A))\<inverse>)"
proof -
  have chains: "(\<exists>ts. \<forall>i. higher_order_step S V R A (ts i) (ts (Suc i))) \<longleftrightarrow>
    (\<exists>ts. \<forall>i. (ts i, ts (Suc i)) \<in> ho_relation (map to_ho_type S) (map to_ho_type V) (map to_ho_rule R) (to_ho_type A))"
  proof
    assume "\<exists>ts. \<forall>i. higher_order_step S V R A (ts i) (ts (Suc i))"
    then obtain ts where "\<forall>i. higher_order_step S V R A (ts i) (ts (Suc i))" by blast
    then show "\<exists>ts. \<forall>i. (ts i, ts (Suc i)) \<in> ho_relation (map to_ho_type S) (map to_ho_type V) (map to_ho_rule R) (to_ho_type A)"
      by (intro exI[of _ "to_ho_term \<circ> ts"]) (simp add: higher_order_step_iff)
  next
    assume "\<exists>ts. \<forall>i. (ts i, ts (Suc i)) \<in> ho_relation (map to_ho_type S) (map to_ho_type V) (map to_ho_rule R) (to_ho_type A)"
    then obtain ts where "\<forall>i. (ts i, ts (Suc i)) \<in> ho_relation (map to_ho_type S) (map to_ho_type V) (map to_ho_rule R) (to_ho_type A)" by blast
    then show "\<exists>ts. \<forall>i. higher_order_step S V R A (ts i) (ts (Suc i))"
      by (intro exI[of _ "from_ho_term \<circ> ts"]) (simp add: higher_order_step_iff)
  qed
  show ?thesis using chains by (simp add: no_infinite_steps_def wf_iff_no_infinite_down_chain)
qed

theorem higher_order_terminates_iff:
  "higher_order_terminates S R \<longleftrightarrow>
    (\<forall>V A. wf ((ho_relation (map to_ho_type S) V (map to_ho_rule R) A)\<inverse>))"
proof
  assume terminating: "higher_order_terminates S R"
  show "\<forall>V A. wf ((ho_relation (map to_ho_type S) V (map to_ho_rule R) A)\<inverse>)"
  proof (intro allI)
    fix V A
    have "wf ((ho_relation (map to_ho_type S) (map to_ho_type (map from_ho_type V))
        (map to_ho_rule R) (to_ho_type (from_ho_type A)))\<inverse>)"
      using terminating unfolding higher_order_terminates_def higher_order_typed_termination_iff by blast
    then show "wf ((ho_relation (map to_ho_type S) V (map to_ho_rule R) A)\<inverse>)"
      by (simp add: comp_def)
  qed
next
  assume "\<forall>V A. wf ((ho_relation (map to_ho_type S) V (map to_ho_rule R) A)\<inverse>)"
  then show "higher_order_terminates S R"
    unfolding higher_order_terminates_def higher_order_typed_termination_iff by blast
qed

corollary higher_order_nonterminates_iff:
  "\<not> higher_order_terminates S R \<longleftrightarrow>
    (\<exists>V A. \<not> wf ((ho_relation (map to_ho_type S) V (map to_ho_rule R) A)\<inverse>))"
  by (simp add: higher_order_terminates_iff)
end
