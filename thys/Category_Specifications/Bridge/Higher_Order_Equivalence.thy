theory Higher_Order_Equivalence
  imports Category_Specifications.Higher_Order_Spec
    Higher_Order_Checker.Higher_Order_Core Rewriting_Sequence_Equivalence
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
    by (simp add: map_option.compositionality comp_def)
qed (auto split: option.splits higher_type.splits)
lemma translate_lift [simp]:
  "to_ho_term (higher_lift d k t) = ho_lift d k (to_ho_term t)"
  by (induct t arbitrary: k) auto
lemma translate_beta_subst [simp]:
  "to_ho_term (higher_beta_subst u k t) = ho_beta_subst (to_ho_term u) k (to_ho_term t)"
  by (induct t arbitrary: k) auto
lemma translate_meta_apply:
  "ho_meta_apply (to_ho_term t) (map to_ho_term us) = map_option to_ho_term (higher_meta_apply t us)"
  by (induct us arbitrary: t) (auto split: higher_term.splits)
lemma those_map_option:
  "those (map (map_option f) xs) = map_option (map f) (those xs)"
  by (induct xs) (auto split: option.splits)
lemma translate_instantiate:
  "ho_instantiate (to_ho_term \<circ> sigma) d (to_ho_pattern p) =
    map_option to_ho_term (higher_instantiate sigma d p)"
  by (induct p arbitrary: d)
    (auto simp: comp_def translate_meta_apply those_map_option map_map split: option.splits)
lemma translate_erase [simp]:
  "ho_erase_pattern (to_ho_pattern p) = to_ho_term (higher_erase_pattern p)"
  by (induct p) (auto simp: foldl_map map_map comp_def foldl_cong)
lemma translate_rule_welltyped [simp]:
  "ho_rule_welltyped (map to_ho_type S) (to_ho_rule r) = higher_rule_welltyped S r"
  by (cases r) (auto simp: to_ho_rule_def ho_rule_welltyped_def higher_rule_welltyped_def
      translate_typeof split: option.splits)
lemma translate_typed_subst:
  "ho_typed_subst (map to_ho_type S) (map to_ho_type V) (map to_ho_type B)
    (map to_ho_type G) (to_ho_term \<circ> sigma) = higher_typed_subst S V B G sigma"
  by (auto simp: ho_typed_subst_def higher_typed_subst_def translate_typeof comp_def nth_map)
end
