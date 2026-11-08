theory Higher_Order_Spec_Base
  imports Rewriting_Sequences_Spec
begin

text \<open>Simply typed applicative terms with explicit de Bruijn binders.
Free rule variables and function symbols occupy distinct namespaces.
Rewriting uses arity-aware meta-substitution, in union with beta, not arbitrary
matching modulo beta or eta. No first-order erasure is used.\<close>

datatype higher_type = SpecHBase nat | SpecHArrow higher_type higher_type
datatype higher_term = SpecHBound nat | SpecHFree nat | SpecHConst nat
  | SpecHApp higher_term higher_term | SpecHAbs higher_type higher_term

fun higher_lookup where
  "higher_lookup xs n = (if n < length xs then Some (xs ! n) else None)"

fun higher_typeof :: "higher_type list \<Rightarrow> higher_type list \<Rightarrow> higher_type list
    \<Rightarrow> higher_term \<Rightarrow> higher_type option" where
  "higher_typeof S V B (SpecHBound n) = higher_lookup B n"
| "higher_typeof S V B (SpecHFree n) = higher_lookup V n"
| "higher_typeof S V B (SpecHConst n) = higher_lookup S n"
| "higher_typeof S V B (SpecHApp f x) = (case higher_typeof S V B f of
    Some (SpecHArrow A C) \<Rightarrow> (if higher_typeof S V B x = Some A then Some C else None)
  | _ \<Rightarrow> None)"
| "higher_typeof S V B (SpecHAbs A t) = map_option (SpecHArrow A) (higher_typeof S V (A # B) t)"

fun higher_lift :: "nat \<Rightarrow> nat \<Rightarrow> higher_term \<Rightarrow> higher_term" where
  "higher_lift d k (SpecHBound n) = SpecHBound (if n < k then n else n+d)"
| "higher_lift d k (SpecHFree n) = SpecHFree n"
| "higher_lift d k (SpecHConst n) = SpecHConst n"
| "higher_lift d k (SpecHApp f x) = SpecHApp (higher_lift d k f) (higher_lift d k x)"
| "higher_lift d k (SpecHAbs A t) = SpecHAbs A (higher_lift d (Suc k) t)"

fun higher_beta_subst :: "higher_term \<Rightarrow> nat \<Rightarrow> higher_term \<Rightarrow> higher_term" where
  "higher_beta_subst u k (SpecHBound n) = (if n < k then SpecHBound n
    else if n = k then higher_lift k 0 u else SpecHBound (n-1))"
| "higher_beta_subst u k (SpecHFree n) = SpecHFree n"
| "higher_beta_subst u k (SpecHConst n) = SpecHConst n"
| "higher_beta_subst u k (SpecHApp f x) = SpecHApp (higher_beta_subst u k f) (higher_beta_subst u k x)"
| "higher_beta_subst u k (SpecHAbs A t) = SpecHAbs A (higher_beta_subst u (Suc k) t)"

text \<open>Meta-application is explicit in rules. Only the designated
meta-arguments are contracted; ordinary application is never normalized.
Meta-substitution images are represented by exactly the required leading
abstractions (possibly followed by further, ordinary abstractions).\<close>

datatype higher_pattern = SpecPBound nat | SpecPConst nat | SpecPApp higher_pattern higher_pattern
  | SpecPAbs higher_type higher_pattern | SpecPMeta nat "higher_pattern list"

fun higher_meta_apply :: "higher_term \<Rightarrow> higher_term list \<Rightarrow> higher_term option" where
  "higher_meta_apply t [] = Some t"
| "higher_meta_apply t (u#us) = (case t of SpecHAbs A b \<Rightarrow>
    higher_meta_apply (higher_beta_subst u 0 b) us | _ \<Rightarrow> None)"

fun higher_instantiate :: "(nat \<Rightarrow> higher_term) \<Rightarrow> nat \<Rightarrow> higher_pattern \<Rightarrow> higher_term option" where
  "higher_instantiate s d (SpecPBound n) = Some (SpecHBound n)"
| "higher_instantiate s d (SpecPConst n) = Some (SpecHConst n)"
| "higher_instantiate s d (SpecPApp f x) = (case higher_instantiate s d f of None \<Rightarrow> None
    | Some a \<Rightarrow> map_option (SpecHApp a) (higher_instantiate s d x))"
| "higher_instantiate s d (SpecPAbs A t) = map_option (SpecHAbs A) (higher_instantiate s (Suc d) t)"
| "higher_instantiate s d (SpecPMeta n ts) = (case those (map (higher_instantiate s d) ts) of
    None \<Rightarrow> None | Some us \<Rightarrow> higher_meta_apply (higher_lift d 0 (s n)) us)"

fun higher_erase_pattern :: "higher_pattern \<Rightarrow> higher_term" where
  "higher_erase_pattern (SpecPBound n) = SpecHBound n"
| "higher_erase_pattern (SpecPConst n) = SpecHConst n"
| "higher_erase_pattern (SpecPApp f x) = SpecHApp (higher_erase_pattern f) (higher_erase_pattern x)"
| "higher_erase_pattern (SpecPAbs A t) = SpecHAbs A (higher_erase_pattern t)"
| "higher_erase_pattern (SpecPMeta n ts) = foldl SpecHApp (SpecHFree n) (map higher_erase_pattern ts)"

type_synonym higher_rule = "higher_type list \<times> higher_pattern \<times> higher_pattern"

definition higher_rule_welltyped where
  "higher_rule_welltyped S r \<longleftrightarrow> (case r of (G,l,u) \<Rightarrow>
    case higher_typeof S G [] (higher_erase_pattern l) of None \<Rightarrow> False
      | Some A \<Rightarrow> higher_typeof S G [] (higher_erase_pattern u) = Some A)"

definition higher_typed_subst where
  "higher_typed_subst S V B G s \<longleftrightarrow>
    (\<forall>n<length G. higher_typeof S V B (s n) = Some (G!n))"

inductive higher_step :: "higher_type list \<Rightarrow> higher_type list \<Rightarrow> higher_rule list
    \<Rightarrow> higher_type list \<Rightarrow> higher_term \<Rightarrow> higher_term \<Rightarrow> bool" for S V R where
  rule: "(G,l,r) \<in> set R \<Longrightarrow> higher_rule_welltyped S (G,l,r) \<Longrightarrow>
    higher_typed_subst S V B G s \<Longrightarrow>
    higher_instantiate s 0 l = Some t \<Longrightarrow> higher_instantiate s 0 r = Some u \<Longrightarrow>
    higher_step S V R B t u"
| beta: "higher_step S V R B (SpecHApp (SpecHAbs A t) u) (higher_beta_subst u 0 t)"
| app_left: "higher_step S V R B t u \<Longrightarrow> higher_step S V R B (SpecHApp t x) (SpecHApp u x)"
| app_right: "higher_step S V R B t u \<Longrightarrow> higher_step S V R B (SpecHApp x t) (SpecHApp x u)"
| abs: "higher_step S V R (A#B) t u \<Longrightarrow> higher_step S V R B (SpecHAbs A t) (SpecHAbs A u)"

end
