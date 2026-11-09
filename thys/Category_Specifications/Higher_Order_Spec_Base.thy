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

text \<open>Typing uses three finite environments: S lists constant types, V
lists free-variable types, and B lists enclosing binder types, innermost first.
An out-of-range index has no type. Arrow types describe ordinary application.\<close>
fun higher_typeof :: "higher_type list \<Rightarrow> higher_type list \<Rightarrow> higher_type list
    \<Rightarrow> higher_term \<Rightarrow> higher_type option" where
  "higher_typeof S V B (SpecHBound n) = higher_lookup B n"
| "higher_typeof S V B (SpecHFree n) = higher_lookup V n"
| "higher_typeof S V B (SpecHConst n) = higher_lookup S n"
| "higher_typeof S V B (SpecHApp f x) = (case higher_typeof S V B f of
    Some (SpecHArrow A C) \<Rightarrow> (if higher_typeof S V B x = Some A then Some C else None)
  | _ \<Rightarrow> None)"
| "higher_typeof S V B (SpecHAbs A t) = map_option (SpecHArrow A) (higher_typeof S V (A # B) t)"

text \<open>Lifting by d leaves indices below cutoff k bound locally and shifts
all others by d. Crossing an abstraction increases the cutoff by one.\<close>
fun higher_lift :: "nat \<Rightarrow> nat \<Rightarrow> higher_term \<Rightarrow> higher_term" where
  "higher_lift d k (SpecHBound n) = SpecHBound (if n < k then n else n+d)"
| "higher_lift d k (SpecHFree n) = SpecHFree n"
| "higher_lift d k (SpecHConst n) = SpecHConst n"
| "higher_lift d k (SpecHApp f x) = SpecHApp (higher_lift d k f) (higher_lift d k x)"
| "higher_lift d k (SpecHAbs A t) = SpecHAbs A (higher_lift d (Suc k) t)"

text \<open>Beta substitution replaces index k by u, lifting u across the k
remaining binders. Greater indices decrease because the contracted binder is
removed. This is capture-avoiding substitution, not textual replacement.\<close>
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

text \<open>In a rule instance, s supplies the meta-variable images and d counts
surrounding rule abstractions. Images are lifted through those abstractions;
only explicit meta-arguments are applied. Failure is represented by None.\<close>
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

text \<open>The category's rule syntax is beta-normal, has a constant head on
the left, and uses each free meta-variable at a fixed arity there. Its left
arguments are distinct bound variables; right occurrences have at least that
arity, with extra ordinary arguments represented by application nodes.\<close>
fun higher_pattern_head where
  "higher_pattern_head (SpecPApp p q) = higher_pattern_head p"
| "higher_pattern_head p = p"
fun higher_pattern_metas where
  "higher_pattern_metas (SpecPBound n) = {}"
| "higher_pattern_metas (SpecPConst n) = {}"
| "higher_pattern_metas (SpecPApp p q) = higher_pattern_metas p \<union> higher_pattern_metas q"
| "higher_pattern_metas (SpecPAbs A p) = higher_pattern_metas p"
| "higher_pattern_metas (SpecPMeta n ps) = insert n (\<Union>(higher_pattern_metas ` set ps))"
fun higher_left_pattern where
  "higher_left_pattern ar (SpecPBound n) = True"
| "higher_left_pattern ar (SpecPConst n) = True"
| "higher_left_pattern ar (SpecPAbs A p) = higher_left_pattern ar p"
| "higher_left_pattern ar (SpecPApp p q) =
    ((\<exists>n. higher_pattern_head p = SpecPConst n \<or> higher_pattern_head p = SpecPBound n) \<and>
      higher_left_pattern ar p \<and> higher_left_pattern ar q)"
| "higher_left_pattern ar (SpecPMeta n ps) =
    (length ps = ar n \<and> distinct ps \<and> (\<forall>p\<in>set ps. \<exists>i. p = SpecPBound i))"
fun higher_right_pattern where
  "higher_right_pattern ar (SpecPBound n) = True"
| "higher_right_pattern ar (SpecPConst n) = True"
| "higher_right_pattern ar (SpecPAbs A p) = higher_right_pattern ar p"
| "higher_right_pattern ar (SpecPApp p q) =
    ((\<forall>A b. higher_pattern_head p \<noteq> SpecPAbs A b) \<and>
      higher_right_pattern ar p \<and> higher_right_pattern ar q)"
| "higher_right_pattern ar (SpecPMeta n ps) =
    (length ps = ar n \<and> list_all (higher_right_pattern ar) ps)"
definition higher_category_rule where
  "higher_category_rule S rule \<longleftrightarrow> higher_rule_welltyped S rule \<and>
    (case rule of (G,l,r) \<Rightarrow> (\<exists>c. higher_pattern_head l = SpecPConst c) \<and>
      higher_pattern_metas r \<subseteq> higher_pattern_metas l \<and>
      (\<exists>ar. higher_left_pattern ar l \<and> higher_right_pattern ar r))"

text \<open>G gives the types of a rule's meta-variables. Each substitution image
has its assigned type in the current S, V and B environments.\<close>
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
