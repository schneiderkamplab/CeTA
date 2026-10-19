theory Higher_Order_Core
  imports Main
begin

text \<open>Simply typed applicative terms with explicit de Bruijn binders.
Free rule variables and function symbols occupy distinct namespaces.
Rewriting uses arity-aware meta-substitution, in union with beta, not arbitrary
matching modulo beta or eta. No first-order erasure is used.\<close>

datatype ho_type = HBase nat | HArrow ho_type ho_type
datatype ho_term = HBound nat | HFree nat | HConst nat
  | HApp ho_term ho_term | HAbs ho_type ho_term

fun ho_lookup where
  "ho_lookup xs n = (if n < length xs then Some (xs ! n) else None)"

fun ho_typeof :: "ho_type list \<Rightarrow> ho_type list \<Rightarrow> ho_type list
    \<Rightarrow> ho_term \<Rightarrow> ho_type option" where
  "ho_typeof S V B (HBound n) = ho_lookup B n"
| "ho_typeof S V B (HFree n) = ho_lookup V n"
| "ho_typeof S V B (HConst n) = ho_lookup S n"
| "ho_typeof S V B (HApp f x) = (case ho_typeof S V B f of
    Some (HArrow A C) \<Rightarrow> (if ho_typeof S V B x = Some A then Some C else None)
  | _ \<Rightarrow> None)"
| "ho_typeof S V B (HAbs A t) = map_option (HArrow A) (ho_typeof S V (A # B) t)"

fun ho_lift :: "nat \<Rightarrow> nat \<Rightarrow> ho_term \<Rightarrow> ho_term" where
  "ho_lift d k (HBound n) = HBound (if n < k then n else n+d)"
| "ho_lift d k (HFree n) = HFree n"
| "ho_lift d k (HConst n) = HConst n"
| "ho_lift d k (HApp f x) = HApp (ho_lift d k f) (ho_lift d k x)"
| "ho_lift d k (HAbs A t) = HAbs A (ho_lift d (Suc k) t)"

fun ho_subst :: "(nat \<Rightarrow> ho_term) \<Rightarrow> nat \<Rightarrow> ho_term \<Rightarrow> ho_term" where
  "ho_subst s d (HBound n) = HBound n"
| "ho_subst s d (HFree n) = ho_lift d 0 (s n)"
| "ho_subst s d (HConst n) = HConst n"
| "ho_subst s d (HApp f x) = HApp (ho_subst s d f) (ho_subst s d x)"
| "ho_subst s d (HAbs A t) = HAbs A (ho_subst s (Suc d) t)"

fun ho_beta_subst :: "ho_term \<Rightarrow> nat \<Rightarrow> ho_term \<Rightarrow> ho_term" where
  "ho_beta_subst u k (HBound n) = (if n < k then HBound n
    else if n = k then ho_lift k 0 u else HBound (n-1))"
| "ho_beta_subst u k (HFree n) = HFree n"
| "ho_beta_subst u k (HConst n) = HConst n"
| "ho_beta_subst u k (HApp f x) = HApp (ho_beta_subst u k f) (ho_beta_subst u k x)"
| "ho_beta_subst u k (HAbs A t) = HAbs A (ho_beta_subst u (Suc k) t)"

text \<open>Meta-application is explicit in rules. Only the designated
meta-arguments are contracted; ordinary application is never normalized.
Meta-substitution images are represented by exactly the required leading
abstractions (possibly followed by further, ordinary abstractions).\<close>

datatype ho_pattern = PBound nat | PConst nat | PApp ho_pattern ho_pattern
  | PAbs ho_type ho_pattern | PMeta nat "ho_pattern list"

fun ho_meta_apply :: "ho_term \<Rightarrow> ho_term list \<Rightarrow> ho_term option" where
  "ho_meta_apply t [] = Some t"
| "ho_meta_apply t (u#us) = (case t of HAbs A b \<Rightarrow>
    ho_meta_apply (ho_beta_subst u 0 b) us | _ \<Rightarrow> None)"

fun ho_instantiate :: "(nat \<Rightarrow> ho_term) \<Rightarrow> nat \<Rightarrow> ho_pattern \<Rightarrow> ho_term option" where
  "ho_instantiate s d (PBound n) = Some (HBound n)"
| "ho_instantiate s d (PConst n) = Some (HConst n)"
| "ho_instantiate s d (PApp f x) = (case ho_instantiate s d f of None \<Rightarrow> None
    | Some a \<Rightarrow> map_option (HApp a) (ho_instantiate s d x))"
| "ho_instantiate s d (PAbs A t) = map_option (HAbs A) (ho_instantiate s (Suc d) t)"
| "ho_instantiate s d (PMeta n ts) = (case those (map (ho_instantiate s d) ts) of
    None \<Rightarrow> None | Some us \<Rightarrow> ho_meta_apply (ho_lift d 0 (s n)) us)"

fun ho_erase_pattern :: "ho_pattern \<Rightarrow> ho_term" where
  "ho_erase_pattern (PBound n) = HBound n"
| "ho_erase_pattern (PConst n) = HConst n"
| "ho_erase_pattern (PApp f x) = HApp (ho_erase_pattern f) (ho_erase_pattern x)"
| "ho_erase_pattern (PAbs A t) = HAbs A (ho_erase_pattern t)"
| "ho_erase_pattern (PMeta n ts) = foldl HApp (HFree n) (map ho_erase_pattern ts)"

type_synonym ho_rule = "ho_type list \<times> ho_pattern \<times> ho_pattern"

definition ho_rule_welltyped where
  "ho_rule_welltyped S r \<longleftrightarrow> (case r of (G,l,u) \<Rightarrow>
    case ho_typeof S G [] (ho_erase_pattern l) of None \<Rightarrow> False
      | Some A \<Rightarrow> ho_typeof S G [] (ho_erase_pattern u) = Some A)"

definition ho_typed_subst where
  "ho_typed_subst S V B G s \<longleftrightarrow>
    (\<forall>n<length G. ho_typeof S V B (s n) = Some (G!n))"

inductive ho_step :: "ho_type list \<Rightarrow> ho_type list \<Rightarrow> ho_rule list
    \<Rightarrow> ho_type list \<Rightarrow> ho_term \<Rightarrow> ho_term \<Rightarrow> bool" for S V R where
  rule: "(G,l,r) \<in> set R \<Longrightarrow> ho_rule_welltyped S (G,l,r) \<Longrightarrow>
    ho_typed_subst S V B G s \<Longrightarrow>
    ho_instantiate s 0 l = Some t \<Longrightarrow> ho_instantiate s 0 r = Some u \<Longrightarrow>
    ho_step S V R B t u"
| beta: "ho_step S V R B (HApp (HAbs A t) u) (ho_beta_subst u 0 t)"
| app_left: "ho_step S V R B t u \<Longrightarrow> ho_step S V R B (HApp t x) (HApp u x)"
| app_right: "ho_step S V R B t u \<Longrightarrow> ho_step S V R B (HApp x t) (HApp x u)"
| abs: "ho_step S V R (A#B) t u \<Longrightarrow> ho_step S V R B (HAbs A t) (HAbs A u)"

datatype ho_step_proof = HRule nat "ho_term list" | HBeta
  | HLeft ho_step_proof | HRight ho_step_proof | HUnder ho_step_proof

fun ho_check_step :: "ho_type list \<Rightarrow> ho_type list \<Rightarrow> ho_rule list
    \<Rightarrow> ho_type list \<Rightarrow> ho_term \<Rightarrow> ho_step_proof \<Rightarrow> ho_term option" where
  "ho_check_step S V R B t (HRule i ss) =
    (if i < length R then case R!i of (G,l,r) \<Rightarrow>
      if length ss = length G \<and> ho_rule_welltyped S (G,l,r) \<and>
        ho_typed_subst S V B G ((!) ss) \<and> ho_instantiate ((!) ss) 0 l = Some t
      then ho_instantiate ((!) ss) 0 r else None
     else None)"
| "ho_check_step S V R B t HBeta = (case t of
      HApp (HAbs A b) u \<Rightarrow> Some (ho_beta_subst u 0 b) | _ \<Rightarrow> None)"
| "ho_check_step S V R B t (HLeft p) = (case t of
      HApp f x \<Rightarrow> map_option (\<lambda>u. HApp u x) (ho_check_step S V R B f p) | _ \<Rightarrow> None)"
| "ho_check_step S V R B t (HRight p) = (case t of
      HApp f x \<Rightarrow> map_option (HApp f) (ho_check_step S V R B x p) | _ \<Rightarrow> None)"
| "ho_check_step S V R B t (HUnder p) = (case t of
      HAbs A b \<Rightarrow> map_option (HAbs A) (ho_check_step S V R (A#B) b p) | _ \<Rightarrow> None)"

theorem ho_check_step_sound:
  "ho_check_step S V R B t p = Some u \<Longrightarrow> ho_step S V R B t u"
proof (induction p arbitrary: B t u)
  case (HRule i ss)
  then show ?case
    by (auto split: if_splits prod.splits; metis nth_mem ho_step.rule)
next
  case HBeta
  then show ?case by (auto split: ho_term.splits intro: ho_step.beta)
next
  case (HLeft p)
  then show ?case by (auto split: ho_term.splits option.splits intro: ho_step.app_left)
next
  case (HRight p)
  then show ?case by (auto split: ho_term.splits option.splits intro: ho_step.app_right)
next
  case (HUnder p)
  then show ?case by (auto split: ho_term.splits option.splits intro: ho_step.abs)
qed

definition ho_relation where
  "ho_relation S V R A = {(t,u). ho_typeof S V [] t = Some A \<and>
    ho_typeof S V [] u = Some A \<and> ho_step S V R [] t u}"

fun ho_check_path where
  "ho_check_path S V R A t [] = Some t"
| "ho_check_path S V R A t (p#ps) =
    (case ho_check_step S V R [] t p of None \<Rightarrow> None | Some u \<Rightarrow>
      if ho_typeof S V [] t = Some A \<and> ho_typeof S V [] u = Some A
      then ho_check_path S V R A u ps else None)"

lemma ho_check_path_sound:
  "ho_check_path S V R A t ps = Some u \<Longrightarrow> (t,u) \<in> (ho_relation S V R A)^*"
  by (induction ps arbitrary: t)
     (auto simp: ho_relation_def split: option.splits if_splits
       intro: converse_rtrancl_into_rtrancl dest: ho_check_step_sound)

definition ho_check_loop where
  "ho_check_loop S V R A t ps \<longleftrightarrow>
    ps \<noteq> [] \<and> ho_check_path S V R A t ps = Some t"

theorem ho_check_loop_sound:
  assumes "ho_check_loop S V R A t ps"
  shows "\<not> wf ((ho_relation S V R A)\<inverse>)"
proof -
  obtain p qs where ps: "ps=p#qs" using assms unfolding ho_check_loop_def by (cases ps) auto
  obtain u where step: "ho_check_step S V R [] t p = Some u"
    and types: "ho_typeof S V [] t = Some A" "ho_typeof S V [] u = Some A"
    and path: "ho_check_path S V R A u qs = Some t"
    using assms unfolding ho_check_loop_def ps by (auto split: option.splits if_splits)
  have first: "(t,u) \<in> ho_relation S V R A"
    using ho_check_step_sound[OF step] types unfolding ho_relation_def by simp
  have rest: "(u,t) \<in> (ho_relation S V R A)^*" by (rule ho_check_path_sound[OF path])
  have cycle: "(t,t) \<in> (ho_relation S V R A)^+" using first rest by (rule rtrancl_into_trancl2)
  show ?thesis using cycle by (metis converse_iff trancl_converse wf_irrefl wf_trancl)
qed

end
