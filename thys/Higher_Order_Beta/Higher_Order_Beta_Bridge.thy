theory Higher_Order_Beta_Bridge
  imports "Higher_Order_Lambda.StrongNorm" "Higher_Order_Checker.Higher_Order_Core"
begin

text \<open>Constants and free variables are injected into disjoint free-index
namespaces of Isabelle's existing simply-typed lambda calculus. Bound indices
are preserved. This is used only for beta normalization, never to erase
rewrite rules or higher-order application obligations.\<close>

fun ho_db :: "nat \<Rightarrow> ho_term \<Rightarrow> dB" where
  "ho_db d (HBound n) = Var n"
| "ho_db d (HFree n) = Var (d + 2*n)"
| "ho_db d (HConst n) = Var (d + 2*n + 1)"
| "ho_db d (HApp f x) = App (ho_db d f) (ho_db d x)"
| "ho_db d (HAbs A t) = Abs (ho_db (Suc d) t)"

fun ho_db_type :: "ho_type \<Rightarrow> LambdaType.type" where
  "ho_db_type (HBase n) = Atom n"
| "ho_db_type (HArrow A B) = Fun (ho_db_type A) (ho_db_type B)"

definition ho_db_env where
  "ho_db_env S V B n = (if n < length B then ho_db_type (B!n)
    else if even (n - length B) then ho_db_type (V!((n-length B) div 2))
    else ho_db_type (S!((n-length B) div 2)))"

lemma ho_db_env_cons:
  "ho_db_env S V (A#B) = shift (ho_db_env S V B) 0 (ho_db_type A)"
  by (rule ext) (rename_tac n, case_tac n, auto simp: ho_db_env_def shift_def)

lemma ho_db_typing:
  "ho_typeof S V B t = Some A \<Longrightarrow>
    typing (ho_db_env S V B) (ho_db (length B) t) (ho_db_type A)"
proof (induction t arbitrary: B A)
  case (HBound n)
  then show ?case by (auto simp: ho_db_env_def split: if_splits)
next
  case (HFree n)
  then show ?case by (auto simp: ho_db_env_def split: if_splits)
next
  case (HConst n)
  then show ?case by (auto simp: ho_db_env_def split: if_splits)
next
  case (HApp f x)
  obtain T where f: "ho_typeof S V B f = Some (HArrow T A)"
    and x: "ho_typeof S V B x = Some T"
    using HApp.prems by (auto split: option.splits ho_type.splits if_splits)
  have ft: "typing (ho_db_env S V B) (ho_db (length B) f) (Fun (ho_db_type T) (ho_db_type A))"
    using HApp.IH(1)[OF f] by simp
  show ?case using typing.App[OF ft HApp.IH(2)[OF x]] by simp
next
  case (HAbs T t)
  obtain C where t: "ho_typeof S V (T#B) t = Some C" and A: "A=HArrow T C"
    using HAbs.prems by (auto split: option.splits)
  have body: "typing (shift (ho_db_env S V B) 0 (ho_db_type T))
      (ho_db (Suc (length B)) t) (ho_db_type C)"
    using HAbs.IH[OF t] by (simp add: ho_db_env_cons)
  show ?case using typing.Abs[OF body] A by simp
qed

lemma ho_db_lift:
  "c \<le> d \<Longrightarrow> ho_db (d+k) (ho_lift k c t) = liftn k (ho_db d t) c"
proof (induction t arbitrary: d c)
  case (HAbs A t)
  have "ho_db (Suc d+k) (ho_lift k (Suc c) t) = liftn k (ho_db (Suc d) t) (Suc c)"
    by (rule HAbs.IH) (use HAbs.prems in simp)
  then show ?case by simp
qed (auto simp: add.assoc add.commute add.left_commute)

lemma ho_db_beta_subst:
  "ho_db (d+k) (ho_beta_subst u k t) = substn (ho_db (Suc (d+k)) t) (ho_db d u) k"
proof (induction t arbitrary: k)
  case (HAbs A t)
  have "ho_db (d+Suc k) (ho_beta_subst u (Suc k) t) =
    substn (ho_db (Suc (d+Suc k)) t) (ho_db d u) (Suc k)" by (rule HAbs.IH)
  then show ?case by (simp only: ho_beta_subst.simps ho_db.simps substn.simps add_Suc_right; simp)
qed (auto simp: ho_db_lift add.assoc)

lemma ho_db_beta_step:
  "ho_step S V [] B t u \<Longrightarrow> beta (ho_db d t) (ho_db d u)"
  by (induction arbitrary: d rule: ho_step.induct)
     (auto simp: ho_db_beta_subst[where k=0, simplified] substn_subst_0 intro: beta.intros)

theorem ho_empty_rules_beta_termination:
  "ho_typeof S V B t = Some A \<Longrightarrow> termip beta (ho_db (length B) t)"
  by (rule type_implies_termi, rule ho_db_typing)

lemma ho_accp_simulation:
  assumes mono: "\<And>x y. P x y \<Longrightarrow> Q (f x) (f y)"
    and acc: "Wellfounded.accp Q (f t)"
  shows "Wellfounded.accp P t"
proof -
  have aux: "Wellfounded.accp Q x \<Longrightarrow> \<forall>t. f t=x \<longrightarrow> Wellfounded.accp P t" for x
    by (erule accp_induct) (blast intro: accpI dest: mono)
  show ?thesis using aux[OF acc] by blast
qed

theorem ho_empty_rules_termination:
  "wf ((ho_relation S V [] A)\<inverse>)"
proof -
  let ?P = "\<lambda>u t. (t,u) \<in> ho_relation S V [] A"
  have all: "\<forall>t. Wellfounded.accp ?P t"
  proof
    fix t
    show "Wellfounded.accp ?P t"
    proof (cases "ho_typeof S V [] t = Some A")
      case True
      have acc: "termip beta (ho_db 0 t)"
        using ho_empty_rules_beta_termination[OF True] by simp
      show ?thesis
        by (rule ho_accp_simulation[where f="ho_db 0", OF _ acc])
           (auto simp: ho_relation_def intro: ho_db_beta_step)
    next
      case False
      show ?thesis by (rule accp.accI) (use False in \<open>auto simp: ho_relation_def\<close>)
    qed
  qed
  have "wfp ?P" by (rule accp_wfpI[OF all])
  then show ?thesis by (simp add: wfp_def converse_unfold)
qed

end
