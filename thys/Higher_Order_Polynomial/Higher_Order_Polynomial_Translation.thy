theory Higher_Order_Polynomial_Translation
  imports Higher_Order_Polynomial_Normalization
begin

fun ho_polynomial_zero where
  "ho_polynomial_zero (HBase b) = HPNumber b 0"
| "ho_polynomial_zero (HArrow A B) = HPAbstract A B (ho_polynomial_zero B)"

fun ho_base_result where
  "ho_base_result (HBase b) = b"
| "ho_base_result (HArrow A B) = ho_base_result B"

fun ho_polynomial_lower where
  "ho_polynomial_lower (HBase b) p = p"
| "ho_polynomial_lower (HArrow A B) p =
    ho_polynomial_lower B (HPApply A B p (ho_polynomial_zero A))"

fun ho_polynomial_raise where
  "ho_polynomial_raise (HBase b) p c = HPAdd b p c"
| "ho_polynomial_raise (HArrow A B) p c = HPAbstract A B
    (ho_polynomial_raise B (HPApply A B (ho_polynomial_rename Suc p) (HPVar 0))
      (ho_polynomial_rename Suc c))"

lemma ho_polynomial_zero_eval:
  "ho_polynomial_eval e (ho_polynomial_zero A)=ho_zero A"
  by (induction A arbitrary: e) simp_all

lemma ho_polynomial_lower_eval:
  "ho_polynomial_eval e (ho_polynomial_lower A p)=ho_lower A (ho_polynomial_eval e p)"
  by (induction A arbitrary: p e) (simp_all add: ho_polynomial_zero_eval)

lemma ho_polynomial_raise_eval:
  "ho_polynomial_eval e (ho_polynomial_raise A p c)=
    ho_raise A (ho_polynomial_eval e p) (ho_polynomial_eval e c)"
  by (induction A arbitrary: p c e)
     (simp_all add: ho_polynomial_eval_rename ho_env_lift_def ho_env_cons_def ho_polynomial_eval_lift)

lemma ho_polynomial_zero_type:
  "ho_polynomial_type G (ho_polynomial_zero A) A"
  by (induction A arbitrary: G) (auto intro: ho_polynomial_type.intros)

lemma ho_polynomial_lower_type:
  "ho_polynomial_type G p A \<Longrightarrow>
    ho_polynomial_type G (ho_polynomial_lower A p) (HBase (ho_base_result A))"
proof (induction A arbitrary: G p)
  case (HBase b)
  then show ?case by simp
next
  case (HArrow A B)
  have app: "ho_polynomial_type G (HPApply A B p (ho_polynomial_zero A)) B"
    by (rule ho_polynomial_type.app[OF HArrow.prems ho_polynomial_zero_type])
  show ?case using HArrow.IH(2)[OF app] by simp
qed

lemma ho_polynomial_rename_type:
  "ho_polynomial_type G p A \<Longrightarrow>
    (\<And>n. n<length G \<Longrightarrow> r n<length D \<and> D!(r n)=G!n) \<Longrightarrow>
    ho_polynomial_type D (ho_polynomial_rename r p) A"
proof (induction arbitrary: D r rule: ho_polynomial_type.induct)
  case (var n G)
  have n: "r n<length D" and eq: "D!(r n)=G!n" using var.prems[OF var.hyps] by auto
  show ?case using ho_polynomial_type.var[OF n] by (simp add: eq)
next
  case (number G b n)
  show ?case by (simp add: ho_polynomial_type.number)
next
  case (add G p a q b c)
  show ?case using ho_polynomial_type.add[OF add.IH(1)[OF add.prems] add.IH(2)[OF add.prems]] by simp
next
  case (multiply G p a q b c)
  show ?case using ho_polynomial_type.multiply[OF multiply.IH(1)[OF multiply.prems] multiply.IH(2)[OF multiply.prems]] by simp
next
  case (app G f A B x)
  show ?case using ho_polynomial_type.app[OF app.IH(1)[OF app.prems] app.IH(2)[OF app.prems]] by simp
next
  case (abs A G t B)
  have ren: "ho_rename_up r n<length (A#D) \<and> (A#D)!(ho_rename_up r n)=(A#G)!n"
    if "n<length (A#G)" for n
    using that abs.prems by (cases n) (auto simp: ho_rename_up_def)
  show ?case using ho_polynomial_type.abs[OF abs.IH[OF ren]] by simp
qed

lemma ho_polynomial_weaken_type:
  "ho_polynomial_type G p A \<Longrightarrow> ho_polynomial_type (T#G) (ho_polynomial_rename Suc p) A"
  by (rule ho_polynomial_rename_type) simp_all

lemma ho_polynomial_raise_type:
  "ho_polynomial_type G p A \<Longrightarrow> ho_polynomial_type G c (HBase b) \<Longrightarrow>
    ho_polynomial_type G (ho_polynomial_raise A p c) A"
proof (induction A arbitrary: G p c)
  case (HBase a)
  show ?case using ho_polynomial_type.add[OF HBase.prems] by simp
next
  case (HArrow A B)
  have f: "ho_polynomial_type (A#G) (ho_polynomial_rename Suc p) (HArrow A B)"
    by (rule ho_polynomial_weaken_type[OF HArrow.prems(1)])
  have x: "ho_polynomial_type (A#G) (HPVar 0) A"
    using ho_polynomial_type.var[where n=0 and G="A#G"] by simp
  have c: "ho_polynomial_type (A#G) (ho_polynomial_rename Suc c) (HBase b)"
    by (rule ho_polynomial_weaken_type[OF HArrow.prems(2)])
  show ?case using ho_polynomial_type.abs[OF HArrow.IH(2)[OF ho_polynomial_type.app[OF f x] c]] by simp
qed

fun ho_polynomial_translate where
  "ho_polynomial_translate ps (HEVar n) = HPVar n"
| "ho_polynomial_translate ps (HEConst n) = (if n<length ps then ps!n else HPNumber 0 0)"
| "ho_polynomial_translate ps (HEApp A B f x) =
    ho_polynomial_raise B (HPApply A B (ho_polynomial_translate ps f) (ho_polynomial_translate ps x))
      (ho_polynomial_lower A (ho_polynomial_translate ps x))"
| "ho_polynomial_translate ps (HEAbs A B t) = HPAbstract A B (ho_polynomial_translate ps t)"

lemma ho_polynomial_closed_type_context:
  "ho_polynomial_type [] p A \<Longrightarrow> ho_polynomial_type G p A"
proof -
  assume ty: "ho_polynomial_type [] p A"
  have id: "ho_polynomial_rename (\<lambda>n. n) p=p" for p
  proof (induction p)
    case (HPAbstract A B p)
    have up: "ho_rename_up (\<lambda>n. n)=(\<lambda>n. n)"
      by (rule ext; rename_tac n; case_tac n) (simp_all add: ho_rename_up_def)
    show ?case by (simp add: up HPAbstract.IH)
  qed simp_all
  have "ho_polynomial_type G (ho_polynomial_rename (\<lambda>n. n) p) A"
    by (rule ho_polynomial_rename_type[OF ty]) simp
  then show ?thesis by (simp add: id)
qed

theorem ho_polynomial_translate_type:
  assumes ty: "ho_expression_type S G t A" and check: "ho_check_polynomial_signature S ps"
  shows "ho_polynomial_type G (ho_polynomial_translate ps t) A"
using ty
proof induction
  case (var n G)
  then show ?case by (simp add: ho_polynomial_type.var)
next
  case (const n G)
  have n: "n<length ps" and p: "ho_polynomial_typeof [] (ps!n)=Some (S!n)"
    using check const.hyps by (auto simp: ho_check_polynomial_signature_iff)
  show ?case using ho_polynomial_closed_type_context[OF ho_polynomial_typeof_sound[OF p]] by (simp add: n)
next
  case (app G f A B x)
  have applied: "ho_polynomial_type G (HPApply A B (ho_polynomial_translate ps f) (ho_polynomial_translate ps x)) B"
    by (rule ho_polynomial_type.app[OF app.IH])
  show ?case using ho_polynomial_raise_type[OF applied ho_polynomial_lower_type[OF app.IH(2)]] by simp
next
  case (abs A G t B)
  show ?case using ho_polynomial_type.abs[OF abs.IH] by simp
qed

theorem ho_polynomial_translate_eval:
  assumes check: "ho_check_polynomial_signature S ps"
  shows "ho_polynomial_eval e (ho_polynomial_translate ps t) =
    ho_evaluate (ho_polynomial_interpretation ps) e t"
proof (induction t arbitrary: e)
  case (HEConst n)
  have eq: "ho_polynomial_eval e (ps!n)=ho_polynomial_eval Var (ps!n)" if "n<length ps"
  proof -
    have ty: "ho_polynomial_type [] (ps!n) (S!n)"
      by (rule ho_polynomial_typeof_sound) (use check that in \<open>simp add: ho_check_polynomial_signature_iff\<close>)
    show ?thesis by (rule ho_polynomial_eval_cong[OF ty]) simp
  qed
  show ?case by (simp add: ho_polynomial_interpretation_def eq)
next
  case (HEApp A B f x)
  then show ?case by (simp add: ho_polynomial_raise_eval ho_polynomial_lower_eval ho_sem_app_def)
qed simp_all

end
