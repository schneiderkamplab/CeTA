theory Higher_Order_Weak_Polynomial
  imports Higher_Order_Semantic_Call_Order
begin

fun ho_weak_polynomial_translate where
  "ho_weak_polynomial_translate ps (HEVar n) = HPVar n"
| "ho_weak_polynomial_translate ps (HEConst n) = (if n<length ps then ps!n else HPNumber 0 0)"
| "ho_weak_polynomial_translate ps (HEApp A B f x) =
    HPApply A B (ho_weak_polynomial_translate ps f) (ho_weak_polynomial_translate ps x)"
| "ho_weak_polynomial_translate ps (HEAbs A B t) = HPAbstract A B (ho_weak_polynomial_translate ps t)"

theorem ho_weak_polynomial_translate_type:
  assumes ty: "ho_expression_type S G t A" and check: "ho_check_polynomial_signature S ps"
  shows "ho_polynomial_type G (ho_weak_polynomial_translate ps t) A"
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
  have applied: "ho_polynomial_type G (HPApply A B (ho_weak_polynomial_translate ps f) (ho_weak_polynomial_translate ps x)) B"
    by (rule ho_polynomial_type.app[OF app.IH])
  show ?case using applied by simp
next
  case (abs A G t B)
  show ?case using ho_polynomial_type.abs[OF abs.IH] by simp
qed

theorem ho_weak_polynomial_translate_eval:
  assumes check: "ho_check_polynomial_signature S ps"
  shows "ho_polynomial_eval e (ho_weak_polynomial_translate ps t) =
    ho_weak_evaluate (ho_polynomial_interpretation ps) e t"
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
  then show ?case by (simp add: ho_plain_app_def)
qed simp_all

end
