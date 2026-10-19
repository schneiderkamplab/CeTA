theory Higher_Order_Semantic_Application
  imports Higher_Order_Cost
begin

text \<open>Application is interpreted compositionally on lambda terms. Its
cost is itself a term, rather than a meta-level natural number: this matters
for commutation with substitution under abstractions.\<close>

fun ho_lower where
  "ho_lower (HBase b) t = t"
| "ho_lower (HArrow A B) t = ho_lower B (App t (ho_zero A))"

lemma ho_zero_subst [simp]: "(ho_zero A)[v/k]=ho_zero A"
  by (induction A arbitrary: v k) simp_all

lemma ho_lower_subst:
  "(ho_lower A t)[v/k]=ho_lower A (t[v/k])"
  by (induction A arbitrary: t v k) simp_all

lemma ho_lower_numeral:
  "ho_value A t \<Longrightarrow> ho_numeral (ho_lower A t) (ho_observe A t)"
proof (induction A arbitrary: t)
  case (HBase b)
  then obtain n where n: "ho_numeral t n" by auto
  show ?case using n ho_observe_numeral[OF n] by simp
next
  case (HArrow A B)
  have point: "ho_value B (App t (ho_zero A))"
    using HArrow.prems ho_zero_value[of A] by simp
  from HArrow.IH(2)[OF point] show ?case by simp
qed

fun ho_raise where
  "ho_raise (HBase b) t c = ho_add t c"
| "ho_raise (HArrow A B) t c =
    Abs (ho_raise B (App (lift t 0) (Var 0)) (lift c 0))"

lemma ho_raise_subst:
  "(ho_raise A t c)[v/k]=ho_raise A (t[v/k]) (c[v/k])"
  by (induction A arbitrary: t c v k) (simp_all add: ho_add_subst)

lemma ho_raise_application:
  "beta (App (ho_raise (HArrow A B) t c) x) (ho_raise B (App t x) c)"
  using beta.beta[of "ho_raise B (App (lift t 0) (Var 0)) (lift c 0)" x]
  by (simp add: ho_raise_subst)

lemma ho_raise_numeral:
  "ho_numeral c n \<Longrightarrow> beta\<^sup>*\<^sup>* (ho_raise A t c) (ho_shift_value A t n)"
proof (induction A arbitrary: t c)
  case (HBase b)
  show ?case using ho_add_betas[OF rtranclp.rtrancl_refl HBase.prems[unfolded ho_numeral_def]]
    by simp
next
  case (HArrow A B)
  have path: "beta\<^sup>*\<^sup>* (lift c 0) (ho_church n)"
    using lift_preserves_beta'[OF HArrow.prems[unfolded ho_numeral_def], of 0] by simp
  have inner: "beta\<^sup>*\<^sup>* (ho_raise B (App (lift t 0) (Var 0)) (lift c 0))
      (ho_shift_value B (App (lift t 0) (Var 0)) n)"
    by (rule HArrow.IH(2)) (rule path[folded ho_numeral_def])
  show ?case by (simp only: ho_raise.simps ho_shift_value.simps; rule rtrancl_beta_Abs[OF inner])
qed

definition ho_sem_app where
  "ho_sem_app A B f x = ho_raise B (App f x) (ho_lower A x)"

lemma ho_sem_app_subst:
  "(ho_sem_app A B f x)[v/k]=ho_sem_app A B (f[v/k]) (x[v/k])"
  by (simp add: ho_sem_app_def ho_raise_subst ho_lower_subst)

lemma ho_sem_app_path:
  "ho_value A x \<Longrightarrow> beta\<^sup>*\<^sup>* (ho_sem_app A B f x)
    (ho_shift_value B (App f x) (ho_observe A x))"
  unfolding ho_sem_app_def by (rule ho_raise_numeral[OF ho_lower_numeral])

lemma ho_sem_app_value:
  assumes f: "ho_value (HArrow A B) f" and x: "ho_value A x"
  shows "ho_value B (ho_sem_app A B f x)"
proof -
  have v: "ho_value B (App f x)" using f x by simp
  have shifted: "ho_value B (ho_shift_value B (App f x) (ho_observe A x))"
    by (rule ho_shift_value_closed[OF v])
  show ?thesis using ho_value_beta[OF ho_sem_app_path[OF x], of B] shifted by simp
qed

lemma ho_sem_app_ge:
  assumes f: "ho_value (HArrow A B) f" and g: "ho_value (HArrow A B) g"
    and x: "ho_value A x" and y: "ho_value A y"
    and fg: "ho_value_ge (HArrow A B) f g" and xy: "ho_value_ge A x y"
  shows "ho_value_ge B (ho_sem_app A B f x) (ho_sem_app A B g y)"
proof -
  have left: "ho_value_ge B (App f x) (App g x)" using fg x by simp
  have right: "ho_value_ge B (App g x) (App g y)" using g x y xy by simp
  have point: "ho_value_ge B (App f x) (App g y)"
    by (rule ho_value_ge_trans[OF left right])
  have cost: "ho_observe A x\<ge>ho_observe A y" by (rule ho_value_ge_observe[OF xy])
  have shifted: "ho_value_ge B (ho_shift_value B (App f x) (ho_observe A x))
      (ho_shift_value B (App g y) (ho_observe A y))"
    by (rule ho_shift_ge_cost[OF point cost])
  have eq: "ho_value_ge B (ho_sem_app A B f x) (ho_sem_app A B g y) =
      ho_value_ge B (ho_shift_value B (App f x) (ho_observe A x))
        (ho_shift_value B (App g y) (ho_observe A y))"
    by (rule ho_ge_beta[OF ho_sem_app_path[OF x] ho_sem_app_path[OF y]])
  show ?thesis using eq shifted by simp
qed

lemma ho_sem_app_gt_left:
  assumes x: "ho_value A x" and fg: "ho_value_gt (HArrow A B) f g"
  shows "ho_value_gt B (ho_sem_app A B f x) (ho_sem_app A B g x)"
proof -
  have point: "ho_value_gt B (App f x) (App g x)" using fg x by simp
  have shifted: "ho_value_gt B (ho_shift_value B (App f x) (ho_observe A x))
      (ho_shift_value B (App g x) (ho_observe A x))" by (rule ho_shift_gt[OF point])
  have eq: "ho_value_gt B (ho_sem_app A B f x) (ho_sem_app A B g x) =
      ho_value_gt B (ho_shift_value B (App f x) (ho_observe A x))
        (ho_shift_value B (App g x) (ho_observe A x))"
    by (rule ho_gt_beta[OF ho_sem_app_path[OF x] ho_sem_app_path[OF x]])
  show ?thesis using eq shifted by simp
qed

lemma ho_sem_app_gt_right:
  assumes f: "ho_value (HArrow A B) f" and x: "ho_value A x" and y: "ho_value A y"
    and xy: "ho_value_gt A x y"
  shows "ho_value_gt B (ho_sem_app A B f x) (ho_sem_app A B f y)"
proof -
  have weak: "ho_value_ge A x y" by (rule ho_value_gt_ge[OF xy])
  have point: "ho_value_ge B (App f x) (App f y)" using f x y weak by simp
  have cost: "ho_observe A x>ho_observe A y" by (rule ho_value_gt_observe[OF xy])
  have shifted: "ho_value_gt B (ho_shift_value B (App f x) (ho_observe A x))
      (ho_shift_value B (App f y) (ho_observe A y))"
    by (rule ho_shift_gt_cost[OF point cost])
  have eq: "ho_value_gt B (ho_sem_app A B f x) (ho_sem_app A B f y) =
      ho_value_gt B (ho_shift_value B (App f x) (ho_observe A x))
        (ho_shift_value B (App f y) (ho_observe A y))"
    by (rule ho_gt_beta[OF ho_sem_app_path[OF x] ho_sem_app_path[OF y]])
  show ?thesis using eq shifted by simp
qed

lemma ho_sem_app_dominates:
  assumes f: "ho_value (HArrow A B) f" and x: "ho_value A x"
  shows "ho_value_ge B (ho_sem_app A B f x) (App f x)"
proof -
  have v: "ho_value B (App f x)" using f x by simp
  have shifted: "ho_value_ge B (ho_shift_value B (App f x) (ho_observe A x)) (App f x)"
    by (rule ho_shift_dominates[OF v])
  have eq: "ho_value_ge B (ho_sem_app A B f x) (App f x) =
      ho_value_ge B (ho_shift_value B (App f x) (ho_observe A x)) (App f x)"
    by (rule ho_ge_beta[OF ho_sem_app_path[OF x] rtranclp.rtrancl_refl])
  show ?thesis using eq shifted by simp
qed

lemma ho_lift_lift_zero:
  "lift (lift t 0) (Suc k) = lift (lift t k) 0"
  by (rule lift_lift) simp

lemma ho_add_lift:
  "lift (ho_add t u) k = ho_add (lift t k) (lift u k)"
  by (simp add: ho_add_def numeral_2_eq_2 ho_lift_lift_zero)

lemma ho_zero_lift [simp]: "lift (ho_zero A) k=ho_zero A"
  by (induction A arbitrary: k) (simp_all add: ho_lift_lift_zero ho_church_def)

lemma ho_lower_lift:
  "lift (ho_lower A t) k=ho_lower A (lift t k)"
  by (induction A arbitrary: t k) simp_all

lemma ho_raise_lift:
  "lift (ho_raise A t c) k=ho_raise A (lift t k) (lift c k)"
  by (induction A arbitrary: t c k) (simp_all add: ho_add_lift ho_lift_lift_zero)

lemma ho_sem_app_lift:
  "lift (ho_sem_app A B f x) k=ho_sem_app A B (lift f k) (lift x k)"
  by (simp add: ho_sem_app_def ho_raise_lift ho_lower_lift)

end
