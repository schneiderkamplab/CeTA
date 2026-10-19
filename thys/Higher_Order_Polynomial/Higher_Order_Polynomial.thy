theory Higher_Order_Polynomial
  imports "Higher_Order_Values.Higher_Order_Source_Order"
begin

text \<open>Finite higher-order polynomial programs. Function application in an
interpretation is ordinary weakly monotone application; the additional strict
application cost belongs to the interpretation of source terms, not to this
program language. Natural-number arithmetic is shared across base sorts.\<close>

datatype ho_polynomial = HPVar nat | HPNumber nat nat
  | HPAdd nat ho_polynomial ho_polynomial
  | HPMultiply nat ho_polynomial ho_polynomial
  | HPApply ho_type ho_type ho_polynomial ho_polynomial
  | HPAbstract ho_type ho_type ho_polynomial

inductive ho_polynomial_type :: "ho_type list \<Rightarrow> ho_polynomial \<Rightarrow> ho_type \<Rightarrow> bool" where
  var: "n<length G \<Longrightarrow> ho_polynomial_type G (HPVar n) (G!n)"
| number: "ho_polynomial_type G (HPNumber b n) (HBase b)"
| add: "ho_polynomial_type G p (HBase a) \<Longrightarrow> ho_polynomial_type G q (HBase b) \<Longrightarrow>
    ho_polynomial_type G (HPAdd c p q) (HBase c)"
| multiply: "ho_polynomial_type G p (HBase a) \<Longrightarrow> ho_polynomial_type G q (HBase b) \<Longrightarrow>
    ho_polynomial_type G (HPMultiply c p q) (HBase c)"
| app: "ho_polynomial_type G f (HArrow A B) \<Longrightarrow> ho_polynomial_type G x A \<Longrightarrow>
    ho_polynomial_type G (HPApply A B f x) B"
| abs: "ho_polynomial_type (A#G) t B \<Longrightarrow>
    ho_polynomial_type G (HPAbstract A B t) (HArrow A B)"

fun ho_polynomial_eval where
  "ho_polynomial_eval e (HPVar n) = e n"
| "ho_polynomial_eval e (HPNumber b n) = ho_church n"
| "ho_polynomial_eval e (HPAdd b p q) = ho_add (ho_polynomial_eval e p) (ho_polynomial_eval e q)"
| "ho_polynomial_eval e (HPMultiply b p q) = ho_multiply (ho_polynomial_eval e p) (ho_polynomial_eval e q)"
| "ho_polynomial_eval e (HPApply A B f x) = App (ho_polynomial_eval e f) (ho_polynomial_eval e x)"
| "ho_polynomial_eval e (HPAbstract A B t) = Abs (ho_polynomial_eval (ho_env_lift e) t)"

lemma ho_multiply_subst:
  "(ho_multiply t u)[v/k] = ho_multiply (t[v/k]) (u[v/k])"
  by (simp add: ho_multiply_def)

lemma ho_polynomial_eval_subst:
  "(ho_polynomial_eval e p)[v/k]=ho_polynomial_eval (\<lambda>n. (e n)[v/k]) p"
  by (induction p arbitrary: e v k)
     (simp_all add: ho_add_subst ho_multiply_subst ho_env_lift_subst)

lemma ho_polynomial_abstraction_beta:
  "beta (App (ho_polynomial_eval e (HPAbstract A B t)) x)
    (ho_polynomial_eval (ho_env_cons x e) t)"
  using beta.beta[of "ho_polynomial_eval (ho_env_lift e) t" x]
  by (simp add: ho_polynomial_eval_subst ho_env_lift_beta)

lemma ho_add_value:
  "ho_value (HBase a) t \<Longrightarrow> ho_value (HBase b) u \<Longrightarrow> ho_value (HBase c) (ho_add t u)"
  by (auto intro: ho_add_numeral)

lemma ho_multiply_value:
  "ho_value (HBase a) t \<Longrightarrow> ho_value (HBase b) u \<Longrightarrow> ho_value (HBase c) (ho_multiply t u)"
  by (auto intro: ho_multiply_numeral)

lemma ho_add_ge:
  assumes "ho_value_ge (HBase a) t t'" "ho_value_ge (HBase b) u u'"
  shows "ho_value_ge (HBase c) (ho_add t u) (ho_add t' u')"
proof -
  obtain m n k l where nums: "ho_numeral t m" "ho_numeral t' n" "n\<le>m"
    "ho_numeral u k" "ho_numeral u' l" "l\<le>k" using assms by auto
  have left: "ho_numeral (ho_add t u) (m+k)" by (rule ho_add_numeral[OF nums(1,4)])
  have right: "ho_numeral (ho_add t' u') (n+l)" by (rule ho_add_numeral[OF nums(2,5)])
  have le: "n+l\<le>m+k" using nums(3,6) by simp
  show ?thesis unfolding ho_value_ge.simps using left right le by blast
qed

lemma ho_multiply_ge:
  assumes "ho_value_ge (HBase a) t t'" "ho_value_ge (HBase b) u u'"
  shows "ho_value_ge (HBase c) (ho_multiply t u) (ho_multiply t' u')"
proof -
  obtain m n k l where nums: "ho_numeral t m" "ho_numeral t' n" "n\<le>m"
    "ho_numeral u k" "ho_numeral u' l" "l\<le>k" using assms by auto
  have left: "ho_numeral (ho_multiply t u) (m*k)" by (rule ho_multiply_numeral[OF nums(1,4)])
  have right: "ho_numeral (ho_multiply t' u') (n*l)" by (rule ho_multiply_numeral[OF nums(2,5)])
  have le: "n*l\<le>m*k" by (rule mult_le_mono[OF nums(3,6)])
  show ?thesis unfolding ho_value_ge.simps using left right le by blast
qed

lemma ho_plain_app_ge:
  assumes g: "ho_value (HArrow A B) g" and x: "ho_value A x" and y: "ho_value A y"
    and fg: "ho_value_ge (HArrow A B) f g" and xy: "ho_value_ge A x y"
  shows "ho_value_ge B (App f x) (App g y)"
proof -
  have first: "ho_value_ge B (App f x) (App g x)" using fg x by simp
  have second: "ho_value_ge B (App g x) (App g y)" using g x y xy by simp
  show ?thesis by (rule ho_value_ge_trans[OF first second])
qed

theorem ho_polynomial_fundamental:
  "ho_polynomial_type G t A \<Longrightarrow>
    (\<forall>e. ho_env_value G e \<longrightarrow> ho_value A (ho_polynomial_eval e t)) \<and>
    (\<forall>e d. ho_env_value G e \<longrightarrow> ho_env_value G d \<longrightarrow> ho_env_ge G e d \<longrightarrow>
      ho_value_ge A (ho_polynomial_eval e t) (ho_polynomial_eval d t))"
proof (induction rule: ho_polynomial_type.induct)
  case (var n G)
  then show ?case by (auto simp: ho_env_value_def ho_env_ge_def)
next
  case (number G b n)
  have v: "ho_value (HBase b) (ho_church n)"
    unfolding ho_value.simps by (rule exI[where x=n]) (rule ho_numeral_church)
  show ?case unfolding ho_polynomial_eval.simps using v ho_value_ge_refl[OF v] by blast
next
  case (add G p a q b c)
  show ?case unfolding ho_polynomial_eval.simps using add.IH by (blast intro: ho_add_value ho_add_ge)
next
  case (multiply G p a q b c)
  show ?case unfolding ho_polynomial_eval.simps using multiply.IH by (blast intro: ho_multiply_value ho_multiply_ge)
next
  case (app G f A B x)
  note fv = app.IH(1)[THEN conjunct1, rule_format]
  note fg = app.IH(1)[THEN conjunct2, rule_format]
  note xv = app.IH(2)[THEN conjunct1, rule_format]
  note xg = app.IH(2)[THEN conjunct2, rule_format]
  have ev: "ho_value B (ho_polynomial_eval e (HPApply A B f x))"
    if "ho_env_value G e" for e
    using fv[OF that] xv[OF that] by simp
  have order: "ho_value_ge B (ho_polynomial_eval e (HPApply A B f x)) (ho_polynomial_eval d (HPApply A B f x))"
    if "ho_env_value G e" "ho_env_value G d" "ho_env_ge G e d" for e d
    unfolding ho_polynomial_eval.simps
    by (rule ho_plain_app_ge[OF fv[OF that(2)] xv[OF that(1)] xv[OF that(2)] fg[OF that] xg[OF that]])
  show ?case using ev order by blast
next
  case (abs A G t B)
  note ev = abs.IH[THEN conjunct1, rule_format]
  note order = abs.IH[THEN conjunct2, rule_format]
  have path: "beta\<^sup>*\<^sup>* (App (ho_polynomial_eval e (HPAbstract A B t)) x)
      (ho_polynomial_eval (ho_env_cons x e) t)" for e x
    by (rule r_into_rtranclp) (rule ho_polynomial_abstraction_beta)
  have appvalue: "ho_value B (App (ho_polynomial_eval e (HPAbstract A B t)) x)"
    if e: "ho_env_value G e" and x: "ho_value A x" for e x
  proof -
    have v: "ho_value B (ho_polynomial_eval (ho_env_cons x e) t)"
      by (rule ev[OF ho_env_cons_value[OF x e]])
    have eq: "ho_value B (App (ho_polynomial_eval e (HPAbstract A B t)) x) =
        ho_value B (ho_polynomial_eval (ho_env_cons x e) t)" by (rule ho_value_beta[OF path])
    show ?thesis using v eq by simp
  qed
  have apporder: "ho_value_ge B (App (ho_polynomial_eval e (HPAbstract A B t)) x)
      (App (ho_polynomial_eval d (HPAbstract A B t)) y)"
    if e: "ho_env_value G e" and d: "ho_env_value G d" and ed: "ho_env_ge G e d"
      and x: "ho_value A x" and y: "ho_value A y" and xy: "ho_value_ge A x y" for e d x y
  proof -
    have g: "ho_value_ge B (ho_polynomial_eval (ho_env_cons x e) t) (ho_polynomial_eval (ho_env_cons y d) t)"
      by (rule order[OF ho_env_cons_value[OF x e] ho_env_cons_value[OF y d] ho_env_cons_ge[OF xy ed]])
    have eq: "ho_value_ge B (App (ho_polynomial_eval e (HPAbstract A B t)) x)
        (App (ho_polynomial_eval d (HPAbstract A B t)) y) =
      ho_value_ge B (ho_polynomial_eval (ho_env_cons x e) t) (ho_polynomial_eval (ho_env_cons y d) t)"
      by (rule ho_ge_beta[OF path path])
    show ?thesis using g eq by simp
  qed
  have val: "ho_value (HArrow A B) (ho_polynomial_eval e (HPAbstract A B t))"
    if e: "ho_env_value G e" for e
    unfolding ho_value.simps(2)
    using appvalue[OF e] apporder[OF e e ho_env_ge_refl[OF e]] by blast
  have ge: "ho_value_ge (HArrow A B) (ho_polynomial_eval e (HPAbstract A B t))
      (ho_polynomial_eval d (HPAbstract A B t))"
    if "ho_env_value G e" "ho_env_value G d" "ho_env_ge G e d" for e d
    unfolding ho_value_ge.simps(2)
    using apporder[OF that] ho_value_ge_refl by blast
  show ?case using val ge by blast
qed

fun ho_polynomial_typeof where
  "ho_polynomial_typeof G (HPVar n) = ho_lookup G n"
| "ho_polynomial_typeof G (HPNumber b n) = Some (HBase b)"
| "ho_polynomial_typeof G (HPAdd b p q) = (case (ho_polynomial_typeof G p, ho_polynomial_typeof G q) of
    (Some (HBase a), Some (HBase c)) \<Rightarrow> Some (HBase b) | _ \<Rightarrow> None)"
| "ho_polynomial_typeof G (HPMultiply b p q) = (case (ho_polynomial_typeof G p, ho_polynomial_typeof G q) of
    (Some (HBase a), Some (HBase c)) \<Rightarrow> Some (HBase b) | _ \<Rightarrow> None)"
| "ho_polynomial_typeof G (HPApply A B f x) =
    (if ho_polynomial_typeof G f=Some (HArrow A B) \<and> ho_polynomial_typeof G x=Some A then Some B else None)"
| "ho_polynomial_typeof G (HPAbstract A B t) =
    (if ho_polynomial_typeof (A#G) t=Some B then Some (HArrow A B) else None)"

theorem ho_polynomial_typeof_sound:
  "ho_polynomial_typeof G t=Some A \<Longrightarrow> ho_polynomial_type G t A"
  by (induction t arbitrary: G A;
      auto intro: ho_polynomial_type.intros split: option.splits ho_type.splits if_splits;
      blast intro: ho_polynomial_type.intros)

lemma ho_church_body_lift_at:
  "2\<le>k \<Longrightarrow> lift (ho_church_body n) k=ho_church_body n"
  by (induction n) auto

lemma ho_church_lift_at [simp]: "lift (ho_church n) k=ho_church n"
  by (simp add: ho_church_def ho_church_body_lift_at)

lemma ho_multiply_lift:
  "lift (ho_multiply t u) k=ho_multiply (lift t k) (lift u k)"
  by (simp add: ho_multiply_def ho_lift_lift_zero)

lemma ho_polynomial_eval_lift:
  "lift (ho_polynomial_eval e p) k=ho_polynomial_eval (\<lambda>n. lift (e n) k) p"
  by (induction p arbitrary: e k)
     (simp_all add: ho_add_lift ho_multiply_lift ho_env_lift_lift)

lemma ho_polynomial_eval_cong:
  assumes ty: "ho_polynomial_type G p A" and env: "\<And>n. n<length G \<Longrightarrow> e n=d n"
  shows "ho_polynomial_eval e p=ho_polynomial_eval d p"
using ty env
proof (induction arbitrary: e d rule: ho_polynomial_type.induct)
  case (var n G)
  show ?case using var.prems[OF var.hyps] by simp
next
  case (number G b n)
  show ?case by simp
next
  case (add G p a q b c)
  show ?case using add.IH(1)[OF add.prems] add.IH(2)[OF add.prems] by simp
next
  case (multiply G p a q b c)
  show ?case using multiply.IH(1)[OF multiply.prems] multiply.IH(2)[OF multiply.prems] by simp
next
  case (app G f A B x)
  show ?case using app.IH(1)[OF app.prems] app.IH(2)[OF app.prems] by simp
next
  case (abs A G t B)
  have eq: "ho_env_lift e n=ho_env_lift d n" if "n<length (A#G)" for n
    using that abs.prems by (cases n) (auto simp: ho_env_lift_def ho_env_cons_def)
  show ?case using abs.IH[OF eq] by simp
qed

lemma ho_polynomial_closed_subst:
  "ho_polynomial_type [] p A \<Longrightarrow> (ho_polynomial_eval e p)[v/k]=ho_polynomial_eval e p"
  unfolding ho_polynomial_eval_subst by (rule ho_polynomial_eval_cong[where G="[]"]; simp_all)

lemma ho_polynomial_closed_lift:
  "ho_polynomial_type [] p A \<Longrightarrow> lift (ho_polynomial_eval e p) k=ho_polynomial_eval e p"
  unfolding ho_polynomial_eval_lift by (rule ho_polynomial_eval_cong[where G="[]"]; simp_all)

definition ho_polynomial_interpretation where
  "ho_polynomial_interpretation ps n =
    (if n<length ps then ho_polynomial_eval Var (ps!n) else ho_church 0)"

definition ho_check_polynomial_signature where
  "ho_check_polynomial_signature S ps \<longleftrightarrow>
    length ps=length S \<and> list_all (\<lambda>n. ho_polynomial_typeof [] (ps!n)=Some (S!n)) [0..<length S]"

lemma ho_check_polynomial_signature_iff:
  "ho_check_polynomial_signature S ps \<longleftrightarrow>
    length ps=length S \<and> (\<forall>n<length S. ho_polynomial_typeof [] (ps!n)=Some (S!n))"
  by (auto simp: ho_check_polynomial_signature_def list_all_iff)

theorem ho_polynomial_signature_closed:
  assumes check: "ho_check_polynomial_signature S ps"
  shows "ho_interpretation_closed (ho_polynomial_interpretation ps)"
proof -
  have typed: "ho_polynomial_type [] (ps!n) (S!n)" if "n<length ps" for n
    by (rule ho_polynomial_typeof_sound) (use check that in \<open>simp add: ho_check_polynomial_signature_iff\<close>)
  have sub: "(ho_polynomial_interpretation ps n)[v/k]=ho_polynomial_interpretation ps n" for n v k
    unfolding ho_polynomial_interpretation_def
    using ho_polynomial_closed_subst[OF typed] by auto
  have lif: "lift (ho_polynomial_interpretation ps n) k=ho_polynomial_interpretation ps n" for n k
    unfolding ho_polynomial_interpretation_def
    using ho_polynomial_closed_lift[OF typed] by auto
  show ?thesis unfolding ho_interpretation_closed_def using sub lif by blast
qed

theorem ho_polynomial_signature_value:
  assumes check: "ho_check_polynomial_signature S ps"
  shows "ho_env_value S (ho_polynomial_interpretation ps)"
  unfolding ho_env_value_def
proof (intro allI impI)
  fix n assume n: "n<length S"
  have ty: "ho_polynomial_type [] (ps!n) (S!n)"
    by (rule ho_polynomial_typeof_sound) (use check n in \<open>simp add: ho_check_polynomial_signature_iff\<close>)
  have ev: "ho_env_value [] Var" by (simp add: ho_env_value_def)
  have v: "ho_value (S!n) (ho_polynomial_eval Var (ps!n))"
    by (rule ho_polynomial_fundamental[OF ty, THEN conjunct1, rule_format, OF ev])
  show "ho_value (S!n) (ho_polynomial_interpretation ps n)"
    using check n v by (simp add: ho_check_polynomial_signature_iff ho_polynomial_interpretation_def)
qed

end
