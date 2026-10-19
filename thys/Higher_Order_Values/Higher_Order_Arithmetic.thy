theory Higher_Order_Arithmetic
  imports Higher_Order_Values
begin

fun ho_iter where
  "ho_iter 0 f x=x"
| "ho_iter (Suc n) f x=App f (ho_iter n f x)"

lemma ho_church_body_iter:
  "ho_church_body n=ho_iter n (Var 1) (Var 0)"
  by (induction n) auto

lemma ho_iter_subst:
  "(ho_iter n f x)[u/k]=ho_iter n (f[u/k]) (x[u/k])"
  by (induction n) auto

lemma ho_iter_add:
  "ho_iter m f (ho_iter n f x)=ho_iter (m+n) f x"
  by (induction m) auto

lemma ho_church_body_lift:
  "2\<le>k \<Longrightarrow> liftn d (ho_church_body n) k=ho_church_body n"
  by (induction n) auto

lemma ho_church_lift [simp]:
  "liftn d (ho_church n) 0=ho_church n"
  by (simp add: ho_church_def ho_church_body_lift)

lemma ho_church_apply:
  "beta\<^sup>*\<^sup>* (App (App (ho_church n) f) x) (ho_iter n f x)"
proof -
  have first: "beta (App (App (ho_church n) f) x)
      (App (Abs (ho_iter n (lift f 0) (Var 0))) x)"
    using beta.beta[of "Abs (ho_church_body n)" f]
    by (auto simp: ho_church_def ho_church_body_iter ho_iter_subst subst_Var intro: beta.appL)
  have second: "beta (App (Abs (ho_iter n (lift f 0) (Var 0))) x) (ho_iter n f x)"
    using beta.beta[of "ho_iter n (lift f 0) (Var 0)" x]
    by (simp add: ho_iter_subst)
  show ?thesis using first second by (meson r_into_rtranclp rtranclp_trans)
qed

lemma ho_liftn_betas:
  "beta\<^sup>*\<^sup>* t u \<Longrightarrow> beta\<^sup>*\<^sup>* (liftn n t k) (liftn n u k)"
  by (induction n) (auto intro: lift_preserves_beta')

definition ho_add where
  "ho_add t u = Abs (Abs (App (App (liftn 2 t 0) (Var 1))
                  (App (App (liftn 2 u 0) (Var 1)) (Var 0))))"

lemma ho_add_betas:
  "beta\<^sup>*\<^sup>* t t' \<Longrightarrow> beta\<^sup>*\<^sup>* u u' \<Longrightarrow>
   beta\<^sup>*\<^sup>* (ho_add t u) (ho_add t' u')"
  unfolding ho_add_def
  by (intro rtrancl_beta_Abs rtrancl_beta_App rtranclp.rtrancl_refl ho_liftn_betas)

lemma ho_add_church:
  "beta\<^sup>*\<^sup>* (ho_add (ho_church m) (ho_church n)) (ho_church (m+n))"
proof -
  have inner: "beta\<^sup>*\<^sup>* (App (App (ho_church n) (Var 1)) (Var 0))
      (ho_iter n (Var 1) (Var 0))" by (rule ho_church_apply)
  have outer: "beta\<^sup>*\<^sup>*
      (App (App (ho_church m) (Var 1)) (App (App (ho_church n) (Var 1)) (Var 0)))
      (ho_iter m (Var 1) (ho_iter n (Var 1) (Var 0)))"
    by (rule rtranclp_trans[OF rtrancl_beta_AppR[OF inner] ho_church_apply])
  have lhs: "ho_add (ho_church m) (ho_church n) =
      Abs (Abs (App (App (ho_church m) (Var 1))
        (App (App (ho_church n) (Var 1)) (Var 0))))"
    by (simp only: ho_add_def ho_church_lift)
  have rhs: "ho_church (m+n)=Abs (Abs (ho_iter m (Var 1) (ho_iter n (Var 1) (Var 0))))"
    by (simp add: ho_church_def ho_church_body_iter ho_iter_add)
  show ?thesis unfolding lhs rhs
    by (rule rtrancl_beta_Abs[OF rtrancl_beta_Abs[OF outer]])
qed

lemma ho_add_numeral:
  "ho_numeral t m \<Longrightarrow> ho_numeral u n \<Longrightarrow> ho_numeral (ho_add t u) (m+n)"
  unfolding ho_numeral_def
  by (rule rtranclp_trans[OF ho_add_betas ho_add_church])

lemma ho_church_apply_one:
  "beta (App (ho_church n) f) (Abs (ho_iter n (lift f 0) (Var 0)))"
  using beta.beta[of "Abs (ho_church_body n)" f]
  by (simp add: ho_church_def ho_church_body_iter ho_iter_subst subst_Var)

lemma ho_iter_church:
  "beta\<^sup>*\<^sup>* (ho_iter m (App (ho_church n) f) x) (ho_iter (m*n) f x)"
proof (induction m)
  case 0
  show ?case by simp
next
  case (Suc m)
  have first: "beta\<^sup>*\<^sup>*
      (App (App (ho_church n) f) (ho_iter m (App (ho_church n) f) x))
      (App (App (ho_church n) f) (ho_iter (m*n) f x))"
    by (rule rtrancl_beta_AppR[OF Suc.IH])
  have second: "beta\<^sup>*\<^sup>* (App (App (ho_church n) f) (ho_iter (m*n) f x))
      (ho_iter n f (ho_iter (m*n) f x))" by (rule ho_church_apply)
  show ?case using rtranclp_trans[OF first second] by (simp add: ho_iter_add)
qed

definition ho_multiply where
  "ho_multiply t u = Abs (App (lift t 0) (App (lift u 0) (Var 0)))"

lemma ho_church_lift1 [simp]: "lift (ho_church n) 0=ho_church n"
  using ho_church_lift[where d="Suc 0" and n=n] by (simp only: liftn_lift liftn_0)

lemma ho_multiply_church:
  "beta\<^sup>*\<^sup>* (ho_multiply (ho_church m) (ho_church n)) (ho_church (m*n))"
proof -
  have first: "beta (App (ho_church m) (App (ho_church n) (Var 0)))
      (Abs (ho_iter m (App (ho_church n) (Var 1)) (Var 0)))"
    using ho_church_apply_one[of m "App (ho_church n) (Var 0)"] by simp
  have second: "beta\<^sup>*\<^sup>* (Abs (ho_iter m (App (ho_church n) (Var 1)) (Var 0)))
      (Abs (ho_iter (m*n) (Var 1) (Var 0)))"
    by (rule rtrancl_beta_Abs[OF ho_iter_church])
  have path: "beta\<^sup>*\<^sup>* (App (ho_church m) (App (ho_church n) (Var 0)))
      (Abs (ho_iter (m*n) (Var 1) (Var 0)))"
    using first second by (meson r_into_rtranclp rtranclp_trans)
  have lhs: "ho_multiply (ho_church m) (ho_church n)=
      Abs (App (ho_church m) (App (ho_church n) (Var 0)))"
    by (simp only: ho_multiply_def ho_church_lift1)
  have rhs: "ho_church (m*n)=Abs (Abs (ho_iter (m*n) (Var 1) (Var 0)))"
    by (simp only: ho_church_def ho_church_body_iter)
  show ?thesis unfolding lhs rhs by (rule rtrancl_beta_Abs[OF path])
qed

lemma ho_multiply_betas:
  "beta\<^sup>*\<^sup>* t t' \<Longrightarrow> beta\<^sup>*\<^sup>* u u' \<Longrightarrow>
    beta\<^sup>*\<^sup>* (ho_multiply t u) (ho_multiply t' u')"
  unfolding ho_multiply_def
  by (intro rtrancl_beta_Abs rtrancl_beta_App rtranclp.rtrancl_refl lift_preserves_beta')

lemma ho_multiply_numeral:
  "ho_numeral t m \<Longrightarrow> ho_numeral u n \<Longrightarrow>
    ho_numeral (ho_multiply t u) (m*n)"
  unfolding ho_numeral_def
  by (rule rtranclp_trans[OF ho_multiply_betas ho_multiply_church])

lemma ho_church_body_subst:
  "2\<le>k \<Longrightarrow> (ho_church_body n)[t/k]=ho_church_body n"
  by (induction n) (auto simp: subst_Var)

lemma ho_church_subst [simp]: "(ho_church n)[t/k]=ho_church n"
  by (simp add: ho_church_def ho_church_body_subst)

lemma ho_lift_subst_zero [simp]:
  "(lift t 0)[lift v 0/Suc k]=lift (t[v/k]) 0"
  using lift_subst_lt[where i=0 and j=k and t=t and s=v] by simp

lemma ho_add_subst:
  "(ho_add t u)[v/k]=ho_add (t[v/k]) (u[v/k])"
  by (simp add: ho_add_def numeral_2_eq_2)

fun ho_shift_value where
  "ho_shift_value (HBase b) t n = ho_add t (ho_church n)"
| "ho_shift_value (HArrow A B) t n =
    Abs (ho_shift_value B (App (lift t 0) (Var 0)) n)"

lemma ho_shift_value_subst:
  "(ho_shift_value A t n)[v/k]=ho_shift_value A (t[v/k]) n"
  by (induction A arbitrary: t v k)
     (simp_all add: ho_add_subst)

lemma ho_shift_value_application:
  "beta (App (ho_shift_value (HArrow A B) t n) x)
    (ho_shift_value B (App t x) n)"
  using beta.beta[of "ho_shift_value B (App (lift t 0) (Var 0)) n" x]
  by (simp add: ho_shift_value_subst)

end
