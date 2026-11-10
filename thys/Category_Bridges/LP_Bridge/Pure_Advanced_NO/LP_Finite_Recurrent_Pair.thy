theory LP_Finite_Recurrent_Pair
  imports Category_LP_NO_Bridge.LP_Finite_NO_Checkers
begin

lemma lp_finite_rec_put_eval:
  assumes vars: "vars_term C\<subseteq>{x}"
  shows "lp_finite_eval (lp_rec_put C x t) \<rho> = lp_finite_eval C (\<lambda>_. lp_finite_eval t \<rho>)"
  unfolding lp_rec_put_def lp_finite_eval_subst
  by (rule lp_finite_eval_cong) (use vars in auto)


lemma lp_finite_rec_power_eval:
  assumes vars: "vars_term C\<subseteq>{x}"
  shows "lp_finite_eval (lp_rec_power C x n t) \<rho> =
    ((\<lambda>u. lp_finite_eval C (\<lambda>_.u))^^n) (lp_finite_eval t \<rho>)"
  unfolding lp_rec_power_def
  by (induct n) (simp_all add: funpow_Suc_right lp_finite_rec_put_eval[OF vars])


lemma lp_finite_rec_fill_eval:
  assumes vars: "\<Union>(vars_term ` set (snd A))\<subseteq>{x,y}" and xy: "x\<noteq>y"
  shows "lp_finite_atom_eval (lp_rec_fill A x y u v) \<rho> =
    lp_finite_atom_eval A (\<lambda>z. if z=x then lp_finite_eval u \<rho> else lp_finite_eval v \<rho>)"
  unfolding lp_rec_fill_def
  apply (subst lp_atom_subst_comp)
  unfolding lp_atom_subst_def
  using vars xy by (auto intro!: map_cong lp_finite_eval_cong)


theorem lp_finite_recurrent_pair_sound:
  fixes P :: "('f,'v) lp_clause list"
  assumes xy: "x\<noteq>y" and av: "\<Union>(vars_term ` set (snd A))\<subseteq>{x,y}"
    and cv: "vars_term C\<subseteq>{x}" and sg: "ground s" and bound: "n\<le>m"
    and shapes: "lp_rec_templates A C x y s d n m a b c keep=(h1,b1,h2,b2)"
    and run1: "lp_match_run P [h1] steps1=Some (b1#bs1)"
    and run2: "lp_match_run P [h2] steps2=Some (b2#bs2)"
    and progress: "steps1\<noteq>[]" "steps2\<noteq>[]"
  shows "\<not>SN_on (lp_ld P)
    {[lp_finite_atom_eval (lp_rec_fill A x y s (lp_rec_power C x m s)) Var]}"
proof -
  let ?f = "\<lambda>u. lp_finite_eval C (\<lambda>_.u)"
  let ?s = "lp_finite_eval s Var"
  let ?F = "\<lambda>i k. lp_finite_atom_eval A (\<lambda>z. if z=x then (?f ^^ (d * i)) ?s else (?f ^^ (m + d * k)) ?s)"
  have seed: "\<And>\<rho>. lp_finite_eval s \<rho>=?s"
    by (rule lp_finite_eval_cong) (use sg in \<open>auto simp: ground_vars_term_empty\<close>)
  have h1: "h1=lp_rec_fill A x y (Var x) (lp_rec_power C x (n+d) (Var y))"
    and b1: "b1=lp_rec_fill A x y (lp_rec_power C x (a*d) (Var x)) (lp_rec_power C x n (Var y))"
    and h2: "h2=lp_rec_fill A x y (Var x) (lp_rec_power C x m s)"
    and b2: "b2=lp_rec_fill A x y (lp_rec_power C x (b*d) (if keep then Var x else s))
      (lp_rec_power C x (m+c*d) (Var x))"
    using shapes unfolding lp_rec_templates_def by auto
  have pump: "\<And>i k tail. \<exists>l tail'. (?F i (Suc k)#tail,?F l k#tail')\<in>(lp_ld P)\<^sup>+"
  proof -
    fix i k tail
    let ?rho = "\<lambda>z. if z=x then (?f ^^ (d * i)) ?s else (?f ^^ (m - n + d * k)) ?s"
    have sum1: "(n + d) + (m - n + d * k) = m + d * Suc k" using bound
      by (simp only: mult_Suc_right; arith)
    have sum2: "n + (m - n + d * k) = m + d * k" using bound by arith
    have start: "lp_finite_atom_eval h1 ?rho=?F i (Suc k)"
      unfolding h1
      apply (subst lp_finite_rec_fill_eval[OF av xy])
      apply (rule arg_cong[where f="lp_finite_atom_eval A"])
      apply (rule ext)
      using xy by (auto simp: lp_finite_rec_power_eval[OF cv] lp_funpow_join sum1)
    have finish: "lp_finite_atom_eval b1 ?rho=?F (i+a) k"
      unfolding b1
      apply (subst lp_finite_rec_fill_eval[OF av xy])
      apply (rule arg_cong[where f="lp_finite_atom_eval A"])
      apply (rule ext)
      using xy by (auto simp: lp_finite_rec_power_eval[OF cv] lp_funpow_join sum2 algebra_simps)
    have path: "(?F i (Suc k)#tail,?F (i+a) k#(map (\<lambda>a. lp_finite_atom_eval a ?rho) bs1 @ tail))\<in>(lp_ld P)\<^sup>+"
      using lp_finite_match_run_nonempty_sound[OF run1 progress(1), of ?rho tail]
      by (simp add: start finish)
    show "\<exists>l tail'. (?F i (Suc k)#tail,?F l k#tail')\<in>(lp_ld P)\<^sup>+"
      using path by auto
  qed
  have reset: "\<And>i tail. \<exists>l k tail'. (?F i 0#tail,?F l k#tail')\<in>(lp_ld P)\<^sup>+"
  proof -
    fix i tail
    let ?rho = "\<lambda>z. if z=x then (?f ^^ (d * i)) ?s else ?s"
    have start: "lp_finite_atom_eval h2 ?rho=?F i 0"
      unfolding h2
      apply (subst lp_finite_rec_fill_eval[OF av xy, where u="Var x" and v="lp_rec_power C x m s" and \<rho> = ?rho])
      apply (rule arg_cong[where f="lp_finite_atom_eval A"])
      apply (rule ext)
      by (simp only: lp_finite_rec_power_eval[OF cv] seed[of ?rho] Term.eval_term.simps
          mult_0_right add_0_right if_True refl)
    have finish: "lp_finite_atom_eval b2 ?rho=?F (if keep then i+b else b) (i+c)"
      unfolding b2
      apply (subst lp_finite_rec_fill_eval[OF av xy, where u="lp_rec_power C x (b*d) (if keep then Var x else s)"
        and v="lp_rec_power C x (m+c*d) (Var x)" and \<rho> = ?rho])
      apply (rule arg_cong[where f="lp_finite_atom_eval A"])
      apply (rule ext)
      by (cases keep) (simp_all only: lp_finite_rec_power_eval[OF cv] seed[of ?rho] Term.eval_term.simps
          if_True if_False refl lp_funpow_join algebra_simps)
    have path: "(?F i 0#tail,?F (if keep then i+b else b) (i+c)#(map (\<lambda>a. lp_finite_atom_eval a ?rho) bs2 @ tail))\<in>(lp_ld P)\<^sup>+"
      using lp_finite_match_run_nonempty_sound[OF run2 progress(2), of ?rho tail]
      by (simp add: start finish)
    show "\<exists>l k tail'. (?F i 0#tail,?F l k#tail')\<in>(lp_ld P)\<^sup>+"
      using path by auto
  qed
  have bad: "\<not>SN_on (lp_ld P) {[?F 0 0]}"
    by (rule lp_recurrent_serial[where F = ?F and R="lp_ld P" and m=0 and k=0 and tail="[]", OF pump reset])
  have initial: "lp_finite_atom_eval (lp_rec_fill A x y s (lp_rec_power C x m s)) Var = ?F 0 0"
    apply (subst lp_finite_rec_fill_eval[OF av xy, where u=s and v="lp_rec_power C x m s" and \<rho>=Var])
    apply (subst lp_finite_rec_power_eval[OF cv, where n=m and t=s and \<rho>=Var])
    by (simp only: mult_0_right add_0_right funpow.simps id_apply)
  show ?thesis using bad unfolding initial .
qed


end
