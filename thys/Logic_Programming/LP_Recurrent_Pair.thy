theory LP_Recurrent_Pair
  imports LP_Source_Neutral
begin

text \<open>Two-phase recurrent pairs. The numerical invariant is separate
  from the checked source derivations. Each phase may be a nonempty matching
  trace, including explicitly resolved successful prefixes.

  This is the recurrent-pair construction of Payet, Recurrent Pairs Revisited
  (LOPSTR 2025, Definition 3), parameterized by natural quotients rather than
  divisibility tests. The pump reduces the second exponent by d and increases
  the first by a*d. The reset increases its second exponent by c*d and either
  retains or resets its first exponent. Writing the reset exponent as m+c*d
  avoids an unsound truncated subtraction when the reset exponent is below m.
  Context holes may occur repeatedly. All source transitions are checked in
  the infinite-tree leftmost relation, without an occurs-check assumption.\<close>

lemma lp_recurrent_drain:
  assumes pump: "\<And>m k tail. \<exists>l tail'.
    (F m (Suc k)#tail,F l k#tail')\<in>R\<^sup>+"
  shows "\<exists>l tail'. (F m k#tail,F l 0#tail')\<in>R\<^sup>*"
proof (induct k arbitrary: m tail)
  case 0 show ?case by (intro exI[where x=m] exI[where x=tail]) simp
next
  case (Suc k)
  obtain l tail' where first: "(F m (Suc k)#tail,F l k#tail')\<in>R\<^sup>+"
    using pump[of m k tail] by auto
  obtain j tail'' where rest: "(F l k#tail',F j 0#tail'')\<in>R\<^sup>*"
    using Suc.hyps[of l tail'] by auto
  show ?case by (intro exI[where x=j] exI[where x=tail''])
    (rule rtrancl_trans[OF trancl_into_rtrancl[OF first] rest])
qed

lemma lp_recurrent_serial:
  assumes pump: "\<And>m k tail. \<exists>l tail'.
    (F m (Suc k)#tail,F l k#tail')\<in>R\<^sup>+"
    and reset: "\<And>m tail. \<exists>l k tail'. (F m 0#tail,F l k#tail')\<in>R\<^sup>+"
  shows "\<not>SN_on R {F m k#tail}"
proof -
  have bad: "\<not>SN_on (R\<^sup>+) {F m k#tail}"
  proof (rule lp_serial_not_SN[where X="{gs. \<exists>m k tail. gs=F m k#tail}"])
    show "F m k#tail\<in>{gs. \<exists>m k tail. gs=F m k#tail}" by auto
  next
    fix gs assume "gs\<in>{gs. \<exists>m k tail. gs=F m k#tail}"
    then obtain m k tail where gs: "gs=F m k#tail" by auto
    obtain l tail' where first: "(F m k#tail,F l 0#tail')\<in>R\<^sup>*"
      using lp_recurrent_drain[where F=F and R=R and m=m and k=k and tail=tail, OF pump] by auto
    obtain j n tail'' where rest: "(F l 0#tail',F j n#tail'')\<in>R\<^sup>+"
      using reset[of l tail'] by auto
    have path: "(gs,F j n#tail'')\<in>R\<^sup>+"
      unfolding gs by (rule rtrancl_trancl_trancl[OF first rest])
    show "\<exists>t\<in>{gs. \<exists>m k tail. gs=F m k#tail}. (gs,t)\<in>R\<^sup>+"
      using path by auto
  qed
  show ?thesis using bad SN_on_trancl by blast
qed

definition lp_rec_put where
  "lp_rec_put C x t = C\<cdot>(\<lambda>z. if z=x then t else Var z)"

definition lp_rec_power where
  "lp_rec_power C x n t = ((lp_rec_put C x)^^n) t"

definition lp_rec_fill where
  "lp_rec_fill A x y u v = lp_atom_subst A
    (\<lambda>z. if z=x then u else if z=y then v else Var z)"

lemma lp_rec_put_eval:
  assumes vars: "vars_term C\<subseteq>{x}"
  shows "lp_ieval (lp_rec_put C x t) \<rho> = lp_ieval C (\<lambda>_. lp_ieval t \<rho>)"
  unfolding lp_rec_put_def lp_ieval_finite_subst
  by (rule lp_ieval_cong) (use vars in auto)

lemma lp_rec_power_eval:
  assumes vars: "vars_term C\<subseteq>{x}"
  shows "lp_ieval (lp_rec_power C x n t) \<rho> =
    ((\<lambda>u. lp_ieval C (\<lambda>_.u))^^n) (lp_ieval t \<rho>)"
  unfolding lp_rec_power_def
  by (induct n) (simp_all add: funpow_Suc_right lp_rec_put_eval[OF vars])

lemma lp_rec_fill_eval:
  assumes vars: "\<Union>(vars_term ` set (snd A))\<subseteq>{x,y}" and xy: "x\<noteq>y"
  shows "lp_atom_eval (lp_rec_fill A x y u v) \<rho> =
    lp_atom_eval A (\<lambda>z. if z=x then lp_ieval u \<rho> else lp_ieval v \<rho>)"
  unfolding lp_rec_fill_def
  apply (subst lp_atom_eval_finite_subst)
  unfolding lp_atom_eval_def
  using vars xy by (auto intro!: map_cong lp_ieval_cong)

definition lp_rec_templates where
  "lp_rec_templates A C x y s d n m a b c keep = (
    lp_rec_fill A x y (Var x) (lp_rec_power C x (n+d) (Var y)),
    lp_rec_fill A x y (lp_rec_power C x (a*d) (Var x)) (lp_rec_power C x n (Var y)),
    lp_rec_fill A x y (Var x) (lp_rec_power C x m s),
    lp_rec_fill A x y (lp_rec_power C x (b*d) (if keep then Var x else s))
      (lp_rec_power C x (m+c*d) (Var x)))"

lemma lp_funpow_join:
  "(f^^r) ((f^^t) u) = (f^^(r+t)) u"
  by (simp add: funpow_add)

theorem lp_recurrent_pair_sound:
  fixes P :: "('f,'v) lp_clause list"
  assumes xy: "x\<noteq>y" and av: "\<Union>(vars_term ` set (snd A))\<subseteq>{x,y}"
    and cv: "vars_term C\<subseteq>{x}" and sg: "ground s" and bound: "n\<le>m"
    and shapes: "lp_rec_templates A C x y s d n m a b c keep=(h1,b1,h2,b2)"
    and run1: "lp_match_run P [h1] steps1=Some (b1#bs1)"
    and run2: "lp_match_run P [h2] steps2=Some (b2#bs2)"
    and progress: "steps1\<noteq>[]" "steps2\<noteq>[]"
  shows "\<not>SN_on (lp_ild P)
    {[lp_atom_eval (lp_rec_fill A x y s (lp_rec_power C x m s)) LPIVar]}"
proof -
  let ?f = "\<lambda>u. lp_ieval C (\<lambda>_.u)"
  let ?s = "lp_ieval s LPIVar"
  let ?F = "\<lambda>i k. lp_atom_eval A (\<lambda>z. if z=x then (?f ^^ (d * i)) ?s else (?f ^^ (m + d * k)) ?s)"
  have seed: "\<And>\<rho>. lp_ieval s \<rho>=?s"
    by (rule lp_ieval_cong) (use sg in \<open>auto simp: ground_vars_term_empty\<close>)
  have h1: "h1=lp_rec_fill A x y (Var x) (lp_rec_power C x (n+d) (Var y))"
    and b1: "b1=lp_rec_fill A x y (lp_rec_power C x (a*d) (Var x)) (lp_rec_power C x n (Var y))"
    and h2: "h2=lp_rec_fill A x y (Var x) (lp_rec_power C x m s)"
    and b2: "b2=lp_rec_fill A x y (lp_rec_power C x (b*d) (if keep then Var x else s))
      (lp_rec_power C x (m+c*d) (Var x))"
    using shapes unfolding lp_rec_templates_def by auto
  have pump: "\<And>i k tail. \<exists>l tail'. (?F i (Suc k)#tail,?F l k#tail')\<in>(lp_ild P)\<^sup>+"
  proof -
    fix i k tail
    let ?rho = "\<lambda>z. if z=x then (?f ^^ (d * i)) ?s else (?f ^^ (m - n + d * k)) ?s"
    have sum1: "(n + d) + (m - n + d * k) = m + d * Suc k" using bound
      by (simp only: mult_Suc_right; arith)
    have sum2: "n + (m - n + d * k) = m + d * k" using bound by arith
    have start: "lp_atom_eval h1 ?rho=?F i (Suc k)"
      unfolding h1
      apply (subst lp_rec_fill_eval[OF av xy])
      apply (rule arg_cong[where f="lp_atom_eval A"])
      apply (rule ext)
      using xy by (auto simp: lp_rec_power_eval[OF cv] lp_funpow_join sum1)
    have finish: "lp_atom_eval b1 ?rho=?F (i+a) k"
      unfolding b1
      apply (subst lp_rec_fill_eval[OF av xy])
      apply (rule arg_cong[where f="lp_atom_eval A"])
      apply (rule ext)
      using xy by (auto simp: lp_rec_power_eval[OF cv] lp_funpow_join sum2 algebra_simps)
    have path: "(?F i (Suc k)#tail,?F (i+a) k#(map (\<lambda>a. lp_atom_eval a ?rho) bs1 @ tail))\<in>(lp_ild P)\<^sup>+"
      using lp_match_run_nonempty_sound[OF run1 progress(1), of ?rho tail]
      by (simp add: start finish)
    show "\<exists>l tail'. (?F i (Suc k)#tail,?F l k#tail')\<in>(lp_ild P)\<^sup>+"
      using path by auto
  qed
  have reset: "\<And>i tail. \<exists>l k tail'. (?F i 0#tail,?F l k#tail')\<in>(lp_ild P)\<^sup>+"
  proof -
    fix i tail
    let ?rho = "\<lambda>z. if z=x then (?f ^^ (d * i)) ?s else ?s"
    have start: "lp_atom_eval h2 ?rho=?F i 0"
      unfolding h2
      apply (subst lp_rec_fill_eval[OF av xy, where u="Var x" and v="lp_rec_power C x m s" and \<rho> = ?rho])
      apply (rule arg_cong[where f="lp_atom_eval A"])
      apply (rule ext)
      by (simp only: lp_rec_power_eval[OF cv] seed[of ?rho] lp_ieval.simps
          mult_0_right add_0_right if_True refl)
    have finish: "lp_atom_eval b2 ?rho=?F (if keep then i+b else b) (i+c)"
      unfolding b2
      apply (subst lp_rec_fill_eval[OF av xy, where u="lp_rec_power C x (b*d) (if keep then Var x else s)"
        and v="lp_rec_power C x (m+c*d) (Var x)" and \<rho> = ?rho])
      apply (rule arg_cong[where f="lp_atom_eval A"])
      apply (rule ext)
      by (cases keep) (simp_all only: lp_rec_power_eval[OF cv] seed[of ?rho] lp_ieval.simps
          if_True if_False refl lp_funpow_join algebra_simps)
    have path: "(?F i 0#tail,?F (if keep then i+b else b) (i+c)#(map (\<lambda>a. lp_atom_eval a ?rho) bs2 @ tail))\<in>(lp_ild P)\<^sup>+"
      using lp_match_run_nonempty_sound[OF run2 progress(2), of ?rho tail]
      by (simp add: start finish)
    show "\<exists>l k tail'. (?F i 0#tail,?F l k#tail')\<in>(lp_ild P)\<^sup>+"
      using path by auto
  qed
  have bad: "\<not>SN_on (lp_ild P) {[?F 0 0]}"
    by (rule lp_recurrent_serial[where F = ?F and R="lp_ild P" and m=0 and k=0 and tail="[]", OF pump reset])
  have initial: "lp_atom_eval (lp_rec_fill A x y s (lp_rec_power C x m s)) LPIVar = ?F 0 0"
    apply (subst lp_rec_fill_eval[OF av xy, where u=s and v="lp_rec_power C x m s" and \<rho>=LPIVar])
    apply (subst lp_rec_power_eval[OF cv, where n=m and t=s and \<rho>=LPIVar])
    by (simp only: mult_0_right add_0_right funpow.simps id_apply)
  show ?thesis using bad unfolding initial .
qed

end
