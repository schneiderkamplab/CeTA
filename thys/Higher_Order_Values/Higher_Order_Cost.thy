theory Higher_Order_Cost
  imports Higher_Order_Arithmetic
begin

lemma ho_numeral_church [simp]: "ho_numeral (ho_church n) n"
  by (simp add: ho_numeral_def)

lemma ho_value_beta:
  "beta\<^sup>*\<^sup>* t u \<Longrightarrow> ho_value A t = ho_value A u"
  by (rule ho_values_beta[THEN conjunct1, rule_format])

lemma ho_ge_beta:
  "beta\<^sup>*\<^sup>* t u \<Longrightarrow> beta\<^sup>*\<^sup>* v w \<Longrightarrow>
    ho_value_ge A t v = ho_value_ge A u w"
  by (rule ho_values_beta[THEN conjunct2, THEN conjunct1, rule_format])

lemma ho_gt_beta:
  "beta\<^sup>*\<^sup>* t u \<Longrightarrow> beta\<^sup>*\<^sup>* v w \<Longrightarrow>
    ho_value_gt A t v = ho_value_gt A u w"
  by (rule ho_values_beta[THEN conjunct2, THEN conjunct2, rule_format])

lemma ho_shift_path:
  "beta\<^sup>*\<^sup>* (App (ho_shift_value (HArrow A B) t n) x)
      (ho_shift_value B (App t x) n)"
  by (rule r_into_rtranclp) (rule ho_shift_value_application)

lemma ho_shift_ge:
  "ho_value_ge A t u \<Longrightarrow> ho_value_ge A (ho_shift_value A t n) (ho_shift_value A u n)"
proof (induction A arbitrary: t u)
  case (HBase b)
  then obtain m k where ns: "ho_numeral t m" "ho_numeral u k" "k\<le>m" by auto
  have t: "ho_numeral (ho_add t (ho_church n)) (m+n)"
    by (rule ho_add_numeral[OF ns(1) ho_numeral_church])
  have u: "ho_numeral (ho_add u (ho_church n)) (k+n)"
    by (rule ho_add_numeral[OF ns(2) ho_numeral_church])
  have "k+n\<le>m+n" using ns(3) by simp
  then show ?case unfolding ho_value_ge.simps ho_shift_value.simps using t u by blast
next
  case (HArrow A B)
  show ?case unfolding ho_value_ge.simps(2)
  proof (intro allI impI)
    fix x assume x: "ho_value A x"
    have point: "ho_value_ge B (App t x) (App u x)" using HArrow.prems x by simp
    have ih: "ho_value_ge B (ho_shift_value B (App t x) n) (ho_shift_value B (App u x) n)"
      by (rule HArrow.IH(2)[OF point])
    have eq: "ho_value_ge B (App (ho_shift_value (HArrow A B) t n) x)
        (App (ho_shift_value (HArrow A B) u n) x) =
      ho_value_ge B (ho_shift_value B (App t x) n) (ho_shift_value B (App u x) n)"
      by (rule ho_ge_beta[OF ho_shift_path ho_shift_path])
    show
      "ho_value_ge B (App (ho_shift_value (HArrow A B) t n) x)
        (App (ho_shift_value (HArrow A B) u n) x)"
      using ih eq by simp
  qed
qed

lemma ho_shift_gt:
  "ho_value_gt A t u \<Longrightarrow> ho_value_gt A (ho_shift_value A t n) (ho_shift_value A u n)"
proof (induction A arbitrary: t u)
  case (HBase b)
  then obtain m k where ns: "ho_numeral t m" "ho_numeral u k" "k<m" by auto
  have t: "ho_numeral (ho_add t (ho_church n)) (m+n)"
    by (rule ho_add_numeral[OF ns(1) ho_numeral_church])
  have u: "ho_numeral (ho_add u (ho_church n)) (k+n)"
    by (rule ho_add_numeral[OF ns(2) ho_numeral_church])
  have "k+n<m+n" using ns(3) by simp
  then show ?case unfolding ho_value_gt.simps ho_shift_value.simps using t u by blast
next
  case (HArrow A B)
  show ?case unfolding ho_value_gt.simps(2)
  proof (intro allI impI)
    fix x assume x: "ho_value A x"
    have point: "ho_value_gt B (App t x) (App u x)" using HArrow.prems x by simp
    have ih: "ho_value_gt B (ho_shift_value B (App t x) n) (ho_shift_value B (App u x) n)"
      by (rule HArrow.IH(2)[OF point])
    have eq: "ho_value_gt B (App (ho_shift_value (HArrow A B) t n) x)
        (App (ho_shift_value (HArrow A B) u n) x) =
      ho_value_gt B (ho_shift_value B (App t x) n) (ho_shift_value B (App u x) n)"
      by (rule ho_gt_beta[OF ho_shift_path ho_shift_path])
    show
      "ho_value_gt B (App (ho_shift_value (HArrow A B) t n) x)
        (App (ho_shift_value (HArrow A B) u n) x)"
      using ih eq by simp
  qed
qed

lemma ho_shift_value_closed:
  "ho_value A t \<Longrightarrow> ho_value A (ho_shift_value A t n)"
proof (induction A arbitrary: t)
  case (HBase b)
  then obtain m where "ho_numeral t m" by auto
  from ho_add_numeral[OF this ho_numeral_church, of n]
  show ?case by auto
next
  case (HArrow A B)
  have val: "ho_value B (App (ho_shift_value (HArrow A B) t n) x)"
    if x: "ho_value A x" for x
  proof -
    have v: "ho_value B (App t x)" using HArrow.prems x by simp
    have shifted: "ho_value B (ho_shift_value B (App t x) n)"
      by (rule HArrow.IH(2)[OF v])
    have eq: "ho_value B (App (ho_shift_value (HArrow A B) t n) x) =
        ho_value B (ho_shift_value B (App t x) n)"
      by (rule ho_value_beta[OF ho_shift_path])
    show ?thesis using eq shifted by simp
  qed
  have mono: "ho_value_ge B (App (ho_shift_value (HArrow A B) t n) x)
      (App (ho_shift_value (HArrow A B) t n) y)"
    if "ho_value A x" "ho_value A y" "ho_value_ge A x y" for x y
  proof -
    have g: "ho_value_ge B (App t x) (App t y)" using HArrow.prems that by simp
    have shifted: "ho_value_ge B (ho_shift_value B (App t x) n)
        (ho_shift_value B (App t y) n)" by (rule ho_shift_ge[OF g])
    have eq: "ho_value_ge B (App (ho_shift_value (HArrow A B) t n) x)
        (App (ho_shift_value (HArrow A B) t n) y) =
        ho_value_ge B (ho_shift_value B (App t x) n) (ho_shift_value B (App t y) n)"
      by (rule ho_ge_beta[OF ho_shift_path ho_shift_path])
    show ?thesis using shifted eq by simp
  qed
  show ?case unfolding ho_value.simps(2) using val mono by blast
qed

lemma ho_value_ge_observe:
  "ho_value_ge A t u \<Longrightarrow> ho_observe A t \<ge> ho_observe A u"
proof (induction A arbitrary: t u)
  case (HBase b)
  then obtain m n where ns: "ho_numeral t m" "ho_numeral u n" "m\<ge>n" by auto
  show ?case using ns(3) ho_observe_numeral[OF ns(1)] ho_observe_numeral[OF ns(2)] by simp
next
  case (HArrow A B)
  have point: "ho_value_ge B (App t (ho_zero A)) (App u (ho_zero A))"
    using HArrow.prems ho_zero_value[of A] by simp
  from HArrow.IH(2)[OF point] show ?case by simp
qed

lemma ho_shift_ge_cost:
  "ho_value_ge A t u \<Longrightarrow> n\<ge>m \<Longrightarrow>
    ho_value_ge A (ho_shift_value A t n) (ho_shift_value A u m)"
proof (induction A arbitrary: t u)
  case (HBase b)
  then obtain a c where ns: "ho_numeral t a" "ho_numeral u c" "a\<ge>c" by auto
  have t: "ho_numeral (ho_add t (ho_church n)) (a+n)"
    by (rule ho_add_numeral[OF ns(1) ho_numeral_church])
  have u: "ho_numeral (ho_add u (ho_church m)) (c+m)"
    by (rule ho_add_numeral[OF ns(2) ho_numeral_church])
  have "a+n\<ge>c+m" using ns(3) HBase.prems(2) by simp
  then show ?case unfolding ho_value_ge.simps ho_shift_value.simps using t u by blast
next
  case (HArrow A B)
  show ?case unfolding ho_value_ge.simps(2)
  proof (intro allI impI)
    fix x assume x: "ho_value A x"
    have point: "ho_value_ge B (App t x) (App u x)" using HArrow.prems(1) x by simp
    have ih: "ho_value_ge B (ho_shift_value B (App t x) n) (ho_shift_value B (App u x) m)"
      by (rule HArrow.IH(2)[OF point HArrow.prems(2)])
    have eq: "ho_value_ge B (App (ho_shift_value (HArrow A B) t n) x)
        (App (ho_shift_value (HArrow A B) u m) x) =
      ho_value_ge B (ho_shift_value B (App t x) n) (ho_shift_value B (App u x) m)"
      by (rule ho_ge_beta[OF ho_shift_path ho_shift_path])
    show "ho_value_ge B (App (ho_shift_value (HArrow A B) t n) x)
        (App (ho_shift_value (HArrow A B) u m) x)" using ih eq by simp
  qed
qed

lemma ho_shift_gt_cost:
  "ho_value_ge A t u \<Longrightarrow> n>m \<Longrightarrow>
    ho_value_gt A (ho_shift_value A t n) (ho_shift_value A u m)"
proof (induction A arbitrary: t u)
  case (HBase b)
  then obtain a c where ns: "ho_numeral t a" "ho_numeral u c" "a\<ge>c" by auto
  have t: "ho_numeral (ho_add t (ho_church n)) (a+n)"
    by (rule ho_add_numeral[OF ns(1) ho_numeral_church])
  have u: "ho_numeral (ho_add u (ho_church m)) (c+m)"
    by (rule ho_add_numeral[OF ns(2) ho_numeral_church])
  have "a+n>c+m" using ns(3) HBase.prems(2) by simp
  then show ?case unfolding ho_value_gt.simps ho_shift_value.simps using t u by blast
next
  case (HArrow A B)
  show ?case unfolding ho_value_gt.simps(2)
  proof (intro allI impI)
    fix x assume x: "ho_value A x"
    have point: "ho_value_ge B (App t x) (App u x)" using HArrow.prems(1) x by simp
    have ih: "ho_value_gt B (ho_shift_value B (App t x) n) (ho_shift_value B (App u x) m)"
      by (rule HArrow.IH(2)[OF point HArrow.prems(2)])
    have eq: "ho_value_gt B (App (ho_shift_value (HArrow A B) t n) x)
        (App (ho_shift_value (HArrow A B) u m) x) =
      ho_value_gt B (ho_shift_value B (App t x) n) (ho_shift_value B (App u x) m)"
      by (rule ho_gt_beta[OF ho_shift_path ho_shift_path])
    show "ho_value_gt B (App (ho_shift_value (HArrow A B) t n) x)
        (App (ho_shift_value (HArrow A B) u m) x)" using ih eq by simp
  qed
qed

lemma ho_shift_dominates:
  "ho_value A t \<Longrightarrow> ho_value_ge A (ho_shift_value A t n) t"
proof (induction A arbitrary: t)
  case (HBase b)
  then obtain m where numeral: "ho_numeral t m" by auto
  have raised: "ho_numeral (ho_add t (ho_church n)) (m+n)"
    by (rule ho_add_numeral[OF numeral ho_numeral_church])
  have bound: "m\<le>m+n" by simp
  show ?case unfolding ho_shift_value.simps ho_value_ge.simps using raised numeral bound by blast
next
  case (HArrow A B)
  show ?case unfolding ho_value_ge.simps(2)
  proof (intro allI impI)
    fix x assume x: "ho_value A x"
    have v: "ho_value B (App t x)" using HArrow.prems x by simp
    have ih: "ho_value_ge B (ho_shift_value B (App t x) n) (App t x)"
      by (rule HArrow.IH(2)[OF v])
    have eq: "ho_value_ge B (App (ho_shift_value (HArrow A B) t n) x) (App t x) =
        ho_value_ge B (ho_shift_value B (App t x) n) (App t x)"
      by (rule ho_ge_beta[OF ho_shift_path rtranclp.rtrancl_refl])
    show "ho_value_ge B (App (ho_shift_value (HArrow A B) t n) x) (App t x)"
      using ih eq by simp
  qed
qed

end
