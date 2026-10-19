theory Higher_Order_Values
  imports "Higher_Order_Beta.Higher_Order_Application" "Higher_Order_Lambda.ParRed"
begin

text \<open>A syntactic carrier avoids a dependent universe of HOL function
types. Natural values are represented by Church numerals modulo beta reduction;
higher types use extensional, weakly monotone application on these carriers.
This is semantic infrastructure, not yet an executable order processor.\<close>

fun ho_church_body where
  "ho_church_body 0 = Var 0"
| "ho_church_body (Suc n) = App (Var 1) (ho_church_body n)"

definition ho_church where
  "ho_church n = Abs (Abs (ho_church_body n))"

lemma ho_church_body_normal:
  "\<not> beta (ho_church_body n) u"
  by (induction n arbitrary: u) (auto elim: beta_cases)

lemma ho_church_normal:
  "\<not> beta (ho_church n) u"
  by (auto simp: ho_church_def ho_church_body_normal elim: beta_cases)

lemma ho_church_body_injective:
  "ho_church_body n=ho_church_body m \<Longrightarrow> n=m"
  by (induction n arbitrary: m; case_tac m) auto

lemma ho_church_injective:
  "ho_church n=ho_church m \<longleftrightarrow> n=m"
  by (auto simp: ho_church_def dest: ho_church_body_injective)

lemma ho_normal_path:
  "(\<And>v. \<not> P t v) \<Longrightarrow> P\<^sup>*\<^sup>* t u \<Longrightarrow> u=t"
  by (metis converse_rtranclpE)

lemma ho_church_path:
  "beta\<^sup>*\<^sup>* (ho_church n) t \<Longrightarrow> t=ho_church n"
  by (meson ho_normal_path ho_church_normal)

definition ho_numeral where
  "ho_numeral t n \<longleftrightarrow> beta\<^sup>*\<^sup>* t (ho_church n)"

lemma ho_numeral_unique:
  "ho_numeral t n \<Longrightarrow> ho_numeral t m \<Longrightarrow> n=m"
  using beta_confluent
  unfolding ho_numeral_def diamond_def commute_def square_def
  by (metis ho_church_path ho_church_injective)

lemma ho_numeral_expand:
  "beta\<^sup>*\<^sup>* t u \<Longrightarrow> ho_numeral u n \<Longrightarrow> ho_numeral t n"
  by (auto simp: ho_numeral_def intro: rtranclp_trans)

lemma ho_numeral_reduce:
  "beta\<^sup>*\<^sup>* t u \<Longrightarrow> ho_numeral t n \<Longrightarrow> ho_numeral u n"
  using beta_confluent
  unfolding ho_numeral_def diamond_def commute_def square_def
  by (metis ho_church_path)

fun ho_value and ho_value_ge where
  "ho_value (HBase b) t = (\<exists>n. ho_numeral t n)"
| "ho_value (HArrow A B) t =
    ((\<forall>x. ho_value A x \<longrightarrow> ho_value B (App t x)) \<and>
     (\<forall>x y. ho_value A x \<and> ho_value A y \<and> ho_value_ge A x y \<longrightarrow>
       ho_value_ge B (App t x) (App t y)))"
| "ho_value_ge (HBase b) t u = (\<exists>m n. ho_numeral t m \<and> ho_numeral u n \<and> m\<ge>n)"
| "ho_value_ge (HArrow A B) t u =
    (\<forall>x. ho_value A x \<longrightarrow> ho_value_ge B (App t x) (App u x))"

fun ho_value_gt where
  "ho_value_gt (HBase b) t u = (\<exists>m n. ho_numeral t m \<and> ho_numeral u n \<and> m>n)"
| "ho_value_gt (HArrow A B) t u =
    (\<forall>x. ho_value A x \<longrightarrow> ho_value_gt B (App t x) (App u x))"

lemma ho_value_ge_refl:
  "ho_value A t \<Longrightarrow> ho_value_ge A t t"
  by (induction A arbitrary: t) auto

lemma ho_value_ge_trans:
  "ho_value_ge A t u \<Longrightarrow> ho_value_ge A u v \<Longrightarrow> ho_value_ge A t v"
proof (induction A arbitrary: t u v)
  case (HBase b)
  then obtain m n k l where ns: "ho_numeral t m" "ho_numeral u n"
    "ho_numeral u k" "ho_numeral v l" "n\<le>m" "l\<le>k" by auto
  have "n=k" by (rule ho_numeral_unique[OF ns(2,3)])
  then have "l\<le>m" using ns(5,6) by simp
  then show ?case using ns(1,4) by auto
next
  case (HArrow A B)
  then show ?case by auto
qed

lemma ho_value_gt_ge:
  "ho_value_gt A t u \<Longrightarrow> ho_value_ge A t u"
proof (induction A arbitrary: t u)
  case (HBase b)
  then obtain m n where ns: "ho_numeral t m" "ho_numeral u n" "m>n" by auto
  have "m\<ge>n" using ns(3) by simp
  then show ?case using ns(1,2) by auto
next
  case (HArrow A B)
  then show ?case by auto
qed

lemma ho_numeral_beta:
  "beta\<^sup>*\<^sup>* t u \<Longrightarrow> ho_numeral t n = ho_numeral u n"
  by (blast intro: ho_numeral_expand ho_numeral_reduce)

lemma ho_values_beta:
  "(\<forall>t u. beta\<^sup>*\<^sup>* t u \<longrightarrow> ho_value A t = ho_value A u) \<and>
   (\<forall>t u v w. beta\<^sup>*\<^sup>* t u \<longrightarrow> beta\<^sup>*\<^sup>* v w \<longrightarrow>
      ho_value_ge A t v = ho_value_ge A u w) \<and>
   (\<forall>t u v w. beta\<^sup>*\<^sup>* t u \<longrightarrow> beta\<^sup>*\<^sup>* v w \<longrightarrow>
      ho_value_gt A t v = ho_value_gt A u w)"
proof (induction A)
  case (HBase b)
  then show ?case by (auto dest: ho_numeral_beta)
next
  case (HArrow A B)
  note vi = HArrow.IH(2)[THEN conjunct1, rule_format]
  note gi = HArrow.IH(2)[THEN conjunct2, THEN conjunct1, rule_format]
  note ti = HArrow.IH(2)[THEN conjunct2, THEN conjunct2, rule_format]
  have vb: "ho_value B (App t x) = ho_value B (App u x)"
    if "beta\<^sup>*\<^sup>* t u" for t u x
    by (rule vi[OF rtrancl_beta_AppL[OF that]])
  have gb: "ho_value_ge B (App t x) (App v y) = ho_value_ge B (App u x) (App w y)"
    if "beta\<^sup>*\<^sup>* t u" "beta\<^sup>*\<^sup>* v w" for t u v w x y
    by (rule gi[OF rtrancl_beta_AppL[OF that(1)] rtrancl_beta_AppL[OF that(2)]])
  have tb: "ho_value_gt B (App t x) (App v y) = ho_value_gt B (App u x) (App w y)"
    if "beta\<^sup>*\<^sup>* t u" "beta\<^sup>*\<^sup>* v w" for t u v w x y
    by (rule ti[OF rtrancl_beta_AppL[OF that(1)] rtrancl_beta_AppL[OF that(2)]])
  have vv: "ho_value (HArrow A B) t = ho_value (HArrow A B) u"
    if "beta\<^sup>*\<^sup>* t u" for t u
    by (simp only: ho_value.simps vb[OF that] gb[OF that that])
  have gg: "ho_value_ge (HArrow A B) t v = ho_value_ge (HArrow A B) u w"
    if "beta\<^sup>*\<^sup>* t u" "beta\<^sup>*\<^sup>* v w" for t u v w
    by (simp only: ho_value_ge.simps gb[OF that])
  have tt: "ho_value_gt (HArrow A B) t v = ho_value_gt (HArrow A B) u w"
    if "beta\<^sup>*\<^sup>* t u" "beta\<^sup>*\<^sup>* v w" for t u v w
    by (simp only: ho_value_gt.simps tb[OF that])
  show ?case using vv gg tt by blast
qed

fun ho_zero where
  "ho_zero (HBase b) = ho_church 0"
| "ho_zero (HArrow A B) = Abs (lift (ho_zero B) 0)"

lemma ho_zero_application:
  "beta (App (ho_zero (HArrow A B)) x) (ho_zero B)"
  using beta.beta[of "lift (ho_zero B) 0" x] by simp

lemma ho_zero_value:
  "ho_value A (ho_zero A)"
proof (induction A)
  case (HBase b)
  show ?case unfolding ho_value.simps ho_zero.simps
    by (rule exI[where x=0]) (simp add: ho_numeral_def)
next
  case (HArrow A B)
  have path: "beta\<^sup>*\<^sup>* (App (ho_zero (HArrow A B)) x) (ho_zero B)" for x
    by (rule r_into_rtranclp) (rule ho_zero_application)
  have vb: "ho_value B (App (ho_zero (HArrow A B)) x)" for x
    using ho_values_beta[of B, THEN conjunct1, rule_format, OF path[of x]] HArrow.IH(2) by simp
  have gb: "ho_value_ge B (App (ho_zero (HArrow A B)) x) (App (ho_zero (HArrow A B)) y)" for x y
    using ho_values_beta[of B, THEN conjunct2, THEN conjunct1, rule_format, OF path[of x] path[of y]]
      ho_value_ge_refl[OF HArrow.IH(2)] by simp
  show ?case unfolding ho_value.simps(2) using vb gb by blast
qed

fun ho_observe where
  "ho_observe (HBase b) t = (THE n. ho_numeral t n)"
| "ho_observe (HArrow A B) t = ho_observe B (App t (ho_zero A))"

lemma ho_observe_numeral:
  "ho_numeral t n \<Longrightarrow> (THE m. ho_numeral t m)=n"
  by (rule the_equality) (auto dest: ho_numeral_unique)

lemma ho_value_gt_observe:
  "ho_value_gt A t u \<Longrightarrow> ho_observe A t > ho_observe A u"
proof (induction A arbitrary: t u)
  case (HBase b)
  then obtain m n where ns: "ho_numeral t m" "ho_numeral u n" "m>n" by auto
  show ?case using ns(3) ho_observe_numeral[OF ns(1)] ho_observe_numeral[OF ns(2)] by simp
next
  case (HArrow A B)
  have "ho_value_gt B (App t (ho_zero A)) (App u (ho_zero A))"
    using HArrow.prems ho_zero_value[of A] by simp
  from HArrow.IH(2)[OF this] show ?case by simp
qed

theorem ho_value_gt_wellfounded:
  "wf {(u,t). ho_value_gt A t u}"
  by (rule wf_subset[OF wf_measure[of "ho_observe A"]])
     (auto dest: ho_value_gt_observe)

end
