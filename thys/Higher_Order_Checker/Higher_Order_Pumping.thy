theory Higher_Order_Pumping
  imports Higher_Order_Embedding
begin

text \<open>A typed first-order fragment of the higher-order syntax supports
substitution pumping. Applications remain typed higher-order applications;
there is no erasure to an untyped rewrite system.\<close>

fun ho_plain where
  "ho_plain (HBound n) = False"
| "ho_plain (HFree n) = True"
| "ho_plain (HConst n) = True"
| "ho_plain (HApp f x) = (ho_plain f \<and> ho_plain x)"
| "ho_plain (HAbs A t) = False"

fun ho_plain_pattern where
  "ho_plain_pattern (PConst n) = True"
| "ho_plain_pattern (PApp f x) = (ho_plain_pattern f \<and> ho_plain_pattern x)"
| "ho_plain_pattern (PMeta n ts) = (ts=[] )"
| "ho_plain_pattern _ = False"

lemma ho_lift_zero [simp]: "ho_lift 0 d t = t"
  by (induction t arbitrary: d) auto

lemma ho_plain_pattern_erase:
  "ho_plain_pattern p \<Longrightarrow> ho_plain (ho_erase_pattern p)"
  by (induction p) auto

lemma ho_plain_pattern_instance:
  "ho_plain_pattern p \<Longrightarrow>
   ho_instantiate s 0 p = Some (ho_subst s 0 (ho_erase_pattern p))"
  by (induction p) auto

lemma ho_plain_subst_type:
  assumes plain: "ho_plain t" and ty: "ho_typeof S G [] t = Some A"
    and sub: "ho_typed_subst S V [] G s"
  shows "ho_typeof S V [] (ho_subst s 0 t) = Some A"
  using plain ty
  by (induction t arbitrary: A)
     (auto simp: ho_typed_subst_def sub[unfolded ho_typed_subst_def]
       split: option.splits ho_type.splits if_splits)

lemma ho_plain_subst_compose:
  "ho_plain t \<Longrightarrow> ho_subst s 0 (ho_subst q 0 t) =
    ho_subst (\<lambda>n. ho_subst s 0 (q n)) 0 t"
  by (induction t) auto

fun ho_pump_subst where
  "ho_pump_subst q 0 = HFree"
| "ho_pump_subst q (Suc n) = (\<lambda>i. ho_subst (ho_pump_subst q n) 0 (q i))"

lemma ho_pump_subst_typed:
  assumes q: "ho_typed_subst S G [] G q"
    and plain: "\<And>i. i<length G \<Longrightarrow> ho_plain (q i)"
  shows "ho_typed_subst S G [] G (ho_pump_subst q n)"
proof (induction n)
  case 0
  then show ?case by (simp add: ho_typed_subst_def)
next
  case (Suc n)
  show ?case unfolding ho_typed_subst_def
  proof (intro allI impI)
    fix i assume i: "i<length G"
    have ty: "ho_typeof S G [] (q i) = Some (G!i)"
      using q i unfolding ho_typed_subst_def by blast
    show "ho_typeof S G [] (ho_pump_subst q (Suc n) i) = Some (G!i)"
      using ho_plain_subst_type[OF plain[OF i] ty Suc.IH] by simp
  qed
qed

theorem ho_plain_rule_pumping:
  assumes rule: "(G,l,r) \<in> set R"
    and plain: "ho_plain_pattern l" "ho_plain_pattern r"
    and typed: "ho_rule_welltyped S (G,l,r)"
    and q: "ho_typed_subst S G [] G q"
    and qp: "\<And>i. i<length G \<Longrightarrow> ho_plain (q i)"
    and inst: "ho_erase_pattern r = ho_subst q 0 (ho_erase_pattern l)"
    and A: "ho_typeof S G [] (ho_erase_pattern l) = Some A"
  shows "\<not> wf ((ho_relation S G R A)\<inverse>)"
proof -
  let ?u = "\<lambda>n. ho_subst (ho_pump_subst q n) 0 (ho_erase_pattern l)"
  have st: "ho_typed_subst S G [] G (ho_pump_subst q n)" for n
    by (rule ho_pump_subst_typed[OF q qp])
  have ut: "ho_typeof S G [] (?u n) = Some A" for n
    by (rule ho_plain_subst_type[OF ho_plain_pattern_erase[OF plain(1)] A st])
  have step: "(?u n, ?u (Suc n)) \<in> ho_relation S G R A" for n
  proof -
    have rhs: "ho_subst (ho_pump_subst q n) 0 (ho_erase_pattern r) = ?u (Suc n)"
      unfolding inst using ho_plain_subst_compose[OF ho_plain_pattern_erase[OF plain(1)]] by simp
    have "ho_step S G R [] (?u n) (?u (Suc n))"
      by (rule ho_step.rule[OF rule typed st ho_plain_pattern_instance[OF plain(1)]])
         (use ho_plain_pattern_instance[OF plain(2), of "ho_pump_subst q n"] rhs in simp)
    then show ?thesis using ut[of n] ut[of "Suc n"] by (simp add: ho_relation_def)
  qed
  show ?thesis
  proof
    assume wf: "wf ((ho_relation S G R A)\<inverse>)"
    have nonempty: "range ?u \<noteq> {}" by simp
    obtain z where z: "z \<in> range ?u"
      "\<And>y. (y,z) \<in> (ho_relation S G R A)\<inverse> \<Longrightarrow> y \<notin> range ?u"
      using wf_iff_ex_minimal[THEN iffD1, OF wf, rule_format, OF nonempty] by blast
    obtain n where n: "z=?u n" using z(1) by blast
    have "(?u (Suc n),z) \<in> (ho_relation S G R A)\<inverse>" using step[of n] n by simp
    then show False using z(2) by blast
  qed
qed

definition ho_check_rule_pump where
  "ho_check_rule_pump S R i ss \<longleftrightarrow> i<length R \<and>
    (case R!i of (G,l,r) \<Rightarrow> length ss=length G \<and>
      ho_plain_pattern l \<and> ho_plain_pattern r \<and> ho_rule_welltyped S (G,l,r) \<and>
      list_all ho_plain ss \<and> ho_typed_subst S G [] G ((!) ss) \<and>
      ho_erase_pattern r = ho_subst ((!) ss) 0 (ho_erase_pattern l))"

theorem ho_check_rule_pump_sound:
  assumes "ho_check_rule_pump S R i ss"
  shows "\<exists>G A. \<not> wf ((ho_relation S G R A)\<inverse>)"
proof -
  obtain G l r where entry: "R!i=(G,l,r)" by (cases "R!i") auto
  have inR: "(G,l,r) \<in> set R" using assms entry
    unfolding ho_check_rule_pump_def by (metis conjunct1 nth_mem)
  obtain A where A: "ho_typeof S G [] (ho_erase_pattern l) = Some A"
    using assms entry by (auto simp: ho_check_rule_pump_def ho_rule_welltyped_def split: option.splits)
  have "\<not> wf ((ho_relation S G R A)\<inverse>)"
    by (rule ho_plain_rule_pumping[OF inR _ _ _ _ _ _ A])
       (use assms entry in \<open>auto simp: ho_check_rule_pump_def list_all_iff\<close>)
  then show ?thesis by blast
qed

end
