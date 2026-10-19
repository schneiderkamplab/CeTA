theory Cycle_Morphism
  imports Cycle_Transport
begin

definition spell :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "spell A xs = concat (map A xs)"

lemma spell_simps[simp]:
  "spell A [] = []"
  "spell A (x#xs) = A x @ spell A xs"
  "spell A (xs@ys) = spell A xs @ spell A ys"
  by (simp_all add: spell_def)

lemma spell_compose[simp]:
  "spell A (spell F xs) = spell (\<lambda>x. spell A (F x)) xs"
  by (induct xs) auto

locale cycle_morphism =
  fixes R :: "'a srs" and pivot :: "'a list"
    and A :: "nat \<Rightarrow> 'a list" and F :: "nat \<Rightarrow> nat list"
    and I B :: "nat set"
  assumes transport: "i\<in>I \<Longrightarrow> (A i @ pivot,pivot @ spell A (F i))\<in>(srs_step R)^*"
    and positive: "i\<in>B \<Longrightarrow> (A i @ pivot,pivot @ spell A (F i))\<in>(srs_step R)^+"
    and closed: "i\<in>I \<Longrightarrow> set (F i) \<subseteq> I"
    and marked: "i\<in>B \<Longrightarrow> set (F i) \<inter> B \<noteq> {}"
    and subset: "B \<subseteq> I"
begin

lemma sweep:
  assumes "set xs \<subseteq> I"
  shows "(spell A xs @ pivot,pivot @ spell A (spell F xs))\<in>(srs_step R)^* \<and>
    (set xs \<inter> B \<noteq> {} \<longrightarrow>
      (spell A xs @ pivot,pivot @ spell A (spell F xs))\<in>(srs_step R)^+)"
  using assms
proof (induct xs)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  have xi: "x\<in>I" and tail: "set xs\<subseteq>I" using Cons.prems by auto
  have ih: "(spell A xs @ pivot,pivot @ spell A (spell F xs))\<in>(srs_step R)^*"
    using Cons.hyps[OF tail] by blast
  have first: "(A x @ (spell A xs @ pivot),A x @ (pivot @ spell A (spell F xs)))\<in>(srs_step R)^*"
    using rtrancl_srs_step_ctxtI[OF ih, of "A x" "[]"] by simp
  have last: "((A x @ pivot) @ spell A (spell F xs),
      (pivot @ spell A (F x)) @ spell A (spell F xs))\<in>(srs_step R)^*"
    using rtrancl_srs_step_ctxtI[OF transport[OF xi], of "[]" "spell A (spell F xs)"] by simp
  have weak: "(spell A (x#xs) @ pivot,pivot @ spell A (spell F (x#xs)))\<in>(srs_step R)^*"
    using first last by (simp only: spell_simps append_assoc; meson rtrancl_trans)
  have strict: "set (x#xs)\<inter>B\<noteq>{} \<Longrightarrow>
      (spell A (x#xs) @ pivot,pivot @ spell A (spell F (x#xs)))\<in>(srs_step R)^+"
  proof -
    assume active: "set (x#xs)\<inter>B\<noteq>{}"
    show ?thesis
    proof (cases "x\<in>B")
      case True
      have last': "((A x @ pivot) @ spell A (spell F xs),
          (pivot @ spell A (F x)) @ spell A (spell F xs))\<in>(srs_step R)^+"
        using trancl_srs_step_ctxtI[OF positive[OF True], of "[]" "spell A (spell F xs)"] by simp
      show ?thesis using first last'
        by (simp only: spell_simps append_assoc; meson rtrancl_trancl_trancl)
    next
      case False
      with active have "set xs\<inter>B\<noteq>{}" by auto
      with Cons.hyps[OF tail] have ih': "(spell A xs @ pivot,pivot @ spell A (spell F xs))\<in>(srs_step R)^+" by blast
      have first': "(A x @ (spell A xs @ pivot),A x @ (pivot @ spell A (spell F xs)))\<in>(srs_step R)^+"
        using trancl_srs_step_ctxtI[OF ih', of "A x" "[]"] by simp
      show ?thesis using first' last
        by (simp only: spell_simps append_assoc; meson trancl_rtrancl_trancl)
    qed
  qed
  show ?case using weak strict by blast
qed

lemma image_invariant:
  assumes "set xs\<subseteq>I" "set xs\<inter>B\<noteq>{}"
  shows "set (spell F xs)\<subseteq>I \<and> set (spell F xs)\<inter>B\<noteq>{}"
  using assms closed marked unfolding spell_def by (auto; blast)

theorem nontermination:
  assumes "B\<noteq>{}"
  shows "\<not> SN (cycle_step R)"
proof -
  obtain b where b: "b\<in>B" using assms by blast
  let ?xs = "\<lambda>n. ((spell F)^^n) [b]"
  have invariant: "set (?xs n)\<subseteq>I \<and> set (?xs n)\<inter>B\<noteq>{}" for n
  proof (induct n)
    case 0 then show ?case using b subset by auto
  next
    case (Suc n)
    then show ?case using image_invariant[of "?xs n"] by (simp add: funpow_Suc_right)
  qed
  let ?t = "\<lambda>n. spell A (?xs n) @ pivot"
  have "\<not> SN ((cycle_step R)^+)"
  proof (rule steps_imp_not_SN[of ?t Suc])
    fix n
    have step: "(spell A (?xs n) @ pivot,pivot @ spell A (spell F (?xs n)))\<in>(srs_step R)^+"
      using sweep[of "?xs n"] invariant[of n] by blast
    have "(?t n,spell A (spell F (?xs n)) @ pivot)\<in>(cycle_step R)^+"
      by (rule ordinary_steps_rotate[OF step])
    then show "(?t n,?t (Suc n))\<in>(cycle_step R)^+" by (simp add: funpow_Suc_right)
  qed
  then show ?thesis using SN_imp_SN_trancl by blast
qed

end

definition check_cycle_morphism :: "('a list \<times> 'a list) list \<Rightarrow> 'a list \<Rightarrow>
  'a list list \<Rightarrow> nat list list \<Rightarrow> (nat\<times>nat) list list \<Rightarrow> nat list \<Rightarrow> bool" where
  "check_cycle_morphism R pivot A F T B =
    (length F = length A \<and> length T = length A \<and> B\<noteq>[] \<and>
     list_all (\<lambda>i. i<length A) B \<and>
     list_all (\<lambda>i.
       list_all (\<lambda>j. j<length A) (F!i) \<and>
       cycle_trace R (A!i @ pivot) (T!i) = Some (pivot @ spell ((!) A) (F!i)) \<and>
       (i\<in>set B \<longrightarrow> T!i\<noteq>[] \<and> list_ex (\<lambda>j. j\<in>set B) (F!i)))
       [0..<length A])"

theorem check_cycle_morphism_sound:
  assumes check: "check_cycle_morphism R pivot A F T B"
  shows "\<not> SN (cycle_step (set R))"
proof -
  have local: "i<length A \<Longrightarrow>
       set (F!i)\<subseteq>{..<length A} \<and>
       cycle_trace R (A!i @ pivot) (T!i) = Some (pivot @ spell ((!) A) (F!i)) \<and>
       (i\<in>set B \<longrightarrow> T!i\<noteq>[] \<and> set (F!i)\<inter>set B\<noteq>{})" for i
    using check unfolding check_cycle_morphism_def
    by (auto simp: list_all_iff list_ex_iff)
  have subset: "set B\<subseteq>{..<length A}" and nonempty: "set B\<noteq>{}"
    using check by (auto simp: check_cycle_morphism_def list_all_iff)
  interpret M: cycle_morphism "set R" pivot "(!) A" "(!) F" "{..<length A}" "set B"
  proof (unfold_locales)
    fix i assume "i\<in>{..<length A}"
    with local[of i] have "cycle_trace R (A!i @ pivot) (T!i) = Some (pivot @ spell ((!) A) (F!i))" by auto
    then show "(A!i @ pivot,pivot @ spell ((!) A) (F!i))\<in>(srs_step (set R))^*"
      using checked_cycle_trace by blast
  next
    fix i assume bi: "i\<in>set B"
    with subset local[of i] have trace: "cycle_trace R (A!i @ pivot) (T!i) = Some (pivot @ spell ((!) A) (F!i))"
      and strict: "T!i\<noteq>[]" by auto
    show "(A!i @ pivot,pivot @ spell ((!) A) (F!i))\<in>(srs_step (set R))^+"
      using checked_cycle_trace[OF trace] strict by blast
  next
    fix i assume "i\<in>{..<length A}"
    then show "set (F!i)\<subseteq>{..<length A}" using local[of i] by auto
  next
    fix i assume "i\<in>set B"
    then show "set (F!i)\<inter>set B\<noteq>{}" using subset local[of i] by auto
  next
    show "set B\<subseteq>{..<length A}" by (rule subset)
  qed
  show ?thesis by (rule M.nontermination[OF nonempty])
qed

definition mirror_srs :: "'a srs \<Rightarrow> 'a srs" where
  "mirror_srs R = (\<lambda>(l,r). (rev l,rev r)) ` R"

lemma mirror_srs_step:
  assumes "(x,y)\<in>srs_step (mirror_srs R)"
  shows "(rev x,rev y)\<in>srs_step R"
  using assms
proof (induct rule: srs_step.induct)
  case (step l r u v)
  then obtain a b where ab: "(a,b)\<in>R" and lr: "l=rev a" "r=rev b"
    by (auto simp: mirror_srs_def)
  show ?case using srs_step.step[OF ab, of "rev v" "rev u"] by (simp add: lr append_assoc)
qed

lemma mirror_cycle_step:
  assumes "(x,y)\<in>cycle_step (mirror_srs R)"
  shows "(rev x,rev y)\<in>cycle_step R"
proof -
  obtain a b c d where xy: "x=a@b" "y=d@c"
    and step: "(b@a,c@d)\<in>srs_step (mirror_srs R)"
    using assms by (auto simp: cycle_step_def)
  have reversed: "(rev a @ rev b,rev d @ rev c)\<in>srs_step R"
    using mirror_srs_step[OF step] by simp
  show ?thesis unfolding cycle_step_def xy
    by (intro CollectI case_prodI exI[of _ "rev b"] exI[of _ "rev a"]
        exI[of _ "rev d"] exI[of _ "rev c"]) (simp add: reversed)
qed

lemma mirror_cycle_nontermination:
  assumes "\<not> SN (cycle_step (mirror_srs R))"
  shows "\<not> SN (cycle_step R)"
proof -
  obtain f where f: "\<And>n. (f n,f (Suc n))\<in>cycle_step (mirror_srs R)"
    using assms unfolding SN_defs by auto
  have "\<And>n. (rev (f n),rev (f (Suc n)))\<in>cycle_step R"
    using f mirror_cycle_step by blast
  then show ?thesis unfolding SN_defs
    by (intro notI) (erule notE, rule exI[of _ "\<lambda>n. rev (f n)"], auto)
qed

definition check_cycle_morphism_direction where
  "check_cycle_morphism_direction R pivot A F T B mirrored =
    check_cycle_morphism (if mirrored then map (\<lambda>(l,r). (rev l,rev r)) R else R) pivot A F T B"

theorem check_cycle_morphism_direction_sound:
  assumes "check_cycle_morphism_direction R pivot A F T B mirrored"
  shows "\<not> SN (cycle_step (set R))"
  using assms check_cycle_morphism_sound[of "map (\<lambda>(l,r). (rev l,rev r)) R" pivot A F T B]
    check_cycle_morphism_sound[of R pivot A F T B]
    mirror_cycle_nontermination[of "set R"]
  by (cases mirrored) (auto simp: check_cycle_morphism_direction_def mirror_srs_def)

export_code check_cycle_transport check_cycle_embedding check_cycle_morphism_direction cycle_nat
  in Haskell module_name Cycle_Checker

end
