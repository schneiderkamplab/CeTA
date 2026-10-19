theory Cycle_Transport
  imports Not_SN.Nonloop_SRS
begin

text \<open>Cycle rewriting is ordinary string rewriting modulo rotation on
both sides. Every step contains one genuine rule application; rotation alone
never counts as progress. This representation has exactly the same infinite
derivations as rewriting equivalence classes of words under rotation.\<close>

definition cycle_step :: "'a srs \<Rightarrow> 'a srs" where
  "cycle_step R = {(x,y). \<exists>a b c d.
    x = a @ b \<and> (b @ a,c @ d) \<in> srs_step R \<and> y = d @ c}"

lemma ordinary_cycle_step:
  "(x,y) \<in> srs_step R \<Longrightarrow> (x,y) \<in> cycle_step R"
  unfolding cycle_step_def
  by (intro CollectI case_prodI exI[of _ "[]"] exI[of _ x]
      exI[of _ "[]"] exI[of _ y]) simp

lemma ordinary_cycle_steps:
  "(x,y) \<in> (srs_step R)^+ \<Longrightarrow> (x,y) \<in> (cycle_step R)^+"
  by (rule trancl_mono) (auto intro: ordinary_cycle_step)

lemma ordinary_steps_rotate:
  assumes "(x,c @ d) \<in> (srs_step R)^+"
  shows "(x,d @ c) \<in> (cycle_step R)^+"
proof -
  obtain y where xy: "(x,y) \<in> (srs_step R)^*"
    and yz: "(y,c @ d) \<in> srs_step R"
    using assms by (meson tranclD2)
  have first: "(x,y) \<in> (cycle_step R)^*"
    using xy by (induct rule: rtrancl_induct)
      (auto intro: rtrancl_into_rtrancl ordinary_cycle_step)
  have last: "(y,d @ c) \<in> cycle_step R"
    unfolding cycle_step_def
    by (intro CollectI case_prodI exI[of _ "[]"] exI[of _ y]
        exI[of _ c] exI[of _ d]) (simp add: yz)
  show ?thesis using first last by (meson rtrancl_into_trancl1)
qed

fun word_power :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list" where
  "word_power u 0 = []"
| "word_power u (Suc n) = u @ word_power u n"

lemma word_power_add:
  "word_power u (m+n) = word_power u m @ word_power u n"
  by (induct m) auto

text \<open>The criterion is generic in both words and both exponents.
It is not ordinary self-embedding: the rotation is essential.\<close>

theorem cycle_transport_nontermination:
  assumes deriv: "(word_power u p @ v, v @ word_power u s) \<in> (srs_step R)^+"
    and growth: "p \<le> s"
  shows "\<not> SN (cycle_step R)"
proof -
  let ?t = "\<lambda>n. word_power u (p+n) @ v"
  have infinite: "\<not> SN ((cycle_step R)^+)"
  proof (rule steps_imp_not_SN[of ?t "\<lambda>n. n+(s-p)"])
    fix n
    have d: "(word_power u n @ (word_power u p @ v),
       word_power u n @ (v @ word_power u s)) \<in> (srs_step R)^+"
      using trancl_srs_step_ctxtI[OF deriv, of "word_power u n" "[]"] by simp
    have rotated: "(word_power u n @ word_power u p @ v,
        word_power u s @ word_power u n @ v) \<in> (cycle_step R)^+"
      by (rule ordinary_steps_rotate)
        (use d in \<open>simp add: append_assoc\<close>)
    show "(?t n, ?t (n+(s-p))) \<in> (cycle_step R)^+"
      using rotated growth by (simp add: append_assoc[symmetric]
        word_power_add[symmetric] add.commute add.left_commute)
  qed
  then show ?thesis using SN_imp_SN_trancl by blast
qed

theorem cycle_transport_right_nontermination:
  assumes deriv: "(v @ word_power u p, word_power u s @ v) \<in> (srs_step R)^+"
    and growth: "p \<le> s"
  shows "\<not> SN (cycle_step R)"
proof -
  let ?t = "\<lambda>n. v @ word_power u (p+n)"
  have infinite: "\<not> SN ((cycle_step R)^+)"
  proof (rule steps_imp_not_SN[of ?t "\<lambda>n. n+(s-p)"])
    fix n
    have d: "((v @ word_power u p) @ word_power u n,
       (word_power u s @ v) @ word_power u n) \<in> (srs_step R)^+"
      using trancl_srs_step_ctxtI[OF deriv, of "[]" "word_power u n"] by simp
    have rotated: "(v @ word_power u p @ word_power u n,
        (v @ word_power u n) @ word_power u s) \<in> (cycle_step R)^+"
      by (rule ordinary_steps_rotate)
        (use d in \<open>simp add: append_assoc\<close>)
    show "(?t n, ?t (n+(s-p))) \<in> (cycle_step R)^+"
      using rotated growth by (simp add: append_assoc word_power_add[symmetric] add.commute add.left_commute)
  qed
  then show ?thesis using SN_imp_SN_trancl by blast
qed

fun cycle_trace :: "('a list \<times> 'a list) list \<Rightarrow> 'a list \<Rightarrow>
    (nat \<times> nat) list \<Rightarrow> 'a list option" where
  "cycle_trace R w [] = Some w"
| "cycle_trace R w ((i,k)#ss) =
    (if i < length R then
      (let (l,r) = R!i in
        if k + length l \<le> length w \<and> take (length l) (drop k w) = l
        then cycle_trace R (take k w @ r @ drop (k+length l) w) ss
        else None)
     else None)"

lemma checked_cycle_trace:
  assumes "cycle_trace R w ss = Some z"
  shows "(w,z) \<in> (srs_step (set R))^* \<and>
    (ss \<noteq> [] \<longrightarrow> (w,z) \<in> (srs_step (set R))^+)"
  using assms
proof (induct ss arbitrary: w)
  case Nil
  then show ?case by auto
next
  case (Cons st ss)
  obtain i k where st: "st=(i,k)" by (cases st) auto
  obtain l r where rule: "R!i=(l,r)" by (cases "R!i") auto
  from Cons.prems have index: "i < length R"
    and bound: "k+length l \<le> length w"
    and matches: "take (length l) (drop k w)=l"
    and rest: "cycle_trace R (take k w @ r @ drop (k+length l) w) ss = Some z"
    by (auto simp: st rule Let_def split: if_splits)
  have original: "w = take k w @ l @ drop (k+length l) w"
  proof -
    have "take k w @ take (length l) (drop k w) @ drop (length l) (drop k w) = w"
      by (simp only: append_take_drop_id)
    then show ?thesis using matches by (simp add: drop_drop add.commute)
  qed
  have member: "(l,r) \<in> set R" using index rule by (metis nth_mem)
  have step: "(w, take k w @ r @ drop (k+length l) w) \<in> srs_step (set R)"
    using srs_step.step[OF member, of "take k w" "drop (k+length l) w"] original by simp
  have tail: "(take k w @ r @ drop (k+length l) w,z) \<in> (srs_step (set R))^*"
    using Cons.hyps[OF rest] by blast
  have full: "(w,z) \<in> (srs_step (set R))^+"
    using step tail by (meson rtrancl_into_trancl2)
  then show ?case by auto
qed

definition check_cycle_transport :: "('a list \<times> 'a list) list \<Rightarrow>
  'a list \<Rightarrow> (nat \<times> nat) list \<Rightarrow>
  'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
  'a list \<Rightarrow> bool \<Rightarrow> bool" where
  "check_cycle_transport R w ss u v p s ext right =
    (ss \<noteq> [] \<and> u \<noteq> [] \<and> v \<noteq> [] \<and> 0<p \<and> p\<le>s \<and>
      (case cycle_trace R w ss of None \<Rightarrow> False | Some z \<Rightarrow>
        if right then ext @ w = v @ word_power u p \<and>
                       ext @ z = word_power u s @ v
        else w @ ext = word_power u p @ v \<and>
             z @ ext = v @ word_power u s))"

theorem check_cycle_transport_sound:
  assumes "check_cycle_transport R w ss u v p s ext right"
  shows "\<not> SN (cycle_step (set R))"
proof -
  from assms obtain z where trace: "cycle_trace R w ss = Some z"
    and nonempty: "ss \<noteq> []" and growth: "p\<le>s"
    and ends: "if right then ext @ w = v @ word_power u p \<and> ext @ z = word_power u s @ v
      else w @ ext = word_power u p @ v \<and> z @ ext = v @ word_power u s"
    by (auto simp: check_cycle_transport_def split: option.splits if_splits)
  have d: "(w,z) \<in> (srs_step (set R))^+" using checked_cycle_trace[OF trace] nonempty by blast
  show ?thesis
  proof (cases right)
    case True
    have "(ext @ w,ext @ z) \<in> (srs_step (set R))^+"
      using trancl_srs_step_ctxtI[OF d, of ext "[]"] by simp
    then have "(v @ word_power u p,word_power u s @ v) \<in> (srs_step (set R))^+"
      using ends True by simp
    then show ?thesis by (rule cycle_transport_right_nontermination[OF _ growth])
  next
    case False
    have "(w @ ext,z @ ext) \<in> (srs_step (set R))^+"
      using trancl_srs_step_ctxtI[OF d, of "[]" ext] by simp
    then have "(word_power u p @ v,v @ word_power u s) \<in> (srs_step (set R))^+"
      using ends False by simp
    then show ?thesis by (rule cycle_transport_nontermination[OF _ growth])
  qed
qed

definition cycle_nat :: "integer \<Rightarrow> nat" where
  "cycle_nat = nat_of_integer"

definition check_cycle_embedding :: "('a list \<times> 'a list) list \<Rightarrow>
  'a list \<Rightarrow> (nat \<times> nat) list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "check_cycle_embedding R w ss l r =
    (ss \<noteq> [] \<and> cycle_trace R w ss = Some (l @ w @ r))"

lemma word_power_snoc:
  "word_power u (Suc n) = word_power u n @ u"
  by (induct n) auto

theorem check_cycle_embedding_sound:
  assumes "check_cycle_embedding R w ss l r"
  shows "\<not> SN (cycle_step (set R))"
proof -
  have d: "(w,l @ w @ r) \<in> (srs_step (set R))^+"
    using checked_cycle_trace assms unfolding check_cycle_embedding_def by blast
  let ?t = "\<lambda>n. word_power l n @ w @ word_power r n"
  have infinite: "\<not> SN ((cycle_step (set R))^+)"
  proof (rule steps_imp_not_SN[of ?t Suc])
    fix n
    have "(?t n,word_power l n @ (l @ w @ r) @ word_power r n) \<in> (srs_step (set R))^+"
      by (rule trancl_srs_step_ctxtI[OF d])
    then have "(?t n,?t (Suc n)) \<in> (srs_step (set R))^+"
      by (simp only: word_power_snoc[of l] word_power.simps(2)[of r] append_assoc)
    then show "(?t n,?t (Suc n)) \<in> (cycle_step (set R))^+" by (rule ordinary_cycle_steps)
  qed
  then show ?thesis using SN_imp_SN_trancl by blast
qed

export_code check_cycle_transport check_cycle_embedding cycle_nat in Haskell module_name Cycle_Checker

end
