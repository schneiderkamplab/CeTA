theory Sparse_Tiling_Termination
  imports Sparse_Tiling_Coverage
begin

text \<open>The well-founded suffix/rewrite order used to extend local RFC
termination to arbitrary strings.\<close>

definition sparse_suffix where
  "sparse_suffix = {(s,t). \<exists>u. u \<noteq> [] \<and> s = u @ t}"

lemma sparse_suffix_SN:
  assumes sn: "SN_on (sparse_word_step R) {u @ v}"
  shows "SN_on (sparse_word_step R) {v}"
proof (rule SN_onI)
  fix f
  assume start: "f 0 \<in> {v}" and steps: "chain (sparse_word_step R) f"
  have lifted: "chain (sparse_word_step R) (\<lambda>i. u @ f i)"
    using sparse_word_step_context[of _ _ R u "[]"] steps by auto
  have "\<not> SN_on (sparse_word_step R) {u @ f 0}"
    by (rule chain_imp_not_SN_on[OF lifted])
  then show False using sn start by simp
qed

lemma sparse_suffix_terminates: "SN (sparse_suffix :: ('a list \<times> 'a list) set)"
  unfolding SN_iff_wf
proof (rule wf_subset[OF wf_measure[of length]])
  show "sparse_suffix\<inverse> \<subseteq> measure length"
    unfolding sparse_suffix_def by auto
qed

definition sparse_suffix_order where
  "sparse_suffix_order R = restrict_SN (sparse_word_step R) (sparse_word_step R) \<union>
    restrict_SN sparse_suffix (sparse_word_step R)"

lemma sparse_suffix_order_terminates: "SN (sparse_suffix_order R)"
proof -
  let ?r = "restrict_SN (sparse_word_step R) (sparse_word_step R)"
  let ?s = "restrict_SN sparse_suffix (sparse_word_step R)"
  have r: "SN ?r" by simp
  have s: "SN ?s"
    by (rule SN_on_subset1[OF sparse_suffix_terminates]) (auto simp: restrict_SN_def)
  have commute: "quasi_commute ?r ?s"
    unfolding quasi_commute_def
  proof
    fix pair
    assume "pair \<in> ?s O ?r"
    then obtain x y z where pair: "pair = (x,z)" and suffix: "(x,y) \<in> sparse_suffix"
      and step: "(y,z) \<in> sparse_word_step R" and sn: "SN_on (sparse_word_step R) {x}"
      unfolding restrict_SN_def by auto
    obtain u where nonempty: "u \<noteq> []" and x: "x = u @ y"
      using suffix unfolding sparse_suffix_def by blast
    have lifted: "(x,u @ z) \<in> sparse_word_step R"
      using sparse_word_step_context[OF step, of u "[]"] by (simp add: x)
    have middle_sn: "SN_on (sparse_word_step R) {u @ z}"
      by (rule step_preserves_SN_on[OF lifted sn])
    have first: "(x,u @ z) \<in> ?r" using lifted sn unfolding restrict_SN_def by blast
    have second: "(u @ z,z) \<in> ?s"
      using nonempty middle_sn unfolding restrict_SN_def sparse_suffix_def by blast
    have tail: "(u @ z,z) \<in> (?r \<union> ?s)\<^sup>*"
      using second by auto
    show "pair \<in> ?r O (?r \<union> ?s)\<^sup>*" using pair first tail by auto
  qed
  show ?thesis unfolding sparse_suffix_order_def by (rule quasi_commute_imp_SN[OF r s commute])
qed

lemma sparse_step_append_cases:
  assumes step: "(u @ v,t) \<in> sparse_word_step R"
  obtains (left) u' where "(u,u') \<in> sparse_word_step R" "t = u' @ v"
    | (right) v' where "(v,v') \<in> sparse_word_step R" "t = u @ v'"
    | (cross) x a b y r where "u = x @ a" "v = b @ y" "a \<noteq> []" "b \<noteq> []"
        "(a @ b,r) \<in> R" "t = x @ r @ y"
proof -
  obtain x y l r where rule: "(l,r) \<in> R" and source: "u @ v = x @ (l @ y)"
    and target: "t = x @ r @ y" using step unfolding sparse_word_step_def by blast
  obtain a where cases: "u = x @ a \<and> a @ v = l @ y \<or> u @ a = x \<and> v = a @ (l @ y)"
    using source append_eq_append_conv2 by blast
  then show thesis
  proof
    assume before: "u = x @ a \<and> a @ v = l @ y"
    obtain b where split: "a = l @ b \<and> b @ v = y \<or> a @ b = l \<and> v = b @ y"
      using before append_eq_append_conv2 by blast
    then show thesis
    proof
      assume inside: "a = l @ b \<and> b @ v = y"
      have rewrite: "(u,x @ r @ b) \<in> sparse_word_step R"
        using sparse_word_stepI[OF rule, of x b] before inside by simp
      have result: "t = (x @ r @ b) @ v" using target inside by (simp add: append_assoc)
      show thesis by (rule left[OF rewrite result])
    next
      assume overlap: "a @ b = l \<and> v = b @ y"
      show thesis
      proof (cases "a = []")
        case True
        have rewrite: "(v,r @ y) \<in> sparse_word_step R"
          using sparse_word_stepI[OF rule, of "[]" y] overlap True by simp
        have result: "t = u @ (r @ y)" using before target True by simp
        show thesis by (rule right[OF rewrite result])
      next
        case False
        show thesis
        proof (cases "b = []")
          case True
          have rewrite: "(u,x @ r) \<in> sparse_word_step R"
            using sparse_word_stepI[OF rule, of x "[]"] before overlap True by simp
          have result: "t = (x @ r) @ v" using target overlap True by (simp add: append_assoc)
          show thesis by (rule left[OF rewrite result])
        next
          case b: False
          show thesis using cross before overlap False b rule target by blast
        qed
      qed
    qed
  next
    assume after: "u @ a = x \<and> v = a @ (l @ y)"
    have rewrite: "(v,a @ r @ y) \<in> sparse_word_step R"
      using sparse_word_stepI[OF rule, of a y] after by simp
    have result: "t = u @ (a @ r @ y)" using target after by (simp add: append_assoc)
    show thesis by (rule right[OF rewrite result])
  qed
qed

lemma sparse_rfc_append_SN:
  assumes local: "SN_on (sparse_word_step R) (sparse_rfc R)"
    and member: "u \<in> sparse_rfc R" and suffix: "SN_on (sparse_word_step R) {v}"
  shows "SN_on (sparse_word_step R) {u @ v}"
proof -
  let ?R = "sparse_word_step R"
  have extension: "SN_on ?R {v} \<longrightarrow> (\<forall>u\<in>sparse_rfc R. SN_on ?R {u @ v})" for v
  proof (rule SN_induct[OF sparse_suffix_order_terminates])
    fix v
    assume outer: "\<And>w. (v,w) \<in> sparse_suffix_order R \<Longrightarrow>
      SN_on ?R {w} \<longrightarrow> (\<forall>u\<in>sparse_rfc R. SN_on ?R {u @ w})"
    show "SN_on ?R {v} \<longrightarrow> (\<forall>u\<in>sparse_rfc R. SN_on ?R {u @ v})"
    proof (intro impI ballI)
      fix u
      assume sn: "SN_on ?R {v}" and member: "u \<in> sparse_rfc R"
      have claim: "u \<in> sparse_rfc R \<longrightarrow> SN_on ?R {u @ v}"
      proof (rule SN_on_induct[OF local member])
        fix u
        assume inner: "\<And>w. (u,w) \<in> ?R \<Longrightarrow> w \<in> sparse_rfc R \<longrightarrow> SN_on ?R {w @ v}"
        show "u \<in> sparse_rfc R \<longrightarrow> SN_on ?R {u @ v}"
        proof
          assume member: "u \<in> sparse_rfc R"
          show "SN_on ?R {u @ v}"
          proof (rule step_reflects_SN_on)
            fix t
            assume step: "(u @ v,t) \<in> ?R"
            show "SN_on ?R {t}"
            proof (rule sparse_step_append_cases[OF step])
              fix w
              assume left: "(u,w) \<in> ?R" "t = w @ v"
              have "w \<in> sparse_rfc R" by (rule sparse_rfc.sparse_rewrite[OF member left(1)])
              then show ?thesis using inner[OF left(1)] left(2) by simp
            next
              fix w
              assume right: "(v,w) \<in> ?R" "t = u @ w"
              have smaller: "(v,w) \<in> sparse_suffix_order R"
                using right(1) sn unfolding sparse_suffix_order_def restrict_SN_def by blast
              have "SN_on ?R {w}" by (rule step_preserves_SN_on[OF right(1) sn])
              then show ?thesis using outer[OF smaller] member right(2) by blast
            next
              fix x a b y r
              assume cross: "u = x @ a" "v = b @ y" "a \<noteq> []" "b \<noteq> []" "(a @ b,r) \<in> R" "t = x @ r @ y"
              have prefix: "x @ r \<in> sparse_rfc R"
                using sparse_rfc.overlap[of x a R b r] member cross by blast
              have smaller: "(v,y) \<in> sparse_suffix_order R"
                using cross(2,4) sn unfolding sparse_suffix_order_def restrict_SN_def sparse_suffix_def by blast
              have "SN_on ?R {y}" using sparse_suffix_SN[of R b y] sn cross(2) by simp
              then have "SN_on ?R {(x @ r) @ y}" using outer[OF smaller] prefix by blast
              then show ?thesis by (simp add: cross(6) append_assoc)
            qed
          qed
        qed
      qed
      show "SN_on ?R {u @ v}" using claim member by blast
    qed
  qed
  show ?thesis using extension suffix member by blast
qed

lemma sparse_rfc_prepend_SN:
  assumes local: "SN_on (sparse_word_step R) (sparse_rfc R)"
    and proper: "\<And>l r. (l,r) \<in> R \<Longrightarrow> l \<noteq> []"
    and suffix: "SN_on (sparse_word_step R) {v}"
  shows "SN_on (sparse_word_step R) {a # v}"
  using suffix
proof (induction rule: SN_on_induct_acc_style)
  case (IH v)
  show ?case
  proof (rule step_reflects_SN_on)
    fix t
    assume step: "(a # v,t) \<in> sparse_word_step R"
    obtain x y l r where rule: "(l,r) \<in> R" and source: "a # v = x @ l @ y"
      and target: "t = x @ r @ y" using step unfolding sparse_word_step_def by blast
    show "SN_on (sparse_word_step R) {t}"
    proof (cases x)
      case Nil
      obtain b ls where l: "l = b # ls" using proper[OF rule] by (cases l) auto
      have v: "v = ls @ y" using source by (simp add: Nil l)
      have sn: "SN_on (sparse_word_step R) {y}"
        using sparse_suffix_SN[of R ls y] IH.hyps v by simp
      have member: "r \<in> sparse_rfc R" by (rule sparse_rfc.rhs[OF rule])
      have "SN_on (sparse_word_step R) {r @ y}"
        by (rule sparse_rfc_append_SN[OF local member sn])
      then show ?thesis by (simp add: target Nil)
    next
      case (Cons b xs)
      have source': "v = xs @ l @ y" and head: "b = a" using source Cons by auto
      have reduct: "(v,xs @ r @ y) \<in> sparse_word_step R"
        using sparse_word_stepI[OF rule, of xs y] source' by simp
      have "SN_on (sparse_word_step R) {a # (xs @ r @ y)}" by (rule IH.IH[OF reduct])
      then show ?thesis by (simp add: target Cons head)
    qed
  qed
qed

lemma sparse_rfc_termination:
  assumes local: "SN_on (sparse_word_step R) (sparse_rfc R)"
    and proper: "\<And>l r. (l,r) \<in> R \<Longrightarrow> l \<noteq> []"
  shows "SN (sparse_word_step R)"
proof (rule SN_I)
  fix w
  show "SN_on (sparse_word_step R) {w}"
  proof (induction w)
    case Nil
    show ?case by (rule step_reflects_SN_on) (auto simp: sparse_word_step_def dest: proper)
  next
    case (Cons a v)
    show ?case by (rule sparse_rfc_prepend_SN[OF local _ Cons.IH]) (meson proper)
  qed
qed

lemma sparse_check_termination_sound:
  assumes checked: "sparse_check_coverage q z ts rs ss"
    and target: "SN (sparse_word_step (set ss))"
  shows "SN (sparse_word_step (set rs))"
proof (rule sparse_rfc_termination[OF sparse_check_coverage_sound[OF checked target]])
  fix l r
  assume "(l,r) \<in> set rs"
  then show "l \<noteq> []" using checked
    by (auto simp only: sparse_check_coverage_def sparse_check_tiles_def list_all_iff split: prod.splits)
qed

lemma sparse_example_terminates:
  "SN (sparse_word_step (set [([3::nat,3],[2,3]),([2,1],[1,3])]))"
proof (rule sparse_check_termination_sound[OF sparse_coverage_example])
  show "SN (sparse_word_step (set []))" by (simp add: sparse_word_step_def)
qed

end
