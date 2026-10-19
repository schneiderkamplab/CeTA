theory Higher_Order_Embedding
  imports Higher_Order_Core
begin

text \<open>Typed self-embedding through application contexts. No abstraction
is crossed by the hole, so plugging never changes the binding environment.\<close>

datatype ho_context = HHole | HCLeft ho_context ho_term | HCRight ho_term ho_context

fun ho_fill where
  "ho_fill HHole t = t"
| "ho_fill (HCLeft C x) t = HApp (ho_fill C t) x"
| "ho_fill (HCRight x C) t = HApp x (ho_fill C t)"

lemma ho_fill_type:
  "ho_typeof S V B x = ho_typeof S V B y \<Longrightarrow>
   ho_typeof S V B (ho_fill C x) = ho_typeof S V B (ho_fill C y)"
  by (induction C) (auto split: option.splits ho_type.splits)

lemma ho_fill_step:
  "ho_step S V R B x y \<Longrightarrow> ho_step S V R B (ho_fill C x) (ho_fill C y)"
  by (induction C) (auto intro: ho_step.intros)

lemma ho_fill_relation:
  assumes "ho_typeof S V [] t = Some A" "ho_typeof S V [] (ho_fill C t) = Some A"
    "(x,y) \<in> ho_relation S V R A"
  shows "(ho_fill C x, ho_fill C y) \<in> ho_relation S V R A"
  using assms ho_fill_type[of S V "[]" x t C] ho_fill_type[of S V "[]" y t C]
    ho_fill_step[of S V R "[]" x y C]
  by (auto simp: ho_relation_def)

lemma relation_embedding_not_wf:
  assumes first: "(t,f t) \<in> r^+"
    and mono: "\<And>x y. (x,y) \<in> r \<Longrightarrow> (f x,f y) \<in> r"
  shows "\<not> wf (r\<inverse>)"
proof -
  have lift: "\<And>x y. (x,y) \<in> r^+ \<Longrightarrow> (f x,f y) \<in> r^+"
    by (erule trancl_induct) (auto intro: r_into_trancl trancl_into_trancl mono)
  have chain: "\<And>n. ((f^^n) t,(f^^Suc n) t) \<in> r^+"
  proof -
    fix n
    show "((f^^n) t,(f^^Suc n) t) \<in> r^+"
    proof (induction n)
      case 0
      show ?case using first by simp
    next
      case (Suc n)
      show ?case using lift[OF Suc.IH] by (simp only: funpow.simps(2) o_apply)
    qed
  qed
  show ?thesis
  proof
    assume "wf (r\<inverse>)"
    then have wf: "wf ((r^+)\<inverse>)"
      using wf_trancl[of "r\<inverse>"] by (simp only: trancl_converse)
    let ?B = "range (\<lambda>n. (f^^n) t)"
    have nonempty: "?B \<noteq> {}" by simp
    have minimal: "\<exists>z \<in> ?B. \<forall>y. (y,z) \<in> (r^+)\<inverse> \<longrightarrow> y \<notin> ?B"
      using wf_iff_ex_minimal[THEN iffD1, OF wf, rule_format, OF nonempty] .
    obtain z where z: "z \<in> ?B" "\<And>y. (y,z) \<in> (r^+)\<inverse> \<Longrightarrow> y \<notin> ?B"
      using minimal by blast
    obtain n where n: "z=(f^^n) t" using z(1) by blast
    have "((f^^Suc n) t,z) \<in> (r^+)\<inverse>" using chain[of n] n by simp
    then show False using z(2) by blast
  qed
qed

definition ho_check_embedding where
  "ho_check_embedding S V R A t ps C \<longleftrightarrow>
    ps \<noteq> [] \<and> ho_typeof S V [] t = Some A \<and>
    ho_typeof S V [] (ho_fill C t) = Some A \<and>
    ho_check_path S V R A t ps = Some (ho_fill C t)"

theorem ho_check_embedding_sound:
  assumes "ho_check_embedding S V R A t ps C"
  shows "\<not> wf ((ho_relation S V R A)\<inverse>)"
proof -
  obtain p qs where ps: "ps=p#qs"
    using assms unfolding ho_check_embedding_def by (cases ps) auto
  obtain u where step: "ho_check_step S V R [] t p = Some u"
    and types: "ho_typeof S V [] t = Some A" "ho_typeof S V [] u = Some A"
    and path: "ho_check_path S V R A u qs = Some (ho_fill C t)"
    using assms unfolding ho_check_embedding_def ps by (auto split: option.splits if_splits)
  have first: "(t,u) \<in> ho_relation S V R A"
    using ho_check_step_sound[OF step] types unfolding ho_relation_def by simp
  have rest: "(u,ho_fill C t) \<in> (ho_relation S V R A)^*"
    by (rule ho_check_path_sound[OF path])
  have chain: "(t,ho_fill C t) \<in> (ho_relation S V R A)^+"
    using first rest by (rule rtrancl_into_trancl2)
  show ?thesis
    by (rule relation_embedding_not_wf[where f="ho_fill C" and t=t, OF chain])
       (use assms in \<open>auto simp: ho_check_embedding_def intro: ho_fill_relation\<close>)
qed

end
