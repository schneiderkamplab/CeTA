theory LP_Answer_Graph
  imports LP_SEG_Answer_Contracts
begin

text \<open>Shared graph progress and successful-return coverage, independent
of the source language. LP with cut and its Prolog extension instantiate the
same proof. The representation must cover each complete ordered state and every
success event. Silent cycles require a strictly decreasing natural weight.\<close>

definition lp_answer_steps where
  "lp_answer_steps T = {(s,t). \<exists>event. T s event t}"

definition lp_answer_graph_valid where
  "lp_answer_graph_valid T R rep ret weight =
    (\<forall>ss t event tt. rep ss t \<longrightarrow> T ss event tt \<longrightarrow>
       ((\<exists>u. (t,u)\<in>R\<^sup>+ \<and> rep tt u) \<or>
        (rep tt t \<and> weight tt < (weight ss::nat))) \<and>
       (\<forall>\<eta>. event=Some \<eta> \<longrightarrow> (t,ret \<eta>)\<in>R\<^sup>*))"

lemma lp_answer_graph_SN:
  assumes valid: "lp_answer_graph_valid T R rep ret weight"
    and sn: "SN_on R {t}"
    and represented: "rep ss t"
  shows "SN_on (lp_answer_steps T) {ss}"
proof -
  have all: "\<forall>ss. rep ss t \<longrightarrow> SN_on (lp_answer_steps T) {ss}"
  proof (rule SN_on_induct[OF SN_on_trancl[OF sn] singletonI])
    fix t
    assume outer: "\<And>u. (t,u)\<in>R\<^sup>+ \<Longrightarrow>
      \<forall>ss. rep ss u \<longrightarrow> SN_on (lp_answer_steps T) {ss}"
    have local: "\<forall>ss. weight ss=k \<longrightarrow> rep ss t \<longrightarrow>
      SN_on (lp_answer_steps T) {ss}" for k
    proof (induct k rule: less_induct)
      case (less k)
      show ?case
      proof (intro allI impI)
        fix ss assume w: "weight ss=k" and rep: "rep ss t"
        show "SN_on (lp_answer_steps T) {ss}"
        proof (rule step_reflects_SN_on)
          fix tt assume step: "(ss,tt)\<in>lp_answer_steps T"
          obtain event where event: "T ss event tt"
            using step by (auto simp: lp_answer_steps_def)
          have covered: "(\<exists>u. (t,u)\<in>R\<^sup>+ \<and> rep tt u) \<or>
            (rep tt t \<and> weight tt < weight ss)"
            using valid rep event unfolding lp_answer_graph_valid_def by blast
          show "SN_on (lp_answer_steps T) {tt}"
            using covered outer less.hyps w by blast
        qed
      qed
    qed
    show "\<forall>ss. rep ss t \<longrightarrow> SN_on (lp_answer_steps T) {ss}"
      using local by blast
  qed
  show ?thesis using all represented by blast
qed

lemma lp_answer_graph_path:
  assumes valid: "lp_answer_graph_valid T R rep ret weight"
    and path: "(ss,tt)\<in>(lp_answer_steps T)\<^sup>*"
    and represented: "rep ss t"
  shows "\<exists>u. (t,u)\<in>R\<^sup>* \<and> rep tt u"
  using path represented
proof (induct rule: rtrancl_induct)
  case base then show ?case by blast
next
  case (step us vs)
  obtain u where before: "(t,u)\<in>R\<^sup>*" and rep: "rep us u"
    using step.hyps(3)[OF step.prems] by blast
  obtain event where event: "T us event vs"
    using step.hyps(2) by (auto simp: lp_answer_steps_def)
  have covered: "(\<exists>v. (u,v)\<in>R\<^sup>+ \<and> rep vs v) \<or>
    (rep vs u \<and> weight vs < weight us)"
    using valid rep event unfolding lp_answer_graph_valid_def by blast
  have successor: "\<exists>v. (u,v)\<in>R\<^sup>* \<and> rep vs v"
  proof (cases "\<exists>v. (u,v)\<in>R\<^sup>+ \<and> rep vs v")
    case True
    then obtain v where uv: "(u,v)\<in>R\<^sup>+" and rv: "rep vs v" by blast
    have "(u,v)\<in>R\<^sup>*" by (rule trancl_into_rtrancl[OF uv])
    then show ?thesis using rv by blast
  next
    case False
    then have "rep vs u" using covered by blast
    then show ?thesis by blast
  qed
  obtain v where uv: "(u,v)\<in>R\<^sup>*" and repv: "rep vs v"
    using successor by blast
  have tv: "(t,v)\<in>R\<^sup>*" by (rule rtrancl_trans[OF before uv])
  show ?case using tv repv by blast
qed

end
