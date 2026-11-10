theory LP_Cut_Domain_Return_Contracts
  imports LP_Cut_Domain_Return_Answers
begin

context cut_runtime_domain
begin

text \<open>A cut-aware return contract describes the actual ordered execution,
including saved alternatives and their environments. It does not require the
cut-erased program to terminate. The return encoding may retain both original
inputs and successful outputs. This is an overapproximation of answers, not a
claim that every residual rewrite is an attainable source answer.\<close>

definition precise_return_contract where
  "precise_return_contract P ss R t ret =
    (SN_on (precise_source P) {map fst ss} \<and>
     (\<forall>us event_tail \<eta>. (ss,us)\<in>(precise_answer_steps P)\<^sup>* \<longrightarrow>
       precise_answer_transition P us (Some \<eta>) event_tail \<longrightarrow>
       (t,ret \<eta>)\<in>R\<^sup>*))"

text \<open>Local graph obligations combine progress with successful-return
coverage. Administrative stuttering is permitted only with a decreasing natural
measure. In particular a recursive cycle cannot be erased from the residual.
The representation includes the whole annotated stack, not just its active call.
The relation R can be a TRS rewrite relation or the residual LP relation.\<close>

definition precise_return_graph_valid where
  "precise_return_graph_valid P R rep ret weight =
    (\<forall>ss t event tt. rep ss t \<longrightarrow> precise_answer_transition P ss event tt \<longrightarrow>
       ((\<exists>u. (t,u)\<in>R\<^sup>+ \<and> rep tt u) \<or>
        (rep tt t \<and> weight tt < (weight ss::nat))) \<and>
       (\<forall>\<eta>. event=Some \<eta> \<longrightarrow> (t,ret \<eta>)\<in>R\<^sup>*))"

lemma precise_return_graph_SN:
  assumes valid: "precise_return_graph_valid P R rep ret weight"
    and sn: "SN_on R {t}"
    and represented: "rep ss t"
  shows "SN_on (precise_answer_steps P) {ss}"
proof -
  have all: "\<forall>ss. rep ss t \<longrightarrow> SN_on (precise_answer_steps P) {ss}"
  proof (rule SN_on_induct[OF SN_on_trancl[OF sn] singletonI])
    fix t
    assume outer: "\<And>u. (t,u)\<in>R\<^sup>+ \<Longrightarrow>
      \<forall>ss. rep ss u \<longrightarrow> SN_on (precise_answer_steps P) {ss}"
    have local: "\<forall>ss. weight ss=k \<longrightarrow> rep ss t \<longrightarrow>
      SN_on (precise_answer_steps P) {ss}" for k
    proof (induct k rule: less_induct)
      case (less k)
      show ?case
      proof (intro allI impI)
        fix ss assume w: "weight ss=k" and rep: "rep ss t"
        show "SN_on (precise_answer_steps P) {ss}"
        proof (rule step_reflects_SN_on)
          fix tt assume step: "(ss,tt)\<in>precise_answer_steps P"
          obtain event where event: "precise_answer_transition P ss event tt"
            using step by (auto simp: precise_answer_steps_def)
          have covered: "(\<exists>u. (t,u)\<in>R\<^sup>+ \<and> rep tt u) \<or>
            (rep tt t \<and> weight tt < weight ss)"
            using valid rep event unfolding precise_return_graph_valid_def by blast
          show "SN_on (precise_answer_steps P) {tt}"
            using covered outer less.hyps w by blast
        qed
      qed
    qed
    show "\<forall>ss. rep ss t \<longrightarrow> SN_on (precise_answer_steps P) {ss}"
      using local by blast
  qed
  show ?thesis using all represented by blast
qed

lemma precise_return_graph_path:
  assumes valid: "precise_return_graph_valid P R rep ret weight"
    and path: "(ss,tt)\<in>(precise_answer_steps P)\<^sup>*"
    and represented: "rep ss t"
  shows "\<exists>u. (t,u)\<in>R\<^sup>* \<and> rep tt u"
  using path represented
proof (induct rule: rtrancl_induct)
  case base then show ?case by blast
next
  case (step us vs)
  obtain u where before: "(t,u)\<in>R\<^sup>*" and rep: "rep us u"
    using step.hyps(3)[OF step.prems] by blast
  obtain event where event: "precise_answer_transition P us event vs"
    using step.hyps(2) by (auto simp: precise_answer_steps_def)
  have covered: "(\<exists>v. (u,v)\<in>R\<^sup>+ \<and> rep vs v) \<or>
    (rep vs u \<and> weight vs < weight us)"
    using valid rep event unfolding precise_return_graph_valid_def by blast
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

theorem precise_return_graph_contract:
  assumes valid: "precise_return_graph_valid P R rep ret weight"
    and sn: "SN_on R {t}"
    and represented: "rep ss t"
  shows "precise_return_contract P ss R t ret"
proof -
  have source: "SN_on (precise_source P) {map fst ss}"
    using precise_return_graph_SN[OF valid sn represented]
      precise_answer_instrumentation_SN by blast
  have returns: "(t,ret \<eta>)\<in>R\<^sup>*"
    if path: "(ss,us)\<in>(precise_answer_steps P)\<^sup>*"
      and event: "precise_answer_transition P us (Some \<eta>) tail" for us \<eta> tail
  proof -
    obtain u where before: "(t,u)\<in>R\<^sup>*" and rep: "rep us u"
      using precise_return_graph_path[OF valid path represented] by blast
    have returned: "(u,ret \<eta>)\<in>R\<^sup>*"
      using valid rep event unfolding precise_return_graph_valid_def by blast
    show ?thesis by (rule rtrancl_trans[OF before returned])
  qed
  show ?thesis using source returns unfolding precise_return_contract_def by blast
qed

text \<open>Continuation assumptions may therefore be discharged using the
residual return relation, but only for actual successful source events. This
lemma does not itself assert the still separate sequencing/attachment theorem.\<close>

lemma precise_return_contract_success:
  assumes contract: "precise_return_contract P ss R t ret"
    and path: "(ss,us)\<in>(precise_answer_steps P)\<^sup>*"
    and success: "precise_answer_transition P us (Some \<eta>) tail"
    and continuation: "\<And>\<rho>. (t,ret \<rho>)\<in>R\<^sup>* \<Longrightarrow> C \<rho>"
  shows "C \<eta>"
  using assms unfolding precise_return_contract_def by blast

end
end
