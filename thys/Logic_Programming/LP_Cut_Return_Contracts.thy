theory LP_Cut_Return_Contracts
  imports LP_Cut_Answers LP_Answer_Graph
begin

text \<open>A cut-aware return contract describes the actual ordered execution,
including saved alternatives and their environments. It does not require the
cut-erased program to terminate. The return encoding may retain both original
inputs and successful outputs. This is an overapproximation of answers, not a
claim that every residual rewrite is an attainable source answer.\<close>

definition lpc_return_contract where
  "lpc_return_contract P ss R t ret =
    (SN_on (lp_cut_mgu_source P) {map fst ss} \<and>
     (\<forall>us event_tail \<eta>. (ss,us)\<in>(lpc_answer_steps P)\<^sup>* \<longrightarrow>
       lpc_answer_transition P us (Some \<eta>) event_tail \<longrightarrow>
       (t,ret \<eta>)\<in>R\<^sup>*))"

text \<open>Local graph obligations combine progress with successful-return
coverage. Administrative stuttering is permitted only with a decreasing natural
measure. In particular a recursive cycle cannot be erased from the residual.
The representation includes the whole annotated stack, not just its active call.
The relation R can be a TRS rewrite relation or the residual LP relation.\<close>

definition lpc_return_graph_valid where
  "lpc_return_graph_valid P R rep ret weight =
    (\<forall>ss t event tt. rep ss t \<longrightarrow> lpc_answer_transition P ss event tt \<longrightarrow>
       ((\<exists>u. (t,u)\<in>R\<^sup>+ \<and> rep tt u) \<or>
        (rep tt t \<and> weight tt < (weight ss::nat))) \<and>
       (\<forall>\<eta>. event=Some \<eta> \<longrightarrow> (t,ret \<eta>)\<in>R\<^sup>*))"

lemma lpc_return_graph_SN:
  assumes valid: "lpc_return_graph_valid P R rep ret weight"
    and sn: "SN_on R {t}"
    and represented: "rep ss t"
  shows "SN_on (lpc_answer_steps P) {ss}"
  using lp_answer_graph_SN[of "lpc_answer_transition P" R rep ret weight t ss]
  assms by (simp add: lp_answer_graph_valid_def lpc_return_graph_valid_def
    lp_answer_steps_def lpc_answer_steps_def)

lemma lpc_return_graph_path:
  assumes valid: "lpc_return_graph_valid P R rep ret weight"
    and path: "(ss,tt)\<in>(lpc_answer_steps P)\<^sup>*"
    and represented: "rep ss t"
  shows "\<exists>u. (t,u)\<in>R\<^sup>* \<and> rep tt u"
  using lp_answer_graph_path[of "lpc_answer_transition P" R rep ret weight ss tt t]
  assms by (simp add: lp_answer_graph_valid_def lpc_return_graph_valid_def
    lp_answer_steps_def lpc_answer_steps_def)

theorem lpc_return_graph_contract:
  assumes valid: "lpc_return_graph_valid P R rep ret weight"
    and sn: "SN_on R {t}"
    and represented: "rep ss t"
  shows "lpc_return_contract P ss R t ret"
proof -
  have source: "SN_on (lp_cut_mgu_source P) {map fst ss}"
    using lpc_return_graph_SN[OF valid sn represented]
      lpc_answer_instrumentation_SN by blast
  have returns: "(t,ret \<eta>)\<in>R\<^sup>*"
    if path: "(ss,us)\<in>(lpc_answer_steps P)\<^sup>*"
      and event: "lpc_answer_transition P us (Some \<eta>) tail" for us \<eta> tail
  proof -
    obtain u where before: "(t,u)\<in>R\<^sup>*" and rep: "rep us u"
      using lpc_return_graph_path[OF valid path represented] by blast
    have returned: "(u,ret \<eta>)\<in>R\<^sup>*"
      using valid rep event unfolding lpc_return_graph_valid_def by blast
    show ?thesis by (rule rtrancl_trans[OF before returned])
  qed
  show ?thesis using source returns unfolding lpc_return_contract_def by blast
qed

text \<open>Continuation assumptions may therefore be discharged using the
residual return relation, but only for actual successful source events. This
lemma does not itself assert the still separate sequencing/attachment theorem.\<close>

lemma lpc_return_contract_success:
  assumes contract: "lpc_return_contract P ss R t ret"
    and path: "(ss,us)\<in>(lpc_answer_steps P)\<^sup>*"
    and success: "lpc_answer_transition P us (Some \<eta>) tail"
    and continuation: "\<And>\<rho>. (t,ret \<rho>)\<in>R\<^sup>* \<Longrightarrow> C \<rho>"
  shows "C \<eta>"
  using assms unfolding lpc_return_contract_def by blast

end
