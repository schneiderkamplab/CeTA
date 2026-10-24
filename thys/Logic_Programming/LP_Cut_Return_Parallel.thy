theory LP_Cut_Return_Parallel
  imports LP_Cut_Return_Barriers
begin

lemma lpc_answers_append_all_suffixes:
  assumes sn: "SN_on (lpc_answer_steps P) {ss}"
    and prefix: "lpc_answers_covered P ss C"
    and tails: "\<And>n. lpc_answers_covered P (drop n es) C"
  shows "lpc_answers_covered P (ss@es) C"
proof -
  have all: "lpc_answers_covered P us C \<longrightarrow>
    (\<forall>es. (\<forall>n. lpc_answers_covered P (drop n es) C) \<longrightarrow>
      lpc_answers_covered P (us@es) C)"
    if finite: "SN_on (lpc_answer_steps P) {us}" for us
  proof (rule SN_on_induct[OF finite singletonI], intro impI allI)
    fix us es
    assume ih: "\<And>vs. (us,vs)\<in>lpc_answer_steps P \<Longrightarrow>
      lpc_answers_covered P vs C \<longrightarrow>
      (\<forall>es. (\<forall>n. lpc_answers_covered P (drop n es) C) \<longrightarrow>
        lpc_answers_covered P (vs@es) C)"
      and covered: "lpc_answers_covered P us C"
      and suffix: "\<forall>n. lpc_answers_covered P (drop n es) C"
    show "lpc_answers_covered P (us@es) C"
    proof (cases "us=[]")
      case True then show ?thesis using suffix[rule_format,of 0] by simp
    next
      case False
      show ?thesis
      proof (rule lpc_answers_covered_intro)
        fix event result assume step: "lpc_answer_transition P (us@es) event result"
        obtain vs n where local: "lpc_answer_transition P us event vs"
          and shape: "result=vs@drop n es"
          using lpc_answer_append_suffix[OF False step] by blast
        have edge: "(us,vs)\<in>lpc_answer_steps P" using local by (auto simp: lpc_answer_steps_def)
        have child: "lpc_answers_covered P vs C" by (rule lpc_answers_covered_child[OF covered local])
        have joined: "lpc_answers_covered P (vs@drop n es) C"
          using ih[OF edge] child suffix by (simp add: drop_drop)
        show "(\<forall>rho. event=Some rho \<longrightarrow> C rho) \<and> lpc_answers_covered P result C"
          using lpc_answers_covered_event[OF covered] local joined shape by blast
      qed
    qed
  qed
  show ?thesis using all[OF sn] prefix tails by blast
qed

theorem lpc_return_contract_singletons:
  assumes children: "\<And>e. e\<in>set ss \<Longrightarrow> lpc_return_contract P [e] R t ret"
  shows "lpc_return_contract P ss R t ret"
  using children
proof (induct ss rule: length_induct)
  case (1 ss)
  have sn: "SN_on (lp_cut_mgu_source P) {map fst ss}"
    by (rule lpc_mgu_singleton_stack_SN)
      (use "1.prems" in \<open>auto simp: lpc_return_contract_def\<close>)
  have covered: "lpc_answers_covered P ss (\<lambda>rho. (t,ret rho)\<in>R\<^sup>*)"
  proof (cases ss)
    case Nil show ?thesis unfolding Nil
      by (rule lpc_answers_covered_intro) (auto elim: lpc_answer_transition.cases)
  next
    case (Cons e es)
    have first: "lpc_return_contract P [e] R t ret" using "1.prems" Cons by simp
    have tails: "lpc_return_contract P (drop n es) R t ret" for n
      by (rule "1.hyps"[rule_format]) (use "1.prems" Cons in \<open>auto dest: in_set_dropD\<close>)
    have finite: "SN_on (lpc_answer_steps P) {[e]}"
      using first by (simp add: lpc_return_contract_def lpc_answer_instrumentation_SN)
    have covered_first: "lpc_answers_covered P [e] (\<lambda>rho. (t,ret rho)\<in>R\<^sup>*)"
      using first by (auto simp: lpc_return_contract_def lpc_answers_covered_def)
    have covered_tail: "lpc_answers_covered P (drop n es) (\<lambda>rho. (t,ret rho)\<in>R\<^sup>*)" for n
      using tails[of n] by (auto simp: lpc_return_contract_def lpc_answers_covered_def)
    show ?thesis using lpc_answers_append_all_suffixes[OF finite covered_first covered_tail]
      by (simp add: Cons)
  qed
  show ?case using sn covered by (auto simp: lpc_return_contract_def lpc_answers_covered_def)
qed

end
