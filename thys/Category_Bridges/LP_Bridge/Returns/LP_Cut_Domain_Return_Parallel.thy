theory LP_Cut_Domain_Return_Parallel
  imports LP_Cut_Domain_Return_Barriers
begin

context cut_runtime_domain
begin

lemma precise_answers_append_all_suffixes:
  assumes sn: "SN_on (precise_answer_steps P) {ss}"
    and prefix: "precise_answers_covered P ss C"
    and tails: "\<And>n. precise_answers_covered P (drop n es) C"
  shows "precise_answers_covered P (ss@es) C"
proof -
  have all: "precise_answers_covered P us C \<longrightarrow>
    (\<forall>es. (\<forall>n. precise_answers_covered P (drop n es) C) \<longrightarrow>
      precise_answers_covered P (us@es) C)"
    if finite: "SN_on (precise_answer_steps P) {us}" for us
  proof (rule SN_on_induct[OF finite singletonI], intro impI allI)
    fix us es
    assume ih: "\<And>vs. (us,vs)\<in>precise_answer_steps P \<Longrightarrow>
      precise_answers_covered P vs C \<longrightarrow>
      (\<forall>es. (\<forall>n. precise_answers_covered P (drop n es) C) \<longrightarrow>
        precise_answers_covered P (vs@es) C)"
      and covered: "precise_answers_covered P us C"
      and suffix: "\<forall>n. precise_answers_covered P (drop n es) C"
    show "precise_answers_covered P (us@es) C"
    proof (cases "us=[]")
      case True then show ?thesis using suffix[rule_format,of 0] by simp
    next
      case False
      show ?thesis
      proof (rule precise_answers_covered_intro)
        fix event result assume step: "precise_answer_transition P (us@es) event result"
        obtain vs n where local: "precise_answer_transition P us event vs"
          and shape: "result=vs@drop n es"
          using precise_answer_append_suffix[OF False step] by blast
        have edge: "(us,vs)\<in>precise_answer_steps P" using local by (auto simp: precise_answer_steps_def)
        have child: "precise_answers_covered P vs C" by (rule precise_answers_covered_child[OF covered local])
        have joined: "precise_answers_covered P (vs@drop n es) C"
          using ih[OF edge] child suffix by (simp add: drop_drop)
        show "(\<forall>rho. event=Some rho \<longrightarrow> C rho) \<and> precise_answers_covered P result C"
          using precise_answers_covered_event[OF covered] local joined shape by blast
      qed
    qed
  qed
  show ?thesis using all[OF sn] prefix tails by blast
qed

theorem precise_return_contract_singletons:
  assumes children: "\<And>e. e\<in>set ss \<Longrightarrow> precise_return_contract P [e] R t ret"
  shows "precise_return_contract P ss R t ret"
  using children
proof (induct ss rule: length_induct)
  case (1 ss)
  have sn: "SN_on (precise_source P) {map fst ss}"
    by (rule precise_singleton_stack_SN)
      (use "1.prems" in \<open>auto simp: precise_return_contract_def\<close>)
  have covered: "precise_answers_covered P ss (\<lambda>rho. (t,ret rho)\<in>R\<^sup>*)"
  proof (cases ss)
    case Nil show ?thesis unfolding Nil
      by (rule precise_answers_covered_intro) (auto elim: precise_answer_transition.cases)
  next
    case (Cons e es)
    have first: "precise_return_contract P [e] R t ret" using "1.prems" Cons by simp
    have tails: "precise_return_contract P (drop n es) R t ret" for n
      by (rule "1.hyps"[rule_format]) (use "1.prems" Cons in \<open>auto dest: in_set_dropD\<close>)
    have finite: "SN_on (precise_answer_steps P) {[e]}"
      using first by (simp add: precise_return_contract_def precise_answer_instrumentation_SN)
    have covered_first: "precise_answers_covered P [e] (\<lambda>rho. (t,ret rho)\<in>R\<^sup>*)"
      using first by (auto simp: precise_return_contract_def precise_answers_covered_def)
    have covered_tail: "precise_answers_covered P (drop n es) (\<lambda>rho. (t,ret rho)\<in>R\<^sup>*)" for n
      using tails[of n] by (auto simp: precise_return_contract_def precise_answers_covered_def)
    show ?thesis using precise_answers_append_all_suffixes[OF finite covered_first covered_tail]
      by (simp add: Cons)
  qed
  show ?case using sn covered by (auto simp: precise_return_contract_def precise_answers_covered_def)
qed


end
end
