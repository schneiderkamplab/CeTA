theory LP_Prolog_Stopped_Answers
  imports LP_Answer_Stop_Contracts LP_Prolog_Builtin_Domain LP_Prolog_Undefined_XML
begin

text \<open>The stop predicate is exactly the existing source semantics'
undefined-procedure condition. Builtins are excluded even if they have no
source clauses. This is instrumentation of lp_prolog_source, not a replacement
operational semantics. Unsupported builtin domains retain their obligations.\<close>

definition lpp_undefined_answer_stop where
  "lpp_undefined_answer_stop P B ss =
    (lpp_undefined P (map fst ss) \<and> \<not>lpp_builtin_active B (map fst ss))"

lemma lpp_undefined_answer_stop_nonempty:
  "lpp_undefined_answer_stop P B ss \<Longrightarrow> ss\<noteq>[]"
  by (auto simp: lpp_undefined_answer_stop_def lpp_undefined_def)

lemma lpp_stopped_source_lifts:
  assumes step: "(map fst ss,t)\<in>lp_prolog_source P B (lpp_domain_source P B U D)"
  shows "\<exists>event tt. lp_answer_stop (lpp_domain_answers P B U D)
    (lpp_undefined_answer_stop P B) ss event tt \<and> map fst tt=t"
proof (cases "lpp_undefined_answer_stop P B ss")
  case True
  have "t=[]" using step True
    by (auto simp: lp_prolog_source_def lpp_undefined_answer_stop_def)
  then show ?thesis using True lpp_undefined_answer_stop_nonempty[OF True]
    by (auto simp: lp_answer_stop_def)
next
  case False
  have nonempty: "ss\<noteq>[]" using step by (cases ss) (auto simp: lp_prolog_source_empty)
  have domain: "(map fst ss,t)\<in>lpp_domain_source P B U D"
    using step False
    by (auto simp: lp_prolog_source_def lpp_domain_source_def
      lpp_undefined_answer_stop_def intro: lpp_atomic_source.base)
  obtain event tt where lifted: "lpp_domain_answers P B U D ss event tt" "map fst tt=t"
    using lpp_domain_source_lifts[OF domain] by blast
  show ?thesis using False nonempty lifted by (auto simp: lp_answer_stop_def)
qed

theorem lpp_stopped_source_SN:
  assumes sn: "SN_on (lp_answer_steps (lp_answer_stop (lpp_domain_answers P B U D)
    (lpp_undefined_answer_stop P B))) {ss}"
  shows "SN_on (lp_prolog_source P B (lpp_domain_source P B U D)) {map fst ss}"
proof (rule SN_on_induct[OF sn singletonI])
  fix xs
  assume ih: "\<And>ys. (xs,ys)\<in>lp_answer_steps
    (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)) \<Longrightarrow>
    SN_on (lp_prolog_source P B (lpp_domain_source P B U D)) {map fst ys}"
  show "SN_on (lp_prolog_source P B (lpp_domain_source P B U D)) {map fst xs}"
  proof (rule step_reflects_SN_on)
    fix t assume step: "(map fst xs,t)\<in>lp_prolog_source P B (lpp_domain_source P B U D)"
    obtain event ys where lifted: "lp_answer_stop (lpp_domain_answers P B U D)
      (lpp_undefined_answer_stop P B) xs event ys" "map fst ys=t"
      using lpp_stopped_source_lifts[OF step] by blast
    show "SN_on (lp_prolog_source P B (lpp_domain_source P B U D)) {t}"
      using ih lifted by (auto simp: lp_answer_steps_def)
  qed
qed

lemma lpp_undefined_stop_attach:
  assumes active: "lpc_prefix_active ss"
  shows "lpp_undefined_answer_stop P B (lpc_attach_answers rest ss) =
    lpp_undefined_answer_stop P B ss"
proof -
  obtain frame rho tail where shape: "ss=(frame,rho)#tail"
    using active by (cases ss) (auto split: prod.splits)
  show ?thesis using active unfolding shape
    by (cases frame)
      (auto simp: lpc_attach_answers_def lpp_undefined_answer_stop_def
        lpp_undefined_def lpp_builtin_active_def dest: lpc_attach_nonempty_head)
qed

lemma lpp_stopped_retains_unsupported_builtin:
  assumes bad: "lpp_builtin_domain_bad B D (map fst ss)"
  shows "lp_answer_stop (lpp_domain_answers P B U D)
    (lpp_undefined_answer_stop P B) ss None ss"
proof -
  have active: "lpp_builtin_active B (map fst ss)"
    using bad by (cases "(B,D,map fst ss)" rule: lpp_builtin_domain_bad.cases)
      (auto simp: lpp_builtin_active_def)
  have nonempty: "ss\<noteq>[]" using bad by (cases ss) auto
  show ?thesis using active nonempty bad
    by (simp add: lp_answer_stop_def lpp_undefined_answer_stop_def lpp_domain_answers_def)
qed

ML \<open>
val audited = [@{thm lpp_stopped_retains_unsupported_builtin}, @{thm lpp_undefined_stop_attach}, @{thm lpp_stopped_source_lifts}, @{thm lpp_stopped_source_SN}];
val names = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = names [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof audited orelse
  exists (fn n => not (member (op =) inherited n)) (names audited)
  then error "Untrusted stopped-source bridge dependency" else ();
\<close>
end
