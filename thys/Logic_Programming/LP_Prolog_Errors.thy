theory LP_Prolog_Errors
  imports LP_Cut_Most_General_Source
begin

text \<open>Uncaught Prolog errors terminate the complete ordered computation:
there is no continuation into a saved alternative. This bridge permits terminal
error exits in addition to the existing rational-tree MGU source relation.
It does not treat an unsupported builtin, blocking IO or cyclic meta expansion
as an error. A source processor must separately justify its error predicate.\<close>

definition lp_prolog_stop_extension where
  "lp_prolog_stop_extension R E = R \<union> {(s,t). E s \<and> s \<noteq> [] \<and> t=[]}"

lemma lp_prolog_stop_extension_SN:
  assumes sn: "SN_on R {s}" and empty: "\<And>t. ([],t) \<notin> R"
  shows "SN_on (lp_prolog_stop_extension R E) {s}"
proof -
  have stopped: "SN_on (lp_prolog_stop_extension R E) {[]}"
    by (rule step_reflects_SN_on) (use empty in \<open>auto simp: lp_prolog_stop_extension_def\<close>)
  show ?thesis
  proof (rule SN_on_induct[OF sn singletonI])
    fix x
    assume ih: "\<And>y. (x,y) \<in> R \<Longrightarrow> SN_on (lp_prolog_stop_extension R E) {y}"
    show "SN_on (lp_prolog_stop_extension R E) {x}"
      by (rule step_reflects_SN_on)
        (use ih stopped in \<open>auto simp: lp_prolog_stop_extension_def\<close>)
  qed
qed

lemma lp_cut_mgu_source_empty:
  "([],t) \<notin> lp_cut_mgu_source P"
  by (auto elim: lp_cut_mgu_source.cases)

corollary lp_prolog_uncaught_errors_preserve_termination:
  "SN_on (lp_cut_mgu_source P) {s} \<Longrightarrow>
   SN_on (lp_prolog_stop_extension (lp_cut_mgu_source P) E) {s}"
  by (rule lp_prolog_stop_extension_SN) (auto simp: lp_cut_mgu_source_empty)

lemma lp_prolog_error_does_not_resume_alternatives:
  assumes "E (LPCGoals gs # es)"
  shows "(LPCGoals gs # es,[]) \<in> lp_prolog_stop_extension R E"
  using assms by (simp add: lp_prolog_stop_extension_def)

end
