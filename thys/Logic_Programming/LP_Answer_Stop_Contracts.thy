theory LP_Answer_Stop_Contracts
  imports LP_Answer_Contracts LP_Scoped_Answer_Composition
begin

text \<open>A reusable contract adapter for source-justified uncaught errors.
The predicate stop is a separate semantic obligation. An error produces no
answer and clears the complete annotated stack, including saved alternatives.
This adapter does not license treating an unsupported operation as an error.\<close>

definition lp_answer_stop where
  "lp_answer_stop T stop ss event tt =
    (ss\<noteq>[] \<and> (if stop ss then event=None \<and> tt=[] else T ss event tt))"

lemma lp_answer_stop_empty[simp]:
  "\<not>lp_answer_stop T stop [] event tt"
  by (simp add: lp_answer_stop_def)

lemma lp_answer_stop_path:
  assumes path: "(ss,tt)\<in>(lp_answer_steps (lp_answer_stop T stop))\<^sup>*"
  shows "(ss,tt)\<in>(lp_answer_steps T)\<^sup>* \<or> tt=[]"
  using path
proof (induct rule: rtrancl_induct)
  case base then show ?case by simp
next
  case (step y z)
  have "y\<noteq>[] \<and> ((y,z)\<in>lp_answer_steps T \<or> z=[])"
    using step.hyps(2) by (auto simp: lp_answer_steps_def lp_answer_stop_def split: if_splits)
  then show ?case using step by (meson rtrancl_into_rtrancl)
qed

lemma lp_answer_stop_actual:
  assumes actual: "lp_actual_answer (lp_answer_stop T stop) ss rho"
  shows "lp_actual_answer T ss rho"
  using actual lp_answer_stop_path[where T=T and stop=stop and ss=ss]
  by (auto simp: lp_actual_answer_def lp_answer_stop_def split: if_splits)

lemma lp_answer_stop_SN:
  assumes sn: "SN_on (lp_answer_steps T) {ss}"
  shows "SN_on (lp_answer_steps (lp_answer_stop T stop)) {ss}"
proof -
  have empty: "SN_on (lp_answer_steps (lp_answer_stop T stop)) {[]}"
    by (rule step_reflects_SN_on) (auto simp: lp_answer_steps_def)
  show ?thesis
  proof (rule SN_on_induct[OF sn singletonI])
    fix x
    assume ih: "\<And>y. (x,y)\<in>lp_answer_steps T \<Longrightarrow>
      SN_on (lp_answer_steps (lp_answer_stop T stop)) {y}"
    show "SN_on (lp_answer_steps (lp_answer_stop T stop)) {x}"
    proof (rule step_reflects_SN_on)
      fix y assume step: "(x,y)\<in>lp_answer_steps (lp_answer_stop T stop)"
      have "(x,y)\<in>lp_answer_steps T \<or> y=[]"
        using step by (auto simp: lp_answer_steps_def lp_answer_stop_def split: if_splits)
      then show "SN_on (lp_answer_steps (lp_answer_stop T stop)) {y}"
        using ih empty by blast
    qed
  qed
qed

lemma lp_answer_stop_coverage:
  assumes covered: "lp_answers_covered T ss C"
  shows "lp_answers_covered (lp_answer_stop T stop) ss C"
  using covered lp_answer_stop_path[where T=T and stop=stop and ss=ss]
  by (auto simp: lp_answers_covered_def lp_answer_stop_def split: if_splits)

theorem lp_answer_stop_contract:
  "lp_answer_contract T ss R t ret \<Longrightarrow>
   lp_answer_contract (lp_answer_stop T stop) ss R t ret"
  using lp_answer_stop_SN lp_answer_stop_coverage
  by (auto simp: lp_answer_contract_def)

theorem lp_answer_stop_error_contract:
  assumes error: "stop ss"
  shows "lp_answer_contract (lp_answer_stop T stop) ss R t ret"
proof -
  have empty: "lp_answer_contract (lp_answer_stop T stop) [] R t ret"
    by (rule lp_answer_contract_intro) simp
  show ?thesis by (rule lp_answer_contract_intro)
    (use error empty in \<open>auto simp: lp_answer_stop_def\<close>)
qed

text \<open>One-step certificates can be reused directly with stopped child
contracts. This avoids the invalid reverse lifting of a child termination
contract from the stopped relation to the original relation.\<close>

lemma lp_answer_stop_primitive:
  assumes lower: "\<And>vs v out. (t,v)\<in>R\<^sup>+ \<Longrightarrow> rep vs v out \<Longrightarrow>
    lp_answer_contract (lp_answer_stop T stop) vs R v out"
    and local: "\<And>event tt. T ss event tt \<Longrightarrow>
      (\<exists>u. (t,u)\<in>R\<^sup>+ \<and> rep tt u ret) \<and>
      (\<forall>rho. event=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*)"
  shows "lp_answer_contract (lp_answer_stop T stop) ss R t ret"
proof (cases "stop ss")
  case True then show ?thesis by (rule lp_answer_stop_error_contract)
next
  case False
  show ?thesis
  proof (rule lp_answer_contract_intro)
    fix event tt assume step: "lp_answer_stop T stop ss event tt"
    have original: "T ss event tt" using step False by (simp add: lp_answer_stop_def)
    obtain u where progress: "(t,u)\<in>R\<^sup>+" and represented: "rep tt u ret"
      using local[OF original] by blast
    have child: "lp_answer_contract (lp_answer_stop T stop) tt R t ret"
      by (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF progress]
        lower[OF progress represented]])
    show "(\<forall>rho. event=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*) \<and>
      lp_answer_contract (lp_answer_stop T stop) tt R t ret"
      using child local[OF original] by blast
  qed
qed

lemma lp_answer_stop_error_no_answers:
  assumes error: "stop ss"
  shows "\<not>lp_actual_answer (lp_answer_stop T stop) ss rho"
proof -
  have contract: "lp_answer_contract (lp_answer_stop T stop) ss {} False (\<lambda>_. True)"
    by (rule lp_answer_stop_error_contract) (rule error)
  show ?thesis using lp_actual_answer_covered[OF contract] by auto
qed

lemma lp_answer_stop_retains_unstopped_loop:
  "ss\<noteq>[] \<Longrightarrow> \<not>stop ss \<Longrightarrow> T ss None ss \<Longrightarrow>
    lp_answer_stop T stop ss None ss"
  by (simp add: lp_answer_stop_def)

lemma lp_answer_stop_attach_reflect:
  assumes active: "lpc_prefix_active ss"
    and same: "stop (lpc_attach_answers rest ss)=stop ss"
    and reflect: "\<And>event result. T (lpc_attach_answers rest ss) event result \<Longrightarrow>
      event=None \<and> (\<exists>vs. T ss None vs \<and> result=lpc_attach_answers rest vs)"
    and step: "lp_answer_stop T stop (lpc_attach_answers rest ss) event result"
  shows "event=None \<and> (\<exists>vs. lp_answer_stop T stop ss None vs \<and>
    result=lpc_attach_answers rest vs)"
proof (cases "stop ss")
  case True
  have nonempty: "ss\<noteq>[]" using active by (cases ss) auto
  show ?thesis using step same True nonempty
    by (auto simp: lp_answer_stop_def lpc_attach_answers_def)
next
  case False
  have original: "T (lpc_attach_answers rest ss) event result"
    using step same False by (simp add: lp_answer_stop_def)
  obtain vs where facts: "event=None" "T ss None vs" "result=lpc_attach_answers rest vs"
    using reflect[OF original] by blast
  have nonempty: "ss\<noteq>[]" using active by (cases ss) auto
  show ?thesis using facts False nonempty by (auto simp: lp_answer_stop_def)
qed

lemma lp_answer_stop_append_suffix:
  assumes nonempty: "ss\<noteq>[]"
    and same: "stop (ss@bs)=stop ss"
    and reflect: "\<And>ev result. T (ss@bs) ev result \<Longrightarrow>
      \<exists>tt n. T ss ev tt \<and> result=tt@drop n bs"
    and step: "lp_answer_stop T stop (ss@bs) event result"
  shows "\<exists>tt n. lp_answer_stop T stop ss event tt \<and> result=tt@drop n bs"
proof (cases "stop ss")
  case True
  have shape: "event=None" "result=[]" using step same True
    by (auto simp: lp_answer_stop_def)
  show ?thesis by (intro exI[of _ "[]"] exI[of _ "length bs"])
    (use True nonempty shape in \<open>simp add: lp_answer_stop_def\<close>)
next
  case False
  have original: "T (ss@bs) event result" using step same False by (simp add: lp_answer_stop_def)
  show ?thesis using reflect[OF original] nonempty False by (auto simp: lp_answer_stop_def)
qed

ML \<open>
val audited = [@{thm lp_answer_stop_append_suffix}, @{thm lp_answer_stop_attach_reflect}, @{thm lp_answer_stop_error_no_answers}, @{thm lp_answer_stop_actual}, @{thm lp_answer_stop_path}, @{thm lp_answer_stop_SN},
  @{thm lp_answer_stop_primitive}, @{thm lp_answer_stop_contract}, @{thm lp_answer_stop_error_contract}];
val names = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = names [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof audited orelse
  exists (fn n => not (member (op =) inherited n)) (names audited)
  then error "Untrusted stopped-answer contract dependency" else ();
\<close>
end
