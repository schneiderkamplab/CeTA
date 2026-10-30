theory LP_Prolog_Builtin_Domain
  imports LP_Prolog_Integer_Comparison_Check
begin

text \<open>An unsupported builtin must not become a stuck, terminating state
merely because its evaluator has no rule. The domain envelope adds a self-loop
at each such call. A source termination proof therefore has to establish the
supported domain at every reachable builtin. Outside that domain the theorem
allows arbitrary builtin outcomes; it does not silently assume failure.\<close>

fun lpp_builtin_domain_bad where
  "lpp_builtin_domain_bad B D (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#saved) =
    ((f,length ts)\<in>B \<and> \<not>D f ts)"
| "lpp_builtin_domain_bad B D s = False"

definition lpp_domain_source where
  "lpp_domain_source P B U D = lpp_atomic_source P B U \<union>
    {(s,t). s=t \<and> lpp_builtin_domain_bad B D s}"

lemma lpp_domain_SN_transfer:
  assumes sn: "SN_on (R\<union>{(x,y). x=y \<and> unsupported x}) {s}"
    and inclusion: "\<And>x y. (x,y)\<in>S \<Longrightarrow> \<not>unsupported x \<Longrightarrow> (x,y)\<in>R"
  shows "SN_on S {s}"
proof (rule SN_on_induct[OF sn singletonI])
  fix x
  assume ih: "\<And>y. (x,y)\<in>R\<union>{(x,y). x=y \<and> unsupported x} \<Longrightarrow> SN_on S {y}"
  show "SN_on S {x}"
  proof (cases "unsupported x")
    case True
    show ?thesis by (rule ih) (use True in auto)
  next
    case False
    show ?thesis
    proof (rule step_reflects_SN_on)
      fix y assume edge: "(x,y)\<in>S"
      have "(x,y)\<in>R" by (rule inclusion[OF edge False])
      then show "SN_on S {y}" by (intro ih) auto
    qed
  qed
qed

lemma lpp_atomic_domain_inclusion:
  assumes selected: "\<And>f ts outcome. V f ts outcome \<Longrightarrow> (f,length ts)\<in>B"
    and agrees: "\<And>f ts outcome. D f ts \<Longrightarrow> V f ts outcome \<Longrightarrow> U f ts outcome"
    and step: "(s,t)\<in>lpp_atomic_source P B V"
    and domain: "\<not>lpp_builtin_domain_bad B D s"
  shows "(s,t)\<in>lpp_atomic_source P B U"
  using step domain
  by (cases rule: lpp_atomic_source.cases)
    (auto dest: selected intro: lpp_atomic_source.intros agrees)

theorem lpp_domain_source_sound:
  assumes sn: "SN_on (lpp_domain_source P B U D) {s}"
    and selected: "\<And>f ts outcome. V f ts outcome \<Longrightarrow> (f,length ts)\<in>B"
    and agrees: "\<And>f ts outcome. D f ts \<Longrightarrow> V f ts outcome \<Longrightarrow> U f ts outcome"
  shows "SN_on (lpp_atomic_source P B V) {s}"
  by (rule lpp_domain_SN_transfer[OF sn[unfolded lpp_domain_source_def]])
    (rule lpp_atomic_domain_inclusion[OF selected agrees])

definition lpp_domain_answers where
  "lpp_domain_answers P B U D ss event tt =
    (lpp_answer_transition P B U ss event tt \<or>
     (lpp_builtin_domain_bad B D (map fst ss) \<and> event=None \<and> tt=ss))"

lemma lpp_domain_answers_erases:
  "lpp_domain_answers P B U D ss event tt \<Longrightarrow>
   (map fst ss,map fst tt)\<in>lpp_domain_source P B U D"
  by (auto simp: lpp_domain_answers_def lpp_domain_source_def dest: lpp_answer_transition_erases)

lemma lpp_domain_source_lifts:
  assumes step: "(map fst ss,t)\<in>lpp_domain_source P B U D"
  shows "\<exists>event tt. lpp_domain_answers P B U D ss event tt \<and> map fst tt=t"
proof (cases "(map fst ss,t)\<in>lpp_atomic_source P B U")
  case True
  obtain event tt where "lpp_answer_transition P B U ss event tt" "map fst tt=t"
    using lpp_answer_source_lifts[where ss=ss, OF True] by blast
  then show ?thesis by (auto simp: lpp_domain_answers_def)
next
  case False
  then have "t=map fst ss" "lpp_builtin_domain_bad B D (map fst ss)"
    using step by (auto simp: lpp_domain_source_def)
  then show ?thesis unfolding lpp_domain_answers_def by blast
qed

lemma lpp_domain_instrumentation_SN:
  assumes sn: "SN_on (lp_answer_steps (lpp_domain_answers P B U D)) {ss}"
  shows "SN_on (lpp_domain_source P B U D) {map fst ss}"
proof (rule SN_on_induct[OF sn singletonI])
  fix s
  assume ih: "\<And>t. (s,t)\<in>lp_answer_steps (lpp_domain_answers P B U D) \<Longrightarrow>
    SN_on (lpp_domain_source P B U D) {map fst t}"
  show "SN_on (lpp_domain_source P B U D) {map fst s}"
  proof (rule step_reflects_SN_on)
    fix u assume step: "(map fst s,u)\<in>lpp_domain_source P B U D"
    obtain event t where lifted: "lpp_domain_answers P B U D s event t" and u: "u=map fst t"
      using lpp_domain_source_lifts[OF step] by blast
    show "SN_on (lpp_domain_source P B U D) {u}"
      using ih[of t] lifted by (auto simp: u lp_answer_steps_def)
  qed
qed

lemma lpp_domain_answers_supported:
  "\<not>lpp_builtin_domain_bad B D (map fst ss) \<Longrightarrow>
    lpp_domain_answers P B U D ss event tt = lpp_answer_transition P B U ss event tt"
  by (simp add: lpp_domain_answers_def)

text \<open>The source envelope uses the same answer-graph progress theorem as
LP and LP with cut. Domain coverage is a separate obligation at every represented
state, not an assumption extracted from the final numeric path.\<close>

lemma lpp_domain_graph_valid:
  assumes graph: "lp_answer_graph_valid (lpp_answer_transition P B U) R rep ret weight"
    and supported: "\<And>ss t. rep ss t \<Longrightarrow> \<not>lpp_builtin_domain_bad B D (map fst ss)"
  shows "lp_answer_graph_valid (lpp_domain_answers P B U D) R rep ret weight"
  using graph supported
  by (auto simp: lp_answer_graph_valid_def lpp_domain_answers_def)

theorem lpp_domain_graph_source_SN:
  assumes graph: "lp_answer_graph_valid (lpp_answer_transition P B U) R rep ret weight"
    and supported: "\<And>ss t. rep ss t \<Longrightarrow> \<not>lpp_builtin_domain_bad B D (map fst ss)"
    and sn: "SN_on R {t}" and represented: "rep ss t"
    and selected: "\<And>f ts outcome. V f ts outcome \<Longrightarrow> (f,length ts)\<in>B"
    and agrees: "\<And>f ts outcome. D f ts \<Longrightarrow> V f ts outcome \<Longrightarrow> U f ts outcome"
  shows "SN_on (lpp_atomic_source P B V) {map fst ss}"
proof -
  have valid: "lp_answer_graph_valid (lpp_domain_answers P B U D) R rep ret weight"
    by (rule lpp_domain_graph_valid[OF graph supported])
  have instrumented: "SN_on (lp_answer_steps (lpp_domain_answers P B U D)) {ss}"
    by (rule lp_answer_graph_SN[OF valid sn represented])
  have envelope: "SN_on (lpp_domain_source P B U D) {map fst ss}"
    by (rule lpp_domain_instrumentation_SN[OF instrumented])
  show ?thesis by (rule lpp_domain_source_sound[OF envelope selected agrees])
qed

ML \<open>
val checked = [@{thm lpp_domain_source_sound}, @{thm lpp_domain_instrumentation_SN},
  @{thm lpp_domain_graph_source_SN}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted builtin-domain dependency" else ();
\<close>
end
