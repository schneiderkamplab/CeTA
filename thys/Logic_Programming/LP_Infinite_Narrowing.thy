theory LP_Infinite_Narrowing
  imports LP_Infinite_Terms
begin

inductive_set lp_iactive :: "('f,'v) trs \<Rightarrow> 'f set \<Rightarrow> ('f,'w) lp_iterm rel"
  for R U where
  root: "(l,r) \<in> R \<Longrightarrow> (lp_ieval l \<rho>,lp_ieval r \<rho>) \<in> lp_iactive R U"
| frame: "f \<in> U \<Longrightarrow> (s,t) \<in> lp_iactive R U \<Longrightarrow>
    (LPIFun f (s#ss),LPIFun f (t#ss)) \<in> lp_iactive R U"

definition lp_inarrow :: "('f,'v) trs \<Rightarrow> 'f set \<Rightarrow> ('f,'w) lp_iterm rel" where
  "lp_inarrow R U = {(s,t). \<exists>\<sigma>. (lp_isubst s \<sigma>,t) \<in> lp_iactive R U}"

context lp_filter
begin

lemma infinite_active_projection:
  fixes R :: "('f,'v) trs" and a :: "('f,'v) term"
  assumes step: "(s,t) \<in> lp_iactive R U"
    and pr: "lp_iproject \<pi> s a"
    and vars: "\<And>l r. (l,r) \<in> R \<Longrightarrow> vars_term (af_term \<pi> r) \<subseteq> vars_term (af_term \<pi> l)"
  obtains b where "lp_iproject \<pi> t b" "(a,b) \<in> rstep (af_rule \<pi> ` R)"
  using step pr
proof (induct arbitrary: a thesis rule: lp_iactive.induct)
  case (root l r \<rho>)
  show ?case by (rule lp_infinite_rule_projection[OF root.prems(2) vars[OF root.hyps] root.hyps])
    (rule root.prems(1))
next
  case (frame f s t ss)
  obtain indices where pi: "afs \<pi> (f,Suc (length ss)) = AFList (0#map Suc indices)"
    and bounds: "set indices \<subseteq> {0..<length ss}"
    using active[OF frame.hyps(1), of "length ss"] by blast
  obtain us where a: "a = Fun f us" and raw:
    "list_all2 (\<lambda>i x. i < length (s#ss) \<and> lp_iproject \<pi> ((s#ss)!i) x) (0#map Suc indices) us"
    using frame.prems(2) pi by (cases rule: lp_iproject.cases) auto
  obtain x xs where us: "us=x#xs" and px: "lp_iproject \<pi> s x"
    and tail: "list_all2 (\<lambda>i y. i < length ss \<and> lp_iproject \<pi> (ss!i) y) indices xs"
    using raw by (cases us) (auto simp: list_all2_map1)
  obtain y where py: "lp_iproject \<pi> t y" and xy: "(x,y) \<in> rstep (af_rule \<pi> ` R)"
    by (rule frame.hyps(3)[OF _ px]) blast
  have target: "lp_iproject \<pi> (LPIFun f (t#ss)) (Fun f (y#xs))"
    by (rule lp_iproject.list) (use pi py tail in \<open>auto simp: list_all2_map1\<close>)
  have step: "(a,Fun f (y#xs)) \<in> rstep (af_rule \<pi> ` R)"
    using rstep_ctxt[OF xy, of "More f [] Hole xs"] by (simp add: a us)
  show ?case by (rule frame.prems(1)[OF target step])
qed

theorem infinite_narrowing_terminates:
  fixes s :: "('f,'w) lp_iterm"
    and R :: "('f,'v) trs" and a :: "('f,'v) term"
  assumes sn: "SN (rstep (af_rule \<pi> ` R))"
    and vars: "\<And>l r. (l,r) \<in> R \<Longrightarrow> vars_term (af_term \<pi> r) \<subseteq> vars_term (af_term \<pi> l)"
    and pr: "lp_iproject \<pi> s a"
  shows "SN_on (lp_inarrow R U) {s}"
proof -
  have general: "\<And>a. SN_on (rstep (af_rule \<pi> ` R)) {a} \<Longrightarrow>
    \<forall>s::('f,'w) lp_iterm. lp_iproject \<pi> s a \<longrightarrow> SN_on (lp_inarrow R U) {s}"
  proof -
    fix a assume finite: "SN_on (rstep (af_rule \<pi> ` R)) {a}"
    show "\<forall>s::('f,'w) lp_iterm. lp_iproject \<pi> s a \<longrightarrow> SN_on (lp_inarrow R U) {s}"
    proof (rule SN_on_induct[OF finite singletonI], intro allI impI)
      fix a and s :: "('f,'w) lp_iterm"
      assume ih: "\<And>b. (a,b) \<in> rstep (af_rule \<pi> ` R) \<Longrightarrow>
        \<forall>t::('f,'w) lp_iterm. lp_iproject \<pi> t b \<longrightarrow> SN_on (lp_inarrow R U) {t}"
        and pr: "lp_iproject \<pi> s a"
      show "SN_on (lp_inarrow R U) {s}"
      proof (rule step_reflects_SN_on)
        fix t assume st: "(s,t) \<in> lp_inarrow R U"
        obtain \<sigma> where step: "(lp_isubst s \<sigma>,t) \<in> lp_iactive R U"
          using st unfolding lp_inarrow_def by blast
        obtain b where pb: "lp_iproject \<pi> t b" and ab: "(a,b) \<in> rstep (af_rule \<pi> ` R)"
          by (rule infinite_active_projection[OF step lp_iproject_subst[OF pr] vars]) blast
        show "SN_on (lp_inarrow R U) {t}" using ih[OF ab] pb by blast
      qed
    qed
  qed
  have finite: "SN_on (rstep (af_rule \<pi> ` R)) {a}"
    using sn unfolding SN_on_def by blast
  show ?thesis using general[OF finite] pr by blast
qed

end
end
