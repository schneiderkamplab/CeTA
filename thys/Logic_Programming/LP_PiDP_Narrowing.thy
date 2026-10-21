theory LP_PiDP_Narrowing
  imports LP_PiDP_Projection LP_Infinite_Narrowing
begin

text \<open>Resolution can instantiate discarded arguments between calls. These
  links must not be confused with ordinary rewriting. Instantiation preserves
  an existing finite ground projection, even for rational-tree substitutions.
  We therefore allow it explicitly in the weak relation of a Pi-DP chain.\<close>

definition lp_pi_link :: "('f,'v) trs \<Rightarrow> ('f,'w) lp_iterm rel" where
  "lp_pi_link R = lp_irewrite R \<union> {(s,t). \<exists>\<sigma>. t = lp_isubst s \<sigma>}"

lemma lp_pi_link_projection:
  fixes R :: "('f,'v) trs" and a :: "('f,'v) term"
  assumes step: "(s,t) \<in> lp_pi_link R"
    and projection: "lp_iproject \<pi> s a"
    and vars: "\<And>l r. (l,r) \<in> R \<Longrightarrow> vars_term (af_term \<pi> r) \<subseteq> vars_term (af_term \<pi> l)"
  obtains b where "lp_iproject \<pi> t b" "(a,b) \<in> (rstep (af_rule \<pi> ` R))\<^sup>*"
proof (cases "(s,t) \<in> lp_irewrite R")
  case True
  show ?thesis by (rule lp_irewrite_projection[OF True projection vars]) (auto intro: that)
next
  case False
  obtain \<sigma> where t: "t = lp_isubst s \<sigma>"
    using step False unfolding lp_pi_link_def by blast
  have "lp_iproject \<pi> t a" unfolding t by (rule lp_iproject_subst[OF projection])
  then show ?thesis by (rule that) simp
qed

lemma lp_pi_links_projection:
  fixes R :: "('f,'v) trs" and a :: "('f,'v) term"
  assumes steps: "(s,t) \<in> (lp_pi_link R)\<^sup>*"
    and projection: "lp_iproject \<pi> s a"
    and vars: "\<And>l r. (l,r) \<in> R \<Longrightarrow> vars_term (af_term \<pi> r) \<subseteq> vars_term (af_term \<pi> l)"
  obtains b where "lp_iproject \<pi> t b" "(a,b) \<in> (rstep (af_rule \<pi> ` R))\<^sup>*"
  using steps projection
proof (induct arbitrary: thesis rule: rtrancl_induct)
  case base
  show ?case by (rule base.prems(1)[OF base.prems(2)]) simp
next
  case (step y z)
  obtain b where pb: "lp_iproject \<pi> y b" and ab: "(a,b) \<in> (rstep (af_rule \<pi> ` R))\<^sup>*"
    by (rule step.hyps(3)[OF _ step.prems(2)]) blast
  obtain c where pc: "lp_iproject \<pi> z c" and bc: "(b,c) \<in> (rstep (af_rule \<pi> ` R))\<^sup>*"
    by (rule lp_pi_link_projection[OF step.hyps(2) pb vars]) blast
  show ?case by (rule step.prems(1)[OF pc rtrancl_trans[OF ab bc]])
qed

lemma lp_iactive_irewrite:
  "(s,t) \<in> lp_iactive R U \<Longrightarrow> (s,t) \<in> lp_irewrite R"
proof (induct rule: lp_iactive.induct)
  case (root l r \<rho>)
  then show ?case by (rule lp_irewrite.root)
next
  case (frame f s t ss)
  have "(LPIFun f (s#ss), LPIFun f ((s#ss)[0:=t])) \<in> lp_irewrite R"
    by (rule lp_irewrite.arg) (use frame.hyps(3) in auto)
  then show ?case by simp
qed

lemma lp_inarrow_pi_links:
  assumes "(s,t) \<in> lp_inarrow R U"
  shows "(s,t) \<in> (lp_pi_link R)\<^sup>*"
proof -
  obtain \<sigma> where active: "(lp_isubst s \<sigma>,t) \<in> lp_iactive R U"
    using assms unfolding lp_inarrow_def by blast
  have first: "(s,lp_isubst s \<sigma>) \<in> lp_pi_link R"
    unfolding lp_pi_link_def by blast
  have second: "(lp_isubst s \<sigma>,t) \<in> lp_pi_link R"
    using lp_iactive_irewrite[OF active] unfolding lp_pi_link_def by blast
  show ?thesis by (rule rtrancl_into_rtrancl[OF r_into_rtrancl[OF first] second])
qed

definition lp_pi_narrow_chain :: "('f,'v) trs \<Rightarrow> ('f,'v) trs \<Rightarrow> 'f afs \<Rightarrow>
    (nat \<Rightarrow> ('f,'v) term) \<Rightarrow> (nat \<Rightarrow> ('f,'v) term) \<Rightarrow>
    (nat \<Rightarrow> 'v \<Rightarrow> ('f,'w) lp_iterm) \<Rightarrow> bool" where
  "lp_pi_narrow_chain D R \<pi> ls rs valuations = (\<forall>i::nat.
    (ls i,rs i) \<in> D \<and>
    (lp_ieval (rs i) (valuations i), lp_ieval (ls (Suc i)) (valuations (Suc i))) \<in> (lp_pi_link R)\<^sup>* \<and>
    (\<exists>a::('f,'v) term. lp_iproject \<pi> (lp_ieval (ls i) (valuations i)) a) \<and>
    (\<exists>b::('f,'v) term. lp_iproject \<pi> (lp_ieval (rs i) (valuations i)) b))"

theorem lp_pi_narrow_chain_filter:
  fixes D R :: "('f,'v) trs"
  assumes chain: "lp_pi_narrow_chain D R \<pi> ls rs valuations"
    and vars: "\<And>l r. (l,r) \<in> R \<Longrightarrow> vars_term (af_term \<pi> r) \<subseteq> vars_term (af_term \<pi> l)"
  shows "min_ichain (False,False,af_rule \<pi> ` D,{},{},{},af_rule \<pi> ` R)
    (\<lambda>i. af_term \<pi> (ls i)) (\<lambda>i. af_term \<pi> (rs i))
    (\<lambda>i x. lp_projection \<pi> (valuations i x))"
proof -
  let ?subst = "\<lambda>i x. (lp_projection \<pi> (valuations i x) :: ('f,'v) term)"
  have pair: "\<And>i. (af_term \<pi> (ls i),af_term \<pi> (rs i)) \<in> af_rule \<pi> ` D"
    using chain unfolding lp_pi_narrow_chain_def af_rule_alt_def by force
  have link: "\<And>i. (af_term \<pi> (rs i) \<cdot> ?subst i,
      af_term \<pi> (ls (Suc i)) \<cdot> ?subst (Suc i)) \<in> (rstep (af_rule \<pi> ` R))\<^sup>*"
  proof -
    fix i
    obtain a :: "('f,'v) term" where pa: "lp_iproject \<pi> (lp_ieval (rs i) (valuations i)) a"
      using chain unfolding lp_pi_narrow_chain_def by blast
    obtain b :: "('f,'v) term" where pb: "lp_iproject \<pi> (lp_ieval (ls (Suc i)) (valuations (Suc i))) b"
      using chain unfolding lp_pi_narrow_chain_def by blast
    have path: "(lp_ieval (rs i) (valuations i),lp_ieval (ls (Suc i)) (valuations (Suc i))) \<in> (lp_pi_link R)\<^sup>*"
      using chain unfolding lp_pi_narrow_chain_def by blast
    obtain c where pc: "lp_iproject \<pi> (lp_ieval (ls (Suc i)) (valuations (Suc i))) c"
      and ac: "(a,c) \<in> (rstep (af_rule \<pi> ` R))\<^sup>*"
      by (rule lp_pi_links_projection[OF path pa vars]) blast
    have cb: "c=b" by (rule lp_iproject_unique[OF pc pb])
    show "(af_term \<pi> (rs i) \<cdot> ?subst i,
      af_term \<pi> (ls (Suc i)) \<cdot> ?subst (Suc i)) \<in> (rstep (af_rule \<pi> ` R))\<^sup>*"
      using ac unfolding cb lp_iproject_ieval_inverse[OF pa] lp_iproject_ieval_inverse[OF pb] .
  qed
  show ?thesis using pair link by (simp add: ichain.simps NF_subst_def)
qed

corollary lp_pi_narrow_filter_processor:
  fixes D R :: "('f,'v) trs"
  assumes finite: "finite_dpp (False,False,af_rule \<pi> ` D,{},{},{},af_rule \<pi> ` R)"
    and vars: "\<And>l r. (l,r) \<in> R \<Longrightarrow> vars_term (af_term \<pi> r) \<subseteq> vars_term (af_term \<pi> l)"
  shows "\<not> lp_pi_narrow_chain D R \<pi> ls rs valuations"
  using lp_pi_narrow_chain_filter[OF _ vars] finite unfolding finite_dpp_def by blast

end
