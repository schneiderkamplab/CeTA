theory LP_PiDP_Projection
  imports LP_Infinite_Terms
begin

text \<open>Full infinitary rewriting, used for connecting dependency pairs.
  Unlike the continuation-machine relation, this permits rewriting at every
  finite position. Only the argument-filter projection must remain finite.\<close>

inductive_set lp_irewrite :: "('f,'v) trs \<Rightarrow> ('f,'w) lp_iterm rel"
  for R where
  root: "(l,r) \<in> R \<Longrightarrow> (lp_ieval l \<rho>,lp_ieval r \<rho>) \<in> lp_irewrite R"
| arg: "i < length ts \<Longrightarrow> (ts!i,t) \<in> lp_irewrite R \<Longrightarrow>
    (LPIFun f ts, LPIFun f (ts[i:=t])) \<in> lp_irewrite R"

lemma lp_rsteps_context:
  "(s,t) \<in> (rstep R)\<^sup>* \<Longrightarrow>
    (ctxt_apply_term C s,ctxt_apply_term C t) \<in> (rstep R)\<^sup>*"
  by (induct rule: rtrancl_induct) (auto intro: rtrancl_into_rtrancl rstep_ctxt)

lemma lp_rsteps_arguments:
  assumes "list_all2 (\<lambda>s t. (s,t) \<in> (rstep R)\<^sup>*) xs ys"
  shows "(Fun f (pre@xs),Fun f (pre@ys)) \<in> (rstep R)\<^sup>*"
  using assms
proof (induct arbitrary: pre rule: list_all2_induct)
  case Nil
  then show ?case by simp
next
  case (Cons x y xs ys)
  have head: "(Fun f (pre@x#xs),Fun f (pre@y#xs)) \<in> (rstep R)\<^sup>*"
    using lp_rsteps_context[OF Cons.hyps(1), of "More f pre Hole xs"] by simp
  have tail: "(Fun f (pre@y#xs),Fun f (pre@y#ys)) \<in> (rstep R)\<^sup>*"
    using Cons.hyps(3)[of "pre@[y]"] by simp
  show ?case by (rule rtrancl_trans[OF head tail])
qed

lemma lp_projection_arguments:
  assumes projection: "list_all2 (\<lambda>i a. i<length ts \<and> lp_iproject \<pi> (ts!i) a) indices us"
    and length: "length ts'=length ts"
    and local: "\<And>i a. i<length ts \<Longrightarrow> lp_iproject \<pi> (ts!i) a \<Longrightarrow>
      \<exists>b. lp_iproject \<pi> (ts'!i) b \<and> (a,b) \<in> (rstep S)\<^sup>*"
  obtains vs where "list_all2 (\<lambda>i b. i<length ts' \<and> lp_iproject \<pi> (ts'!i) b) indices vs"
    "list_all2 (\<lambda>a b. (a,b) \<in> (rstep S)\<^sup>*) us vs"
  using projection
proof (induct arbitrary: thesis rule: list_all2_induct)
  case Nil
  show ?case by (rule Nil.prems[of "[]"]) simp_all
next
  case (Cons i a indices us)
  obtain b where pb: "lp_iproject \<pi> (ts'!i) b" and ab: "(a,b) \<in> (rstep S)\<^sup>*"
    using local Cons.hyps(1) by blast
  obtain vs where pv: "list_all2 (\<lambda>i b. i<length ts' \<and> lp_iproject \<pi> (ts'!i) b) indices vs"
    and uv: "list_all2 (\<lambda>a b. (a,b) \<in> (rstep S)\<^sup>*) us vs"
    by (rule Cons.hyps(3)) blast
  show ?case by (rule Cons.prems[of "b#vs"]) (use Cons.hyps(1) pb ab pv uv length in auto)
qed

lemma lp_irewrite_projection:
  fixes R :: "('f,'v) trs" and a :: "('f,'v) term"
  assumes step: "(s,t) \<in> lp_irewrite R"
    and projection: "lp_iproject \<pi> s a"
    and vars: "\<And>l r. (l,r) \<in> R \<Longrightarrow> vars_term (af_term \<pi> r) \<subseteq> vars_term (af_term \<pi> l)"
  obtains b where "lp_iproject \<pi> t b" "(a,b) \<in> (rstep (af_rule \<pi> ` R))\<^sup>*"
  using step projection
proof (induct arbitrary: a thesis rule: lp_irewrite.induct)
  case (root l r \<rho>)
  obtain b where pb: "lp_iproject \<pi> (lp_ieval r \<rho>) b"
    and ab: "(a,b) \<in> rstep (af_rule \<pi> ` R)"
    by (rule lp_infinite_rule_projection[OF root.prems(2) vars[OF root.hyps] root.hyps]) blast
  show ?case by (rule root.prems(1)[OF pb r_into_rtrancl[OF ab]])
next
  case (arg i ts t f)
  let ?ts = "ts[i:=t]"
  have local: "\<And>j a. j<length ts \<Longrightarrow> lp_iproject \<pi> (ts!j) a \<Longrightarrow>
    \<exists>b. lp_iproject \<pi> (?ts!j) b \<and> (a,b) \<in> (rstep (af_rule \<pi> ` R))\<^sup>*"
  proof -
    fix j and a :: "('f,'v) term"
    assume j: "j<length ts" and pa: "lp_iproject \<pi> (ts!j) a"
    show "\<exists>b. lp_iproject \<pi> (?ts!j) b \<and> (a,b) \<in> (rstep (af_rule \<pi> ` R))\<^sup>*"
    proof (cases "j=i")
      case True
      obtain b where pb: "lp_iproject \<pi> t b" and ab: "(a,b) \<in> (rstep (af_rule \<pi> ` R))\<^sup>*"
        by (rule arg.hyps(3)[OF _ pa[unfolded True]]) blast
      show ?thesis using pb ab arg.hyps(1) True by auto
    next
      case False
      show ?thesis using pa False by auto
    qed
  qed
  show ?case
  proof (cases "afs \<pi> (f,length ts)")
    case (AFList indices)
    obtain us where au: "a=Fun f us"
      and pu: "list_all2 (\<lambda>j x. j<length ts \<and> lp_iproject \<pi> (ts!j) x) indices us"
      using arg.prems(2) AFList by (cases rule: lp_iproject.cases) auto
    obtain vs where pv: "list_all2 (\<lambda>j b. j<length ?ts \<and> lp_iproject \<pi> (?ts!j) b) indices vs"
      and uv: "list_all2 (\<lambda>a b. (a,b) \<in> (rstep (af_rule \<pi> ` R))\<^sup>*) us vs"
      by (rule lp_projection_arguments[OF pu _ local]) (auto)
    have pb: "lp_iproject \<pi> (LPIFun f ?ts) (Fun f vs)"
      by (rule lp_iproject.list[OF _ pv]) (use AFList in auto)
    have ab: "(a,Fun f vs) \<in> (rstep (af_rule \<pi> ` R))\<^sup>*"
      using lp_rsteps_arguments[OF uv, of f "[]"] au by simp
    show ?thesis by (rule arg.prems(1)[OF pb ab])
  next
    case (Collapse j)
    have bound: "j<length ts" and pj: "lp_iproject \<pi> (ts!j) a"
      using arg.prems(2) Collapse by (cases rule: lp_iproject.cases; auto)+
    obtain b where pb: "lp_iproject \<pi> (?ts!j) b" and ab: "(a,b) \<in> (rstep (af_rule \<pi> ` R))\<^sup>*"
      using local bound pj by blast
    have target: "lp_iproject \<pi> (LPIFun f ?ts) b"
      by (rule lp_iproject.collapse[OF _ _ pb]) (use Collapse bound in auto)
    show ?thesis by (rule arg.prems(1)[OF target ab])
  qed
qed

lemma lp_irewrites_projection:
  fixes R :: "('f,'v) trs" and a :: "('f,'v) term"
  assumes steps: "(s,t) \<in> (lp_irewrite R)\<^sup>*"
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
    by (rule lp_irewrite_projection[OF step.hyps(2) pb vars]) blast
  show ?case by (rule step.prems(1)[OF pc rtrancl_trans[OF ab bc]])
qed

text \<open>Projected infinite chains need not be minimal. In particular, one
  must not silently feed the filtered problem to a minimal-DP checker. This
  relation permits arbitrary infinite valuations; constructor restrictions can
  further reduce it when estimating the raw dependency graph.\<close>

definition lp_pi_chain :: "('f,'v) trs \<Rightarrow> ('f,'v) trs \<Rightarrow> 'f afs \<Rightarrow>
    (nat \<Rightarrow> ('f,'v) term) \<Rightarrow> (nat \<Rightarrow> ('f,'v) term) \<Rightarrow>
    (nat \<Rightarrow> 'v \<Rightarrow> ('f,'w) lp_iterm) \<Rightarrow> bool" where
  "lp_pi_chain D R \<pi> ls rs valuations = (\<forall>i::nat.
    (ls i,rs i) \<in> D \<and>
    (lp_ieval (rs i) (valuations i), lp_ieval (ls (Suc i)) (valuations (Suc i))) \<in> (lp_irewrite R)\<^sup>* \<and>
    (\<exists>a::('f,'v) term. lp_iproject \<pi> (lp_ieval (ls i) (valuations i)) a) \<and>
    (\<exists>b::('f,'v) term. lp_iproject \<pi> (lp_ieval (rs i) (valuations i)) b))"

theorem lp_pi_chain_filter:
  fixes D R :: "('f,'v) trs"
  assumes chain: "lp_pi_chain D R \<pi> ls rs valuations"
    and vars: "\<And>l r. (l,r) \<in> R \<Longrightarrow> vars_term (af_term \<pi> r) \<subseteq> vars_term (af_term \<pi> l)"
  shows "min_ichain (False,False,af_rule \<pi> ` D,{},{},{},af_rule \<pi> ` R)
    (\<lambda>i. af_term \<pi> (ls i)) (\<lambda>i. af_term \<pi> (rs i))
    (\<lambda>i x. lp_projection \<pi> (valuations i x))"
proof -
  let ?subst = "\<lambda>i x. (lp_projection \<pi> (valuations i x) :: ('f,'v) term)"
  have pair: "\<And>i. (af_term \<pi> (ls i),af_term \<pi> (rs i)) \<in> af_rule \<pi> ` D"
    using chain unfolding lp_pi_chain_def af_rule_alt_def by force
  have link: "\<And>i. (af_term \<pi> (rs i) \<cdot> ?subst i,
      af_term \<pi> (ls (Suc i)) \<cdot> ?subst (Suc i)) \<in> (rstep (af_rule \<pi> ` R))\<^sup>*"
  proof -
    fix i
    obtain a :: "('f,'v) term" where pa: "lp_iproject \<pi> (lp_ieval (rs i) (valuations i)) a"
      using chain unfolding lp_pi_chain_def by blast
    obtain b :: "('f,'v) term" where pb: "lp_iproject \<pi> (lp_ieval (ls (Suc i)) (valuations (Suc i))) b"
      using chain unfolding lp_pi_chain_def by blast
    have path: "(lp_ieval (rs i) (valuations i),lp_ieval (ls (Suc i)) (valuations (Suc i))) \<in> (lp_irewrite R)\<^sup>*"
      using chain unfolding lp_pi_chain_def by blast
    obtain c where pc: "lp_iproject \<pi> (lp_ieval (ls (Suc i)) (valuations (Suc i))) c"
      and ac: "(a,c) \<in> (rstep (af_rule \<pi> ` R))\<^sup>*"
      by (rule lp_irewrites_projection[OF path pa vars]) blast
    have cb: "c=b" by (rule lp_iproject_unique[OF pc pb])
    show "(af_term \<pi> (rs i) \<cdot> ?subst i,
      af_term \<pi> (ls (Suc i)) \<cdot> ?subst (Suc i)) \<in> (rstep (af_rule \<pi> ` R))\<^sup>*"
      using ac unfolding cb lp_iproject_ieval_inverse[OF pa] lp_iproject_ieval_inverse[OF pb] .
  qed
  show ?thesis using pair link by (simp add: ichain.simps NF_subst_def)
qed

corollary lp_pi_filter_processor:
  fixes D R :: "('f,'v) trs"
  assumes finite: "finite_dpp (False,False,af_rule \<pi> ` D,{},{},{},af_rule \<pi> ` R)"
    and vars: "\<And>l r. (l,r) \<in> R \<Longrightarrow> vars_term (af_term \<pi> r) \<subseteq> vars_term (af_term \<pi> l)"
  shows "\<not> lp_pi_chain D R \<pi> ls rs valuations"
proof
  assume chain: "lp_pi_chain D R \<pi> ls rs valuations"
  have converted: "min_ichain (False,False,af_rule \<pi> ` D,{},{},{},af_rule \<pi> ` R)
    (\<lambda>i. af_term \<pi> (ls i)) (\<lambda>i. af_term \<pi> (rs i))
    (\<lambda>i x. lp_projection \<pi> (valuations i x))"
    by (rule lp_pi_chain_filter[OF chain vars])
  show False using finite converted unfolding finite_dpp_def by blast
qed

end
