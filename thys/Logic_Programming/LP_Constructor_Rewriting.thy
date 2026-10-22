theory LP_Constructor_Rewriting
  imports LP_Constructor_Values
begin

text \<open>Only actual source root steps use constructor valuations. Frames
  may contain unfinished calls, so they are deliberately not required to be
  constructor terms. This distinction is essential for Q-restricted links.\<close>

inductive_set lp_cactive :: "'f set \<Rightarrow> ('f,'v) trs \<Rightarrow> 'f set \<Rightarrow> ('f,'w) lp_iterm rel"
  for C R U where
  root: "(Fun f ts,r)\<in>R \<Longrightarrow>
    (\<And>t. t\<in>set ts \<Longrightarrow> funs_term t\<subseteq>C) \<Longrightarrow>
    (\<And>x. lp_constructor_value C (\<rho> x)) \<Longrightarrow>
    (lp_ieval (Fun f ts) \<rho>,lp_ieval r \<rho>)\<in>lp_cactive C R U"
| frame: "f\<in>U \<Longrightarrow> (s,t)\<in>lp_cactive C R U \<Longrightarrow>
    (LPIFun f (s#ss),LPIFun f (t#ss))\<in>lp_cactive C R U"

lemma lp_cactive_ordinary:
  "(s,t)\<in>lp_cactive C R U \<Longrightarrow> (s,t)\<in>lp_iactive R U"
  by (induct rule: lp_cactive.induct)
    (blast intro: lp_iactive.root, blast intro: lp_iactive.frame)

definition lp_constructor_lhs where
  "lp_constructor_lhs C l = (\<exists>f ts. l=Fun f ts \<and> (\<forall>t\<in>set ts. funs_term t\<subseteq>C))"

lemma lp_cactive_root:
  assumes rule: "(l,r)\<in>R" and shape: "lp_constructor_lhs C l"
    and vals: "\<And>x. lp_constructor_value C (\<rho> x)"
  shows "(lp_ieval l \<rho>,lp_ieval r \<rho>)\<in>lp_cactive C R U"
  using shape unfolding lp_constructor_lhs_def
  by (metis lp_cactive.root rule vals)

definition lp_clink where
  "lp_clink C R U = lp_cactive C R U \<union> {(s,t). \<exists>\<sigma>. t=lp_isubst s \<sigma>}"

lemma lp_clink_ordinary:
  "lp_clink C R U \<subseteq> lp_pi_link R"
  unfolding lp_clink_def lp_pi_link_def
  using lp_cactive_ordinary lp_iactive_irewrite by blast

context lp_filter
begin

lemma constructor_active_projection:
  fixes R :: "('f,'v) trs" and a :: "('f,'v) term"
  assumes st: "(s,t)\<in>lp_cactive C R U"
    and pr: "lp_iproject \<pi> s a"
    and vars: "\<And>l r. (l,r)\<in>R \<Longrightarrow> vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)"
    and roots: "\<And>q. q\<in>Q \<Longrightarrow> \<exists>f ts. q=Fun f ts \<and> f\<notin>C"
  obtains b where "lp_iproject \<pi> t b" "(a,b)\<in>qrstep False Q (af_rule \<pi> ` R)"
  using st pr
proof (induct arbitrary: a thesis rule: lp_cactive.induct)
  case (root f ts r \<rho>)
  show ?case
    by (rule lp_constructor_rule_qprojection[where Q=Q, OF root.hyps(1) root.prems(2)
      vars[OF root.hyps(1)] root.hyps(2,3) roots]) (auto intro: root.prems(1))
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
  obtain y where py: "lp_iproject \<pi> t y" and xy: "(x,y)\<in>qrstep False Q (af_rule \<pi> ` R)"
    by (rule frame.hyps(3)[OF _ px]) blast
  have target: "lp_iproject \<pi> (LPIFun f (t#ss)) (Fun f (y#xs))"
    by (rule lp_iproject.list) (use pi py tail in \<open>auto simp: list_all2_map1\<close>)
  have step: "(a,Fun f (y#xs))\<in>qrstep False Q (af_rule \<pi> ` R)"
    using qrstep.ctxt[OF xy, of "More f [] Hole xs"] by (simp add: a us)
  show ?case by (rule frame.prems(1)[OF target step])
qed

lemma constructor_link_projection:
  fixes R :: "('f,'v) trs" and a :: "('f,'v) term"
  assumes st: "(s,t)\<in>lp_clink C R U"
    and pr: "lp_iproject \<pi> s a"
    and vars: "\<And>l r. (l,r)\<in>R \<Longrightarrow> vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)"
    and roots: "\<And>q. q\<in>Q \<Longrightarrow> \<exists>f ts. q=Fun f ts \<and> f\<notin>C"
  obtains b where "lp_iproject \<pi> t b" "(a,b)\<in>(qrstep False Q (af_rule \<pi> ` R))\<^sup>*"
proof (cases "(s,t)\<in>lp_cactive C R U")
  case True
  show ?thesis by (rule constructor_active_projection[OF True pr vars roots])
    (auto intro: that)
next
  case False
  obtain \<sigma> where t: "t=lp_isubst s \<sigma>"
    using st False unfolding lp_clink_def by blast
  have pt: "lp_iproject \<pi> t a" unfolding t by (rule lp_iproject_subst[OF pr])
  show ?thesis by (rule that[OF pt]) simp
qed

lemma constructor_links_projection:
  fixes R :: "('f,'v) trs" and a :: "('f,'v) term"
  assumes st: "(s,t)\<in>(lp_clink C R U)\<^sup>*"
    and pr: "lp_iproject \<pi> s a"
    and vars: "\<And>l r. (l,r)\<in>R \<Longrightarrow> vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)"
    and roots: "\<And>q. q\<in>Q \<Longrightarrow> \<exists>f ts. q=Fun f ts \<and> f\<notin>C"
  obtains b where "lp_iproject \<pi> t b" "(a,b)\<in>(qrstep False Q (af_rule \<pi> ` R))\<^sup>*"
  using st pr
proof (induct arbitrary: thesis rule: rtrancl_induct)
  case base
  show ?case by (rule base.prems(1)[OF base.prems(2)]) simp
next
  case (step y z)
  obtain b where pb: "lp_iproject \<pi> y b" and ab: "(a,b)\<in>(qrstep False Q (af_rule \<pi> ` R))\<^sup>*"
    by (rule step.hyps(3)[OF _ step.prems(2)]) blast
  obtain c where pc: "lp_iproject \<pi> z c" and bc: "(b,c)\<in>(qrstep False Q (af_rule \<pi> ` R))\<^sup>*"
    by (rule constructor_link_projection[OF step.hyps(2) pb vars roots]) blast
  show ?case by (rule step.prems(1)[OF pc rtrancl_trans[OF ab bc]])
qed

end

definition lp_constructor_chain :: "'f set \<Rightarrow> ('f,'v) trs \<Rightarrow> ('f,'v) trs \<Rightarrow> 'f set \<Rightarrow> 'f afs \<Rightarrow>
    (nat \<Rightarrow> ('f,'v) term) \<Rightarrow> (nat \<Rightarrow> ('f,'v) term) \<Rightarrow>
    (nat \<Rightarrow> 'v \<Rightarrow> ('f,'w) lp_iterm) \<Rightarrow> bool" where
  "lp_constructor_chain C D R U \<pi> ls rs vals = (\<forall>i::nat.
    (ls i,rs i)\<in>D \<and> (\<forall>x. lp_constructor_value C (vals i x)) \<and>
    (lp_ieval (rs i) (vals i),lp_ieval (ls (Suc i)) (vals (Suc i)))\<in>(lp_clink C R U)\<^sup>* \<and>
    (\<exists>a::('f,'v) term. lp_iproject \<pi> (lp_ieval (ls i) (vals i)) a) \<and>
    (\<exists>b::('f,'v) term. lp_iproject \<pi> (lp_ieval (rs i) (vals i)) b))"

end
