theory LP_PiDP_Graph
  imports LP_PiDP_Narrowing
begin

text \<open>Constructor-shape graph overapproximation before filtering. A
  variable is a wildcard, including an infinite or cyclic value. Thus this
  checker never removes an edge merely because a finite occurs check fails.\<close>

fun lp_shape where
  "lp_shape (Var x) s = True"
| "lp_shape (Fun f ps) s = (case s of LPIVar x \<Rightarrow> False
    | LPIFun g ts \<Rightarrow> f=g \<and> list_all2 lp_shape ps ts)"

fun lp_shape_cap where
  "lp_shape_cap D (Var x) = Var x"
| "lp_shape_cap D (Fun f ts) = (if f\<in>D then Var undefined
    else Fun f (map (lp_shape_cap D) ts))"

fun lp_shape_safe where
  "lp_shape_safe D (Var x) = True"
| "lp_shape_safe D (Fun f ts) = (f\<notin>D \<and> list_all (lp_shape_safe D) ts)"

fun lp_shapes_compatible where
  "lp_shapes_compatible (Var x) t = True"
| "lp_shapes_compatible (Fun f ss) (Var x) = True"
| "lp_shapes_compatible (Fun f ss) (Fun g ts) =
    (f=g \<and> list_all2 lp_shapes_compatible ss ts)"

lemma lp_shape_eval: "lp_shape t (lp_ieval t \<rho>)"
  by (induct t) (auto simp: list_all2_map2 list_all2_same)

lemma lp_shape_cap_safe: "lp_shape_safe D (lp_shape_cap D t)"
  by (induct t) (auto simp: list_all_iff)

lemma lp_shape_cap_match:
  "lp_shape t s \<Longrightarrow> lp_shape (lp_shape_cap D t) s"
  by (induct t arbitrary: s) (auto simp: list_all2_conv_all_nth split: lp_iterm.splits)

lemma lp_shape_subst:
  "lp_shape t s \<Longrightarrow> lp_shape t (lp_isubst s \<sigma>)"
  by (induct t arbitrary: s) (auto simp: list_all2_conv_all_nth split: lp_iterm.splits)

lemma lp_shape_compatible:
  assumes "lp_shape p s" "lp_shape q s"
  shows "lp_shapes_compatible p q"
  using assms
proof (induct p arbitrary: q s)
  case (Var x) then show ?case by simp
next
  case (Fun f ps)
  then show ?case by (cases q; cases s) (auto simp: list_all2_conv_all_nth)
qed

lemma lp_shape_rewrite:
  assumes step: "(s,t) \<in> lp_irewrite R"
    and match: "lp_shape p s" and safe: "lp_shape_safe D p"
    and roots: "\<And>l r. (l,r)\<in>R \<Longrightarrow> \<exists>f ts. l=Fun f ts \<and> f\<in>D"
  shows "lp_shape p t"
  using step match safe
proof (induct arbitrary: p rule: lp_irewrite.induct)
  case (root l r \<rho>)
  obtain f ts where l: "l=Fun f ts" and f: "f\<in>D"
    using roots[OF root.hyps] by blast
  show ?case using root.prems f unfolding l by (cases p) auto
next
  case (arg i ts t f)
  show ?case
  proof (cases p)
    case (Var x) then show ?thesis by simp
  next
    case (Fun g ps)
    have len: "length ps=length ts" and g: "g=f"
      and each: "\<And>j. j<length ps \<Longrightarrow> lp_shape (ps!j) (ts!j)"
      and safes: "\<And>j. j<length ps \<Longrightarrow> lp_shape_safe D (ps!j)"
      using arg.prems by (auto simp: Fun list_all2_conv_all_nth list_all_iff)
    have updated: "lp_shape (ps!i) t"
      by (rule arg.hyps(3)) (use each safes len arg.hyps(1) in auto)
    show ?thesis using updated each len g arg.hyps(1)
      by (auto simp: Fun list_all2_conv_all_nth nth_list_update)
  qed
qed

lemma lp_shape_links:
  assumes path: "(s,t) \<in> (lp_pi_link R)\<^sup>*"
    and match: "lp_shape p s" and safe: "lp_shape_safe D p"
    and roots: "\<And>l r. (l,r)\<in>R \<Longrightarrow> \<exists>f ts. l=Fun f ts \<and> f\<in>D"
  shows "lp_shape p t"
  using path match
proof (induct rule: rtrancl_induct)
  case base then show ?case .
next
  case (step y z)
  have py: "lp_shape p y" using step by blast
  show ?case
  proof (cases "(y,z)\<in>lp_irewrite R")
    case True
    show ?thesis by (rule lp_shape_rewrite[OF True py safe]) (rule roots)
  next
    case False
    obtain \<sigma> where "z=lp_isubst y \<sigma>"
      using step.hyps(2) False unfolding lp_pi_link_def by blast
    then show ?thesis using lp_shape_subst[OF py] by blast
  qed
qed

theorem lp_pi_graph_edge:
  assumes path: "(lp_ieval r \<rho>,lp_ieval l \<tau>) \<in> (lp_pi_link R)\<^sup>*"
    and roots: "\<And>l r. (l,r)\<in>R \<Longrightarrow> \<exists>f ts. l=Fun f ts \<and> f\<in>D"
  shows "lp_shapes_compatible (lp_shape_cap D r) l"
proof -
  have first: "lp_shape (lp_shape_cap D r) (lp_ieval r \<rho>)"
    by (rule lp_shape_cap_match[OF lp_shape_eval])
  have last: "lp_shape (lp_shape_cap D r) (lp_ieval l \<tau>)"
    by (rule lp_shape_links[OF path first lp_shape_cap_safe roots])
  show ?thesis by (rule lp_shape_compatible[OF last lp_shape_eval])
qed

lemma lp_nat_descent_stabilizes:
  fixes f :: "nat\<Rightarrow>nat"
  assumes descent: "\<And>i. f (Suc i) \<le> f i"
  obtains N where "\<And>i. f (N+i)=f N"
proof -
  let ?m = "LEAST m. \<exists>n. f n=m"
  have exists: "\<exists>n. f n=?m" by (rule LeastI[of _ "f 0"]) blast
  then obtain N where n: "f N=?m" by blast
  have lower: "\<And>i. f N\<le>f i" unfolding n by (rule Least_le) blast
  have upper: "\<And>i. f (N+i)\<le>f N"
  proof -
    fix i show "f (N+i)\<le>f N"
      by (induct i) (auto intro: order_trans[OF descent])
  qed
  have eq: "\<And>i. f (N+i)=f N"
  proof -
    fix i
    show "f (N+i)=f N" using lower[of "N+i"] upper[of i] by arith
  qed
  show ?thesis by (rule that[OF eq])
qed

theorem lp_pi_graph_decomposition:
  fixes P R :: "('f,'v) trs" and rank :: "('f,'v) rule \<Rightarrow> nat"
    and valuations :: "nat\<Rightarrow>'v\<Rightarrow>('f,'w) lp_iterm"
  assumes roots: "\<And>l r. (l,r)\<in>R \<Longrightarrow> \<exists>f ts. l=Fun f ts \<and> f\<in>D"
    and order: "\<And>l r l' r'. (l,r)\<in>P \<Longrightarrow> (l',r')\<in>P \<Longrightarrow>
      lp_shapes_compatible (lp_shape_cap D r) l' \<Longrightarrow> rank (l',r')\<le>rank (l,r)"
    and components: "\<And>k ls rs (valuations::nat\<Rightarrow>'v\<Rightarrow>('f,'w) lp_iterm).
      \<not> lp_pi_narrow_chain {p\<in>P. rank p=k} R \<pi> ls rs valuations"
  shows "\<not> lp_pi_narrow_chain P R \<pi> ls rs valuations"
proof
  assume chain: "lp_pi_narrow_chain P R \<pi> ls rs valuations"
  have member: "\<And>i. (ls i,rs i)\<in>P" using chain unfolding lp_pi_narrow_chain_def by blast
  have descent: "\<And>i. rank (ls (Suc i),rs (Suc i))\<le>rank (ls i,rs i)"
  proof -
    fix i
    have link: "(lp_ieval (rs i) (valuations i),lp_ieval (ls (Suc i)) (valuations (Suc i)))\<in>(lp_pi_link R)\<^sup>*"
      using chain unfolding lp_pi_narrow_chain_def by blast
    have edge: "lp_shapes_compatible (lp_shape_cap D (rs i)) (ls (Suc i))"
      by (rule lp_pi_graph_edge[OF link roots])
    show "rank (ls (Suc i),rs (Suc i))\<le>rank (ls i,rs i)"
      by (rule order[OF member member edge])
  qed
  obtain N where stable: "\<And>i. rank (ls (N+i),rs (N+i))=rank (ls N,rs N)"
    by (rule lp_nat_descent_stabilizes[where f="\<lambda>i. rank (ls i,rs i)", OF descent]) blast
  have suffix: "lp_pi_narrow_chain {p\<in>P. rank p=rank (ls N,rs N)} R \<pi>
    (\<lambda>i. ls (N+i)) (\<lambda>i. rs (N+i)) (\<lambda>i. valuations (N+i))"
    using chain stable unfolding lp_pi_narrow_chain_def by auto
  show False by (rule components[THEN notE, OF suffix])
qed

end
