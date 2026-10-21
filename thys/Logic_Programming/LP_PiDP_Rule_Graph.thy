theory LP_PiDP_Rule_Graph
  imports LP_PiDP_Graph
begin

text \<open>Rule-aware constructor shapes. A subterm is abstracted only if its
  already abstracted shape can match a rule left-hand side. Variables remain
  independent wildcards; no finite occurs check is assumed.\<close>

fun lp_rule_cap where
  "lp_rule_cap R (Var x) = Var x"
| "lp_rule_cap R (Fun f ts) =
    (let p = Fun f (map (lp_rule_cap R) ts) in
      if list_ex (\<lambda>lr. lp_shapes_compatible p (fst lr)) R
      then Var undefined else p)"

fun lp_rule_shape_safe where
  "lp_rule_shape_safe R (Var x) = True"
| "lp_rule_shape_safe R (Fun f ts) =
    (\<not> list_ex (\<lambda>lr. lp_shapes_compatible (Fun f ts) (fst lr)) R
      \<and> list_all (lp_rule_shape_safe R) ts)"

lemma lp_rule_cap_safe: "lp_rule_shape_safe R (lp_rule_cap R t)"
  by (induct t) (auto simp: Let_def list_all_iff)

lemma lp_rule_cap_match:
  "lp_shape t s \<Longrightarrow> lp_shape (lp_rule_cap R t) s"
  by (induct t arbitrary: s)
    (auto simp: Let_def list_all2_conv_all_nth split: lp_iterm.splits)

lemma lp_rule_shape_rewrite:
  assumes step: "(s,t) \<in> lp_irewrite (set R)"
    and match: "lp_shape p s" and safe: "lp_rule_shape_safe R p"
  shows "lp_shape p t"
  using step match safe
proof (induct arbitrary: p rule: lp_irewrite.induct)
  case (root l r \<rho>)
  have compatible: "lp_shapes_compatible p l"
    by (rule lp_shape_compatible[OF root.prems(1) lp_shape_eval])
  show ?case using root.prems(2) root.hyps compatible
    by (cases p) (auto simp: list_ex_iff)
next
  case (arg i ts t f)
  show ?case
  proof (cases p)
    case (Var x) then show ?thesis by simp
  next
    case (Fun g ps)
    have len: "length ps=length ts" and g: "g=f"
      and each: "\<And>j. j<length ps \<Longrightarrow> lp_shape (ps!j) (ts!j)"
      and safes: "\<And>j. j<length ps \<Longrightarrow> lp_rule_shape_safe R (ps!j)"
      using arg.prems by (auto simp: Fun list_all2_conv_all_nth list_all_iff)
    have updated: "lp_shape (ps!i) t"
      by (rule arg.hyps(3)) (use each safes len arg.hyps(1) in auto)
    show ?thesis using updated each len g arg.hyps(1)
      by (auto simp: Fun list_all2_conv_all_nth nth_list_update)
  qed
qed

lemma lp_rule_shape_links:
  assumes path: "(s,t) \<in> (lp_pi_link (set R))\<^sup>*"
    and match: "lp_shape p s" and safe: "lp_rule_shape_safe R p"
  shows "lp_shape p t"
  using path match
proof (induct rule: rtrancl_induct)
  case base then show ?case .
next
  case (step y z)
  have py: "lp_shape p y" using step by blast
  show ?case
  proof (cases "(y,z)\<in>lp_irewrite (set R)")
    case True
    show ?thesis by (rule lp_rule_shape_rewrite[OF True py safe])
  next
    case False
    obtain \<sigma> where "z=lp_isubst y \<sigma>"
      using step.hyps(2) False unfolding lp_pi_link_def by blast
    then show ?thesis using lp_shape_subst[OF py] by blast
  qed
qed

theorem lp_pi_rule_graph_edge:
  assumes path: "(lp_ieval r \<rho>,lp_ieval l \<tau>) \<in> (lp_pi_link (set R))\<^sup>*"
  shows "lp_shapes_compatible (lp_rule_cap R r) l"
proof -
  have first: "lp_shape (lp_rule_cap R r) (lp_ieval r \<rho>)"
    by (rule lp_rule_cap_match[OF lp_shape_eval])
  have last: "lp_shape (lp_rule_cap R r) (lp_ieval l \<tau>)"
    by (rule lp_rule_shape_links[OF path first lp_rule_cap_safe])
  show ?thesis by (rule lp_shape_compatible[OF last lp_shape_eval])
qed

theorem lp_pi_rule_graph_decomposition:
  fixes P :: "('f,'v) trs" and R :: "('f,'v) rule list"
    and rank :: "('f,'v) rule \<Rightarrow> nat"
    and valuations :: "nat\<Rightarrow>'v\<Rightarrow>('f,'w) lp_iterm"
  assumes order: "\<And>l r l' r'. (l,r)\<in>P \<Longrightarrow> (l',r')\<in>P \<Longrightarrow>
      lp_shapes_compatible (lp_rule_cap R r) l' \<Longrightarrow> rank (l',r')\<le>rank (l,r)"
    and components: "\<And>k ls rs (valuations::nat\<Rightarrow>'v\<Rightarrow>('f,'w) lp_iterm).
      \<not> lp_pi_narrow_chain {p\<in>P. rank p=k} (set R) \<pi> ls rs valuations"
  shows "\<not> lp_pi_narrow_chain P (set R) \<pi> ls rs valuations"
proof
  assume chain: "lp_pi_narrow_chain P (set R) \<pi> ls rs valuations"
  have member: "\<And>i. (ls i,rs i)\<in>P" using chain unfolding lp_pi_narrow_chain_def by blast
  have descent: "\<And>i. rank (ls (Suc i),rs (Suc i))\<le>rank (ls i,rs i)"
  proof -
    fix i
    have link: "(lp_ieval (rs i) (valuations i),lp_ieval (ls (Suc i)) (valuations (Suc i)))\<in>(lp_pi_link (set R))\<^sup>*"
      using chain unfolding lp_pi_narrow_chain_def by blast
    have edge: "lp_shapes_compatible (lp_rule_cap R (rs i)) (ls (Suc i))"
      by (rule lp_pi_rule_graph_edge[OF link])
    show "rank (ls (Suc i),rs (Suc i))\<le>rank (ls i,rs i)"
      by (rule order[OF member member edge])
  qed
  obtain N where stable: "\<And>i. rank (ls (N+i),rs (N+i))=rank (ls N,rs N)"
    by (rule lp_nat_descent_stabilizes[where f="\<lambda>i. rank (ls i,rs i)", OF descent]) blast
  have suffix: "lp_pi_narrow_chain {p\<in>P. rank p=rank (ls N,rs N)} (set R) \<pi>
    (\<lambda>i. ls (N+i)) (\<lambda>i. rs (N+i)) (\<lambda>i. valuations (N+i))"
    using chain stable unfolding lp_pi_narrow_chain_def by auto
  show False by (rule components[THEN notE, OF suffix])
qed

end
