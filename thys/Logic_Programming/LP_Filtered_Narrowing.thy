theory LP_Filtered_Narrowing
  imports "Proof_Checker.Ceta"
begin

hide_const (open) CPF_Proof_Parser.rstep
hide_const (open) CPF_Proof_Parser.afs

text \<open>
  Supporting lemma for TOCL'09 continuation machines, not yet an LP checker.
  Active rewriting is allowed at the root and down argument zero of continuation
  symbols. Narrowing additionally instantiates the entire source configuration.
  Groundness after filtering prevents that instantiation from changing the
  measured source term. The filter must preserve every active frame argument.
  Connecting source LD resolution to this machine is a separate obligation.
\<close>

inductive_set lp_active_step :: "('f,'v) trs \<Rightarrow> 'f set \<Rightarrow> ('f,'v) term rel"
  for R U where
  root: "(l,r) \<in> R \<Longrightarrow> (l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> lp_active_step R U"
| frame: "f \<in> U \<Longrightarrow> (s,t) \<in> lp_active_step R U \<Longrightarrow>
    (Fun f (s # ss), Fun f (t # ss)) \<in> lp_active_step R U"

definition lp_narrow_step where
  "lp_narrow_step R U = {(s,t). \<exists>\<sigma>. (s \<cdot> \<sigma>,t) \<in> lp_active_step R U}"

locale lp_filter =
  fixes \<pi> :: "'f afs" and U :: "'f set"
  assumes active: "\<And>f n. f \<in> U \<Longrightarrow>
    \<exists>is. afs \<pi> (f,Suc n) = AFList (0 # map Suc is) \<and> set is \<subseteq> {0..<n}"
begin

lemma active_filter_step:
  assumes "(s,t) \<in> lp_active_step R U"
  shows "(af_term \<pi> s,af_term \<pi> t) \<in> rstep (af_rule \<pi> ` R)"
  using assms
proof (induct rule: lp_active_step.induct)
  case (root l r \<sigma>)
  have rule: "(af_term \<pi> l,af_term \<pi> r) \<in> af_rule \<pi> ` R"
    using imageI[OF root, of "af_rule \<pi>"] by (simp add: af_rule_alt_def)
  show ?case using rstep_subst[OF rstep_rule[OF rule], of "\<lambda>x. af_term \<pi> (\<sigma> x)"]
    by (simp add: af_subst)
next
  case (frame f s t ss)
  obtain indices where pi: "afs \<pi> (f,Suc (length ss)) = AFList (0 # map Suc indices)"
    and valid: "set indices \<subseteq> {0..<length ss}"
    using active[OF frame(1), of "length ss"] by blast
  let ?tail = "map (\<lambda>i. af_term \<pi> (ss ! i)) indices"
  have left: "af_term \<pi> (Fun f (s#ss)) = Fun f (af_term \<pi> s # ?tail)"
    using valid by (auto simp: pi o_def intro!: map_cong)
  have right: "af_term \<pi> (Fun f (t#ss)) = Fun f (af_term \<pi> t # ?tail)"
    using valid by (auto simp: pi o_def intro!: map_cong)
  show ?case unfolding left right
    using rstep_ctxt[OF frame(3), of "More f [] Hole ?tail"] by simp
qed

lemma filtered_narrow_step:
  assumes gr: "ground (af_term \<pi> s)" and step: "(s,t) \<in> lp_narrow_step R U"
  shows "(af_term \<pi> s,af_term \<pi> t) \<in> rstep (af_rule \<pi> ` R)"
proof -
  obtain \<sigma> where st: "(s \<cdot> \<sigma>,t) \<in> lp_active_step R U"
    using step unfolding lp_narrow_step_def by blast
  have "af_term \<pi> (s \<cdot> \<sigma>) = af_term \<pi> s"
    using gr by (simp add: af_subst ground_subst_apply)
  with active_filter_step[OF st] show ?thesis by simp
qed

theorem filtered_narrowing_terminates:
  assumes sn: "SN (rstep (af_rule \<pi> ` R))"
    and vars: "\<And>l r. (l,r) \<in> af_rule \<pi> ` R \<Longrightarrow> vars_term r \<subseteq> vars_term l"
    and gr: "ground (af_term \<pi> s)"
  shows "SN_on (lp_narrow_step R U) {s}"
proof (rule SN_onI)
  fix f assume start: "f 0 \<in> {s}" and seq: "chain (lp_narrow_step R U) f"
  have step: "\<And>n. (f n,f (Suc n)) \<in> lp_narrow_step R U"
    using seq unfolding chain_def by blast
  have ground: "\<And>n. ground (af_term \<pi> (f n))"
  proof -
    fix n show "ground (af_term \<pi> (f n))"
    proof (induct n)
      case 0 show ?case using gr start by simp
    next
      case (Suc n)
      show ?case by (rule rstep_ground[OF vars Suc filtered_narrow_step[OF Suc step]])
    qed
  qed
  have projected: "chain (rstep (af_rule \<pi> ` R)) (\<lambda>n. af_term \<pi> (f n))"
    unfolding chain_def
    by (intro allI, rule filtered_narrow_step, rule ground, rule step)
  have exists_chain: "\<exists>g. g 0 \<in> UNIV \<and> chain (rstep (af_rule \<pi> ` R)) g"
    by (rule exI[where x="\<lambda>n. af_term \<pi> (f n)"], rule conjI, rule UNIV_I, rule projected)
  from sn exists_chain show False unfolding SN_on_def by contradiction
qed

end
end
