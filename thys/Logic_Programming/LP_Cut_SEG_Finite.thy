theory LP_Cut_SEG_Finite
  imports LP_Cut_SEG_Measure LP_Residual_Roles
begin

text \<open>Only measured values must be finite. Other source variables may
still denote non-ground or rational trees. The no-extra-variables condition on
each extracted rule is essential: finiteness of its left-hand side must cover
every variable used on the right. Normality is kept as a separate obligation
for the innermost/Q-restricted residual.\<close>

definition lpc_seg_finite_value :: "('f,string) lp_iterm \<Rightarrow> ('f,string) term" where
  "lpc_seg_finite_value v = (THE t. lp_ieval t LPIVar=v)"

lemma lpc_seg_finite_value_eval:
  "lpc_seg_finite_value (lp_ieval t LPIVar) = t"
  unfolding lpc_seg_finite_value_def by (rule the_equality) (auto intro: lp_seg_ieval_injective)

lemma lpc_seg_finite_value_sound:
  fixes v :: "('f,string) lp_iterm"
  assumes finite: "lp_seg_ground v"
  shows "lp_ieval (lpc_seg_finite_value v) LPIVar = v"
proof -
  obtain t :: "('f,string) term" where t: "lp_ieval t LPIVar = v"
    using lp_seg_ground_finite[OF finite] by blast
  show ?thesis by (simp only: t[symmetric] lpc_seg_finite_value_eval)
qed

lemma lpc_seg_finite_value_fun:
  assumes finite: "list_all lp_seg_ground vs"
  shows "lpc_seg_finite_value (LPIFun f vs) = Fun f (map lpc_seg_finite_value vs)"
proof -
  have inverse: "lp_ieval (lpc_seg_finite_value v) LPIVar = v" if "v\<in>set vs" for v
    by (rule lpc_seg_finite_value_sound) (use finite that in \<open>auto simp: list_all_iff\<close>)
  have equal: "lp_ieval (Fun f (map lpc_seg_finite_value vs)) LPIVar = LPIFun f vs"
    by (simp add: map_map inverse cong: map_cong)
  show ?thesis by (simp only: equal[symmetric] lpc_seg_finite_value_eval)
qed

lemma lpc_seg_ground_map:
  "lp_seg_ground v \<Longrightarrow> lp_seg_ground (map_lp_iterm d id v)"
  by (induct rule: lp_seg_ground.induct) (auto simp: list_all_iff)

lemma lpc_seg_finite_value_map:
  assumes finite: "lp_seg_ground v"
  shows "lpc_seg_finite_value (map_lp_iterm d id v) =
    map_term d id (lpc_seg_finite_value v)"
proof -
  have equal: "map_lp_iterm d id v =
      lp_ieval (map_term d id (lpc_seg_finite_value v)) LPIVar"
    using lp_signature_eval[of d "lpc_seg_finite_value v" LPIVar]
      lpc_seg_finite_value_sound[OF finite] by simp
  show ?thesis by (simp only: equal lpc_seg_finite_value_eval)
qed

text \<open>All source constructors, including constructors not mentioned in
the program, are mapped into a disjoint data signature. Freshness only against
the finite program signature would not justify innermost root steps.\<close>

lemma lpc_seg_encoded_data_normal:
  assumes finite: "lp_seg_ground v"
    and range: "range d \<subseteq> C"
    and roots: "\<And>q. q\<in>Q \<Longrightarrow> \<exists>f ts. q=Fun f ts \<and> f\<notin>C"
  shows "lpc_seg_finite_value (map_lp_iterm d id v)\<in>NF_terms Q"
proof (rule lp_constructor_finite_nf[OF _ roots])
  have symbols: "funs_term (map_term d id t) \<subseteq> C" for t
    using range by (induct t) auto
  show "funs_term (lpc_seg_finite_value (map_lp_iterm d id v)) \<subseteq> C"
    unfolding lpc_seg_finite_value_map[OF finite]
    by (rule symbols)
qed

lemma lpc_seg_finite_root:
  fixes eta :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes rule: "(l,r)\<in>R"
    and variables: "vars_term r \<subseteq> vars_term l"
    and measured: "lp_ieval t LPIVar = lp_ieval l eta"
    and finite: "lp_seg_ground (lp_ieval l eta)"
    and normal: "\<forall>s\<lhd>t. s\<in>NF_terms Q"
  shows "\<exists>u. (t,u)\<in>qrstep False Q R \<and> lp_ieval u LPIVar = lp_ieval r eta"
proof -
  have groundvals: "\<forall>x\<in>vars_term l. lp_seg_ground (eta x)"
    using finite by (simp add: lp_seg_ground_eval)
  obtain sigma where sigma: "\<forall>x\<in>vars_term l. lp_ieval (sigma x) LPIVar=eta x"
    using lp_seg_finite_valuation[OF groundvals] by blast
  have lhs: "lp_ieval (l\<cdot>sigma) LPIVar = lp_ieval l eta"
    unfolding lp_ieval_finite_subst by (rule lp_ieval_cong) (use sigma in auto)
  have rhs: "lp_ieval (r\<cdot>sigma) LPIVar = lp_ieval r eta"
    unfolding lp_ieval_finite_subst by (rule lp_ieval_cong) (use sigma variables in auto)
  have t: "t=l\<cdot>sigma" by (rule lp_seg_ieval_injective) (use measured lhs in simp)
  have step: "(t,r\<cdot>sigma)\<in>qrstep False Q R"
    unfolding t by (rule lpc_seg_restricted_root[OF rule]) (use normal t in simp)
  show ?thesis using step rhs by blast
qed

lemma lpc_seg_finite_root_values:
  fixes eta :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes rule: "(l,r)\<in>R"
    and variables: "vars_term r \<subseteq> vars_term l"
    and finite: "lp_seg_ground (lp_ieval l eta)"
    and normal: "\<forall>s\<lhd>lpc_seg_finite_value (lp_ieval l eta). s\<in>NF_terms Q"
  shows "(lpc_seg_finite_value (lp_ieval l eta),lpc_seg_finite_value (lp_ieval r eta))\<in>qrstep False Q R"
proof -
  have measured: "lp_ieval (lpc_seg_finite_value (lp_ieval l eta)) LPIVar = lp_ieval l eta"
    by (rule lpc_seg_finite_value_sound[OF finite])
  obtain u where step: "(lpc_seg_finite_value (lp_ieval l eta),u)\<in>qrstep False Q R"
    and target: "lp_ieval u LPIVar = lp_ieval r eta"
    using lpc_seg_finite_root[OF rule variables measured finite normal] by blast
  show ?thesis using step by (simp only: target[symmetric] lpc_seg_finite_value_eval)
qed

lemma lpc_seg_constructor_finite_symbols:
  assumes finite: "lp_seg_ground v"
    and constructor: "lp_constructor_value C v"
  shows "funs_term (lpc_seg_finite_value v) \<subseteq> C"
proof -
  have evaluated: "lp_constructor_value C (lp_ieval (lpc_seg_finite_value v) LPIVar)"
    using constructor by (simp only: lpc_seg_finite_value_sound[OF finite])
  have symbols: "lp_constructor_value C (lp_ieval t LPIVar) \<Longrightarrow> funs_term t \<subseteq> C" for t
    by (induct t) (auto simp: lp_constructor_value_Fun list_all_iff)
  show ?thesis by (rule symbols[OF evaluated])
qed

theorem lpc_seg_constructor_root:
  fixes eta :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes rule: "(Fun f ts,r)\<in>R"
    and variables: "vars_term r \<subseteq> vars_term (Fun f ts)"
    and finite: "lp_seg_ground (lp_ieval (Fun f ts) eta)"
    and symbols: "\<And>t. t\<in>set ts \<Longrightarrow> funs_term t \<subseteq> C"
    and vals: "\<And>x. lp_constructor_value C (eta x)"
    and roots: "\<And>q. q\<in>Q \<Longrightarrow> \<exists>g us. q=Fun g us \<and> g\<notin>C"
  shows "(lpc_seg_finite_value (lp_ieval (Fun f ts) eta),
    lpc_seg_finite_value (lp_ieval r eta))\<in>qrstep False Q R"
proof (rule lpc_seg_finite_root_values[OF rule variables finite])
  have finite_args: "\<And>t. t\<in>set ts \<Longrightarrow> lp_seg_ground (lp_ieval t eta)"
    using finite by (simp add: list_all_iff)
  have constructor_args: "\<And>t. t\<in>set ts \<Longrightarrow> lp_constructor_value C (lp_ieval t eta)"
    by (rule lp_constructor_value_eval[OF symbols vals])
  have args_symbols: "\<And>t. t\<in>set ts \<Longrightarrow>
    funs_term (lpc_seg_finite_value (lp_ieval t eta)) \<subseteq> C"
    by (rule lpc_seg_constructor_finite_symbols[OF finite_args constructor_args])
  have equal: "lpc_seg_finite_value (lp_ieval (Fun f ts) eta) =
    Fun f (map (\<lambda>t. lpc_seg_finite_value (lp_ieval t eta)) ts)"
  proof -
    have eval: "lp_ieval (Fun f (map (\<lambda>t. lpc_seg_finite_value (lp_ieval t eta)) ts)) LPIVar =
      lp_ieval (Fun f ts) eta"
      using lpc_seg_finite_value_sound[OF finite_args] by (simp add: map_map cong: map_cong)
    show ?thesis by (simp only: eval[symmetric] lpc_seg_finite_value_eval)
  qed
  show "\<forall>s\<lhd>lpc_seg_finite_value (lp_ieval (Fun f ts) eta). s\<in>NF_terms Q"
  proof (intro allI impI)
    fix s assume proper: "s\<lhd>lpc_seg_finite_value (lp_ieval (Fun f ts) eta)"
    obtain t where member: "t\<in>set ts"
      and below: "lpc_seg_finite_value (lp_ieval t eta) \<unrhd> s"
      using supt_Fun_imp_arg_supteq[OF proper[unfolded equal]] by auto
    have symbols: "funs_term s \<subseteq> C"
      by (rule subset_trans[OF supteq_imp_funs_term_subset[OF below] args_symbols[OF member]])
    show "s\<in>NF_terms Q" by (rule lp_constructor_finite_nf[OF symbols roots])
  qed
qed

end
