theory LP_Constructor_QDP
  imports LP_Constructor_Chain
begin

context lp_filter
begin

theorem constructor_chain_qdp:
  fixes D R :: "('f,'v) trs"
  assumes chain: "lp_constructor_chain C D R U \<pi> ls rs vals"
    and vars: "\<And>l r. (l,r)\<in>R \<Longrightarrow> vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)"
    and pairs: "\<And>l r. (l,r)\<in>D \<Longrightarrow> funs_term l\<subseteq>C"
    and roots: "\<And>q. q\<in>Q \<Longrightarrow> \<exists>f ts. q=Fun f ts \<and> f\<notin>C"
  shows "min_ichain (False,False,af_rule \<pi> ` D,{},Q,{},af_rule \<pi> ` R)
    (\<lambda>i. af_term \<pi> (ls i)) (\<lambda>i. af_term \<pi> (rs i))
    (\<lambda>i x. lp_projection \<pi> (vals i x))"
proof -
  let ?subst = "\<lambda>i x. (lp_projection \<pi> (vals i x) :: ('f,'v) term)"
  have pair: "\<And>i. (ls i,rs i)\<in>D"
    and valuesC: "\<And>i x. lp_constructor_value C (vals i x)"
    using chain unfolding lp_constructor_chain_def by blast+
  have filtered: "\<And>i. (af_term \<pi> (ls i),af_term \<pi> (rs i))\<in>af_rule \<pi> ` D"
    using pair unfolding af_rule_alt_def by force
  have link: "\<And>i. (af_term \<pi> (rs i)\<cdot>?subst i,
      af_term \<pi> (ls (Suc i))\<cdot>?subst (Suc i))\<in>(qrstep False Q (af_rule \<pi> ` R))\<^sup>*"
  proof -
    fix i
    obtain a :: "('f,'v) term" where pa: "lp_iproject \<pi> (lp_ieval (rs i) (vals i)) a"
      using chain unfolding lp_constructor_chain_def by blast
    obtain b :: "('f,'v) term" where pb: "lp_iproject \<pi> (lp_ieval (ls (Suc i)) (vals (Suc i))) b"
      using chain unfolding lp_constructor_chain_def by blast
    have path: "(lp_ieval (rs i) (vals i),lp_ieval (ls (Suc i)) (vals (Suc i)))\<in>(lp_clink C R U)\<^sup>*"
      using chain unfolding lp_constructor_chain_def by blast
    obtain c where pc: "lp_iproject \<pi> (lp_ieval (ls (Suc i)) (vals (Suc i))) c"
      and ac: "(a,c)\<in>(qrstep False Q (af_rule \<pi> ` R))\<^sup>*"
      by (rule constructor_links_projection[OF path pa vars roots]) blast
    have cb: "c=b" by (rule lp_iproject_unique[OF pc pb])
    show "(af_term \<pi> (rs i)\<cdot>?subst i,af_term \<pi> (ls (Suc i))\<cdot>?subst (Suc i))\<in>(qrstep False Q (af_rule \<pi> ` R))\<^sup>*"
      using ac unfolding cb lp_iproject_ieval_inverse[OF pa] lp_iproject_ieval_inverse[OF pb] .
  qed
  have normal: "\<And>i. af_term \<pi> (ls i)\<cdot>?subst i\<in>NF_terms Q"
  proof -
    fix i
    obtain a :: "('f,'v) term" where pa: "lp_iproject \<pi> (lp_ieval (ls i) (vals i)) a"
      using chain unfolding lp_constructor_chain_def by blast
    have valueC: "lp_constructor_value C (lp_ieval (ls i) (vals i))"
      by (rule lp_constructor_value_eval[OF pairs[OF pair] valuesC])
    have "a\<in>NF_terms Q" by (rule lp_constructor_projection_nf[OF pa valueC roots])
    then show "af_term \<pi> (ls i)\<cdot>?subst i\<in>NF_terms Q"
      unfolding lp_iproject_ieval_inverse[OF pa] .
  qed
  show ?thesis using filtered link normal by (simp add: ichain.simps NF_subst_def)
qed

end

context lp_translation
begin

theorem constructor_qdp_source_termination:
  fixes query :: "('f,'w) lp_iatom" and a :: "('f,'v) term"
  assumes fixed: "lp_data_fixed_program data P" and range: "range data\<subseteq>C"
    and shapes: "\<And>l r. (l,r)\<in>set translated \<Longrightarrow> lp_constructor_lhs C l"
    and frames: "\<And>c i. u c i\<in>U" and marked: "\<And>c i. sharp (u c i)\<in>U"
    and filter: "lp_filter \<pi> U"
    and measured: "lp_iproject \<pi> (mencode sharp (lp_data_config data (LPICall query))) a"
    and rv: "\<And>l r. (l,r)\<in>set translated \<Longrightarrow> vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)"
    and dv: "\<And>l r. (l,r)\<in>set (pi_pairs sharp) \<Longrightarrow> vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)"
    and pairs: "\<And>l r. (l,r)\<in>set (pi_pairs sharp) \<Longrightarrow> funs_term l\<subseteq>C"
    and roots: "\<And>q. q\<in>Q \<Longrightarrow> \<exists>f ts. q=Fun f ts \<and> f\<notin>C"
    and finite: "finite_dpp (False,False,af_rule \<pi> ` set (pi_pairs sharp),{},Q,{},af_rule \<pi> ` set translated)"
  shows "SN_on (lp_ild P) {[query]}"
proof -
  interpret lp_filter \<pi> U by (rule filter)
  have machine: "SN_on (lp_imachine P) {LPICall query}"
  proof (rule ccontr)
    assume "\<not>SN_on (lp_imachine P) {LPICall query}"
    then have min: "lp_iminimal P (LPICall query)" unfolding lp_iminimal_def by simp
    obtain ls rs and vals :: "nat\<Rightarrow>'v\<Rightarrow>('f,'w) lp_iterm" where chain:
      "lp_constructor_chain C (set (pi_pairs sharp)) (set translated) U \<pi> ls rs vals"
      using source_to_constructor_chain[where sharp=sharp, OF fixed range _ frames marked min measured]
        shapes rv dv by blast
    have qchain: "min_ichain (False,False,af_rule \<pi> ` set (pi_pairs sharp),{},Q,{},af_rule \<pi> ` set translated)
      (\<lambda>i. af_term \<pi> (ls i)) (\<lambda>i. af_term \<pi> (rs i))
      (\<lambda>i x. (lp_projection \<pi> (vals i x)::('f,'v) term))"
      apply (rule constructor_chain_qdp[OF chain])
      apply (rule rv, assumption)
      apply (rule pairs, assumption)
      apply (rule roots, assumption)
      done
    show False using qchain finite unfolding finite_dpp_def by blast
  qed
  show ?thesis using lp_imachine_implies_ld_termination[OF machine] by simp
qed

end
end
