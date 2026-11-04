theory LP_Dependency_Triple_Constructor_Chain
  imports LP_Dependency_Triple_Constructor_Simulation LP_Constructor_QDP
begin

lemma lp_clinks_pi:
  assumes path: "(s,t)\<in>(lp_clink C R U)\<^sup>*"
  shows "(s,t)\<in>(lp_pi_link R)\<^sup>*"
  using path
proof (induct rule: rtrancl_induct)
  case base then show ?case by simp
next
  case (step y z)
  have edge: "(y,z)\<in>lp_pi_link R"
    using lp_clink_ordinary[where C=C and R=R and U=U] step.hyps(2) by blast
  show ?case by (rule rtrancl_into_rtrancl[OF step.hyps(3) edge])
qed

context lp_triple_translation
begin

lemma dt_constructor_next_pair:
  fixes a :: "('f,'v) term"
  assumes bad: "\<not> SN_on (dt_constructor_step C U) {s}" and projection: "lp_iproject \<pi> s a"
    and rv: "\<And>l r. (l,r)\<in>set dt_support \<Longrightarrow>
      vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)"
    and dv: "\<And>l r. (l,r)\<in>set dt_pairs \<Longrightarrow>
      vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)"
  obtains l r \<rho> t where "(l,r)\<in>set dt_pairs"
    "\<forall>x. lp_constructor_value C (\<rho> x)"
    "(s,lp_ieval l \<rho>)\<in>(lp_clink C (set dt_support) U)\<^sup>*"
    "(lp_ieval r \<rho>,t)\<in>(lp_clink C (set dt_support) U)\<^sup>*"
    "\<not> SN_on (dt_constructor_step C U) {t}"
    "\<exists>b::('f,'v) term. lp_iproject \<pi> (lp_ieval l \<rho>) b"
    "\<exists>b::('f,'v) term. lp_iproject \<pi> (lp_ieval r \<rho>) b"
proof -
  have successor: "\<exists>t. (s,t)\<in>(dt_constructor_step C U) \<and> \<not>SN_on (dt_constructor_step C U) {t}"
  proof (rule ccontr)
    assume none: "\<not>(\<exists>t. (s,t)\<in>(dt_constructor_step C U) \<and> \<not>SN_on (dt_constructor_step C U) {t})"
    have "SN_on (dt_constructor_step C U) {s}" by (rule step_reflects_SN_on) (use none in blast)
    with bad show False by contradiction
  qed
  obtain t where st: "(s,t)\<in>(dt_constructor_step C U)" and bt: "\<not> SN_on (dt_constructor_step C U) {t}"
    using successor by blast
  obtain l r \<rho> where pair: "(l,r)\<in>set dt_pairs"
    and valsC: "\<forall>x. lp_constructor_value C (\<rho> x)"
    and before: "(s,lp_ieval l \<rho>)\<in>(lp_clink C (set dt_support) U)\<^sup>*"
    and after: "(lp_ieval r \<rho>,t)\<in>(lp_clink C (set dt_support) U)\<^sup>*"
    using st unfolding dt_constructor_step_def dt_constructor_strict_def by blast
  obtain b :: "('f,'v) term" where pb: "lp_iproject \<pi> (lp_ieval l \<rho>) b"
    by (rule lp_pi_links_projection[OF lp_clinks_pi[OF before] projection rv]) blast
  obtain c :: "('f,'v) term" where pc: "lp_iproject \<pi> (lp_ieval r \<rho>) c"
    by (rule lp_infinite_rule_projection[OF pb dv[OF pair] pair]) blast
  show thesis by (rule that[OF pair valsC before after bt]) (use pb pc in blast)+
qed

theorem dt_constructor_nontermination_to_chain:
  fixes s :: "('f,'w) lp_iterm" and a :: "('f,'v) term"
  assumes bad: "\<not> SN_on (dt_constructor_step C U) {s}" and projection: "lp_iproject \<pi> s a"
    and rv: "\<And>l r. (l,r)\<in>set dt_support \<Longrightarrow>
      vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)"
    and dv: "\<And>l r. (l,r)\<in>set dt_pairs \<Longrightarrow>
      vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)"
  shows "\<exists>ls rs (valuations::nat\<Rightarrow>'v\<Rightarrow>('f,'w) lp_iterm).
    lp_constructor_chain C (set dt_pairs) (set dt_support) U \<pi> ls rs valuations"
proof -
  let ?good = "\<lambda>(l,r,(\<rho>::'v\<Rightarrow>('f,'w) lp_iterm),t).
    (l,r)\<in>set dt_pairs \<and> (\<forall>x. lp_constructor_value C (\<rho> x)) \<and>
    (lp_ieval r \<rho>,t)\<in>(lp_clink C (set dt_support) U)\<^sup>* \<and>
    \<not> SN_on (dt_constructor_step C U) {t} \<and>
    (\<exists>b::('f,'v) term. lp_iproject \<pi> (lp_ieval l \<rho>) b) \<and>
    (\<exists>b::('f,'v) term. lp_iproject \<pi> (lp_ieval r \<rho>) b)"
  let ?edge = "\<lambda>(l,r,\<rho>,t) (l',r',\<rho>',t').
    (lp_ieval r \<rho>,lp_ieval l' \<rho>')\<in>(lp_clink C (set dt_support) U)\<^sup>*"
  have initial: "\<exists>z::('f,'v) term \<times> ('f,'v) term \<times>
      ('v\<Rightarrow>('f,'w) lp_iterm) \<times> ('f,'w) lp_iterm. ?good z"
  proof -
    obtain l r and \<rho> :: "'v\<Rightarrow>('f,'w) lp_iterm" and t
      where good: "?good (l,r,\<rho>,t)"
      by (rule dt_constructor_next_pair[OF bad projection rv dv]) auto
    show ?thesis by (rule exI[of _ "(l,r,\<rho>,t)"]) (rule good)
  qed
  have progress: "\<And>z. ?good z \<Longrightarrow> \<exists>z'. ?good z' \<and> ?edge z z'"
  proof -
    fix z :: "('f,'v) term \<times> ('f,'v) term \<times>
      ('v\<Rightarrow>('f,'w) lp_iterm) \<times> ('f,'w) lp_iterm"
    assume good: "?good z"
    obtain l r \<rho> t where z: "z=(l,r,\<rho>,t)" by (cases z) auto
    have bt: "\<not> SN_on (dt_constructor_step C U) {t}"
      and after: "(lp_ieval r \<rho>,t)\<in>(lp_clink C (set dt_support) U)\<^sup>*"
      using good by (simp_all add: z)
    obtain b :: "('f,'v) term" where pb: "lp_iproject \<pi> (lp_ieval r \<rho>) b"
      using good by (auto simp: z)
    obtain c :: "('f,'v) term" where pc: "lp_iproject \<pi> t c"
      by (rule lp_pi_links_projection[OF lp_clinks_pi[OF after] pb rv]) blast
    obtain l' r' \<rho>' t' where next_good: "?good (l',r',\<rho>',t')"
      and before: "(t,lp_ieval l' \<rho>')\<in>(lp_clink C (set dt_support) U)\<^sup>*"
      by (rule dt_constructor_next_pair[OF bt pc rv dv]) auto
    have edge: "?edge z (l',r',\<rho>',t')"
      using rtrancl_trans[OF after before] by (simp add: z)
    show "\<exists>z'. ?good z' \<and> ?edge z z'" using next_good edge by blast
  qed
  obtain z where sequence: "\<forall>i::nat. ?good (z i) \<and> ?edge (z i) (z (Suc i))"
    using dependent_nat_choice[where P="\<lambda>n z. ?good z" and Q="\<lambda>n z z'. ?edge z z'",
      OF initial progress] by blast
  let ?ls = "\<lambda>i. fst (z i)"
  let ?rs = "\<lambda>i. fst (snd (z i))"
  let ?vals = "\<lambda>i. fst (snd (snd (z i)))"
  have chain: "lp_constructor_chain C (set dt_pairs) (set dt_support) U \<pi> ?ls ?rs ?vals"
    using sequence by (auto simp: lp_constructor_chain_def case_prod_beta)
  show ?thesis by (intro exI[of _ ?ls] exI[of _ ?rs] exI[of _ ?vals]) (rule chain)
qed

theorem dt_constructor_chains_imply_triple_termination:
  fixes query :: "('f,'w) lp_iatom" and a :: "('f,'v) term"
  assumes fixed: "lp_data_fixed_program data P" and range: "range data\<subseteq>C"
    and shapes: "\<And>l r. (l,r)\<in>set (lp_translation.translated P inp out pu) \<Longrightarrow> lp_constructor_lhs C l"
    and frames: "\<And>c i. pu c i\<in>U" and marked: "\<And>c i. sharp (du c i)\<in>U"
    and triples: "\<And>h ps goal. (h,ps,goal)\<in>set D \<Longrightarrow>
      lp_data_fixed_atom data h \<and> list_all (lp_data_fixed_atom data) ps \<and>
      lp_data_fixed_atom data goal"
    and no_chain: "\<And>ls rs (vals::nat\<Rightarrow>'v\<Rightarrow>('f,'w) lp_iterm).
      \<not>lp_constructor_chain C (set dt_pairs) (set dt_support) U \<pi> ls rs vals"
    and projection: "lp_iproject \<pi> (lp_itag (sharp \<circ> inp) (lp_data_atom data query)) a"
    and rv: "\<And>l r. (l,r)\<in>set dt_support \<Longrightarrow>
      vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)"
    and dv: "\<And>l r. (l,r)\<in>set dt_pairs \<Longrightarrow>
      vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)"
  shows "SN_on (lp_triple_calls (set D) P) {query}"
proof -
  have sn: "SN_on (dt_constructor_step C U) {lp_itag (sharp \<circ> inp) (lp_data_atom data query)}"
    using dt_constructor_nontermination_to_chain[OF _ projection rv dv] no_chain by blast
  have reflection: "\<forall>q::('f,'w) lp_iatom. lp_itag (sharp \<circ> inp) (lp_data_atom data query) = lp_itag (sharp \<circ> inp) (lp_data_atom data q)
    \<longrightarrow> SN_on (lp_triple_calls (set D) P) {q}"
  proof (rule SN_on_induct[OF SN_on_trancl[OF sn] singletonI])
    fix s :: "('f,'w) lp_iterm"
    assume ih: "\<And>t. (s,t)\<in>(dt_constructor_step C U)\<^sup>+ \<Longrightarrow>
      \<forall>q::('f,'w) lp_iatom. t=lp_itag (sharp \<circ> inp) (lp_data_atom data q) \<longrightarrow>
        SN_on (lp_triple_calls (set D) P) {q}"
    show "\<forall>q::('f,'w) lp_iatom. s=lp_itag (sharp \<circ> inp) (lp_data_atom data q) \<longrightarrow>
      SN_on (lp_triple_calls (set D) P) {q}"
    proof (intro allI impI)
      fix q assume s: "s=lp_itag (sharp \<circ> inp) (lp_data_atom data q)"
      show "SN_on (lp_triple_calls (set D) P) {q}"
      proof (rule step_reflects_SN_on)
        fix r assume qr: "(q,r)\<in>lp_triple_calls (set D) P"
        have edge: "(s,lp_itag (sharp \<circ> inp) (lp_data_atom data r))\<in>(dt_constructor_step C U)\<^sup>+"
          unfolding s by (rule dt_data_constructor_call_simulation[OF fixed range shapes frames marked triples qr])
        show "SN_on (lp_triple_calls (set D) P) {r}" using ih[OF edge] by blast
      qed
    qed
  qed
  show ?thesis using reflection by blast
qed


theorem dt_constructor_qdp_termination:
  fixes query :: "('f,'w) lp_iatom" and a :: "('f,'v) term"
  assumes fixed: "lp_data_fixed_program data P" and range: "range data\<subseteq>C"
    and shapes: "\<And>l r. (l,r)\<in>set (lp_translation.translated P inp out pu) \<Longrightarrow> lp_constructor_lhs C l"
    and frames: "\<And>c i. pu c i\<in>U" and marked: "\<And>c i. sharp (du c i)\<in>U"
    and triples: "\<And>h ps goal. (h,ps,goal)\<in>set D \<Longrightarrow>
      lp_data_fixed_atom data h \<and> list_all (lp_data_fixed_atom data) ps \<and>
      lp_data_fixed_atom data goal"
    and filter: "lp_filter \<pi> U"
    and measured: "lp_iproject \<pi> (lp_itag (sharp \<circ> inp) (lp_data_atom data query)) a"
    and rv: "\<And>l r. (l,r)\<in>set dt_support \<Longrightarrow> vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)"
    and dv: "\<And>l r. (l,r)\<in>set dt_pairs \<Longrightarrow> vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)"
    and pairs: "\<And>l r. (l,r)\<in>set dt_pairs \<Longrightarrow> funs_term l\<subseteq>C"
    and roots: "\<And>t. t\<in>Q \<Longrightarrow> \<exists>f ts. t=Fun f ts \<and> f\<notin>C"
    and finite: "finite_dpp (nfs,False,af_rule \<pi> ` set dt_pairs,{},Q,{},af_rule \<pi> ` set dt_support)"
  shows "SN_on (lp_triple_calls (set D) P) {query}"
proof -
  interpret lp_filter \<pi> U by (rule filter)
  have no_chain: "\<And>ls rs (vals::nat\<Rightarrow>'v\<Rightarrow>('f,'w) lp_iterm).
    \<not>lp_constructor_chain C (set dt_pairs) (set dt_support) U \<pi> ls rs vals"
  proof
    fix ls rs and vals :: "nat\<Rightarrow>'v\<Rightarrow>('f,'w) lp_iterm"
    assume chain: "lp_constructor_chain C (set dt_pairs) (set dt_support) U \<pi> ls rs vals"
    have qchain: "min_ichain (nfs,False,af_rule \<pi> ` set dt_pairs,{},Q,{},af_rule \<pi> ` set dt_support)
      (\<lambda>i. af_term \<pi> (ls i)) (\<lambda>i. af_term \<pi> (rs i))
      (\<lambda>i x. (lp_projection \<pi> (vals i x)::('f,'v) term))"
      by (rule constructor_chain_qdp[OF chain rv pairs roots])
    show False using qchain finite unfolding finite_dpp_def by blast
  qed
  show ?thesis by (rule dt_constructor_chains_imply_triple_termination[
    OF fixed range shapes frames marked triples no_chain measured rv dv])
qed

end
end
