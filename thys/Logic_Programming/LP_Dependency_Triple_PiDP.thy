theory LP_Dependency_Triple_PiDP
  imports LP_Dependency_Triple_Simulation
begin

context lp_triple_translation
begin

lemma dt_next_pair:
  fixes a :: "('f,'v) term"
  assumes bad: "\<not> SN_on dt_step {s}" and projection: "lp_iproject \<pi> s a"
    and rv: "\<And>l r. (l,r)\<in>set dt_support \<Longrightarrow>
      vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)"
    and dv: "\<And>l r. (l,r)\<in>set dt_pairs \<Longrightarrow>
      vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)"
  obtains l r \<rho> t where "(l,r)\<in>set dt_pairs"
    "(s,lp_ieval l \<rho>)\<in>(lp_pi_link (set dt_support))\<^sup>*"
    "(lp_ieval r \<rho>,t)\<in>(lp_pi_link (set dt_support))\<^sup>*"
    "\<not> SN_on dt_step {t}"
    "\<exists>b::('f,'v) term. lp_iproject \<pi> (lp_ieval l \<rho>) b"
    "\<exists>b::('f,'v) term. lp_iproject \<pi> (lp_ieval r \<rho>) b"
proof -
  have successor: "\<exists>t. (s,t)\<in>dt_step \<and> \<not>SN_on dt_step {t}"
  proof (rule ccontr)
    assume none: "\<not>(\<exists>t. (s,t)\<in>dt_step \<and> \<not>SN_on dt_step {t})"
    have "SN_on dt_step {s}" by (rule step_reflects_SN_on) (use none in blast)
    with bad show False by contradiction
  qed
  obtain t where st: "(s,t)\<in>dt_step" and bt: "\<not> SN_on dt_step {t}"
    using successor by blast
  obtain l r \<rho> where pair: "(l,r)\<in>set dt_pairs"
    and before: "(s,lp_ieval l \<rho>)\<in>(lp_pi_link (set dt_support))\<^sup>*"
    and after: "(lp_ieval r \<rho>,t)\<in>(lp_pi_link (set dt_support))\<^sup>*"
    using st unfolding dt_step_def dt_strict_def by blast
  obtain b :: "('f,'v) term" where pb: "lp_iproject \<pi> (lp_ieval l \<rho>) b"
    by (rule lp_pi_links_projection[OF before projection rv]) blast
  obtain c :: "('f,'v) term" where pc: "lp_iproject \<pi> (lp_ieval r \<rho>) c"
    by (rule lp_infinite_rule_projection[OF pb dv[OF pair] pair]) blast
  show thesis by (rule that[OF pair before after bt]) (use pb pc in blast)+
qed

theorem dt_nontermination_to_pi_chain:
  fixes s :: "('f,'w) lp_iterm" and a :: "('f,'v) term"
  assumes bad: "\<not> SN_on dt_step {s}" and projection: "lp_iproject \<pi> s a"
    and rv: "\<And>l r. (l,r)\<in>set dt_support \<Longrightarrow>
      vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)"
    and dv: "\<And>l r. (l,r)\<in>set dt_pairs \<Longrightarrow>
      vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)"
  shows "\<exists>ls rs (valuations::nat\<Rightarrow>'v\<Rightarrow>('f,'w) lp_iterm).
    lp_pi_narrow_chain (set dt_pairs) (set dt_support) \<pi> ls rs valuations"
proof -
  let ?good = "\<lambda>(l,r,(\<rho>::'v\<Rightarrow>('f,'w) lp_iterm),t).
    (l,r)\<in>set dt_pairs \<and>
    (lp_ieval r \<rho>,t)\<in>(lp_pi_link (set dt_support))\<^sup>* \<and>
    \<not> SN_on dt_step {t} \<and>
    (\<exists>b::('f,'v) term. lp_iproject \<pi> (lp_ieval l \<rho>) b) \<and>
    (\<exists>b::('f,'v) term. lp_iproject \<pi> (lp_ieval r \<rho>) b)"
  let ?edge = "\<lambda>(l,r,\<rho>,t) (l',r',\<rho>',t').
    (lp_ieval r \<rho>,lp_ieval l' \<rho>')\<in>(lp_pi_link (set dt_support))\<^sup>*"
  have initial: "\<exists>z::('f,'v) term \<times> ('f,'v) term \<times>
      ('v\<Rightarrow>('f,'w) lp_iterm) \<times> ('f,'w) lp_iterm. ?good z"
  proof -
    obtain l r and \<rho> :: "'v\<Rightarrow>('f,'w) lp_iterm" and t
      where good: "?good (l,r,\<rho>,t)"
      by (rule dt_next_pair[OF bad projection rv dv]) auto
    show ?thesis by (rule exI[of _ "(l,r,\<rho>,t)"]) (rule good)
  qed
  have progress: "\<And>z. ?good z \<Longrightarrow> \<exists>z'. ?good z' \<and> ?edge z z'"
  proof -
    fix z :: "('f,'v) term \<times> ('f,'v) term \<times>
      ('v\<Rightarrow>('f,'w) lp_iterm) \<times> ('f,'w) lp_iterm"
    assume good: "?good z"
    obtain l r \<rho> t where z: "z=(l,r,\<rho>,t)" by (cases z) auto
    have bt: "\<not> SN_on dt_step {t}"
      and after: "(lp_ieval r \<rho>,t)\<in>(lp_pi_link (set dt_support))\<^sup>*"
      using good by (simp_all add: z)
    obtain b :: "('f,'v) term" where pb: "lp_iproject \<pi> (lp_ieval r \<rho>) b"
      using good by (auto simp: z)
    obtain c :: "('f,'v) term" where pc: "lp_iproject \<pi> t c"
      by (rule lp_pi_links_projection[OF after pb rv]) blast
    obtain l' r' \<rho>' t' where next_good: "?good (l',r',\<rho>',t')"
      and before: "(t,lp_ieval l' \<rho>')\<in>(lp_pi_link (set dt_support))\<^sup>*"
      by (rule dt_next_pair[OF bt pc rv dv]) auto
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
  have chain: "lp_pi_narrow_chain (set dt_pairs) (set dt_support) \<pi> ?ls ?rs ?vals"
    using sequence by (auto simp: lp_pi_narrow_chain_def case_prod_beta)
  show ?thesis by (intro exI[of _ ?ls] exI[of _ ?rs] exI[of _ ?vals]) (rule chain)
qed

theorem dt_pi_chains_imply_triple_termination:
  fixes query :: "('f,'w) lp_iatom" and a :: "('f,'v) term"
  assumes no_chain: "\<And>ls rs (vals::nat\<Rightarrow>'v\<Rightarrow>('f,'w) lp_iterm).
      \<not>lp_pi_narrow_chain (set dt_pairs) (set dt_support) \<pi> ls rs vals"
    and projection: "lp_iproject \<pi> (lp_itag (sharp \<circ> inp) query) a"
    and rv: "\<And>l r. (l,r)\<in>set dt_support \<Longrightarrow>
      vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)"
    and dv: "\<And>l r. (l,r)\<in>set dt_pairs \<Longrightarrow>
      vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)"
  shows "SN_on (lp_triple_calls (set D) P) {query}"
proof -
  have sn: "SN_on dt_step {lp_itag (sharp \<circ> inp) query}"
    using dt_nontermination_to_pi_chain[OF _ projection rv dv] no_chain by blast
  have reflection: "\<forall>q::('f,'w) lp_iatom. lp_itag (sharp \<circ> inp) query = lp_itag (sharp \<circ> inp) q
    \<longrightarrow> SN_on (lp_triple_calls (set D) P) {q}"
  proof (rule SN_on_induct[OF SN_on_trancl[OF sn] singletonI])
    fix s :: "('f,'w) lp_iterm"
    assume ih: "\<And>t. (s,t)\<in>dt_step\<^sup>+ \<Longrightarrow>
      \<forall>q::('f,'w) lp_iatom. t=lp_itag (sharp \<circ> inp) q \<longrightarrow>
        SN_on (lp_triple_calls (set D) P) {q}"
    show "\<forall>q::('f,'w) lp_iatom. s=lp_itag (sharp \<circ> inp) q \<longrightarrow>
      SN_on (lp_triple_calls (set D) P) {q}"
    proof (intro allI impI)
      fix q assume s: "s=lp_itag (sharp \<circ> inp) q"
      show "SN_on (lp_triple_calls (set D) P) {q}"
      proof (rule step_reflects_SN_on)
        fix r assume qr: "(q,r)\<in>lp_triple_calls (set D) P"
        have edge: "(s,lp_itag (sharp \<circ> inp) r)\<in>dt_step\<^sup>+"
          unfolding s by (rule dt_call_simulation[OF qr])
        show "SN_on (lp_triple_calls (set D) P) {r}" using ih[OF edge] by blast
      qed
    qed
  qed
  show ?thesis using reflection by blast
qed

end
end
