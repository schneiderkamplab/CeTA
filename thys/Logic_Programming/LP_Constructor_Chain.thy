theory LP_Constructor_Chain
  imports LP_Constructor_Source
begin

context lp_translation
begin

theorem source_to_constructor_chain:
  fixes s :: "('f,'v,'w) lp_iconfig" and a :: "('f,'v) term"
  assumes fixed: "lp_data_fixed_program data P" and range: "range data\<subseteq>C"
    and shapes: "\<And>l r. (l,r)\<in>set translated \<Longrightarrow> lp_constructor_lhs C l"
    and frames: "\<And>c i. u c i\<in>U" and marked: "\<And>c i. sharp (u c i)\<in>U"
    and minimal: "lp_iminimal P s"
    and pr: "lp_iproject \<pi> (mencode sharp (lp_data_config data s)) a"
    and rv: "\<And>l r. (l,r)\<in>set translated \<Longrightarrow> vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)"
    and dv: "\<And>l r. (l,r)\<in>set (pi_pairs sharp) \<Longrightarrow> vars_term (af_term \<pi> r)\<subseteq>vars_term (af_term \<pi> l)"
  shows "\<exists>ls rs (vals::nat\<Rightarrow>'v\<Rightarrow>('f,'w) lp_iterm).
    lp_constructor_chain C (set (pi_pairs sharp)) (set translated) U \<pi> ls rs vals"
proof -
  let ?good = "\<lambda>(l,r,(\<rho>::'v\<Rightarrow>('f,'w) lp_iterm),k). (l,r)\<in>set (pi_pairs sharp) \<and>
    mencode sharp (lp_data_config data k)=lp_ieval r (\<lambda>x. map_lp_iterm data id (\<rho> x)) \<and> lp_iminimal P k \<and>
    (\<exists>b::('f,'v) term. lp_iproject \<pi> (lp_ieval l (\<lambda>x. map_lp_iterm data id (\<rho> x))) b) \<and>
    (\<exists>b::('f,'v) term. lp_iproject \<pi> (lp_ieval r (\<lambda>x. map_lp_iterm data id (\<rho> x))) b)"
  let ?edge = "\<lambda>(l,r,\<rho>,k) (l',r',\<rho>',k').
    (mencode sharp (lp_data_config data k),lp_ieval l' (\<lambda>x. map_lp_iterm data id (\<rho>' x)))\<in>(lp_clink C (set translated) U)\<^sup>*"
  have initial: "\<exists>z::('f,'v) term \<times> ('f,'v) term \<times> ('v\<Rightarrow>('f,'w) lp_iterm) \<times> ('f,'v,'w) lp_iconfig. ?good z"
  proof -
    obtain l r and \<rho> :: "'v\<Rightarrow>('f,'w) lp_iterm" and k where g: "?good (l,r,\<rho>,k)"
      by (rule data_minimal_next_pair[where sharp=sharp, OF fixed range shapes frames marked minimal pr rv dv]) auto
    show ?thesis by (rule exI[where x="(l,r,\<rho>,k)"], rule g)
  qed
  have progress: "\<And>z. ?good z \<Longrightarrow> \<exists>z'. ?good z' \<and> ?edge z z'"
  proof -
    fix z :: "('f,'v) term \<times> ('f,'v) term \<times> ('v\<Rightarrow>('f,'w) lp_iterm) \<times> ('f,'v,'w) lp_iconfig"
    assume g: "?good z"
    obtain l r \<rho> k where z: "z=(l,r,\<rho>,k)" by (cases z) auto
    have min: "lp_iminimal P k" and right: "mencode sharp (lp_data_config data k)=lp_ieval r (\<lambda>x. map_lp_iterm data id (\<rho> x))"
      using g by (simp_all add: z)
    obtain b :: "('f,'v) term" where pb: "lp_iproject \<pi> (mencode sharp (lp_data_config data k)) b"
      using g right by (auto simp: z)
    obtain l' r' \<rho>' k' where g': "?good (l',r',\<rho>',k')" and e: "?edge z (l',r',\<rho>',k')"
      by (rule data_minimal_next_pair[where sharp=sharp, OF fixed range shapes frames marked min pb rv dv]) (auto simp: z)
    show "\<exists>z'. ?good z' \<and> ?edge z z'"
      by (rule exI[where x="(l',r',\<rho>',k')"]) (use g' e in simp)
  qed
  have seq: "\<exists>z. \<forall>i::nat. ?good (z i) \<and> ?edge (z i) (z (Suc i))"
    by (rule dependent_nat_choice[where P="\<lambda>n z. ?good z" and Q="\<lambda>n z z'. ?edge z z'", OF initial])
       (rule progress)
  obtain z where seq_z: "\<forall>i::nat. ?good (z i) \<and> ?edge (z i) (z (Suc i))"
    using seq by blast
  have good: "\<And>i::nat. ?good (z i)" and edge: "\<And>i::nat. ?edge (z i) (z (Suc i))"
    using seq_z by simp_all
  let ?ls = "\<lambda>i. fst (z i)"
  let ?rs = "\<lambda>i. fst (snd (z i))"
  let ?vals = "\<lambda>i x. map_lp_iterm data id (fst (snd (snd (z i))) x)"
  have chain: "lp_constructor_chain C (set (pi_pairs sharp)) (set translated) U \<pi> ?ls ?rs ?vals"
    unfolding lp_constructor_chain_def
    using good edge lp_constructor_value_map[OF range]
    by (auto simp: case_prod_beta)
  show ?thesis by (rule exI[of _ ?ls], rule exI[of _ ?rs], rule exI[of _ ?vals], rule chain)
qed

end
end
