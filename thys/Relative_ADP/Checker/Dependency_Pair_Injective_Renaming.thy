theory Dependency_Pair_Injective_Renaming
  imports Framework.Dependency_Pair_Problem_Impl
begin

text \<open>Injective symbol renaming preserves Q-normal forms and transports
nonminimal dependency-pair chains. These facts do not depend on ADP certificates.\<close>

lemma inj_map_funs_term_NF_terms:
  assumes inj: "inj fg" and nf: "t \<in> NF_terms Q"
  shows "map_funs_term fg t \<in> NF_terms (map_funs_term fg ` Q)"
proof -
  let ?m = "map_funs_term fg"
  let ?g = "the_inv fg"
  have inverse: "?g \<circ> fg = id"
    by (rule ext, insert the_inv_f_f[OF inj], auto)
  have "(?m t, s) \<notin> rstep (Id_on (?m ` Q))" for s
  proof
    assume "(?m t, s) \<in> rstep (Id_on (?m ` Q))"
    from rstep_imp_map_rstep[OF this, of ?g,
        unfolded map_funs_term_comp inverse map_funs_term_ident]
    have "t \<notin> NF (rstep (map_funs_trs ?g (Id_on (?m ` Q))))"
      by auto
    moreover have "map_funs_trs ?g (Id_on (?m ` Q)) = Id_on Q"
      unfolding map_funs_trs.simps Id_on_def
      using the_inv_f_f[OF inj]
      by (force simp: inverse map_funs_term_comp)
    ultimately show False using nf by simp
  qed
  then show ?thesis by auto
qed

lemma inj_map_funs_term_NF_subst:
  assumes inj: "inj fg" and nfs: "NF_subst flag (l,r) sigma Q"
  shows "NF_subst flag (map_funs_term fg l, map_funs_term fg r)
    (map_funs_subst fg sigma) (map_funs_term fg ` Q)"
proof
  fix x
  assume flag and vars:
    "x \<in> vars_term (map_funs_term fg l) \<or>
      x \<in> vars_term (map_funs_term fg r)"
  from vars have "x \<in> vars_rule (l,r)"
    unfolding vars_rule_def by auto
  with nfs `flag` have "sigma x \<in> NF_terms Q"
    unfolding NF_subst_def by auto
  from inj_map_funs_term_NF_terms[OF inj this]
  show "map_funs_subst fg sigma x \<in> NF_terms (map_funs_term fg ` Q)"
    by simp
qed

lemma inj_map_funs_term_qrstep:
  assumes inj: "inj fg" and step: "(s,t) \<in> qrstep nfs Q R"
  shows "(map_funs_term fg s, map_funs_term fg t) \<in>
    qrstep nfs (map_funs_term fg ` Q) (map_funs_trs fg R)"
proof -
  let ?m = "map_funs_term fg"
  from step obtain C l r sigma where lr: "(l,r) \<in> R"
    and s: "s = C \<langle> l \<cdot> sigma \<rangle>"
    and t: "t = C \<langle> r \<cdot> sigma \<rangle>"
    and nf: "\<forall>u \<lhd> l \<cdot> sigma. u \<in> NF_terms Q"
    and subst: "NF_subst nfs (l,r) sigma Q"
    by auto
  have mapped_lr: "(?m l, ?m r) \<in> map_funs_trs fg R"
    using lr unfolding map_funs_trs.simps by force
  have mapped_nf:
    "\<forall>u \<lhd> ?m l \<cdot> map_funs_subst fg sigma.
      u \<in> NF_terms (?m ` Q)"
    unfolding map_funs_subst_distrib[symmetric]
      NF_terms_args_conv[symmetric]
  proof
    fix u
    assume u: "u \<in> set (args (?m (l \<cdot> sigma)))"
    then obtain f ls where ls: "l \<cdot> sigma = Fun f ls"
      by (cases "l \<cdot> sigma", auto)
    from u[unfolded ls] obtain li where li: "li \<in> set ls"
      and u_eq: "u = ?m li" by auto
    from li ls have "li \<in> set (args (l \<cdot> sigma))" by auto
    with nf[unfolded NF_terms_args_conv[symmetric]]
    have "li \<in> NF_terms Q" by auto
    from inj_map_funs_term_NF_terms[OF inj this]
    show "u \<in> NF_terms (?m ` Q)" unfolding u_eq .
  qed
  have mapped_subst:
    "NF_subst nfs (?m l, ?m r) (map_funs_subst fg sigma) (?m ` Q)"
    using inj_map_funs_term_NF_subst[OF inj subst] .
  have "((map_funs_ctxt fg C)\<langle>?m l \<cdot> map_funs_subst fg sigma\<rangle>,
      (map_funs_ctxt fg C)\<langle>?m r \<cdot> map_funs_subst fg sigma\<rangle>)
      \<in> qrstep nfs (?m ` Q) (map_funs_trs fg R)"
  proof (rule qrstepI)
    show "\<forall>u \<lhd> ?m l \<cdot> map_funs_subst fg sigma.
        u \<in> NF_terms (?m ` Q)" by (rule mapped_nf)
    show "(?m l, ?m r) \<in> map_funs_trs fg R" by (rule mapped_lr)
    show "(map_funs_ctxt fg C)\<langle>?m l \<cdot> map_funs_subst fg sigma\<rangle> =
        (map_funs_ctxt fg C)\<langle>?m l \<cdot> map_funs_subst fg sigma\<rangle>" by simp
    show "(map_funs_ctxt fg C)\<langle>?m r \<cdot> map_funs_subst fg sigma\<rangle> =
        (map_funs_ctxt fg C)\<langle>?m r \<cdot> map_funs_subst fg sigma\<rangle>" by simp
    show "NF_subst nfs (?m l, ?m r) (map_funs_subst fg sigma) (?m ` Q)"
      by (rule mapped_subst)
  qed
  then show ?thesis
    unfolding s t map_funs_term_ctxt_distrib map_funs_subst_distrib .
qed

lemma inj_map_funs_term_qrsteps:
  assumes inj: "inj fg" and steps: "(s,t) \<in> (qrstep nfs Q R)\<^sup>*"
  shows "(map_funs_term fg s, map_funs_term fg t) \<in>
    (qrstep nfs (map_funs_term fg ` Q) (map_funs_trs fg R))\<^sup>*"
  using steps
proof (induction)
  case base
  then show ?case by simp
next
  case (step y z)
  have "(map_funs_term fg y, map_funs_term fg z) \<in>
      qrstep nfs (map_funs_term fg ` Q) (map_funs_trs fg R)"
    by (rule inj_map_funs_term_qrstep[OF inj step.hyps(2)])
  with step.IH show ?case by auto
qed

lemma inj_map_funs_term_finite_dpp:
  assumes inj: "inj fg"
    and fin: "finite_dpp (nfs,False,map_funs_trs fg P, {},
      map_funs_term fg ` Q, {}, map_funs_trs fg Rw)"
  shows "finite_dpp (nfs,False,P,{},Q,{},Rw)"
  unfolding finite_dpp_def
proof (intro notI, elim exE)
  fix s t sigma
  let ?dpp = "(nfs, False, P, {}, Q, {}, Rw)"
  let ?mdpp = "(nfs, False, map_funs_trs fg P, {},
    map_funs_term fg ` Q, {}, map_funs_trs fg Rw)"
  let ?m = "map_funs_term fg"
  let ?ms = "map_funs_subst fg"
  assume chain: "min_ichain ?dpp s t sigma"
  then have ichain: "ichain ?dpp s t sigma" by auto
  from ichain[unfolded ichain.simps] have
      pairs: "\<And>i. (s i,t i) \<in> P"
    and nf: "\<And>i. s i \<cdot> sigma i \<in> NF_terms Q"
    and nfs: "\<And>i. NF_subst nfs (s i,t i) (sigma i) Q"
    and steps: "\<And>i. (t i \<cdot> sigma i,
      s (Suc i) \<cdot> sigma (Suc i)) \<in> (qrstep nfs Q Rw)\<^sup>*"
    by auto
  let ?s = "\<lambda>i. ?m (s i)"
  let ?t = "\<lambda>i. ?m (t i)"
  let ?sigma = "\<lambda>i. ?ms (sigma i)"
  have mapped_pairs: "(?s i,?t i) \<in> map_funs_trs fg P" for i
    using pairs[of i] unfolding map_funs_trs.simps by force
  have mapped: "ichain ?mdpp ?s ?t ?sigma"
    unfolding ichain.simps Un_empty_right Un_empty_left
  proof (intro conjI allI disjI1)
    fix i
    show "(?s i,?t i) \<in> map_funs_trs fg P"
      by (rule mapped_pairs)
    show "?s i \<cdot> ?sigma i \<in> NF_terms (map_funs_term fg ` Q)"
      using inj_map_funs_term_NF_terms[OF inj nf[of i]] by simp
    show "NF_subst nfs (?s i,?t i) (?sigma i) (map_funs_term fg ` Q)"
      using inj_map_funs_term_NF_subst[OF inj nfs] .
    show "(?t i \<cdot> ?sigma i, ?s (Suc i) \<cdot> ?sigma (Suc i))
        \<in> (qrstep nfs (map_funs_term fg ` Q) (map_funs_trs fg Rw))\<^sup>*"
      using inj_map_funs_term_qrsteps[OF inj steps[of i]] by simp
  qed (insert mapped_pairs, auto)
  then have "min_ichain ?mdpp ?s ?t ?sigma" by simp
  with fin show False unfolding finite_dpp_def by blast
qed

end
