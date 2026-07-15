(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Innermost_Switch
imports
  TRS.QDP_Framework
  First_Order_Rewriting.Critical_Pairs
  Right_Forward_Closures.Gramlich_Innermost_Switch
  TRS.DP_Transformation
  Sem_Lab.Labelings
  Auxx.Name
begin

lemma irstep_is_inn_step: assumes "wf_trs R" 
  shows "irstep nfs R = inn_rstep R" 
proof 
  {
    fix s t
    assume "(s,t) \<in> irstep nfs R" 
    from qrstepE[OF this[unfolded irstep_def]]
    obtain C \<sigma> l r 
      where NF: "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms (lhss R)" 
        and s: "s = C \<langle> l \<cdot> \<sigma> \<rangle>"  
        and t: "t = C \<langle> r \<cdot> \<sigma> \<rangle>" 
        and lr: "(l,r) \<in> R" by metis
    from NF have "set (args (l \<cdot> \<sigma>)) \<subseteq> NF_trs R"
      unfolding NF_terms_args_conv[symmetric] by auto
    from inn_rstep[OF lr this, of C] s t 
    have "(s,t) \<in> inn_rstep R" by simp
  }
  thus "irstep nfs R \<subseteq> inn_rstep R" by auto
  {
    fix s t
    assume "(s,t) \<in> inn_rstep R"
    from inn_rstep.cases[OF this] obtain C \<sigma> l r 
      where s: "s = C \<langle> l \<cdot> \<sigma> \<rangle>"  
        and t: "t = C \<langle> r \<cdot> \<sigma> \<rangle>" 
        and lr: "(l,r) \<in> R" 
        and NF: "set (args (l \<cdot> \<sigma>)) \<subseteq> NF_trs R" by metis
    from NF have NF: "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms (lhss R)" unfolding 
        NF_terms_args_conv[symmetric] by auto
    from qrstepI[OF this lr s t, of False]
    have "(s, t) \<in> qrstep False (lhss R) R" by auto
    with assms have "(s, t) \<in> qrstep nfs (lhss R) R"
      by (metis wf_trs_imp_wwf_qtrs wwf_qtrs_imp_nfs_False_switch)
    hence "(s,t) \<in> irstep nfs R" unfolding irstep_def .
  }
  thus "inn_rstep R \<subseteq> irstep nfs R" by auto
qed
    


(* it might be tempting to require just WCR (rstep R) instead
   of WCR (qrstep nfs Q R), since then one can use standard 
   joinability of critical pairs to show WCR (rstep R).
   However, this is unsound!
   Consider P = {G(a,f(d),x) \<rightarrow> G(x,x,x)}
            Q = {c}
            R = {b \<rightarrow> a, b \<rightarrow> f(c), c \<rightarrow> d, f(c) \<rightarrow> b}
   Then obviously there is no innermost P-R-chain, so all 
   preconditions of the following lemma are satisfied except
   WCR (qrstep nfs Q R). Instead WCR (rstep R) is satisfied as all
   critical pairs are joinable (w.r.t. rstep R).
   But G(a,f(d),b) \<rightarrow>P G(b,b,b) -Q\<rightarrow>R^* G(a,f(d),b) is an infinite
   minimal (P,Q,R) chain. *)
lemma switch_to_innermost_proc: fixes R :: "('f,'v :: infinite)trs"
  assumes WCR: "WCR_on (qrstep nfs Q R) {t. SN_on (qrstep nfs Q R) {t}}"
  and NF_subset: "NF_trs R \<subseteq> NF_terms Q"
  and no_overlap: "critical_pairs ren (P \<union> Pw) R = {}"
  and m: m
  and vars: "\<And> l r. nfs \<Longrightarrow> (l,r) \<in> R \<Longrightarrow> is_Fun l"
  and fin: "finite_dpp (nfs,m,P,Pw,lhss R,{},R)"
  shows "finite_dpp (nfs,m,P,Pw,Q,{},R)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain s t \<sigma> where chain: "min_ichain (nfs,m,P,Pw,Q,{},R) s t \<sigma>" unfolding finite_dpp_def by blast
  let ?t = "\<lambda> i. t i \<cdot> \<sigma> i"
  let ?s = "\<lambda> i. s (Suc i) \<cdot> \<sigma> (Suc i)"
  from chain m have SN: "\<And> i. SN_on (qrstep nfs Q R) {?t i}"
              and Q: "\<And> i. ?s i \<in> NF_terms Q" 
              and steps: "\<And> i. (?t i, ?s i) \<in> (qrstep nfs Q R)^*"
              and P: "\<And> i. (s i, t i) \<in> P \<union> Pw"
              and inf: "INFM i. (s i, t i) \<in> P"
    by (auto simp: ichain.simps minimal_cond_def)
  let ?\<sigma> = "\<lambda> i x. some_NF (qrstep nfs Q R) (\<sigma> i x)"
  let ?t' = "\<lambda> i. t i \<cdot> ?\<sigma> i"
  let ?s' = "\<lambda> i. s (Suc i) \<cdot> ?\<sigma> (Suc i)"
  {
    fix i x
    assume "x \<in> vars_term (t i)"
    then have "t i \<unrhd> Var x" by auto
    then have "?t i \<unrhd> Var x \<cdot> \<sigma> i" by auto
    from ctxt_closed_SN_on_subt [OF ctxt_closed_qrstep SN this]
    have SN: "SN_on (qrstep nfs Q R) {\<sigma> i x}" by auto
    from some_NF[OF this] have stepsx: "(\<sigma> i x, ?\<sigma> i x) \<in> (qrstep nfs Q R)^*"
      and NFx: "?\<sigma> i x \<in> NF (qrstep nfs Q R)" by auto
  } note steps_NF_x_t = this
  {
    fix i x
    assume "x \<in> vars_term (s (Suc i))"
    then have "s (Suc i) \<unrhd> Var x" by auto
    then have "?s i \<unrhd> Var x \<cdot> \<sigma> (Suc i)" by auto
    from ctxt_closed_SN_on_subt [OF ctxt_closed_qrstep steps_preserve_SN_on[OF steps SN] this]
    have SN: "SN_on (qrstep nfs Q R) {\<sigma> (Suc i) x}" by auto
    from some_NF[OF this] have stepsx: "(\<sigma> (Suc i) x, ?\<sigma> (Suc i) x) \<in> (qrstep nfs Q R)^*"
      and NFx: "?\<sigma> (Suc i) x \<in> NF (qrstep nfs Q R)" by auto
  } note steps_NF_x_s = this
  {
    fix i
    have "(?t i, ?t' i) \<in> (qrstep nfs Q R)^*"
      by (rule subst_qrsteps_imp_qrsteps, insert steps_NF_x_t(1)[of _ i], auto)
  } note stepst = this
  {
    fix i
    have "?s' i \<in> NF (qrstep nfs Q R)"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain v where "(?s' i, v) \<in> qrstep nfs Q R" by auto
      then obtain l r \<tau> C where si: "?s' i = C\<langle>l \<cdot> \<tau>\<rangle>" and "v = C\<langle>r \<cdot> \<tau>\<rangle>" and lr: "(l,r) \<in> R" 
      and NF: "\<forall> u \<lhd> l \<cdot> \<tau>. u \<in> NF_terms Q" and nfs: "NF_subst nfs (l,r) \<tau> Q" by auto
      from si have subt: "?s' i \<unrhd> l \<cdot> \<tau>" by auto
      {
        fix x
        assume x: "x \<in> vars_term (s (Suc i))" and subt: "?\<sigma> (Suc i) x \<unrhd> l \<cdot> \<tau>"
        from subt obtain C where "?\<sigma> (Suc i) x = C\<langle>l\<cdot>\<tau>\<rangle>" by auto
        with NF nfs lr have "(?\<sigma> (Suc i) x, C\<langle>r\<cdot>\<tau>\<rangle>) \<in> qrstep nfs Q R" by auto
        with steps_NF_x_s(2)[OF x] have False by auto
      } note not_in_vars = this
      have "\<exists> u \<unlhd> s (Suc i). l \<cdot> \<tau> = u \<cdot> ?\<sigma> (Suc i)"
        by (rule subt_instance_and_not_subst_imp_subt[OF subt], insert not_in_vars, auto)
      then obtain u where subt: "s (Suc i) \<unrhd> u" and u: "u \<cdot> ?\<sigma> (Suc i) = l \<cdot> \<tau>"
        by auto
      have nvar: "is_Fun u"
      proof
        assume "is_Var u"
        then obtain x where ux: "u = Var x" by auto
        from subt have x: "x \<in> vars_term (s (Suc i))" unfolding ux 
          by (rule subteq_Var_imp_in_vars_term)
        show False  
          by (rule not_in_vars[OF x], unfold u[symmetric] ux, auto)
      qed
      from subt obtain C where subt: "s (Suc i) = C\<langle>u\<rangle>" by auto
      from critical_pairs_exI[OF P lr subt nvar u refl, of ren] no_overlap
      show False by simp
    qed
  } note NF_s = this
  let ?sh = "\<lambda> t i. t (Suc i)"
  from inf have inf: "INFM i. (s (Suc i), t (Suc i)) \<in> P"
    using Infm_shift[of "\<lambda> i. (s i, t i) \<in> P" id "Suc 0"]
    by simp
  from Q_subset_R_imp_same_NF[OF NF_subset vars]
  have NF_conv: "NF_terms (lhss R) = NF (qrstep nfs Q R)" by simp
  { 
    fix i
    have "SN_on (qrstep nfs (lhss R) R) {?t' i}"
      by (rule SN_on_mono[OF steps_preserve_SN_on[OF stepst SN] qrstep_mono],
      insert NF_subset, auto)
  } note SN_t' = this
  have "min_ichain (nfs,m,P,Pw,fst ` R,{},R) (?sh s) (?sh t) (?sh ?\<sigma>)"
    unfolding min_ichain.simps ichain.simps minimal_cond_def Un_empty_left
  proof (intro conjI allI impI, rule P, rule disjI1[OF inf])
    fix i 
    from NF_s[of i] have NFs: "?s' i \<in> NF_terms (lhss R)"
      unfolding NF_conv .
    show "?s' i \<in> NF_terms (lhss R)" by fact
    show "SN_on (qrstep nfs (lhss R) R) {?t' i}" using SN_t'[of i] by simp
    show "NF_subst nfs (s (Suc i), t (Suc i)) (?\<sigma> (Suc i)) (lhss R)"
    proof
      fix x
      assume "x \<in> vars_term (s (Suc i)) \<or> x \<in> vars_term (t (Suc i))"
      then show "?\<sigma> (Suc i) x \<in> NF_terms (lhss R)"
      proof
        assume x: "x \<in> vars_term (t (Suc i))"
        from steps_NF_x_t(2)[OF x]
        show ?thesis unfolding NF_conv .
      next
        assume x: "x \<in> vars_term (s (Suc i))"
        from steps_NF_x_s(2)[OF x]
        show ?thesis unfolding NF_conv .
      qed
    qed
    let ?QR = "qrstep nfs Q R"
    let ?RR = "qrstep nfs (lhss R) R"
    have ts': "(?t i, ?s' i) \<in> ?QR^*"
      by (rule rtrancl_trans[OF steps subst_qrsteps_imp_qrsteps], insert steps_NF_x_s(1)[of _ i], auto)
    from some_NF_WCR[OF SN WCR ts' NF_s]
    have s'i_NF: "?s' i = some_NF ?QR (?t i)" .
    obtain w where w: "w = some_NF ?RR (?t' i)" by auto
    from some_NF[OF SN_t', of i] have stepsw: "(?t' i, w) \<in> ?RR^*" and w: "w \<in> NF ?RR"
      unfolding w by auto
    have stepsw': "(?t i, w) \<in> ?QR^*"
      by (rule rtrancl_trans[OF stepst set_mp[OF rtrancl_mono[OF qrstep_mono] stepsw]], insert NF_subset, auto)
    have w_NF: "w \<in> NF ?QR" unfolding NF_conv[symmetric] using w 
      using Q_subset_R_imp_same_NF[of R "lhss R"] vars by auto
    from some_NF_WCR[OF SN WCR stepsw' w_NF] have w_NF: "w = some_NF ?QR (?t i)" .
    from stepsw show "(?t' i, ?s' i) \<in> ?RR^*" unfolding s'i_NF w_NF .
  qed
  then have "\<not> finite_dpp (nfs,m,P,Pw,lhss R, {}, R)" unfolding finite_dpp_def by blast
  with fin show False by simp
qed

lemma switch_to_innermost_locally_confluent_overlay: 
  assumes WCR: "WCR_on (rstep R) {t. SN_on (rstep R) {t}}"
  and overlay: "\<And> l r. (False,l,r) \<notin> critical_pairs ren R R" 
  and SN: "SN (qrstep nfs (lhss R) R)"
  and wf: "wf_trs R"
shows "SN (rstep R)"
proof (subst SN_innermost_switch_locally_confluent_overlay[symmetric, OF WCR _ wf])
  show "SN (inn_rstep R)" using SN irstep_is_inn_step[OF wf] unfolding irstep_def by auto
qed (insert overlay, auto)

lemma switch_to_innermost_triv_CP_overlay:
  assumes CP: "\<And> b l r. (b,l,r) \<in> critical_pairs ren R R \<Longrightarrow> b \<and> l = r"
    and SN: "SN (qrstep nfs (lhss R) R)"
    and wf: "wf_trs R"
  shows "SN (rstep R)"
proof (rule switch_to_innermost_locally_confluent_overlay[OF _ _ SN wf])
  have "WCR (rstep R)" 
    by (rule critical_pairs[of ren], insert assms(1), auto)
  thus "WCR_on (rstep R) {t. SN_on (rstep R) {t}}" 
    by (auto simp: WCR_defs)
qed (insert CP, auto)

end
