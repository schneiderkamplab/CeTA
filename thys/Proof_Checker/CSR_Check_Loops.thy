(*
Author:  Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Check_Loops
  imports
    Check_Nontermination
    CSR_Checker_Extensions.CSR_Conservative_Checker
begin

definition check_funas_term ::
  "('f :: equal \<times> nat) list \<Rightarrow> ('f,'v) term \<Rightarrow> showsl check"
where
  "check_funas_term F t =
    check (list_all (\<lambda>f. f \<in> set F) (funas_term_list t))
      (showsl_lit (STR ''loop term contains a symbol outside the input signature''))"

definition check_csr_loop ::
  "('f :: {equal,showl}) muL \<Rightarrow> ('f,string) rules \<Rightarrow>
    ('f,string) trs_loop_prf \<Rightarrow> showsl check"
where
  "check_csr_loop \<mu> R prf = (case prf of TRS_loop_prf s rseq \<sigma> C \<Rightarrow> do {
    check_fploop R (mu_to_fp_impl \<mu>) (FP_loop_prf C \<sigma> s rseq);
    let F = funas_trs_list R;
    check_allm (check_funas_term F)
      (s # map (\<lambda>(_,_,t). t) rseq);
    check_allm (\<lambda>(_,t). check_funas_term F t) \<sigma>
  })"

lemma check_funas_term_sound:
  assumes "isOK (check_funas_term F t)"
  shows "funas_term t \<subseteq> set F"
  using assms unfolding check_funas_term_def list_all_iff by auto

lemma funas_mk_subst:
  assumes "\<And>x t. (x,t) \<in> set \<sigma> \<Longrightarrow> funas_term t \<subseteq> F"
  shows "funas_term (mk_subst Var \<sigma> x) \<subseteq> F"
proof (cases "map_of \<sigma> x")
  case None
  then show ?thesis unfolding mk_subst_def by simp
next
  case (Some t)
  from map_of_SomeD[OF Some] assms have "funas_term t \<subseteq> F" by blast
  with Some show ?thesis unfolding mk_subst_def by simp
qed

lemma funas_ctxt_subst:
  fixes C :: "('f,'v) ctxt" and t :: "('f,'v) term"
    and \<sigma> :: "('f,'v) subst"
  assumes Ct: "funas_term (ctxt_apply_term C t) \<subseteq> F"
    and sig: "\<And>x. funas_term (\<sigma> x) \<subseteq> F"
  shows "funas_term (ctxt_subst C \<sigma> n t) \<subseteq> F"
proof (induct n)
  case 0
  from Ct show ?case by auto
next
  case (Suc n)
  from Ct have C: "funas_ctxt C \<subseteq> F" by auto
  from Suc sig have "funas_term (ctxt_subst C \<sigma> n t \<cdot> \<sigma>) \<subseteq> F"
    unfolding funas_term_subst by blast
  with C show ?case by auto
qed

lemma fploop_imp_not_SN_sig:
  fixes P :: "('f,'v) forb_patterns" and R :: "('f,'v) trs"
    and C :: "('f,'v) ctxt" and \<sigma> :: "('f,'v) subst"
    and ts :: "nat \<Rightarrow> ('f,'v) term" and ps :: "nat \<Rightarrow> pos"
  assumes loop: "fploop P R (C, \<sigma>, len, ts, ps)"
    and terms: "\<And>i. i \<le> Suc len \<Longrightarrow> funas_term (C\<langle>ts i\<rangle>) \<subseteq> F"
    and sig: "\<And>x. funas_term (\<sigma> x) \<subseteq> F"
  shows "\<not> SN (sig_step F (fpstep P R))"
proof
  assume SN: "SN (sig_step F (fpstep P R))"
  let ?O = "(sig_step F (fpstep P R))\<^sup>+"
  from SN have SN: "SN ?O" by (rule SN_imp_SN_trancl)
  let ?t = "\<lambda>n. ctxt_subst C \<sigma> n (ts 0)"
  have wf: "\<And>n i. i \<le> Suc len \<Longrightarrow>
      funas_term (ctxt_subst C \<sigma> n (ts i)) \<subseteq> F"
    by (rule funas_ctxt_subst[OF terms sig])
  have segments: "\<forall>n. (?t n, ?t (Suc n)) \<in> ?O"
  proof
    fix n
    let ?u = "\<lambda>i. ctxt_subst C \<sigma> n (ts i)"
    have steps: "\<And>i. i \<le> len \<Longrightarrow>
        (?u i, ?u (Suc i)) \<in> sig_step F (fpstep P R)"
    proof -
      fix i assume i: "i \<le> len"
      from fploop_fpstep_p[OF loop i, of n]
      have "(?u i, ?u (Suc i)) \<in> fpstep P R"
        unfolding fpstep_def by blast
      moreover from wf[of i n] i have "funas_term (?u i) \<subseteq> F" by simp
      moreover from wf[of "Suc i" n] i have "funas_term (?u (Suc i)) \<subseteq> F" by simp
      ultimately show "(?u i, ?u (Suc i)) \<in> sig_step F (fpstep P R)"
        unfolding sig_step_def by auto
    qed
    have prefix: "(?u 0, ?u len) \<in> (sig_step F (fpstep P R))\<^sup>*"
      unfolding rtrancl_fun_conv
      by (rule exI[of _ ?u], rule exI[of _ len], insert steps, auto)
    have last: "(?u len, ?t (Suc n)) \<in> sig_step F (fpstep P R)"
      using steps[of len] fploop_end[OF loop, of n] by simp
    from prefix last show "(?t n, ?t (Suc n)) \<in> ?O" by auto
  qed
  from segments have "\<exists>f. \<forall>i. (f i, f (Suc i)) \<in> ?O"
    by (rule exI[of _ ?t])
  with SN show False unfolding SN_defs by blast
qed

lemma check_csr_loop_sound:
  assumes ok: "isOK (check_csr_loop \<mu> R prf)"
  shows "\<not> SN (sig_step (set (funas_trs_list R))
    (csstep (mu_of \<mu>) (set R)))"
proof -
  obtain s rseq sigmaL C where prf_def: "prf = TRS_loop_prf s rseq sigmaL C"
    by (cases "prf")
  let ?F = "set (funas_trs_list R)"
  let ?\<sigma> = "mk_subst Var sigmaL"
  let ?ts = "\<lambda>i. (s # map (\<lambda>(_,_,t). t) rseq) ! i"
  let ?ps = "\<lambda>i. map (\<lambda>(p,_,_). p) rseq ! i"
  from ok[unfolded check_csr_loop_def prf_def Let_def]
  have fpok: "isOK (check_fploop R (mu_to_fp_impl \<mu>)
      (FP_loop_prf C sigmaL s rseq))"
    and termok: "\<And>t. t \<in> set (s # map (\<lambda>(_,_,t). t) rseq) \<Longrightarrow>
      isOK (check_funas_term (funas_trs_list R) t)"
    and substok: "\<And>x t. (x,t) \<in> set sigmaL \<Longrightarrow>
      isOK (check_funas_term (funas_trs_list R) t)"
    by auto
  from check_fploop[OF fpok]
  have loop: "fploop (set (mu_to_fp_impl \<mu>)) (set R)
      (C, ?\<sigma>, length rseq - 1, ?ts, ?ps)" .
  from fpok have nonempty: "rseq \<noteq> []" by simp
  have term_wf: "\<And>i. i \<le> length rseq \<Longrightarrow> funas_term (?ts i) \<subseteq> ?F"
  proof -
    fix i assume i: "i \<le> length rseq"
    have len: "length (s # map (\<lambda>(_,_,t). t) rseq) = Suc (length rseq)" by simp
    from i have mem: "?ts i \<in> set (s # map (\<lambda>(_,_,t). t) rseq)"
      unfolding set_conv_nth[of "s # map (\<lambda>(_,_,t). t) rseq"] len by auto
    from check_funas_term_sound[OF termok[OF mem]]
    show "funas_term (?ts i) \<subseteq> ?F" .
  qed
  have subst_wf: "\<And>x. funas_term (?\<sigma> x) \<subseteq> ?F"
    by (rule funas_mk_subst, rule check_funas_term_sound[OF substok], assumption)
  have C_wf: "funas_ctxt C \<subseteq> ?F"
  proof -
    from term_wf[of 0] have "funas_term s \<subseteq> ?F" by simp
    moreover from fpok have
      "(\<lambda>(_,_,t). t) (last rseq) = C\<langle>s \<cdot> ?\<sigma>\<rangle>"
      by (simp add: si_subst_subst_incr)
    moreover from term_wf[of "length rseq"] nonempty have
      "funas_term ((\<lambda>(_,_,t). t) (last rseq)) \<subseteq> ?F"
      by (cases rseq, auto simp: last_conv_nth)
    ultimately show ?thesis by auto
  qed
  have terms: "\<And>i. i \<le> Suc (length rseq - 1) \<Longrightarrow>
      funas_term (C\<langle>?ts i\<rangle>) \<subseteq> ?F"
    using nonempty C_wf term_wf by auto
  from fploop_imp_not_SN_sig[OF loop terms subst_wf]
  show ?thesis by (simp add: csstep_iff_fpstep_impl)
qed

end
