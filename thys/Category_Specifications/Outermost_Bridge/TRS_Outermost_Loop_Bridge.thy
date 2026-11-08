theory TRS_Outermost_Loop_Bridge
  imports TRS_Outermost_Equivalence Not_SN.Forbidden_Pattern_Loops_Impl
    Not_SN.Outermost_Forbidden_Patterns Proof_Checker.CSR_Check_Loops
begin
text \<open>A concrete loop can be iterated entirely inside its original ranked
signature. This needs checks on the finite witness, not a signature-extension
hypothesis or restrictions on the category's rules.\<close>
lemma outermost_ctxt_subst_signature:
  assumes "funas_ctxt C \<subseteq> F" "\<And>x. funas_term (mu x) \<subseteq> F"
    "funas_term t \<subseteq> F"
  shows "funas_term (ctxt_subst C mu n t) \<subseteq> F"
  using assms by (induct n) (auto simp: funas_term_subst)

lemma fploop_not_SN_signature:
  assumes loop: "fploop P R (C,mu,len,ts,ps)"
    and ctxt: "funas_ctxt C \<subseteq> F"
    and subst: "\<And>x. funas_term (mu x) \<subseteq> F"
    and terms: "\<And>i. i \<le> Suc len \<Longrightarrow> funas_term (ts i) \<subseteq> F"
  shows "\<not> SN (sig_step F (fpstep P R))"
proof -
  let ?S = "sig_step F (fpstep P R)"
  have iterate: "(ctxt_subst C mu n (ts 0),ctxt_subst C mu (Suc n) (ts 0)) \<in> ?S^+" for n
  proof -
    let ?t = "\<lambda>i. ctxt_subst C mu n (ts i)"
    have wf: "\<And>i. i \<le> Suc len \<Longrightarrow> funas_term (?t i) \<subseteq> F"
      by (rule outermost_ctxt_subst_signature[OF ctxt subst terms])
    have steps_i: "\<And>i. i \<le> len \<Longrightarrow> (?t i,?t (Suc i)) \<in> ?S"
    proof -
      fix i assume i: "i \<le> len"
      have fp: "(?t i,?t (Suc i)) \<in> fpstep P R"
        using fploop_fpstep_p[OF loop i, of n]
        unfolding fpstep_def rel_of_def by blast
      show "(?t i,?t (Suc i)) \<in> ?S"
        by (rule sig_stepI[OF fp]; rule wf) (use i in auto)
    qed
    have steps: "(?t 0,?t len) \<in> ?S^*"
      unfolding rtrancl_fun_conv
      by (rule exI[of _ ?t], rule exI[of _ len], insert steps_i, auto)
    have step: "(?t len,ctxt_subst C mu (Suc n) (ts 0)) \<in> ?S"
      using steps_i[of len] unfolding fploop_end[OF loop, of n] by simp
    from steps step show ?thesis by auto
  qed
  show ?thesis
  proof
    assume "SN ?S"
    then have sn: "SN (?S^+)" by (rule SN_imp_SN_trancl)
    have "\<exists>ts. \<forall>i. (ts i, ts (Suc i)) \<in> ?S^+"
      by (rule exI[of _ "\<lambda>n. ctxt_subst C mu n (ts 0)"], rule allI, rule iterate)
    with sn show False unfolding SN_defs by blast
  qed
qed

lemma check_fploop_not_SN_signature:
  assumes ok: "isOK (check_fploop R P (FP_loop_prf C mu t seq))"
    and ctxt: "funas_ctxt C \<subseteq> F"
    and subst: "\<And>x u. (x,u) \<in> set mu \<Longrightarrow> funas_term u \<subseteq> F"
    and start: "funas_term t \<subseteq> F"
    and terms: "\<And>p r u. (p,r,u) \<in> set seq \<Longrightarrow> funas_term u \<subseteq> F"
  shows "\<not> SN (sig_step F (fpstep (set P) (set R)))"
proof -
  have nonempty: "seq \<noteq> []" using ok by (auto simp: Let_def)
  have images: "\<And>x. funas_term (mk_subst Var mu x) \<subseteq> F"
    by (rule funas_mk_subst[OF subst])
  have ts: "\<And>i. i \<le> Suc (length seq - 1) \<Longrightarrow>
    funas_term ((t # map (\<lambda>(_,_,u). u) seq) ! i) \<subseteq> F"
  proof -
    fix i assume bound: "i \<le> Suc (length seq - 1)"
    have all: "\<forall>u\<in>set (t # map (\<lambda>(_,_,u). u) seq). funas_term u \<subseteq> F"
      using start terms by fastforce
    have index: "i < length (t # map (\<lambda>(_,_,u). u) seq)"
      using nonempty bound by (cases seq) auto
    show "funas_term ((t # map (\<lambda>(_,_,u). u) seq) ! i) \<subseteq> F"
      using all nth_mem[OF index] by blast
  qed
  show ?thesis by (rule fploop_not_SN_signature[OF check_fploop[OF ok] ctxt images ts])
qed

corollary trs_outermost_loop_checker_NO:
  assumes rules: "set Rs = to_rules R"
    and ok: "isOK (check_fploop Rs (o_to_fp_impl (map fst Rs)) (FP_loop_prf C mu t seq))"
    and ctxt: "funas_ctxt C \<subseteq> to_signature A"
    and subst: "\<And>x u. (x,u) \<in> set mu \<Longrightarrow> funas_term u \<subseteq> to_signature A"
    and start: "funas_term t \<subseteq> to_signature A"
    and terms: "\<And>p r u. (p,r,u) \<in> set seq \<Longrightarrow> funas_term u \<subseteq> to_signature A"
  shows "\<not> trs_outermost_terminates A R"
  using check_fploop_not_SN_signature[OF ok ctxt subst start terms]
  by (simp add: trs_outermost_terminates_iff_signature ostep_iff_fpstep rules)
end
