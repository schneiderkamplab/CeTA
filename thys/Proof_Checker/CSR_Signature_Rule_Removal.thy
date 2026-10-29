(* License: LGPL (see file COPYING.LESSER) *)
theory CSR_Signature_Rule_Removal
  imports CSR_Checker_Extensions.CSR_Conservative_Checker
begin

text \<open>Rule-removal reconstruction preserves the caller's signature.
This permits composition with processors whose soundness conclusion is
signature-restricted, without promoting that conclusion to global termination.\<close>

lemma csr_af_rule_removal_sig:
  assumes strict: "Rs \<subseteq> S"
    and weak: "Rr \<subseteq> NS"
    and mono_S: "af_monotone \<mu> S"
    and mono_NS: "af_monotone \<mu> NS"
    and subst_S: "subst.closed S"
    and subst_NS: "subst.closed NS"
    and compat_NS_S: "NS O S \<subseteq> S"
    and SN_S: "SN S"
    and rec: "SN (sig_step F (csstep \<mu> Rr))"
  shows "SN (sig_step F (csstep \<mu> (Rs \<union> Rr)))"
proof -
  have s_sub: "csstep \<mu> Rs \<subseteq> S"
    by (rule csstep_subset_order[OF strict mono_S subst_S])
  have ns_sub: "csstep \<mu> Rr \<subseteq> NS"
    by (rule csstep_subset_order[OF weak mono_NS subst_NS])
  have s_sig: "sig_step F (csstep \<mu> Rs) \<subseteq> S"
    using s_sub unfolding sig_step_def by auto
  have ns_sig: "sig_step F (csstep \<mu> Rr) \<subseteq> NS"
    using ns_sub unfolding sig_step_def by auto
  have rel: "SN_rel (sig_step F (csstep \<mu> Rs)) (sig_step F (csstep \<mu> Rr))"
    by (rule SN_rel_mono[OF s_sig ns_sig],
        unfold SN_rel_defs,
        rule SN_subset[OF compatible_SN'[OF compat_NS_S SN_S]],
        regexp)
  have relto: "SN (relto (sig_step F (csstep \<mu> Rs)) (sig_step F (csstep \<mu> Rr)))"
    by (rule SN_rel_imp_SN_relto[OF rel])
  have fin: "SN (sig_step F (csstep \<mu> Rs) \<union> sig_step F (csstep \<mu> Rr))"
    using relto rec SN_on_Un[of "sig_step F (csstep \<mu> Rs)" "sig_step F (csstep \<mu> Rr)" UNIV]
    by simp
  have sub: "csstep \<mu> (Rs \<union> Rr) \<subseteq> csstep \<mu> Rs \<union> csstep \<mu> Rr"
  proof
    fix st
    assume "st \<in> csstep \<mu> (Rs \<union> Rr)"
    then obtain p lr \<sigma> where
      step: "st \<in> rstep_r_p_s (Rs \<union> Rr) lr p \<sigma>"
      and cond: "csstep_cond \<mu> p (fst st)"
      unfolding csstep_def csstep_p_def by auto
    from step[unfolded rstep_r_p_s_def'] have lr: "lr \<in> Rs \<union> Rr"
      by auto
    from lr show "st \<in> csstep \<mu> Rs \<union> csstep \<mu> Rr"
    proof
      assume "lr \<in> Rs"
      with step cond show ?thesis
        unfolding csstep_def csstep_p_def rstep_r_p_s_def' by force
    next
      assume "lr \<in> Rr"
      with step cond show ?thesis
        unfolding csstep_def csstep_p_def rstep_r_p_s_def' by force
    qed
  qed
  have "sig_step F (csstep \<mu> (Rs \<union> Rr)) \<subseteq>
      sig_step F (csstep \<mu> Rs) \<union> sig_step F (csstep \<mu> Rr)"
    using sub unfolding sig_step_def by auto
  then show ?thesis by (rule SN_subset[OF fin])
qed


lemma csr_rule_removal_af_tt_sig:
  assumes rp: "rel_impl rp"
    and ok: "csr_rule_removal_af_tt rp fs \<mu> Rremove R = return R'"
    and af: "af_subset (mu_of \<mu>) (rel_impl.mono_af rp)"
    and rec: "SN (sig_step F (csstep (mu_of \<mu>) (set R')))"
  shows "SN (sig_step F (csstep (mu_of \<mu>) (set R)))"
proof -
  let ?Rr = "ceta_list_diff R Rremove"
  from ok[unfolded csr_rule_removal_af_tt_def Let_def, simplified] have
    valid: "isOK (rel_impl_redpair rp)"
    and orient: "isOK (rel_impl_s rp Rremove)" "isOK (rel_impl_ns rp ?Rr)"
    and R': "R' = ?Rr"
    by auto
  obtain ss nss where compat: "compat_redpair_order ss nss"
    and S: "set Rremove \<subseteq> ss"
    and NS: "set ?Rr \<subseteq> nss"
    and mono: "af_monotone (rel_impl.mono_af rp) ss"
  proof -
    from Term_Order_Impl.rel_impl_redpair[OF rp valid orient, of undefined undefined]
    obtain ss nss where red:
      "compat_redpair_order ss nss \<and> set Rremove \<subseteq> ss \<and>
       set ?Rr \<subseteq> nss \<and> af_monotone (rel_impl.mono_af rp) ss"
      by auto
    then show ?thesis
      by (intro that[of ss nss]) auto
  qed
  interpret compat_redpair_order ss nss by fact
  have mono_S: "af_monotone (mu_of \<mu>) ss"
    by (rule af_subset_af_monotone[OF af mono])
  have mono_NS: "af_monotone (mu_of \<mu>) nss"
    by (rule ctxt_closed_imp_af_monotone[OF ctxt_NS])
  have rem: "set R - set Rremove = set R'"
    using R' by simp
  have "SN (sig_step F (csstep (mu_of \<mu>) ((set R \<inter> set Rremove) \<union> (set R - set Rremove))))"
    by (rule csr_af_rule_removal_sig[OF _ _ mono_S mono_NS subst_S subst_NS compat_NS_S SN],
        insert S NS rec rem, auto)
  moreover have "(set R \<inter> set Rremove) \<union> (set R - set Rremove) = set R"
    by auto
  ultimately show ?thesis
    by simp
qed

lemma csr_int_rule_removal_tt_sig:
  fixes I :: "(('f::{showl, compare_order}, int) lpoly_interL)"
    and \<mu> :: "'f muL"
  assumes ok: "csr_int_rule_removal_tt I \<mu> Rremove R = return R'"
    and rec: "SN (sig_step F (csstep (mu_of \<mu>) (set R')))"
  shows "SN (sig_step F (csstep (mu_of \<mu>) (set R)))"
proof -
  let ?fs = "remdups (map fst I @ map fst \<mu>)"
  let ?rp = "int_rel_impl I"
  have mono_ok: "csr_int_mu_mono_check TYPE('f) TYPE('f) I \<mu> = return ()"
    using ok unfolding csr_int_rule_removal_tt_def Let_def
    by (cases "csr_int_mu_mono_check TYPE('f) TYPE('f) I \<mu>", simp_all)
  have af_ok: "csr_rule_removal_af_tt ?rp ?fs \<mu> Rremove R = return R'"
    using ok mono_ok unfolding csr_int_rule_removal_tt_def Let_def by simp
  have check_mono: "isOK (csr_int_mu_mono_check TYPE('f) TYPE('f) I \<mu>)"
    using mono_ok unfolding isOK_def by simp
  have all: "\<forall>f\<in>set ?fs. mu_of \<mu> f \<subseteq> rel_impl.mono_af ?rp f"
  proof
    fix f
    assume f: "f \<in> set ?fs"
    have f_union: "f \<in> fst ` set I \<union> fst ` set \<mu>"
      using f by auto
    show "mu_of \<mu> f \<subseteq> rel_impl.mono_af ?rp f"
    proof
      fix x
      assume x: "x \<in> mu_of \<mu> f"
      have sub: "mu_of \<mu> f \<subseteq> rel_impl.mono_af ?rp f"
        using check_mono[unfolded csr_int_mu_mono_check_def csr_mu_mono_check_def isOK_check_allm isOK_check] f
        unfolding Ball_def
        apply (drule_tac x=f in spec)
        apply (drule mp)
        apply assumption
        apply (simp add: create_poly_rel_impl_def Let_def)
        done
      from sub x show "x \<in> rel_impl.mono_af ?rp f"
        by (rule subsetD)
    qed
  qed
  have subset_fs: "set (map fst I @ map fst \<mu>) \<subseteq> set ?fs"
    by auto
  have af: "af_subset (mu_of \<mu>) (rel_impl.mono_af ?rp)"
    by (rule int_carrier_mu_af_subset[OF all subset_fs])
  show ?thesis
    by (rule csr_rule_removal_af_tt_sig[OF int_rel_impl af_ok af rec])
qed

lemma csr_int_mat_rule_removal_tt_sig:
  fixes I :: "(('f::{showl, compare_order}, int mat) lpoly_interL)"
    and \<mu> :: "'f muL"
  assumes ok: "csr_int_mat_rule_removal_tt n sd I \<mu> Rremove R = return R'"
    and rec: "SN (sig_step F (csstep (mu_of \<mu>) (set R')))"
  shows "SN (sig_step F (csstep (mu_of \<mu>) (set R)))"
proof -
  let ?fs = "remdups (map fst I @ map fst \<mu>)"
  let ?rp = "int_mat_rel_impl n sd I"
  have mono_ok: "csr_int_mat_mu_mono_check TYPE('f) TYPE('f) n sd I \<mu> = return ()"
    using ok unfolding csr_int_mat_rule_removal_tt_def Let_def
    by (cases "csr_int_mat_mu_mono_check TYPE('f) TYPE('f) n sd I \<mu>", simp_all)
  have af_ok: "csr_rule_removal_af_tt ?rp ?fs \<mu> Rremove R = return R'"
    using ok mono_ok unfolding csr_int_mat_rule_removal_tt_def Let_def by simp
  have check_mono: "isOK (csr_int_mat_mu_mono_check TYPE('f) TYPE('f) n sd I \<mu>)"
    using mono_ok unfolding isOK_def by simp
  have all: "\<forall>f\<in>set ?fs. mu_of \<mu> f \<subseteq> rel_impl.mono_af ?rp f"
  proof
    fix f
    assume f: "f \<in> set ?fs"
    show "mu_of \<mu> f \<subseteq> rel_impl.mono_af ?rp f"
    proof
      fix x
      assume x: "x \<in> mu_of \<mu> f"
      have sub: "mu_of \<mu> f \<subseteq> rel_impl.mono_af ?rp f"
        using check_mono[
          unfolded csr_int_mat_mu_mono_check_def csr_mu_mono_check_def
            isOK_check_allm isOK_check] f
        unfolding Ball_def
        apply (drule_tac x=f in spec)
        apply (drule mp)
        apply assumption
        apply (simp add: create_poly_rel_impl_def Let_def)
        done
      from sub x show "x \<in> rel_impl.mono_af ?rp f"
        by (rule subsetD)
    qed
  qed
  have subset_fs: "set (map fst I @ map fst \<mu>) \<subseteq> set ?fs"
    by auto
  have af: "af_subset (mu_of \<mu>) (rel_impl.mono_af ?rp)"
    by (rule int_mat_carrier_mu_af_subset[OF all subset_fs])
  show ?thesis
    by (rule csr_rule_removal_af_tt_sig[OF int_mat_rel_impl af_ok af rec])
qed

lemma csr_rule_removal_impl_sig:
  assumes ok: "csr_rule_removal_impl redp \<mu> Rremove R = return R'"
    and rec: "SN (sig_step F (csstep (mu_of \<mu>) (set R')))"
  shows "SN (sig_step F (csstep (mu_of \<mu>) (set R)))"
  using ok rec
  by (cases redp; simp add: csr_int_rule_removal_tt_sig csr_int_mat_rule_removal_tt_sig)

lemma csr_rule_removals_impl_sig_sound:
  assumes proc: "csr_rule_removals_impl ps \<mu> R = return R'"
    and fin: "SN (sig_step F (csstep (mu_of \<mu>) (set R')))"
  shows "SN (sig_step F (csstep (mu_of \<mu>) (set R)))"
  using proc fin
proof (induction ps arbitrary: R)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  obtain redp Rr where p: "p = (redp,Rr)" by (cases p, auto)
  from Cons.prems p obtain R2 where
    step: "csr_rule_removal_impl redp \<mu> Rr R = return R2"
    and rest: "csr_rule_removals_impl ps \<mu> R2 = return R'"
    by (cases "csr_rule_removal_impl redp \<mu> Rr R", auto)
  have residual: "SN (sig_step F (csstep (mu_of \<mu>) (set R2)))"
    by (rule Cons.IH[OF rest Cons.prems(2)])
  show ?case by (rule csr_rule_removal_impl_sig[OF step residual])
qed

end
