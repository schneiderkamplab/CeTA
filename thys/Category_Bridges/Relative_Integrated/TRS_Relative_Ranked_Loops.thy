theory TRS_Relative_Ranked_Loops
  imports Category_Specification_Bridges.TRS_Relative_Equivalence
    Category_Integrated_Base.Category_Integrated_Base
begin

text \<open>A concrete loop can establish nontermination on the declared
signature even when unrestricted relative signature extension is false.\<close>
definition ranked_relative_loop_guard where
  "ranked_relative_loop_guard F s loop_steps sigma C \<longleftrightarrow>
    funas_term s \<subseteq> F \<and> funas_ctxt C \<subseteq> F \<and>
    (\<forall>x. funas_term (mk_subst Var sigma x) \<subseteq> F) \<and>
    (\<forall>p r b t. (p,r,b,t) \<in> set loop_steps \<longrightarrow> funas_term t \<subseteq> F)"

lemma ranked_relative_loop_guard_finite:
  assumes "funas_term s \<subseteq> F" "funas_ctxt C \<subseteq> F"
    "\<And>x u. (x,u) \<in> set sigma \<Longrightarrow> funas_term u \<subseteq> F"
    "\<And>p r b t. (p,r,b,t) \<in> set loop_steps \<Longrightarrow> funas_term t \<subseteq> F"
  shows "ranked_relative_loop_guard F s loop_steps sigma C"
  using assms funas_mk_subst[OF assms(3)]
  by (auto simp: ranked_relative_loop_guard_def)

lemma ranked_rstep_map:
  assumes "(s,t) \<in> sig_step F (Trs.rstep R)"
    "funas_ctxt C \<subseteq> F" "\<forall>x. funas_term (sigma x) \<subseteq> F"
  shows "((ctxt_apply_term C (s \<cdot> sigma)), (ctxt_apply_term C (t \<cdot> sigma))) \<in> sig_step F (Trs.rstep R)"
  using assms by (auto simp: sig_step_def funas_term_subst)

lemma ranked_relto_map:
  assumes step: "(s,t) \<in> relto (sig_step F (Trs.rstep R)) (sig_step F (Trs.rstep S))"
    and ctx: "funas_ctxt C \<subseteq> F" and sub: "\<forall>x. funas_term (sigma x) \<subseteq> F"
  shows "((ctxt_apply_term C (s \<cdot> sigma)),(ctxt_apply_term C (t \<cdot> sigma))) \<in>
    relto (sig_step F (Trs.rstep R)) (sig_step F (Trs.rstep S))"
proof -
  have weak: "((ctxt_apply_term C (u \<cdot> sigma)),(ctxt_apply_term C (v \<cdot> sigma))) \<in> (sig_step F (Trs.rstep S))^*"
    if "(u,v) \<in> (sig_step F (Trs.rstep S))^*" for u v
    using that by (induct rule: rtrancl_induct)
      (simp, meson ranked_rstep_map[OF _ ctx sub] rtrancl_into_rtrancl)
  show ?thesis using step weak ranked_rstep_map[OF _ ctx sub] by blast
qed

lemma ranked_relative_loop:
  assumes path: "(s,(ctxt_apply_term C (s \<cdot> sigma))) \<in>
      (relto (sig_step F (Trs.rstep R)) (sig_step F (Trs.rstep S)))^+"
    and ctx: "funas_ctxt C \<subseteq> F"
    and sub: "\<forall>x. funas_term (sigma x) \<subseteq> F"
  shows "\<not> SN_rel (sig_step F (Trs.rstep R)) (sig_step F (Trs.rstep S))"
proof -
  let ?T = "relto (sig_step F (Trs.rstep R)) (sig_step F (Trs.rstep S))"
  let ?f = "\<lambda>t. (ctxt_apply_term C (t \<cdot> sigma))"
  have lift: "(?f u,?f v) \<in> ?T^+" if "(u,v) \<in> ?T^+" for u v
    using that by (induct rule: trancl_induct)
      (meson ranked_relto_map[OF _ ctx sub] r_into_trancl trancl_trans)+
  have edges: "((?f ^^ n) s,(?f ^^ Suc n) s) \<in> ?T^+" for n
  proof (induct n)
    case 0
    show ?case using path by simp
  next
    case (Suc n)
    have "(?f ((?f ^^ n) s),?f ((?f ^^ Suc n) s)) \<in> ?T^+"
      by (rule lift[OF Suc])
    then show ?case by (simp only: funpow.simps(2) comp_apply)
  qed
  have "\<not> SN (?T^+)"
    by (rule steps_imp_not_SN[of "\<lambda>n. (?f ^^ n) s" Suc]) (rule edges)
  then show ?thesis unfolding SN_rel_defs using SN_imp_SN_trancl by blast
qed
lemma ranked_check_rel_seq:
  assumes checked: "isOK (check_rel_seq Rs Ss loop_steps s t b)"
    and start: "funas_term s \<subseteq> F"
    and finish: "funas_term t \<subseteq> F"
    and terms: "\<forall>p r k u. (p,r,k,u) \<in> set loop_steps \<longrightarrow> funas_term u \<subseteq> F"
  shows "(s,t) \<in> (sig_step F (Trs.rstep (set Rs)) \<union> sig_step F (Trs.rstep (set Ss)))^* \<and>
    (\<not> b \<longrightarrow> (s,t) \<in> (sig_step F (Trs.rstep (set Rs)) \<union> sig_step F (Trs.rstep (set Ss)))^* O
      sig_step F (Trs.rstep (set Rs)) O (sig_step F (Trs.rstep (set Rs)) \<union> sig_step F (Trs.rstep (set Ss)))^*)"
  using assms
proof (induct loop_steps arbitrary: s b)
  case Nil
  then show ?case by (cases b) (auto simp: check_def)
next
  case (Cons entry rest)
  obtain p r k u where entry: "entry=(p,r,k,u)" by (cases entry) blast
  have valid: "funas_term u \<subseteq> F" using Cons.prems(4)[rule_format, of p r k u] by (simp add: entry)
  have checked_tail: "isOK (check_rel_seq Rs Ss rest u t (b \<or> k))"
    using Cons.prems(1) by (cases k; simp add: entry)
  have ih: "(u,t) \<in> (sig_step F (Trs.rstep (set Rs)) \<union> sig_step F (Trs.rstep (set Ss)))^* \<and>
    (\<not> (b \<or> k) \<longrightarrow> (u,t) \<in> (sig_step F (Trs.rstep (set Rs)) \<union> sig_step F (Trs.rstep (set Ss)))^* O
      sig_step F (Trs.rstep (set Rs)) O (sig_step F (Trs.rstep (set Rs)) \<union> sig_step F (Trs.rstep (set Ss)))^*)"
    by (rule Cons.hyps[OF checked_tail valid Cons.prems(3)]) (use Cons.prems(4) in auto)
  show ?case
  proof (cases k)
    case True
    have check: "isOK (check_qrstep (\<lambda>_. True) False Rs p r s u)"
      using Cons.prems(1) by (simp add: entry True)
    have "(s,u) \<in> Trs.rstep (set Rs)"
      using check_qrstep_qrstep[OF _ check, of "[]"] by auto
    then have "(s,u) \<in> sig_step F (Trs.rstep (set Rs))"
      using Cons.prems(2) valid by (simp add: sig_step_def)
    then show ?thesis using ih by (auto intro: converse_rtrancl_into_rtrancl)
  next
    case False
    have check: "isOK (check_qrstep (\<lambda>_. True) False Ss p r s u)"
      using Cons.prems(1) by (simp add: entry False)
    have "(s,u) \<in> Trs.rstep (set Ss)"
      using check_qrstep_qrstep[OF _ check, of "[]"] by auto
    then have st: "(s,u) \<in> sig_step F (Trs.rstep (set Ss))"
      using Cons.prems(2) valid by (simp add: sig_step_def)
    have prepend: "(s,v) \<in> (sig_step F (Trs.rstep (set Rs)) \<union> sig_step F (Trs.rstep (set Ss)))^*"
      if "(u,v) \<in> (sig_step F (Trs.rstep (set Rs)) \<union> sig_step F (Trs.rstep (set Ss)))^*" for v
      using st that by (auto intro: converse_rtrancl_into_rtrancl)
    have reach: "(s,t) \<in> (sig_step F (Trs.rstep (set Rs)) \<union> sig_step F (Trs.rstep (set Ss)))^*"
      by (rule prepend) (use ih in blast)
    have strict: "(s,t) \<in> (sig_step F (Trs.rstep (set Rs)) \<union> sig_step F (Trs.rstep (set Ss)))^* O
      sig_step F (Trs.rstep (set Rs)) O (sig_step F (Trs.rstep (set Rs)) \<union> sig_step F (Trs.rstep (set Ss)))^*"
      if "\<not> b"
    proof -
      note nb = that
      obtain v w where uv: "(u,v) \<in> (sig_step F (Trs.rstep (set Rs)) \<union> sig_step F (Trs.rstep (set Ss)))^*"
        and vw: "(v,w) \<in> sig_step F (Trs.rstep (set Rs))"
        and wt: "(w,t) \<in> (sig_step F (Trs.rstep (set Rs)) \<union> sig_step F (Trs.rstep (set Ss)))^*"
        using ih False nb by auto
      show ?thesis using prepend[OF uv] vw wt by auto
    qed
    show ?thesis using reach strict by blast
  qed
qed

lemma ranked_check_rel_loop_sound:
  assumes checked: "isOK (check_rel_loop s loop_steps sigma C Rs Ss)"
    and guard: "ranked_relative_loop_guard F s loop_steps sigma C"
  shows "\<not> SN_rel (sig_step F (Trs.rstep (set Rs))) (sig_step F (Trs.rstep (set Ss)))"
proof -
  have wf: "funas_term s \<subseteq> F" "funas_ctxt C \<subseteq> F"
    "\<forall>x. funas_term (mk_subst Var sigma x) \<subseteq> F"
    "\<forall>p r b t. (p,r,b,t) \<in> set loop_steps \<longrightarrow> funas_term t \<subseteq> F"
    using guard by (auto simp: ranked_relative_loop_guard_def)
  have target: "funas_term (ctxt_apply_term C (s \<cdot> mk_subst Var sigma)) \<subseteq> F"
    using wf by (auto simp: funas_term_subst)
  let ?P = "sig_step F (Trs.rstep (set Rs))"
  let ?Q = "sig_step F (Trs.rstep (set Ss))"
  have inclusion: "(?P \<union> ?Q)^* O ?P O (?P \<union> ?Q)^* \<subseteq> (relto ?P ?Q)^+"
    by regexp
  have seq: "(s,ctxt_apply_term C (s \<cdot> mk_subst Var sigma)) \<in>
    (sig_step F (Trs.rstep (set Rs)) \<union> sig_step F (Trs.rstep (set Ss)))^* O
      sig_step F (Trs.rstep (set Rs)) O (sig_step F (Trs.rstep (set Rs)) \<union> sig_step F (Trs.rstep (set Ss)))^*"
    using ranked_check_rel_seq[OF checked[unfolded check_rel_loop_def] wf(1) target wf(4)] by simp
  have path: "(s,(ctxt_apply_term C (s \<cdot> mk_subst Var sigma))) \<in>
    (relto (sig_step F (Trs.rstep (set Rs))) (sig_step F (Trs.rstep (set Ss))))^+"
    by (rule subsetD[OF inclusion seq])
  show ?thesis by (rule ranked_relative_loop[OF path wf(2,3)])
qed

lemma relative_integrated_ranked_loop:
  assumes accepted: "certify_integrated_cert_problem False
    (Inn_TRS_input No_Strategy Rs Ss) Termination (Decision False)
    (Inl (Relative_TRS_Nontermination_Proof (Rel_Loop (Rel_trs_loop_prf s loop_steps sigma C)))) = Certified"
    and guard: "ranked_relative_loop_guard F s loop_steps sigma C"
  shows "\<not> SN_rel (sig_step F (Trs.rstep (set Rs))) (sig_step F (Trs.rstep (set Ss)))"
proof -
  interpret I: tp_spec tp_impl by (rule tp_rbt_impl)
  let ?tp = "tp_ops.mk tp_impl False [] Rs Ss"
  have native: "isOK (check_rel_trs_loop tp_impl ?tp (Rel_trs_loop_prf s loop_steps sigma C))"
    using accepted
    by (cases "check_rel_trs_loop tp_impl ?tp (Rel_trs_loop_prf s loop_steps sigma C)";
      simp_all add: certify_integrated_cert_problem_def certify_cert_problem_rfc_absolute_def
        certify_cert_problem_def check_cert_def Let_def default_nfs_flag_def
        del: check_rel_trs_loop.simps split: sum.splits if_splits)
  have checked: "isOK (check_rel_loop s loop_steps sigma C (tp_ops.R tp_impl ?tp) (tp_ops.Rw tp_impl ?tp))"
    using native by auto
  from ranked_check_rel_loop_sound[OF checked guard]
  show ?thesis by simp
qed
end
