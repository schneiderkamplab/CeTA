(*
Author: Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Muterm_Usable_Rules
  imports
    CSR_Checker_Extensions.CSR_Minimal_CSDP_Proofs
    CSR_Innermost_Unhiding_Proofs
begin

text \<open>
  The QCS usable-rule simulation does not intrinsically depend on minimality.
  This full-chain variant is kept in the MU-TERM overlay because its first use
  is the recursive exact-unhiding processor; placing it in the central CSR-DP
  theory would force large checker rebuilds during development.
\<close>

lemma qcs_csr_relto_target_closed_full:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f, n)"
    and closed: "qcs_csr_ur_closed R U \<mu> P"
    and step: "(s, t) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>* O rrstep P O
      (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "qcs_ur_closed_dp_rhs R U \<mu> t"
proof -
  from closed have U_closed: "\<And>lr. lr \<in> U \<Longrightarrow>
      qcs_ur_closed_term R U \<mu> (snd lr)"
    and P_closed: "\<And>dp. dp \<in> P \<Longrightarrow>
      qcs_ur_closed_dp_rhs R U \<mu> (snd dp)"
    unfolding qcs_csr_ur_closed_def by auto
  from step obtain a b where pair: "(a,b) \<in> rrstep P"
    and suffix: "(b,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>*" by auto
  from qcs_ur_closed_rrstep_target[OF P_closed pair]
  have closed_b: "qcs_ur_closed_dp_rhs R U \<mu> b" .
  from qcs_ur_closed_csdp_steps[OF wf fresh U_closed closed_b suffix]
  show ?thesis by auto
qed

lemma qcs_csr_relto_transfer_full:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f, n)"
    and closed: "qcs_csr_ur_closed R U \<mu> P"
    and closed_s: "qcs_ur_closed_dp_rhs R U \<mu> s"
    and step: "(s, t) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>* O rrstep P O
      (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "(s, t) \<in>
      (csdp_step Sharp \<mu> U)\<^sup>* O rrstep P O
      (csdp_step Sharp \<mu> U)\<^sup>* \<and>
    qcs_ur_closed_dp_rhs R U \<mu> t"
proof -
  from closed have U_closed: "\<And>lr. lr \<in> U \<Longrightarrow>
      qcs_ur_closed_term R U \<mu> (snd lr)"
    and P_closed: "\<And>dp. dp \<in> P \<Longrightarrow>
      qcs_ur_closed_dp_rhs R U \<mu> (snd dp)"
    unfolding qcs_csr_ur_closed_def by auto
  from step obtain a b where prefix:
    "(s,a) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
    and pair: "(a,b) \<in> rrstep P"
    and suffix: "(b,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>*" by auto
  from qcs_ur_closed_csdp_steps[OF wf fresh U_closed closed_s prefix]
  have prefix_U: "(s,a) \<in> (csdp_step Sharp \<mu> U)\<^sup>*" by auto
  from qcs_ur_closed_rrstep_target[OF P_closed pair]
  have closed_b: "qcs_ur_closed_dp_rhs R U \<mu> b" .
  from qcs_ur_closed_csdp_steps[OF wf fresh U_closed closed_b suffix]
  have suffix_U: "(b,t) \<in> (csdp_step Sharp \<mu> U)\<^sup>*"
    and closed_t: "qcs_ur_closed_dp_rhs R U \<mu> t" by auto
  show ?thesis using prefix_U pair suffix_U closed_t by auto
qed

theorem finite_csr_dpp_qcs_usable_rules:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f, n)"
    and closed: "qcs_csr_ur_closed R U \<mu> P"
    and fin: "finite_csr_dpp Sharp \<mu> P U"
  shows "finite_csr_dpp Sharp \<mu> P R"
proof (unfold finite_csr_dpp_def SN_rel_on_def SN_on_def, intro notI)
  let ?PR = "rrstep P"
  let ?SR = "csdp_step Sharp \<mu> R"
  let ?SU = "csdp_step Sharp \<mu> U"
  assume "\<exists>f. f 0 \<in> UNIV \<and>
    (\<forall>n. (f n, f (Suc n)) \<in> ?SR\<^sup>* O ?PR O ?SR\<^sup>*)"
  then obtain f where chain:
    "\<And>n. (f n, f (Suc n)) \<in> ?SR\<^sup>* O ?PR O ?SR\<^sup>*"
    by auto
  from qcs_csr_relto_target_closed_full[OF wf fresh closed chain[of 0]]
  have closed_1: "qcs_ur_closed_dp_rhs R U \<mu> (f (Suc 0))" .
  let ?g = "\<lambda>n. f (Suc n)"
  have closed_g: "qcs_ur_closed_dp_rhs R U \<mu> (?g n)" for n
  proof (induct n)
    case 0
    show ?case using closed_1 by simp
  next
    case (Suc n)
    from qcs_csr_relto_transfer_full[
      OF wf fresh closed Suc.hyps chain[of "Suc n"]]
    show ?case by auto
  qed
  have g_step: "(?g n, ?g (Suc n)) \<in> ?SU\<^sup>* O ?PR O ?SU\<^sup>*" for n
    using qcs_csr_relto_transfer_full[
      OF wf fresh closed closed_g[of n] chain[of "Suc n"]] by auto
  from fin have no_U_chain:
    "\<not> (\<exists>h. h 0 \<in> UNIV \<and>
      (\<forall>n. (h n, h (Suc n)) \<in> ?SU\<^sup>* O ?PR O ?SU\<^sup>*))"
    unfolding finite_csr_dpp_def SN_rel_on_def SN_on_def .
  have U_chain: "\<exists>h. h 0 \<in> UNIV \<and>
      (\<forall>n. (h n, h (Suc n)) \<in> ?SU\<^sup>* O ?PR O ?SU\<^sup>*)"
  proof (intro exI[of _ ?g] conjI)
    show "?g 0 \<in> UNIV" by simp
    show "\<forall>n. (?g n, ?g (Suc n)) \<in> ?SU\<^sup>* O ?PR O ?SU\<^sup>*"
      using g_step by simp
  qed
  from no_U_chain U_chain show False by contradiction
qed

text \<open>
  Exact MU-TERM chains differ at one important point from ordinary CS-DP
  chains: a collapsing pair has a variable right-hand side, but that value is
  immediately exposed by one of the checked unhiding rules.  The following
  closure predicate records exactly the rules needed for that macro-step.  It
  deliberately accepts variable pair targets only here; the generic QCS
  usable-rule processor remains unchanged.
\<close>

definition muterm_qcs_ur_closed where
  "muterm_qcs_ur_closed R S W \<mu> P \<longleftrightarrow>
    S \<subseteq> W \<and> W \<subseteq> R \<union> S \<and>
    (\<forall>lr\<in>W \<inter> R.
      qcs_ur_closed_term R (W \<inter> R) \<mu> (snd lr)) \<and>
    (\<forall>lr\<in>S.
      qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (snd lr)) \<and>
    (\<forall>dp\<in>P. is_Var (snd dp) \<or>
      qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (snd dp))"

lemma muterm_qcs_ur_closed_S:
  assumes "muterm_qcs_ur_closed R S W \<mu> P"
  shows "S \<subseteq> W"
  using assms unfolding muterm_qcs_ur_closed_def by auto

lemma muterm_qcs_ur_closed_W:
  assumes "muterm_qcs_ur_closed R S W \<mu> P"
  shows "W \<subseteq> R \<union> S"
  using assms unfolding muterm_qcs_ur_closed_def by auto

lemma muterm_qcs_ur_closed_rule:
  assumes closed: "muterm_qcs_ur_closed R S W \<mu> P"
    and lr: "lr \<in> W \<inter> R"
  shows "qcs_ur_closed_term R (W \<inter> R) \<mu> (snd lr)"
  using closed lr unfolding muterm_qcs_ur_closed_def by auto

lemma muterm_qcs_ur_closed_unhiding_rule:
  assumes closed: "muterm_qcs_ur_closed R S W \<mu> P"
    and lr: "lr \<in> S"
  shows "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (snd lr)"
  using closed lr unfolding muterm_qcs_ur_closed_def by auto

lemma muterm_qcs_ur_closed_pair:
  assumes closed: "muterm_qcs_ur_closed R S W \<mu> P"
    and dp: "dp \<in> P" and rhs: "\<not> is_Var (snd dp)"
  shows "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (snd dp)"
  using closed dp rhs unfolding muterm_qcs_ur_closed_def by auto

lemma muterm_qcs_ur_closed_unhiding_target:
  assumes closed: "muterm_qcs_ur_closed R S W \<mu> P"
    and step: "(s, sharp_term Sharp t) \<in> rrstep S"
  shows "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu>
    (sharp_term Sharp t)"
proof -
  from step obtain l r \<sigma> where lr: "(l,r) \<in> S"
    and target: "sharp_term Sharp t = r \<cdot> \<sigma>"
    unfolding rrstep_def' by auto
  from muterm_qcs_ur_closed_unhiding_rule[OF closed lr]
  have rhs: "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> r" by simp
  from qcs_ur_closed_dp_rhs_subst[OF rhs, of \<sigma>]
  show ?thesis unfolding target .
qed

definition muterm_noncollapsing_rrstep where
  "muterm_noncollapsing_rrstep P s t \<longleftrightarrow>
    (\<exists>l r \<sigma>. (l,r) \<in> P \<and> \<not> is_Var r \<and>
      s = l \<cdot> \<sigma> \<and> t = r \<cdot> \<sigma>)"

lemma muterm_qcs_noncollapsing_target:
  assumes closed: "muterm_qcs_ur_closed R S W \<mu> P"
    and pair: "muterm_noncollapsing_rrstep P s t"
  shows "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> t"
proof -
  from pair obtain l r \<sigma> where lr: "(l,r) \<in> P"
    and r_fun: "\<not> is_Var r" and target: "t = r \<cdot> \<sigma>"
    unfolding muterm_noncollapsing_rrstep_def by auto
  from closed lr r_fun
  have r_closed: "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> r"
    unfolding muterm_qcs_ur_closed_def by auto
  from qcs_ur_closed_dp_rhs_subst[OF r_closed, of \<sigma>]
  show ?thesis unfolding target .
qed

lemma muterm_qcs_noncollapsing_suffix:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and closed: "muterm_qcs_ur_closed R S W \<mu> P"
    and pair: "muterm_noncollapsing_rrstep P s t"
    and suffix: "(t,u) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "(t,u) \<in> (csdp_step Sharp \<mu> (W \<inter> R))\<^sup>* \<and>
    qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> u"
proof -
  have rules: "\<And>lr. lr \<in> W \<inter> R \<Longrightarrow>
    qcs_ur_closed_term R (W \<inter> R) \<mu> (snd lr)"
    by (rule muterm_qcs_ur_closed_rule[OF closed])
  have target: "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> t"
    by (rule muterm_qcs_noncollapsing_target[OF closed pair])
  from qcs_ur_closed_csdp_steps[OF wf fresh rules target suffix]
  show ?thesis by auto
qed

lemma muterm_qcs_collapsing_unhiding_suffix:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and closed: "muterm_qcs_ur_closed R S W \<mu> P"
    and unhide: "(t,sharp_term Sharp v) \<in> rrstep S"
    and suffix: "(sharp_term Sharp v,u) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "(sharp_term Sharp v,u) \<in>
      (csdp_step Sharp \<mu> (W \<inter> R))\<^sup>* \<and>
    qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> u"
proof -
  have rules: "\<And>lr. lr \<in> W \<inter> R \<Longrightarrow>
    qcs_ur_closed_term R (W \<inter> R) \<mu> (snd lr)"
    by (rule muterm_qcs_ur_closed_rule[OF closed])
  have target: "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu>
    (sharp_term Sharp v)"
    by (rule muterm_qcs_ur_closed_unhiding_target[OF closed unhide])
  from qcs_ur_closed_csdp_steps[OF wf fresh rules target suffix]
  show ?thesis by auto
qed

end
