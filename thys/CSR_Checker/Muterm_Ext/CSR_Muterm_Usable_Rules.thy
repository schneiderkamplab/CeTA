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
  MU-TERM keeps ordinary context-sensitive steps and unhiding steps in
  different components.  This is essential for the innermost framework:
  minimality/normal-form obligations concern the source rules, whereas an
  unhiding rule is a bounded bridge immediately following a dependency-pair
  step.  In particular, the bridge must not be flattened into the ordinary
  rewrite-rule component of a generic DPP.
\<close>

definition muterm_typed_pair_step where
  "muterm_typed_pair_step P S =
    {(s,t). muterm_noncollapsing_rrstep P s t} \<union>
    {(s,t). \<exists>x. muterm_collapsing_rrstep P s x \<and> (x,t) \<in> rrstep S}"

definition finite_muterm_typed_dpp where
  "finite_muterm_typed_dpp shp \<mu> R P S \<longleftrightarrow>
    SN_rel (muterm_typed_pair_step P S) (csdp_step shp \<mu> R)"

lemma muterm_typed_pair_step_empty[simp]:
  "muterm_typed_pair_step {} S = {}"
  unfolding muterm_typed_pair_step_def muterm_noncollapsing_rrstep_def
    muterm_collapsing_rrstep_def by auto

lemma muterm_unhiding_relstep_typed:
  assumes wf: "wf_trs R"
    and hp: "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S t"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage Sharp \<mu> D R P S"
    and preserving: "muterm_unhiding_preserving_on Sharp \<mu> R S"
  shows "\<exists>u. has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S u \<and>
    (sharp_term Sharp t,sharp_term Sharp u) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>* O muterm_typed_pair_step P S"
proof -
  from hp have Tinf: "t \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    unfolding has_muterm_unhiding_property_def by auto
  from mu_Tinf_imp_SN_csnr_first_csrstep[OF wf Tinf]
  obtain s v where pref: "(t,s) \<in> (csnrstep \<mu> R)\<^sup>*"
    and root: "(s,v) \<in> csrstep \<mu> R"
    and notSN_v: "\<not> SN_on (csstep \<mu> R) {v}" by auto
  have sv: "(s,v) \<in> csstep \<mu> R"
    using root unfolding csstep_root_nonroot by auto
  have notSN_s: "\<not> SN_on (csstep \<mu> R) {s}"
    by (rule step_notSN_on_source[OF sv notSN_v])
  have sT: "s \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    by (rule csnrsteps_mu_Tinf_preserve[OF wf pref Tinf notSN_s])
  have hp_s: "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S s"
    by (rule muterm_unhiding_preserving_steps[OF wf preserving pref hp sT])
  from csrstep_muterm_unhiding_progress[
      OF wf root hp_s notSN_v defs cover preserving]
  obtain u where hp_u:
      "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S u"
    and event:
      "muterm_noncollapsing_rrstep P (sharp_term Sharp s) (sharp_term Sharp u) \<or>
       (\<exists>x. muterm_collapsing_rrstep P (sharp_term Sharp s) x \<and>
         (x,sharp_term Sharp u) \<in> rrstep S)" by blast
  have strict: "(sharp_term Sharp s,sharp_term Sharp u) \<in>
      muterm_typed_pair_step P S"
    using event unfolding muterm_typed_pair_step_def by blast
  have prefix: "(sharp_term Sharp t,sharp_term Sharp s) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>*"
    by (rule csnrsteps_imp_sharp_csdp_steps[OF pref])
  show ?thesis using hp_u prefix strict by blast
qed

theorem finite_muterm_typed_dpp_imp_SN_csstep:
  assumes wf: "wf_trs R"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage Sharp \<mu> D R P S"
    and preserving: "muterm_unhiding_preserving_on Sharp \<mu> R S"
    and fin: "finite_muterm_typed_dpp Sharp \<mu> R P S"
  shows "SN (csstep \<mu> R)"
proof (rule ccontr)
  assume notSN: "\<not> SN (csstep \<mu> R)"
  from not_SN_imp_Tinf[OF notSN] obtain t0 where
    t0T: "t0 \<in> Tinf (csstep \<mu> R)" by blast
  have hp0: "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S t0"
    by (rule Tinf_has_muterm_unhiding_property[OF t0T])
  have step_ex: "\<And>t. has_muterm_unhiding_property Sharp \<mu>
      (csstep \<mu> R) S t \<Longrightarrow>
      \<exists>u. has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S u \<and>
        (sharp_term Sharp t,sharp_term Sharp u) \<in>
          (csdp_step Sharp \<mu> R)\<^sup>* O muterm_typed_pair_step P S"
    by (rule muterm_unhiding_relstep_typed[OF wf _ defs cover preserving])
  have all_ex: "\<forall>t. \<exists>u.
      has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S t \<longrightarrow>
      has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S u \<and>
      (sharp_term Sharp t,sharp_term Sharp u) \<in>
        (csdp_step Sharp \<mu> R)\<^sup>* O muterm_typed_pair_step P S"
    using step_ex by blast
  from choice[OF all_ex] obtain nxt where nxt:
      "\<And>t. has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S t \<Longrightarrow>
       has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S (nxt t) \<and>
       (sharp_term Sharp t,sharp_term Sharp (nxt t)) \<in>
         (csdp_step Sharp \<mu> R)\<^sup>* O muterm_typed_pair_step P S" by blast
  define ts where "ts = rec_nat t0 (\<lambda>n t. nxt t)"
  have inv: "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S (ts n)"
    for n
    by (induct n, unfold ts_def, use hp0 nxt in auto)
  define f where "f n = sharp_term Sharp (ts n)" for n
  have chain: "(f n,f (Suc n)) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>* O muterm_typed_pair_step P S O
      (csdp_step Sharp \<mu> R)\<^sup>*" for n
    using nxt[OF inv[of n]] unfolding f_def ts_def by auto
  from fin have sn: "SN ((csdp_step Sharp \<mu> R)\<^sup>* O
      muterm_typed_pair_step P S O (csdp_step Sharp \<mu> R)\<^sup>*)"
    unfolding finite_muterm_typed_dpp_def SN_rel_on_def .
  moreover have "\<not> SN ((csdp_step Sharp \<mu> R)\<^sup>* O
      muterm_typed_pair_step P S O (csdp_step Sharp \<mu> R)\<^sup>*)"
    unfolding SN_defs using chain by blast
  ultimately show False by contradiction
qed

text \<open>
  MU-TERM's reduction-triple processor exploits the minimality invariant of
  chains extracted from a minimal nonterminating CSR term.  Keep this
  invariant in the semantic problem instead of labelling an unrestricted DPP
  as minimal.  In particular, the target of every typed macro pair must be
  strongly normalizing for the context-sensitive DP rewrite relation.
\<close>

definition muterm_min_typed_pair_step where
  "muterm_min_typed_pair_step shp \<mu> R P S =
    muterm_typed_pair_step P S \<inter>
      {(s,t). SN_on (csdp_step shp \<mu> R) {t}}"

definition finite_muterm_min_typed_dpp where
  "finite_muterm_min_typed_dpp shp \<mu> R P S \<longleftrightarrow>
    SN_rel (muterm_min_typed_pair_step shp \<mu> R P S)
      (csdp_step shp \<mu> R)"

lemma finite_muterm_typed_imp_finite_min_typed:
  assumes "finite_muterm_typed_dpp shp \<mu> R P S"
  shows "finite_muterm_min_typed_dpp shp \<mu> R P S"
proof -
  from assms have full: "SN_rel (muterm_typed_pair_step P S)
      (csdp_step shp \<mu> R)"
    unfolding finite_muterm_typed_dpp_def .
  have sub: "muterm_min_typed_pair_step shp \<mu> R P S \<subseteq>
      muterm_typed_pair_step P S"
    unfolding muterm_min_typed_pair_step_def by auto
  show ?thesis unfolding finite_muterm_min_typed_dpp_def
    by (rule SN_rel_mono[OF sub subset_refl full])
qed

lemma muterm_unhiding_relstep_min_typed:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and hp: "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S t"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage Sharp \<mu> D R P S"
    and preserving: "muterm_unhiding_preserving_on Sharp \<mu> R S"
  shows "\<exists>u. has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S u \<and>
    (sharp_term Sharp t,sharp_term Sharp u) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>* O
      muterm_min_typed_pair_step Sharp \<mu> R P S"
proof -
  from muterm_unhiding_relstep_typed[OF wf hp defs cover preserving]
  obtain u where hp_u:
      "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S u"
    and step: "(sharp_term Sharp t,sharp_term Sharp u) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>* O muterm_typed_pair_step P S"
    by blast
  from hp_u have uT: "u \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    unfolding has_muterm_unhiding_property_def by auto
  have target: "SN_on (csdp_step Sharp \<mu> R) {sharp_term Sharp u}"
    by (rule mu_Tinf_imp_SN_sharp_csdp[OF wf fresh uT])
  from step obtain v where prefix:
      "(sharp_term Sharp t,v) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
    and strict: "(v,sharp_term Sharp u) \<in> muterm_typed_pair_step P S"
    by auto
  have strict': "(v,sharp_term Sharp u) \<in>
      muterm_min_typed_pair_step Sharp \<mu> R P S"
    unfolding muterm_min_typed_pair_step_def using strict target by auto
  show ?thesis using hp_u prefix strict' by blast
qed

theorem finite_muterm_min_typed_dpp_imp_SN_csstep:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage Sharp \<mu> D R P S"
    and preserving: "muterm_unhiding_preserving_on Sharp \<mu> R S"
    and fin: "finite_muterm_min_typed_dpp Sharp \<mu> R P S"
  shows "SN (csstep \<mu> R)"
proof (rule ccontr)
  assume notSN: "\<not> SN (csstep \<mu> R)"
  from not_SN_imp_Tinf[OF notSN] obtain t0 where
    t0T: "t0 \<in> Tinf (csstep \<mu> R)" by blast
  have hp0: "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S t0"
    by (rule Tinf_has_muterm_unhiding_property[OF t0T])
  let ?A = "(csdp_step Sharp \<mu> R)\<^sup>* O
    muterm_min_typed_pair_step Sharp \<mu> R P S O
    (csdp_step Sharp \<mu> R)\<^sup>*"
  have step_ex: "\<And>t. has_muterm_unhiding_property Sharp \<mu>
      (csstep \<mu> R) S t \<Longrightarrow>
      \<exists>u. has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S u \<and>
        (sharp_term Sharp t,sharp_term Sharp u) \<in> ?A"
  proof -
    fix t
    assume hp: "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S t"
    from muterm_unhiding_relstep_min_typed[
      OF wf fresh hp defs cover preserving]
    obtain u where hp_u:
        "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S u"
      and step: "(sharp_term Sharp t,sharp_term Sharp u) \<in>
        (csdp_step Sharp \<mu> R)\<^sup>* O
        muterm_min_typed_pair_step Sharp \<mu> R P S"
      by blast
    have suffix: "(sharp_term Sharp u,sharp_term Sharp u) \<in>
        (csdp_step Sharp \<mu> R)\<^sup>*" by simp
    show "\<exists>u. has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S u \<and>
      (sharp_term Sharp t,sharp_term Sharp u) \<in> ?A"
      using hp_u step suffix by blast
  qed
  have all_ex: "\<forall>t. \<exists>u.
      has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S t \<longrightarrow>
      has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S u \<and>
      (sharp_term Sharp t,sharp_term Sharp u) \<in> ?A"
    using step_ex by blast
  from choice[OF all_ex] obtain nxt where nxt:
      "\<And>t. has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S t \<Longrightarrow>
       has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S (nxt t) \<and>
       (sharp_term Sharp t,sharp_term Sharp (nxt t)) \<in> ?A" by blast
  define ts where "ts = rec_nat t0 (\<lambda>n t. nxt t)"
  have inv: "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S (ts n)"
    for n
    by (induct n, unfold ts_def, use hp0 nxt in auto)
  define f where "f n = sharp_term Sharp (ts n)" for n
  have chain: "(f n,f (Suc n)) \<in> ?A" for n
    using nxt[OF inv[of n]] unfolding f_def ts_def by auto
  from fin have sn: "SN ?A"
    unfolding finite_muterm_min_typed_dpp_def SN_rel_on_def .
  moreover have "\<not> SN ?A" unfolding SN_defs using chain by blast
  ultimately show False by contradiction
qed

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

lemma muterm_unhiding_next_closed:
  assumes wf: "wf_trs R"
    and hp: "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S t"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage Sharp \<mu> D R P S"
    and preserving: "muterm_unhiding_preserving_on Sharp \<mu> R S"
    and closed: "muterm_qcs_ur_closed R S W \<mu> P"
  shows "\<exists>u. has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S u \<and>
    qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (sharp_term Sharp u)"
proof -
  from hp have Tinf: "t \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    unfolding has_muterm_unhiding_property_def by auto
  from mu_Tinf_imp_SN_csnr_first_csrstep[OF wf Tinf]
  obtain s v where pref: "(t,s) \<in> (csnrstep \<mu> R)\<^sup>*"
    and root: "(s,v) \<in> csrstep \<mu> R"
    and notSN_v: "\<not> SN_on (csstep \<mu> R) {v}" by auto
  have sv: "(s,v) \<in> csstep \<mu> R"
    using root unfolding csstep_root_nonroot by auto
  have notSN_s: "\<not> SN_on (csstep \<mu> R) {s}"
    by (rule step_notSN_on_source[OF sv notSN_v])
  have sT: "s \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    by (rule csnrsteps_mu_Tinf_preserve[OF wf pref Tinf notSN_s])
  have hp_s: "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S s"
    by (rule muterm_unhiding_preserving_steps[OF wf preserving pref hp sT])
  from csrstep_muterm_unhiding_progress[
      OF wf root hp_s notSN_v defs cover preserving]
  obtain u where hp_u:
      "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S u"
    and cases:
      "muterm_noncollapsing_rrstep P (sharp_term Sharp s) (sharp_term Sharp u) \<or>
       (\<exists>x. muterm_collapsing_rrstep P (sharp_term Sharp s) x \<and>
         (x,sharp_term Sharp u) \<in> rrstep S)" by blast
  have target: "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu>
      (sharp_term Sharp u)"
  proof -
    from cases show ?thesis
    proof
      assume noncoll: "muterm_noncollapsing_rrstep P
        (sharp_term Sharp s) (sharp_term Sharp u)"
      show ?thesis
        by (rule muterm_qcs_noncollapsing_target[OF closed noncoll])
    next
      assume "\<exists>x. muterm_collapsing_rrstep P (sharp_term Sharp s) x \<and>
        (x,sharp_term Sharp u) \<in> rrstep S"
      then obtain x where unhide: "(x,sharp_term Sharp u) \<in> rrstep S"
        by blast
      show ?thesis
        by (rule muterm_qcs_ur_closed_unhiding_target[OF closed unhide])
    qed
  qed
  show ?thesis using hp_u target by blast
qed

lemma muterm_unhiding_relstep_usable:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and hp: "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S t"
    and closed_t: "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu>
      (sharp_term Sharp t)"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage Sharp \<mu> D R P S"
    and preserving: "muterm_unhiding_preserving_on Sharp \<mu> R S"
    and closed: "muterm_qcs_ur_closed R S W \<mu> P"
  shows "\<exists>u. has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S u \<and>
    qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (sharp_term Sharp u) \<and>
    (sharp_term Sharp t,sharp_term Sharp u) \<in>
      (rstep W)\<^sup>* O rrstep P O (rstep W)\<^sup>*"
proof -
  from hp have Tinf: "t \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    unfolding has_muterm_unhiding_property_def by auto
  from mu_Tinf_imp_SN_csnr_first_csrstep[OF wf Tinf]
  obtain s v where pref: "(t,s) \<in> (csnrstep \<mu> R)\<^sup>*"
    and root: "(s,v) \<in> csrstep \<mu> R"
    and notSN_v: "\<not> SN_on (csstep \<mu> R) {v}" by auto
  have sv: "(s,v) \<in> csstep \<mu> R"
    using root unfolding csstep_root_nonroot by auto
  have notSN_s: "\<not> SN_on (csstep \<mu> R) {s}"
    by (rule step_notSN_on_source[OF sv notSN_v])
  have sT: "s \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    by (rule csnrsteps_mu_Tinf_preserve[OF wf pref Tinf notSN_s])
  have hp_s: "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S s"
    by (rule muterm_unhiding_preserving_steps[OF wf preserving pref hp sT])
  from csrstep_muterm_unhiding_progress[
      OF wf root hp_s notSN_v defs cover preserving]
  obtain u where hp_u:
      "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S u"
    and cases:
      "muterm_noncollapsing_rrstep P (sharp_term Sharp s) (sharp_term Sharp u) \<or>
       (\<exists>x. muterm_collapsing_rrstep P (sharp_term Sharp s) x \<and>
         (x,sharp_term Sharp u) \<in> rrstep S)" by blast
  have rules: "\<And>lr. lr \<in> W \<inter> R \<Longrightarrow>
      qcs_ur_closed_term R (W \<inter> R) \<mu> (snd lr)"
    by (rule muterm_qcs_ur_closed_rule[OF closed])
  have pref_R: "(sharp_term Sharp t,sharp_term Sharp s) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>*"
    by (rule csnrsteps_imp_sharp_csdp_steps[OF pref])
  from qcs_ur_closed_csdp_steps[OF wf fresh rules closed_t pref_R]
  have pref_UR: "(sharp_term Sharp t,sharp_term Sharp s) \<in>
      (csdp_step Sharp \<mu> (W \<inter> R))\<^sup>*" by auto
  have cs_sub: "csdp_step Sharp \<mu> (W \<inter> R) \<subseteq> rstep W"
  proof -
    have "csdp_step Sharp \<mu> (W \<inter> R) \<subseteq> rstep (W \<inter> R)"
      unfolding csdp_step_def csdp_step_p_def
      by (auto dest: rstep_r_p_s_imp_rstep)
    moreover have "rstep (W \<inter> R) \<subseteq> rstep W"
      by (rule rstep_mono, auto)
    ultimately show ?thesis by blast
  qed
  have prefix: "(sharp_term Sharp t,sharp_term Sharp s) \<in> (rstep W)\<^sup>*"
    using pref_UR rtrancl_mono[OF cs_sub] by blast
  have target_path: "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu>
      (sharp_term Sharp u) \<and>
    (sharp_term Sharp t,sharp_term Sharp u) \<in>
      (rstep W)\<^sup>* O rrstep P O (rstep W)\<^sup>*"
  proof -
    from cases show ?thesis
    proof
    assume noncoll: "muterm_noncollapsing_rrstep P
      (sharp_term Sharp s) (sharp_term Sharp u)"
    have pair: "(sharp_term Sharp s,sharp_term Sharp u) \<in> rrstep P"
      using noncoll unfolding muterm_noncollapsing_rrstep_def rrstep_def' by blast
    show ?thesis
    proof (intro conjI)
      show "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (sharp_term Sharp u)"
        by (rule muterm_qcs_noncollapsing_target[OF closed noncoll])
      show "(sharp_term Sharp t,sharp_term Sharp u) \<in>
          (rstep W)\<^sup>* O rrstep P O (rstep W)\<^sup>*"
        using prefix pair by auto
    qed
    next
    assume "\<exists>x. muterm_collapsing_rrstep P (sharp_term Sharp s) x \<and>
      (x,sharp_term Sharp u) \<in> rrstep S"
    then obtain x where pair_typed:
      "muterm_collapsing_rrstep P (sharp_term Sharp s) x"
      and unhide: "(x,sharp_term Sharp u) \<in> rrstep S" by blast
    have pair: "(sharp_term Sharp s,x) \<in> rrstep P"
      by (rule muterm_collapsing_rrstep_imp_rrstep[OF pair_typed])
    have S_W: "S \<subseteq> W" by (rule muterm_qcs_ur_closed_S[OF closed])
    have unhide_r: "(x,sharp_term Sharp u) \<in> rstep W"
    proof -
      have "(x,sharp_term Sharp u) \<in> rstep S"
        using unhide unfolding rstep_iff_rrstep_or_nrrstep by blast
      moreover have "rstep S \<subseteq> rstep W" by (rule rstep_mono[OF S_W])
      ultimately show ?thesis by blast
    qed
    show ?thesis
    proof (intro conjI)
      show "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (sharp_term Sharp u)"
        by (rule muterm_qcs_ur_closed_unhiding_target[OF closed unhide])
      show "(sharp_term Sharp t,sharp_term Sharp u) \<in>
          (rstep W)\<^sup>* O rrstep P O (rstep W)\<^sup>*"
        using prefix pair unhide_r by auto
    qed
    qed
  qed
  show ?thesis using hp_u target_path by blast
qed

lemma muterm_typed_relto_target_closed:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and closed: "muterm_qcs_ur_closed R S W \<mu> P"
    and step: "(s,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>* O
      muterm_typed_pair_step P S O (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> t"
proof -
  from step obtain a b where event: "(a,b) \<in> muterm_typed_pair_step P S"
    and suffix: "(b,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>*" by auto
  from closed have rules: "\<And>lr. lr \<in> W \<inter> R \<Longrightarrow>
      qcs_ur_closed_term R (W \<inter> R) \<mu> (snd lr)"
    and S_rules: "\<And>lr. lr \<in> S \<Longrightarrow>
      qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (snd lr)"
    unfolding muterm_qcs_ur_closed_def by auto
  have closed_b: "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> b"
  proof -
    from event show ?thesis unfolding muterm_typed_pair_step_def
    proof
      assume noncoll: "(a,b) \<in> {p. case p of (x,y) \<Rightarrow>
        muterm_noncollapsing_rrstep P x y}"
      then have "muterm_noncollapsing_rrstep P a b" by simp
      then show ?thesis
        by (rule muterm_qcs_noncollapsing_target[OF closed])
    next
      assume bridge: "(a,b) \<in>
        {(s,t). \<exists>x. muterm_collapsing_rrstep P s x \<and> (x,t) \<in> rrstep S}"
      then obtain x where pair_typed: "muterm_collapsing_rrstep P a x"
        and unhide: "(x,b) \<in> rrstep S" by auto
      show ?thesis
        by (rule qcs_ur_closed_rrstep_target[OF S_rules unhide])
    qed
  qed
  from qcs_ur_closed_csdp_steps[OF wf fresh rules closed_b suffix]
  show ?thesis by auto
qed

lemma muterm_typed_relto_transfer:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and closed: "muterm_qcs_ur_closed R S W \<mu> P"
    and closed_s: "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> s"
    and step: "(s,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>* O
      muterm_typed_pair_step P S O (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "(s,t) \<in> (rstep W)\<^sup>* O rrstep P O (rstep W)\<^sup>* \<and>
    qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> t"
proof -
  from closed have rules: "\<And>lr. lr \<in> W \<inter> R \<Longrightarrow>
      qcs_ur_closed_term R (W \<inter> R) \<mu> (snd lr)"
    and S_W: "S \<subseteq> W"
    and S_rules: "\<And>lr. lr \<in> S \<Longrightarrow>
      qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (snd lr)"
    unfolding muterm_qcs_ur_closed_def by auto
  have cs_sub: "csdp_step Sharp \<mu> (W \<inter> R) \<subseteq> rstep W"
  proof -
    have "csdp_step Sharp \<mu> (W \<inter> R) \<subseteq> rstep (W \<inter> R)"
      unfolding csdp_step_def csdp_step_p_def
      by (auto dest: rstep_r_p_s_imp_rstep)
    moreover have "rstep (W \<inter> R) \<subseteq> rstep W"
      by (rule rstep_mono, auto)
    ultimately show ?thesis by blast
  qed
  from step obtain a b where prefix: "(s,a) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
    and event: "(a,b) \<in> muterm_typed_pair_step P S"
    and suffix: "(b,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>*" by auto
  from qcs_ur_closed_csdp_steps[OF wf fresh rules closed_s prefix]
  have prefix_U: "(s,a) \<in> (csdp_step Sharp \<mu> (W \<inter> R))\<^sup>*"
    by auto
  have prefix_W: "(s,a) \<in> (rstep W)\<^sup>*"
    using prefix_U rtrancl_mono[OF cs_sub] by blast
  obtain x where pair: "(a,x) \<in> rrstep P"
    and bridge: "(x,b) \<in> (rstep W)\<^sup>*"
    and closed_b: "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> b"
  proof -
    from event show ?thesis unfolding muterm_typed_pair_step_def
    proof
      assume noncoll: "(a,b) \<in> {p. case p of (x,y) \<Rightarrow>
        muterm_noncollapsing_rrstep P x y}"
      then have nc: "muterm_noncollapsing_rrstep P a b" by simp
      have ab: "(a,b) \<in> rrstep P"
        using nc unfolding muterm_noncollapsing_rrstep_def rrstep_def' by blast
      have cb: "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> b"
        by (rule muterm_qcs_noncollapsing_target[OF closed nc])
      show ?thesis by (rule that[OF ab], use cb in auto)
    next
      assume raw: "(a,b) \<in>
        {(s,t). \<exists>x. muterm_collapsing_rrstep P s x \<and> (x,t) \<in> rrstep S}"
      then obtain y where ay_typed: "muterm_collapsing_rrstep P a y"
        and yb: "(y,b) \<in> rrstep S" by auto
      have ay: "(a,y) \<in> rrstep P"
        by (rule muterm_collapsing_rrstep_imp_rrstep[OF ay_typed])
      have yb_W: "(y,b) \<in> (rstep W)\<^sup>*"
      proof -
        have "(y,b) \<in> rstep S"
          using yb unfolding rstep_iff_rrstep_or_nrrstep by blast
        then have "(y,b) \<in> rstep W" using rstep_mono[OF S_W] by blast
        then show ?thesis by auto
      qed
      have cb: "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> b"
        by (rule qcs_ur_closed_rrstep_target[OF S_rules yb])
      show ?thesis by (rule that[OF ay yb_W cb])
    qed
  qed
  from qcs_ur_closed_csdp_steps[OF wf fresh rules closed_b suffix]
  have suffix_U: "(b,t) \<in> (csdp_step Sharp \<mu> (W \<inter> R))\<^sup>*"
    and closed_t: "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> t" by auto
  have suffix_W: "(b,t) \<in> (rstep W)\<^sup>*"
    using suffix_U rtrancl_mono[OF cs_sub] by blast
  have xt: "(x,t) \<in> (rstep W)\<^sup>*"
    using bridge suffix_W by auto
  show ?thesis using prefix_W pair xt closed_t by auto
qed

theorem finite_muterm_typed_dpp_usable:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and closed: "muterm_qcs_ur_closed R S W \<mu> P"
    and fin: "finite_dpp (False,False,P,{},{},{},W)"
  shows "finite_muterm_typed_dpp Sharp \<mu> R P S"
proof (unfold finite_muterm_typed_dpp_def SN_rel_on_def SN_on_def, intro notI)
  let ?A = "(csdp_step Sharp \<mu> R)\<^sup>* O
    muterm_typed_pair_step P S O (csdp_step Sharp \<mu> R)\<^sup>*"
  let ?B = "(rstep W)\<^sup>* O rrstep P O (rstep W)\<^sup>*"
  assume "\<exists>f. f 0 \<in> UNIV \<and> (\<forall>n. (f n,f (Suc n)) \<in> ?A)"
  then obtain f where chain: "\<And>n. (f n,f (Suc n)) \<in> ?A" by auto
  from muterm_typed_relto_target_closed[OF wf fresh closed chain[of 0]]
  have closed_1: "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (f (Suc 0))" .
  let ?g = "\<lambda>n. f (Suc n)"
  have closed_g: "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (?g n)" for n
  proof (induct n)
    case 0
    show ?case using closed_1 by simp
  next
    case (Suc n)
    from muterm_typed_relto_transfer[
      OF wf fresh closed Suc.hyps chain[of "Suc n"]]
    show ?case by auto
  qed
  have g_step: "(?g n,?g (Suc n)) \<in> ?B" for n
    using muterm_typed_relto_transfer[
      OF wf fresh closed closed_g[of n] chain[of "Suc n"]] by auto
  from fin have sn: "SN ?B"
    unfolding finite_dpp_iff_SN_rel CS_rrstep_conv SN_rel_on_def by simp
  have g_chain: "chain ?B ?g" using g_step by simp
  have not_sn: "\<not> SN ?B"
    by (rule not_SN_onI[of ?g], simp, rule g_chain)
  from not_sn sn show False ..
qed

theorem finite_muterm_usable_CSDP_imp_SN_csstep:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage Sharp \<mu> D R P S"
    and preserving: "muterm_unhiding_preserving_on Sharp \<mu> R S"
    and closed: "muterm_qcs_ur_closed R S W \<mu> P"
    and fin: "finite_dpp (False,False,P,{},{},{},W)"
  shows "SN (csstep \<mu> R)"
proof (rule ccontr)
  assume notSN: "\<not> SN (csstep \<mu> R)"
  from not_SN_imp_Tinf[OF notSN] obtain t0 where
    t0T: "t0 \<in> Tinf (csstep \<mu> R)" by blast
  have hp0: "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S t0"
    by (rule Tinf_has_muterm_unhiding_property[OF t0T])
  from muterm_unhiding_next_closed[
      OF wf hp0 defs cover preserving closed]
  obtain t1 where hp1:
      "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S t1"
    and closed1: "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu>
      (sharp_term Sharp t1)" by blast
  let ?A = "(rstep W)\<^sup>* O rrstep P O (rstep W)\<^sup>*"
  have step_ex: "\<And>t. has_muterm_unhiding_property Sharp \<mu>
      (csstep \<mu> R) S t \<Longrightarrow>
      qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (sharp_term Sharp t) \<Longrightarrow>
      \<exists>u. has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S u \<and>
        qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (sharp_term Sharp u) \<and>
        (sharp_term Sharp t,sharp_term Sharp u) \<in> ?A"
    by (rule muterm_unhiding_relstep_usable[
      OF wf fresh _ _ defs cover preserving closed])
  have all_ex: "\<forall>t. \<exists>u.
      (has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S t \<and>
       qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (sharp_term Sharp t)) \<longrightarrow>
      (has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S u \<and>
       qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (sharp_term Sharp u) \<and>
       (sharp_term Sharp t,sharp_term Sharp u) \<in> ?A)"
    using step_ex by blast
  from choice[OF all_ex] obtain nxt where nxt:
      "\<And>t. has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S t \<Longrightarrow>
        qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (sharp_term Sharp t) \<Longrightarrow>
        has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S (nxt t) \<and>
        qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (sharp_term Sharp (nxt t)) \<and>
        (sharp_term Sharp t,sharp_term Sharp (nxt t)) \<in> ?A"
    by blast
  define ts where "ts = rec_nat t1 (\<lambda>n t. nxt t)"
  have ts_inv: "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S (ts n) \<and>
      qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (sharp_term Sharp (ts n))"
    for n
  proof (induct n)
    case 0
    show ?case unfolding ts_def using hp1 closed1 by simp
  next
    case (Suc n)
    from nxt[OF Suc.hyps[THEN conjunct1] Suc.hyps[THEN conjunct2]]
    show ?case unfolding ts_def by simp
  qed
  have ts_step: "(sharp_term Sharp (ts n),sharp_term Sharp (ts (Suc n))) \<in> ?A"
    for n
    using nxt[OF ts_inv[of n, THEN conjunct1] ts_inv[of n, THEN conjunct2]]
    unfolding ts_def by simp
  define f where "f n = sharp_term Sharp (ts n)" for n
  have chain: "\<And>n. (f n,f (Suc n)) \<in> ?A"
    unfolding f_def using ts_step by simp
  have f_chain: "chain ?A f" using chain by simp
  have not_sn: "\<not> SN ?A"
    by (rule not_SN_onI[of f], simp, rule f_chain)
  from fin have rel_sn: "SN_rel (rrstep P) (rstep W)"
    unfolding finite_dpp_iff_SN_rel CS_rrstep_conv by simp
  then have sn: "SN ?A" unfolding SN_rel_on_def .
  from not_sn sn show False ..
qed

corollary finite_muterm_exact_usable_CSDP_imp_SN_csstep:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage Sharp \<mu> D R P S"
    and closed: "muterm_qcs_ur_closed R S W \<mu> P"
    and fin: "finite_dpp (False,False,P,{},{},{},W)"
  shows "SN (csstep \<mu> R)"
  by (rule finite_muterm_usable_CSDP_imp_SN_csstep[
      OF wf fresh defs cover
        muterm_unhiding_preserving_on_from_coverage[OF wf defs cover]
        closed fin])

definition muterm_qcs_ur_closed_check where
  "muterm_qcs_ur_closed_check R S W \<mu> P =
    (list_all (\<lambda>lr. lr \<in> set W) S \<and>
     list_all (\<lambda>lr. lr \<in> set R \<or> lr \<in> set S) W \<and>
     (let U = filter (\<lambda>lr. lr \<in> set R) W
      in list_all (\<lambda>lr. qcs_ur_closed_term_check R U \<mu> (snd lr)) U \<and>
         list_all (\<lambda>lr. qcs_ur_closed_dp_rhs_check R U \<mu> (snd lr)) S \<and>
         list_all (\<lambda>dp. is_Var (snd dp) \<or>
           qcs_ur_closed_dp_rhs_check R U \<mu> (snd dp)) P))"

lemma muterm_qcs_ur_closed_check_sound:
  assumes check: "muterm_qcs_ur_closed_check R S W \<mu> P"
  shows "muterm_qcs_ur_closed (set R) (set S) (set W) (mu_of \<mu>) (set P)"
proof -
  let ?U = "filter (\<lambda>lr. lr \<in> set R) W"
  have U_set: "set ?U = set W \<inter> set R" by auto
  from check have S_W: "set S \<subseteq> set W"
    and W_RS: "set W \<subseteq> set R \<union> set S"
    and U: "\<And>lr. lr \<in> set ?U \<Longrightarrow>
      qcs_ur_closed_term_check R ?U \<mu> (snd lr)"
    and S: "\<And>lr. lr \<in> set S \<Longrightarrow>
      qcs_ur_closed_dp_rhs_check R ?U \<mu> (snd lr)"
    and P: "\<And>dp. dp \<in> set P \<Longrightarrow> is_Var (snd dp) \<or>
      qcs_ur_closed_dp_rhs_check R ?U \<mu> (snd dp)"
    unfolding muterm_qcs_ur_closed_check_def Let_def
    by (auto simp: list_all_iff)
  show ?thesis unfolding muterm_qcs_ur_closed_def
  proof (intro conjI ballI)
    show "set S \<subseteq> set W" by (rule S_W)
    show "set W \<subseteq> set R \<union> set S" by (rule W_RS)
  next
    fix lr
    assume lr: "lr \<in> set W \<inter> set R"
    from qcs_ur_closed_term_check_sound[OF U[of lr]] lr U_set
    show "qcs_ur_closed_term (set R) (set W \<inter> set R)
      (mu_of \<mu>) (snd lr)" by simp
  next
    fix lr
    assume lr: "lr \<in> set S"
    from qcs_ur_closed_dp_rhs_check_sound[OF S[OF lr]] U_set
    show "qcs_ur_closed_dp_rhs (set R) (set W \<inter> set R)
      (mu_of \<mu>) (snd lr)" by simp
  next
    fix dp
    assume dp: "dp \<in> set P"
    from P[OF dp] show "is_Var (snd dp) \<or>
      qcs_ur_closed_dp_rhs (set R) (set W \<inter> set R)
        (mu_of \<mu>) (snd dp)"
    proof
      assume "is_Var (snd dp)"
      then show ?thesis by simp
    next
      assume checked: "qcs_ur_closed_dp_rhs_check R ?U \<mu> (snd dp)"
      from qcs_ur_closed_dp_rhs_check_sound[OF checked] U_set
      show ?thesis by simp
    qed
  qed
qed

datatype (dead 'f, dead 'l, dead 'v) muterm_typed_dp_proof =
    Muterm_Typed_P_Is_Empty
  | Muterm_Typed_Local_Usable
      "('f,'l,'v) trsLL" "('f,'l,'v) dp_termination_proof"
  | Muterm_Typed_CSR_Proof "('f,'l,'v) csr_dp_termination_proof"
  | Muterm_Typed_Dep_Graph
      "(('f,'l,'v) muterm_typed_dp_proof option \<times> ('f,'l,'v) trsLL) list"

definition check_muterm_typed_dep_graph where
  "check_muterm_typed_dep_graph \<mu> R S P dps = do {
    check_wf_trs (R @ S);
    check_subseteq P (concat (map snd dps))
      <+? (\<lambda>dp. showsl_lit (STR ''typed MU-TERM dependency pair '') \<circ>
        showsl_rule dp \<circ> showsl_lit (STR '' is missing in decomposition\<newline>''));
    check_graph_decomp
      (showsl \<circ> fst)
      (Multi_Map.empty (root o fst o fst))
      graph_approx_csr_rt Multi_Map.insert
      (csr_dep_graph_edge_check (csr_dp_root_mu (mu_of \<mu>)) (R @ S))
      (map (\<lambda>(real,Cs). (real \<noteq> None,
        map (\<lambda>(s,t). ((s,t),())) Cs)) dps)
  }"

fun check_muterm_typed_dp_proof ::
  "('tp, ('f::{showl,compare_order,countable},label_type) lab,string) tp_ops \<Rightarrow>
   ('dpp, ('f,label_type) lab,string) dpp_ops \<Rightarrow>
   (('f,label_type) lab) muL \<Rightarrow> showsl \<Rightarrow>
   (('f,label_type) lab,string) rules \<Rightarrow>
   (('f,label_type) lab,string) rules \<Rightarrow>
   (('f,label_type) lab,string) rules \<Rightarrow>
   ('f,label_type,string) muterm_typed_dp_proof \<Rightarrow> showsl check"
and check_muterm_typed_graph_components ::
  "('tp, ('f::{showl,compare_order,countable},label_type) lab,string) tp_ops \<Rightarrow>
   ('dpp, ('f,label_type) lab,string) dpp_ops \<Rightarrow>
   (('f,label_type) lab) muL \<Rightarrow> showsl \<Rightarrow>
   (('f,label_type) lab,string) rules \<Rightarrow>
   (('f,label_type) lab,string) rules \<Rightarrow>
   (('f,label_type) lab,string) rules \<Rightarrow>
   (('f,label_type,string) muterm_typed_dp_proof option \<times>
    ('f,label_type,string) trsLL) list \<Rightarrow> showsl check"
where
  "check_muterm_typed_dp_proof I J \<mu> i R S P Muterm_Typed_P_Is_Empty =
    check (P = []) (i \<circ> showsl_lit (STR '': MU-TERM dependency pairs are not empty''))"
| "check_muterm_typed_dp_proof I J \<mu> i R S P
      (Muterm_Typed_Local_Usable U prf) =
    debug i (STR ''MU-TERM ordinary reduction-pair continuation'') (do {
      check (list_all (\<lambda>lr. lr \<in> set U) S)
        (i \<circ> showsl_lit (STR '': MU-TERM usable rules omit an unhiding rule''));
      check (list_all (\<lambda>lr. lr \<in> set R \<or> lr \<in> set S) U)
        (i \<circ> showsl_lit (STR '': extraneous MU-TERM usable rule''));
      let UR = filter (\<lambda>lr. lr \<in> set R) U;
      check (list_all (\<lambda>lr.
          qcs_ur_closed_term_check R UR \<mu> (snd lr)) UR)
        (i \<circ> showsl_lit (STR '': ordinary MU-TERM rule closure failed''));
      check (list_all (\<lambda>lr.
          qcs_ur_closed_dp_rhs_check R UR \<mu> (snd lr)) S)
        (i \<circ> showsl_lit (STR '': MU-TERM unhiding closure failed''));
      check (list_all (\<lambda>dp. is_Var (snd dp) \<or>
          qcs_ur_closed_dp_rhs_check R UR \<mu> (snd dp)) P)
        (i \<circ> showsl_lit (STR '': MU-TERM pair closure failed''));
      check_dp_termination_proof I J False (add_index i 1)
        (dpp_ops.mk J False False P [] [] [] U) prf
    })"
| "check_muterm_typed_dp_proof I J \<mu> i R S P
      (Muterm_Typed_CSR_Proof prf) =
    debug i (STR ''MU-TERM noncollapsing CSR component'') (do {
      check (list_all (is_Fun \<circ> snd) P)
        (i \<circ> showsl_lit (STR '': collapsing pair requires the typed MU-TERM processor''));
      let dpp = dpp_ops.mk J False False P [] [] [] R;
      check_csr_dp_termination_proof_core I J \<mu> False (add_index i 1) dpp prf
    })"
| "check_muterm_typed_dp_proof I J \<mu> i R S P
      (Muterm_Typed_Dep_Graph edps) =
    debug i (STR ''typed MU-TERM dependency graph'') (do {
      _ \<leftarrow> check_muterm_typed_dep_graph \<mu> R S P edps;
      check_muterm_typed_graph_components I J \<mu> i R S P edps
    })"
| "check_muterm_typed_graph_components I J \<mu> i R S P [] = succeed"
| "check_muterm_typed_graph_components I J \<mu> i R S P
      ((None,C)#rest) =
    check_muterm_typed_graph_components I J \<mu> (add_index i 1) R S P rest"
| "check_muterm_typed_graph_components I J \<mu> i R S P
      ((Some prf,C)#rest) = do {
    check_muterm_typed_dp_proof I J \<mu> (add_index i 1) R S
      (filter (\<lambda>dp. dp \<in> set C) P) prf;
    check_muterm_typed_graph_components I J \<mu> (add_index i 1) R S P rest
  }"

lemma muterm_typed_pair_step_noncollapsing:
  assumes nc: "\<forall>dp\<in>P. is_Fun (snd dp)"
  shows "muterm_typed_pair_step P S = rrstep P"
proof (rule equalityI)
  show "muterm_typed_pair_step P S \<subseteq> rrstep P"
  proof
  fix st
  assume mem: "st \<in> muterm_typed_pair_step P S"
  then show "st \<in> rrstep P"
    unfolding muterm_typed_pair_step_def
  proof
    assume "st \<in> {(s,t). muterm_noncollapsing_rrstep P s t}"
    then obtain s t where st: "st = (s,t)"
      and step: "muterm_noncollapsing_rrstep P s t" by auto
    from step show ?thesis unfolding st muterm_noncollapsing_rrstep_def
      rrstep_def' by auto
  next
    assume "st \<in> {(s,t). \<exists>x.
      muterm_collapsing_rrstep P s x \<and> (x,t) \<in> rrstep S}"
    then obtain s t x where st: "st = (s,t)"
      and collapse: "muterm_collapsing_rrstep P s x" by auto
    from collapse obtain l y \<sigma> where pair: "(l,Var y) \<in> P"
      unfolding muterm_collapsing_rrstep_def by auto
    from nc[rule_format,OF pair] show ?thesis by simp
  qed
  qed
next
  show "rrstep P \<subseteq> muterm_typed_pair_step P S"
  proof
  fix st
  assume mem: "st \<in> rrstep P"
  obtain s t where st: "st = (s,t)" by (cases st)
  from mem obtain l r \<sigma> where pair: "(l,r) \<in> P"
    and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
    unfolding st rrstep_def' by auto
  have "muterm_noncollapsing_rrstep P s t"
    unfolding muterm_noncollapsing_rrstep_def
    using pair nc[rule_format,OF pair] s t by auto
  then show "st \<in> muterm_typed_pair_step P S"
    unfolding st muterm_typed_pair_step_def by auto
  qed
qed

lemma muterm_typed_pair_step_mono:
  assumes "P \<subseteq> Q"
  shows "muterm_typed_pair_step P S \<subseteq> muterm_typed_pair_step Q S"
proof
  fix st
  assume mem: "st \<in> muterm_typed_pair_step P S"
  obtain a b where st: "st = (a,b)" by (cases st)
  have memab: "(a,b) \<in> muterm_typed_pair_step P S" using mem st by simp
  from memab consider
      (noncoll) "muterm_noncollapsing_rrstep P a b"
    | (collapse) x where "muterm_collapsing_rrstep P a x"
        "(x,b) \<in> rrstep S"
    unfolding muterm_typed_pair_step_def by blast
  then show "st \<in> muterm_typed_pair_step Q S"
  proof cases
    case noncoll
    from noncoll obtain l r \<sigma> where pair: "(l,r) \<in> P" and rv: "\<not> is_Var r"
      and a: "a = l \<cdot> \<sigma>" and b: "b = r \<cdot> \<sigma>"
      unfolding muterm_noncollapsing_rrstep_def by auto
    have step: "muterm_noncollapsing_rrstep Q a b"
      unfolding muterm_noncollapsing_rrstep_def
      using assms pair rv a b by blast
    show ?thesis unfolding st muterm_typed_pair_step_def using step by blast
  next
    case (collapse x)
    from collapse(1) obtain l y \<sigma> where pair: "(l,Var y) \<in> P"
      and a: "a = l \<cdot> \<sigma>" and x: "x = \<sigma> y"
      unfolding muterm_collapsing_rrstep_def by auto
    have step: "muterm_collapsing_rrstep Q a x"
      unfolding muterm_collapsing_rrstep_def using assms pair a x by blast
    show ?thesis unfolding st muterm_typed_pair_step_def
      using step collapse(2) by blast
  qed
qed

lemma muterm_min_typed_pair_step_mono:
  assumes "P \<subseteq> Q"
  shows "muterm_min_typed_pair_step shp \<mu> R P S \<subseteq>
    muterm_min_typed_pair_step shp \<mu> R Q S"
  unfolding muterm_min_typed_pair_step_def
  using muterm_typed_pair_step_mono[OF assms] by blast

lemma finite_csr_dpp_imp_finite_muterm_typed_noncollapsing:
  assumes nc: "\<forall>dp\<in>P. is_Fun (snd dp)"
    and fin: "finite_csr_dpp Sharp \<mu> P R"
  shows "finite_muterm_typed_dpp Sharp \<mu> R P S"
  using fin muterm_typed_pair_step_noncollapsing[OF nc]
  unfolding finite_csr_dpp_def finite_muterm_typed_dpp_def by simp

lemma check_muterm_typed_graph_components_member:
  assumes ok: "isOK (check_muterm_typed_graph_components
      I J \<mu> i R S P edps)"
    and mem: "(Some prf,C) \<in> set edps"
  shows "\<exists>j. isOK (check_muterm_typed_dp_proof I J \<mu> j R S
    (filter (\<lambda>dp. dp \<in> set C) P) prf)"
  using ok mem
proof (induct edps arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons head rest)
  obtain po D where head: "head = (po,D)" by (cases head)
  show ?case
  proof (cases po)
    case None
    from Cons.prems(1) head None have tail:
      "isOK (check_muterm_typed_graph_components
        I J \<mu> (add_index i 1) R S P rest)" by simp
    from Cons.prems(2) head None have mem': "(Some prf,C) \<in> set rest"
      by auto
    show ?thesis by (rule Cons.hyps[OF tail mem'])
  next
    case (Some p)
    show ?thesis
    proof (cases "(Some prf,C) = head")
      case True
      from Cons.prems(1) head Some True show ?thesis by auto
    next
      case False
      from Cons.prems(1) head Some have tail:
        "isOK (check_muterm_typed_graph_components
          I J \<mu> (add_index i 1) R S P rest)" by simp
      from Cons.prems(2) False have mem': "(Some prf,C) \<in> set rest"
        by auto
      show ?thesis by (rule Cons.hyps[OF tail mem'])
    qed
  qed
qed

lemma rrstep_subset_csdp_step_union:
  "rrstep S \<subseteq> csdp_step Sharp \<mu> (R \<union> S)"
proof
  fix st
  assume "st \<in> rrstep S"
  then obtain l r \<sigma> where lr: "(l,r) \<in> S"
    and st: "st = (l \<cdot> \<sigma>,r \<cdot> \<sigma>)"
    unfolding rrstep_def' by auto
  have lr_union: "(l,r) \<in> R \<union> S" using lr by blast
  have root: "(l \<cdot> \<sigma>,r \<cdot> \<sigma>) \<in> rstep_r_p_s (R \<union> S) (l,r) [] \<sigma>"
    unfolding rstep_r_p_s_def Let_def using lr_union
    by (simp add: ctxt_supt_id)
  show "st \<in> csdp_step Sharp \<mu> (R \<union> S)"
    unfolding st csdp_step_def csdp_step_p_def
    apply (rule Quasi_Order.mem_rel_ofI)
    apply (rule exI[of _ "[]"])
    apply (rule Quasi_Order.mem_rel_ofI)
    apply (intro conjI)
     apply (rule exI[of _ "(l,r)"])
     apply (rule exI[of _ \<sigma>])
     apply (rule root)
    by (simp add: csdp_step_cond_def)
qed

lemma muterm_typed_relto_witness:
  assumes step: "(s,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>* O
      muterm_typed_pair_step P S O (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "\<exists>l r \<sigma>. (l,r) \<in> P \<and>
    (s,l \<cdot> \<sigma>) \<in> (csdp_step Sharp \<mu> (R \<union> S))\<^sup>* \<and>
    (r \<cdot> \<sigma>,t) \<in> (csdp_step Sharp \<mu> (R \<union> S))\<^sup>* \<and>
    (s,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>* O
      muterm_typed_pair_step {(l,r)} S O (csdp_step Sharp \<mu> R)\<^sup>*"
proof -
  from step obtain a b where pre: "(s,a) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
    and event: "(a,b) \<in> muterm_typed_pair_step P S"
    and post: "(b,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>*" by auto
  have Rsub: "csdp_step Sharp \<mu> R \<subseteq> csdp_step Sharp \<mu> (R \<union> S)"
  proof
    fix st
    assume mem: "st \<in> csdp_step Sharp \<mu> R"
    then obtain a b p lr \<sigma> where st: "st = (a,b)"
      and cond: "csdp_step_cond Sharp \<mu> p a"
      and raw: "(a,b) \<in> rstep_r_p_s R lr p \<sigma>"
      unfolding csdp_step_def csdp_step_p_def by auto
    from raw have lrR: "lr \<in> R"
      unfolding rstep_r_p_s_def Let_def by auto
    have lrRS: "lr \<in> R \<union> S" using lrR by blast
    have raw': "(a,b) \<in> rstep_r_p_s (R \<union> S) lr p \<sigma>"
      using raw lrRS unfolding rstep_r_p_s_def Let_def by auto
    show "st \<in> csdp_step Sharp \<mu> (R \<union> S)"
      unfolding st csdp_step_def csdp_step_p_def using cond raw' by blast
  qed
  have pre': "(s,a) \<in> (csdp_step Sharp \<mu> (R \<union> S))\<^sup>*"
    using pre rtrancl_mono[OF Rsub] by blast
  have post': "(b,t) \<in> (csdp_step Sharp \<mu> (R \<union> S))\<^sup>*"
    using post rtrancl_mono[OF Rsub] by blast
  have event_cases:
      "(a,b) \<in> {(s,t). muterm_noncollapsing_rrstep P s t} \<or>
       (a,b) \<in> {(s,t). \<exists>x.
         muterm_collapsing_rrstep P s x \<and> (x,t) \<in> rrstep S}"
    using event unfolding muterm_typed_pair_step_def by blast
  from event_cases show ?thesis
  proof
    assume raw: "(a,b) \<in> {(s,t). muterm_noncollapsing_rrstep P s t}"
    then have nc: "muterm_noncollapsing_rrstep P a b" by simp
    then obtain l r \<sigma> where pair: "(l,r) \<in> P" and rv: "\<not> is_Var r"
      and a: "a = l \<cdot> \<sigma>" and b: "b = r \<cdot> \<sigma>"
      unfolding muterm_noncollapsing_rrstep_def by blast
    have one: "muterm_noncollapsing_rrstep {(l,r)} a b"
      unfolding muterm_noncollapsing_rrstep_def using pair rv a b by auto
    have typed: "(a,b) \<in> muterm_typed_pair_step {(l,r)} S"
      unfolding muterm_typed_pair_step_def using one by auto
    have body: "(l,r) \<in> P \<and>
        (s,l \<cdot> \<sigma>) \<in> (csdp_step Sharp \<mu> (R \<union> S))\<^sup>* \<and>
        (r \<cdot> \<sigma>,t) \<in> (csdp_step Sharp \<mu> (R \<union> S))\<^sup>* \<and>
        (s,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>* O
          muterm_typed_pair_step {(l,r)} S O (csdp_step Sharp \<mu> R)\<^sup>*"
      using pair pre' post' pre typed post unfolding a b by blast
    show ?thesis using body by blast
  next
    assume raw: "(a,b) \<in> {(s,t). \<exists>x.
      muterm_collapsing_rrstep P s x \<and> (x,t) \<in> rrstep S}"
    then obtain x where collapse: "muterm_collapsing_rrstep P a x"
      and bridge: "(x,b) \<in> rrstep S" by auto
    from collapse obtain l y \<sigma> where pair: "(l,Var y) \<in> P"
      and a: "a = l \<cdot> \<sigma>" and x: "x = \<sigma> y"
      unfolding muterm_collapsing_rrstep_def by blast
    have one: "muterm_collapsing_rrstep {(l,Var y)} a x"
      unfolding muterm_collapsing_rrstep_def using a x by auto
    have typed: "(a,b) \<in> muterm_typed_pair_step {(l,Var y)} S"
      unfolding muterm_typed_pair_step_def using one bridge by auto
    have bridge': "(x,b) \<in> csdp_step Sharp \<mu> (R \<union> S)"
      using rrstep_subset_csdp_step_union bridge by blast
    have post'': "(x,t) \<in> (csdp_step Sharp \<mu> (R \<union> S))\<^sup>*"
      using bridge' post' by auto
    have vy: "Var y \<cdot> \<sigma> = \<sigma> y"
      by (cases "Var y", simp_all)
    have body: "(l,Var y) \<in> P \<and>
        (s,l \<cdot> \<sigma>) \<in> (csdp_step Sharp \<mu> (R \<union> S))\<^sup>* \<and>
        (\<sigma> y,t) \<in> (csdp_step Sharp \<mu> (R \<union> S))\<^sup>* \<and>
        (s,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>* O
          muterm_typed_pair_step {(l,Var y)} S O (csdp_step Sharp \<mu> R)\<^sup>*"
      using pair pre' post'' pre typed post
      unfolding a x by blast
    show ?thesis
      apply (rule_tac x=l in exI)
      apply (rule_tac x="Var y" in exI)
      apply (rule_tac x=\<sigma> in exI)
      using body vy by simp
  qed
qed

lemma muterm_min_typed_relto_witness:
  assumes step: "(s,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>* O
      muterm_min_typed_pair_step Sharp \<mu> R P S O
      (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "\<exists>l r \<sigma>. (l,r) \<in> P \<and>
    (s,l \<cdot> \<sigma>) \<in> (csdp_step Sharp \<mu> (R \<union> S))\<^sup>* \<and>
    (r \<cdot> \<sigma>,t) \<in> (csdp_step Sharp \<mu> (R \<union> S))\<^sup>* \<and>
    (s,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>* O
      muterm_min_typed_pair_step Sharp \<mu> R {(l,r)} S O
      (csdp_step Sharp \<mu> R)\<^sup>*"
proof -
  from step obtain a b where pre: "(s,a) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
    and event: "(a,b) \<in> muterm_min_typed_pair_step Sharp \<mu> R P S"
    and post: "(b,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>*" by auto
  from event have typed: "(a,b) \<in> muterm_typed_pair_step P S"
    and normal: "SN_on (csdp_step Sharp \<mu> R) {b}"
    unfolding muterm_min_typed_pair_step_def by auto
  have Rsub: "csdp_step Sharp \<mu> R \<subseteq> csdp_step Sharp \<mu> (R \<union> S)"
  proof
    fix st
    assume mem: "st \<in> csdp_step Sharp \<mu> R"
    then obtain x y p lr \<tau> where st: "st = (x,y)"
      and cond: "csdp_step_cond Sharp \<mu> p x"
      and raw: "(x,y) \<in> rstep_r_p_s R lr p \<tau>"
      unfolding csdp_step_def csdp_step_p_def by auto
    from raw have lrR: "lr \<in> R"
      unfolding rstep_r_p_s_def Let_def by auto
    have raw': "(x,y) \<in> rstep_r_p_s (R \<union> S) lr p \<tau>"
      using raw lrR unfolding rstep_r_p_s_def Let_def by auto
    show "st \<in> csdp_step Sharp \<mu> (R \<union> S)"
      unfolding st csdp_step_def csdp_step_p_def using cond raw' by blast
  qed
  have pre': "(s,a) \<in> (csdp_step Sharp \<mu> (R \<union> S))\<^sup>*"
    using pre rtrancl_mono[OF Rsub] by blast
  have post': "(b,t) \<in> (csdp_step Sharp \<mu> (R \<union> S))\<^sup>*"
    using post rtrancl_mono[OF Rsub] by blast
  from typed have cases:
      "muterm_noncollapsing_rrstep P a b \<or>
       (\<exists>x. muterm_collapsing_rrstep P a x \<and> (x,b) \<in> rrstep S)"
    unfolding muterm_typed_pair_step_def by blast
  from cases show ?thesis
  proof
    assume nc: "muterm_noncollapsing_rrstep P a b"
    then obtain l r \<sigma> where pair: "(l,r) \<in> P" and rv: "\<not> is_Var r"
      and a: "a = l \<cdot> \<sigma>" and b: "b = r \<cdot> \<sigma>"
      unfolding muterm_noncollapsing_rrstep_def by blast
    have one: "(a,b) \<in> muterm_typed_pair_step {(l,r)} S"
      unfolding muterm_typed_pair_step_def muterm_noncollapsing_rrstep_def
      using rv a b by auto
    have min: "(a,b) \<in> muterm_min_typed_pair_step Sharp \<mu> R {(l,r)} S"
      unfolding muterm_min_typed_pair_step_def using one normal by auto
    show ?thesis
      apply (rule_tac x=l in exI)
      apply (rule_tac x=r in exI)
      apply (rule_tac x=\<sigma> in exI)
      using pair pre' post' pre min post unfolding a b by blast
  next
    assume coll: "\<exists>x. muterm_collapsing_rrstep P a x \<and> (x,b) \<in> rrstep S"
    then obtain x where collapse: "muterm_collapsing_rrstep P a x"
      and bridge: "(x,b) \<in> rrstep S" by blast
    from collapse obtain l y \<sigma> where pair: "(l,Var y) \<in> P"
      and a: "a = l \<cdot> \<sigma>" and x: "x = \<sigma> y"
      unfolding muterm_collapsing_rrstep_def by blast
    have one_coll: "muterm_collapsing_rrstep {(l,Var y)} a x"
      unfolding muterm_collapsing_rrstep_def using a x by auto
    have one: "(a,b) \<in> muterm_typed_pair_step {(l,Var y)} S"
      unfolding muterm_typed_pair_step_def using one_coll bridge by auto
    have min: "(a,b) \<in>
        muterm_min_typed_pair_step Sharp \<mu> R {(l,Var y)} S"
      unfolding muterm_min_typed_pair_step_def using one normal by auto
    have bridge': "(x,b) \<in> csdp_step Sharp \<mu> (R \<union> S)"
      using rrstep_subset_csdp_step_union bridge by blast
    have post'': "(x,t) \<in> (csdp_step Sharp \<mu> (R \<union> S))\<^sup>*"
      using bridge' post' by auto
    have vy: "Var y \<cdot> \<sigma> = \<sigma> y" by simp
    have whole: "(s,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>* O
        muterm_min_typed_pair_step Sharp \<mu> R {(l,Var y)} S O
        (csdp_step Sharp \<mu> R)\<^sup>*"
      using pre min post unfolding a by blast
    show ?thesis
      apply (rule_tac x=l in exI)
      apply (rule_tac x="Var y" in exI)
      apply (rule_tac x=\<sigma> in exI)
      apply (intro conjI)
         apply (rule pair)
        apply (rule pre'[unfolded a])
       apply (simp only: vy, rule post''[unfolded x])
      by (rule whole)
  qed
qed

lemma csr_dep_graph_edge_check_steps_all:
  fixes R :: "(((('f::{showl,compare_order},label_type) lab),'v::compare_order) rules)"
  assumes wf: "wf_trs (set R)"
    and steps: "(t \<cdot> \<sigma>,u \<cdot> \<tau>) \<in>
      (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
  shows "csr_dep_graph_edge_check (csr_dp_root_mu (mu_of \<mu>)) R
    ((((s,t),()),((u,v),())))"
proof (simp only: csr_dep_graph_edge_check.simps, intro conjI notI)
  assume no: "csr_inactive_arg_no_edge (csr_dp_root_mu (mu_of \<mu>)) R t u"
  from csr_inactive_arg_no_edge_sound[OF wf no, of \<sigma> \<tau>] steps
  show False by blast
next
  assume no: "csr_frozen_root_no_edge (csr_dp_root_mu (mu_of \<mu>)) R t u"
  from csr_frozen_root_no_edge_sound[OF wf no, of \<sigma> \<tau>] steps
  show False by blast
next
  assume no: "csr_tcap_no_edge R t u"
  from csr_tcap_no_edge_sound[OF no, of \<sigma> \<tau>] steps
  show False by blast
next
  assume no: "csr_reverse_tcap_no_edge R t u"
  from csr_reverse_tcap_no_edge_sound[OF no, of \<sigma> \<tau>] steps
  show False by blast
next
  assume no: "csr_root_tcap_no_edge (csr_dp_root_mu (mu_of \<mu>)) R t u"
  from csr_root_tcap_no_edge_sound[OF wf no, of \<sigma> \<tau>] steps
  show False by blast
next
  assume no: "csr_shared_inactive_arg_no_edge
    (csr_dp_root_mu (mu_of \<mu>)) R t u"
  from csr_shared_inactive_arg_no_edge_sound[OF wf no, of \<sigma> \<tau>] steps
  show False by blast
next
  assume no: "csr_shared_source_inactive_arg_no_edge
    (csr_dp_root_mu (mu_of \<mu>)) R t u"
  from csr_shared_source_inactive_arg_no_edge_sound[OF wf no, of \<sigma> \<tau>] steps
  show False by blast
qed

lemma check_muterm_typed_dep_graph_select_component:
  fixes \<mu> :: "(('f::{showl,compare_order},label_type) lab) muL"
  assumes check: "isOK (check_muterm_typed_dep_graph \<mu> R S P edps)"
    and pair: "\<And>i. (s i,t i) \<in> set P"
    and steps: "\<And>i. (t i \<cdot> \<sigma> i,s (Suc i) \<cdot> \<sigma> (Suc i)) \<in>
      (csdp_step Sharp (mu_of \<mu>) (set (R @ S)))\<^sup>*"
  shows "\<exists>prf Cs n. (Some prf,Cs) \<in> set edps \<and>
    (\<forall>m. (s (m+n),t (m+n)) \<in> set P \<inter> set Cs)"
proof -
  let ?echeck = "csr_dep_graph_edge_check (csr_dp_root_mu (mu_of \<mu>)) (R @ S)"
  let ?conv = "\<lambda>(real,Cs). (real \<noteq> None,map (\<lambda>(s,t). ((s,t),())) Cs)"
  let ?p = "\<lambda>i. ((s i,t i),())"
  from check have wf: "wf_trs (set (R @ S))"
    and subset: "set P \<subseteq> set (concat (map snd edps))"
    and scc: "isOK (check_graph_decomp (showsl \<circ> fst)
      (Multi_Map.empty (root o fst o fst)) graph_approx_csr_rt
      Multi_Map.insert ?echeck (map ?conv edps))"
    unfolding check_muterm_typed_dep_graph_def by (auto simp: Let_def)
  have path: "\<And>i. ?echeck (?p i,?p (Suc i))"
  proof -
    fix i
    show "?echeck (?p i,?p (Suc i))"
      unfolding Let_def
      by (rule csr_dep_graph_edge_check_steps_all[
        where R="R @ S" and s="s i" and t="t i"
          and u="s (Suc i)" and v="t (Suc i)"
          and \<sigma>="\<sigma> i" and \<tau>="\<sigma> (Suc i)",
        OF wf steps[of i]])
  qed
  have lift_node: "\<And>l r. (l,r) \<in> set (concat (map snd edps)) \<Longrightarrow>
    ((l,r),()) \<in> set (concat (map snd (map ?conv edps)))"
  proof -
    fix l r
    assume lr: "(l,r) \<in> set (concat (map snd edps))"
    then obtain x where x: "x \<in> set edps" and lrx: "(l,r) \<in> set (snd x)"
      by auto
    obtain real Cs where xeq: "x = (real,Cs)" by (cases x,auto)
    from x xeq have mem: "(real,Cs) \<in> set edps" by simp
    from lrx xeq have lrCs: "(l,r) \<in> set Cs" by simp
    have node: "((l,r),()) \<in> set (map (\<lambda>(s,t). ((s,t),())) Cs)"
      using lrCs by force
    have conv_mem: "?conv (real,Cs) \<in> set (map ?conv edps)"
      using mem by (auto split: prod.splits)
    have comp_mem: "snd (?conv (real,Cs)) \<in> set (map snd (map ?conv edps))"
      using conv_mem unfolding set_map by blast
    have node': "((l,r),()) \<in> set (snd (?conv (real,Cs)))" using node by simp
    show "((l,r),()) \<in> set (concat (map snd (map ?conv edps)))"
      using comp_mem node' unfolding set_concat by blast
  qed
  have nodes: "path_nodes ?p \<subseteq> set (concat (map snd (map ?conv edps)))"
    using pair subset lift_node unfolding path_nodes_def by blast
  have key_insert: "\<And>x m. Multi_Map.key_fun m = root \<circ> fst \<circ> fst \<Longrightarrow>
    Multi_Map.key_fun (Multi_Map.insert x m) = root \<circ> fst \<circ> fst" by simp
  have approx: "\<And>m a b. Multi_Map.key_fun m = root \<circ> fst \<circ> fst \<Longrightarrow>
    ?echeck (a,b) \<Longrightarrow> b \<in> set (Multi_Map.values m) \<Longrightarrow>
    b \<in> set (graph_approx_csr_rt m a)"
    unfolding graph_approx_csr_rt.simps by simp
  have component: "\<exists>q C. (?p =\<dots> q) \<and>
    C \<in> set (map snd (filter fst (map ?conv edps))) \<and>
    path_nodes q \<subseteq> set C"
    by (rule check_graph_decomp_sound[of "\<lambda>m. set (Multi_Map.values m)",
      OF values_empty values_insert, of "\<lambda>m. Multi_Map.key_fun m = (root o fst o fst)",
      OF key_fun_empty key_insert approx scc path nodes])
  from component obtain q C where suffix: "?p =\<dots> q"
    and ending: "path_nodes q \<subseteq> set C"
    and component_mem: "C \<in> set (map snd (filter fst (map ?conv edps)))"
    by blast
  from component_mem obtain p Cs where mem: "(Some p,Cs) \<in> set edps"
    and C: "C = map (\<lambda>(s,t). ((s,t),())) Cs" by force
  from suffix obtain n where pq: "\<And>m. ?p (m+n) = q m"
    unfolding Graph.suffix_def by blast
  have CP: "\<And>m. (s (m+n),t (m+n)) \<in> set P \<inter> set Cs"
  proof -
    fix m
    have "?p (m+n) \<in> path_nodes q"
      using pq[of m] unfolding path_nodes_def by blast
    with ending C pair[of "m+n"]
    show "(s (m+n),t (m+n)) \<in> set P \<inter> set Cs" by force
  qed
  show ?thesis
  proof (intro exI conjI)
    show "(Some p,Cs) \<in> set edps" by (rule mem)
    show "\<forall>m. (s (m+n),t (m+n)) \<in> set P \<inter> set Cs"
    proof
      fix m
      show "(s (m+n),t (m+n)) \<in> set P \<inter> set Cs" by (rule CP)
    qed
  qed
qed

lemma check_muterm_typed_dep_graph_sound:
  fixes \<mu> :: "(('f::{showl,compare_order},label_type) lab) muL"
  assumes check: "isOK (check_muterm_typed_dep_graph \<mu> R S P edps)"
    and fin: "\<And>prf C. (Some prf,C) \<in> set edps \<Longrightarrow>
      finite_muterm_typed_dpp Sharp (mu_of \<mu>) (set R)
        (set P \<inter> set C) (set S)"
  shows "finite_muterm_typed_dpp Sharp (mu_of \<mu>) (set R) (set P) (set S)"
proof -
  let ?P = "set P"
  let ?RL = "R @ S"
  let ?RS = "set ?RL"
  show ?thesis
    unfolding finite_muterm_typed_dpp_def SN_rel_on_def SN_on_def
  proof (rule notI)
    let ?A = "(csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
      muterm_typed_pair_step ?P (set S) O
      (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
    assume infinite: "\<exists>f. f 0 \<in> UNIV \<and>
      (\<forall>i. (f i,f (Suc i)) \<in> ?A)"
    then obtain ch where chain: "\<And>i. (ch i,ch (Suc i)) \<in> ?A" by auto
    have ex_step: "\<forall>i. \<exists>l r \<sigma>.
      (l,r) \<in> ?P \<and>
      (ch i,l \<cdot> \<sigma>) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
      (r \<cdot> \<sigma>,ch (Suc i)) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
      (ch i,ch (Suc i)) \<in>
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
        muterm_typed_pair_step {(l,r)} (set S) O
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
    proof
      fix i
      from muterm_typed_relto_witness[OF chain[of i]]
      show "\<exists>l r \<sigma>. (l,r) \<in> ?P \<and>
        (ch i,l \<cdot> \<sigma>) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
        (r \<cdot> \<sigma>,ch (Suc i)) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
        (ch i,ch (Suc i)) \<in>
          (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
          muterm_typed_pair_step {(l,r)} (set S) O
          (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
        by (simp add: set_append)
    qed
    from choice[OF ex_step] obtain s where choose_s: "\<forall>i. \<exists>r \<sigma>.
      (s i,r) \<in> ?P \<and>
      (ch i,s i \<cdot> \<sigma>) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
      (r \<cdot> \<sigma>,ch (Suc i)) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
      (ch i,ch (Suc i)) \<in>
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
        muterm_typed_pair_step {(s i,r)} (set S) O
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
      by blast
    from choice[OF choose_s] obtain t where choose_t: "\<forall>i. \<exists>\<sigma>.
      (s i,t i) \<in> ?P \<and>
      (ch i,s i \<cdot> \<sigma>) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
      (t i \<cdot> \<sigma>,ch (Suc i)) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
      (ch i,ch (Suc i)) \<in>
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
        muterm_typed_pair_step {(s i,t i)} (set S) O
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
      by blast
    from choice[OF choose_t] obtain \<sigma> where chosen: "\<forall>i.
      (s i,t i) \<in> ?P \<and>
      (ch i,s i \<cdot> \<sigma> i) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
      (t i \<cdot> \<sigma> i,ch (Suc i)) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
      (ch i,ch (Suc i)) \<in>
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
        muterm_typed_pair_step {(s i,t i)} (set S) O
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
      by blast
    from chosen have pair: "\<And>i. (s i,t i) \<in> ?P"
      and pre: "\<And>i. (ch i,s i \<cdot> \<sigma> i) \<in>
        (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>*"
      and post: "\<And>i. (t i \<cdot> \<sigma> i,ch (Suc i)) \<in>
        (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>*"
      and typed: "\<And>i. (ch i,ch (Suc i)) \<in>
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
        muterm_typed_pair_step {(s i,t i)} (set S) O
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
      by blast+
    have steps: "\<And>i. (t i \<cdot> \<sigma> i,s (Suc i) \<cdot> \<sigma> (Suc i)) \<in>
      (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>*"
      using post pre by (meson rtrancl_trans)
    from check_muterm_typed_dep_graph_select_component[
      where \<mu>=\<mu> and R=R and S=S and P=P and edps=edps
        and s=s and t=t and \<sigma>=\<sigma>, OF check pair steps]
    obtain p Cs n where mem: "(Some p,Cs) \<in> set edps"
      and CP_all: "\<forall>m. (s (m+n),t (m+n)) \<in> ?P \<inter> set Cs"
      by auto
    from CP_all have CP: "\<And>m. (s (m+n),t (m+n)) \<in> ?P \<inter> set Cs"
      by auto
    let ?tail = "\<lambda>m. ch (m+n)"
    have tail_step: "\<And>m. (?tail m,?tail (Suc m)) \<in>
      (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
      muterm_typed_pair_step (?P \<inter> set Cs) (set S) O
      (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
    proof -
      fix m
      have singleton: "{(s (m+n),t (m+n))} \<subseteq> ?P \<inter> set Cs"
        using CP[of m] by auto
      have mono: "muterm_typed_pair_step {(s (m+n),t (m+n))} (set S)
        \<subseteq> muterm_typed_pair_step (?P \<inter> set Cs) (set S)"
        by (rule muterm_typed_pair_step_mono[OF singleton])
      have suc_add: "Suc m+n = Suc (m+n)" by simp
      have inc: "(csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
          muterm_typed_pair_step {(s (m+n),t (m+n))} (set S) O
          (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* \<subseteq>
          (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
          muterm_typed_pair_step (?P \<inter> set Cs) (set S) O
          (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
        by (meson relcomp_mono mono subset_refl)
      from typed[of "m+n"] inc show "(?tail m,?tail (Suc m)) \<in>
          (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
          muterm_typed_pair_step (?P \<inter> set Cs) (set S) O
          (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
        unfolding suc_add
        by blast
    qed
    have tail_sn: "SN ((csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
      muterm_typed_pair_step (?P \<inter> set Cs) (set S) O
      (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*)"
      using fin[OF mem]
      unfolding finite_muterm_typed_dpp_def SN_rel_on_def .
    have tail_is_chain: "chain
      ((csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
       muterm_typed_pair_step (?P \<inter> set Cs) (set S) O
       (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*) ?tail"
      using tail_step by simp
    have not_tail_sn: "\<not> SN ((csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
      muterm_typed_pair_step (?P \<inter> set Cs) (set S) O
      (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*)"
      by (rule not_SN_onI[of ?tail], simp, rule tail_is_chain)
    from not_tail_sn tail_sn show False ..
  qed
qed


lemma check_muterm_min_typed_dep_graph_sound:
  fixes \<mu> :: "(('f::{showl,compare_order},label_type) lab) muL"
  assumes check: "isOK (check_muterm_typed_dep_graph \<mu> R S P edps)"
    and fin: "\<And>prf C. (Some prf,C) \<in> set edps \<Longrightarrow>
      finite_muterm_min_typed_dpp Sharp (mu_of \<mu>) (set R)
        (set P \<inter> set C) (set S)"
  shows "finite_muterm_min_typed_dpp Sharp (mu_of \<mu>) (set R) (set P) (set S)"
proof -
  let ?P = "set P"
  let ?RL = "R @ S"
  let ?RS = "set ?RL"
  show ?thesis
    unfolding finite_muterm_min_typed_dpp_def SN_rel_on_def SN_on_def
  proof (rule notI)
    let ?A = "(csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
      muterm_min_typed_pair_step Sharp (mu_of \<mu>) (set R) ?P (set S) O
      (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
    assume infinite: "\<exists>f. f 0 \<in> UNIV \<and>
      (\<forall>i. (f i,f (Suc i)) \<in> ?A)"
    then obtain ch where chain: "\<And>i. (ch i,ch (Suc i)) \<in> ?A" by auto
    have ex_step: "\<forall>i. \<exists>l r \<sigma>.
      (l,r) \<in> ?P \<and>
      (ch i,l \<cdot> \<sigma>) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
      (r \<cdot> \<sigma>,ch (Suc i)) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
      (ch i,ch (Suc i)) \<in>
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
        muterm_min_typed_pair_step Sharp (mu_of \<mu>) (set R) {(l,r)} (set S) O
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
    proof
      fix i
      from muterm_min_typed_relto_witness[OF chain[of i]]
      show "\<exists>l r \<sigma>. (l,r) \<in> ?P \<and>
        (ch i,l \<cdot> \<sigma>) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
        (r \<cdot> \<sigma>,ch (Suc i)) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
        (ch i,ch (Suc i)) \<in>
          (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
          muterm_min_typed_pair_step Sharp (mu_of \<mu>) (set R) {(l,r)} (set S) O
          (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
        by (simp add: set_append)
    qed
    from choice[OF ex_step] obtain s where choose_s: "\<forall>i. \<exists>r \<sigma>.
      (s i,r) \<in> ?P \<and>
      (ch i,s i \<cdot> \<sigma>) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
      (r \<cdot> \<sigma>,ch (Suc i)) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
      (ch i,ch (Suc i)) \<in>
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
        muterm_min_typed_pair_step Sharp (mu_of \<mu>) (set R) {(s i,r)} (set S) O
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
      by blast
    from choice[OF choose_s] obtain t where choose_t: "\<forall>i. \<exists>\<sigma>.
      (s i,t i) \<in> ?P \<and>
      (ch i,s i \<cdot> \<sigma>) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
      (t i \<cdot> \<sigma>,ch (Suc i)) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
      (ch i,ch (Suc i)) \<in>
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
        muterm_min_typed_pair_step Sharp (mu_of \<mu>) (set R) {(s i,t i)} (set S) O
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
      by blast
    from choice[OF choose_t] obtain \<sigma> where chosen: "\<forall>i.
      (s i,t i) \<in> ?P \<and>
      (ch i,s i \<cdot> \<sigma> i) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
      (t i \<cdot> \<sigma> i,ch (Suc i)) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
      (ch i,ch (Suc i)) \<in>
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
        muterm_min_typed_pair_step Sharp (mu_of \<mu>) (set R)
          {(s i,t i)} (set S) O
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
      by blast
    from chosen have pair: "\<And>i. (s i,t i) \<in> ?P"
      and pre: "\<And>i. (ch i,s i \<cdot> \<sigma> i) \<in>
        (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>*"
      and post: "\<And>i. (t i \<cdot> \<sigma> i,ch (Suc i)) \<in>
        (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>*"
      and typed: "\<And>i. (ch i,ch (Suc i)) \<in>
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
        muterm_min_typed_pair_step Sharp (mu_of \<mu>) (set R)
          {(s i,t i)} (set S) O
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
      by blast+
    have steps: "\<And>i. (t i \<cdot> \<sigma> i,s (Suc i) \<cdot> \<sigma> (Suc i)) \<in>
      (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>*"
      using post pre by (meson rtrancl_trans)
    from check_muterm_typed_dep_graph_select_component[
      where \<mu>=\<mu> and R=R and S=S and P=P and edps=edps
        and s=s and t=t and \<sigma>=\<sigma>, OF check pair steps]
    obtain p Cs n where mem: "(Some p,Cs) \<in> set edps"
      and CP_all: "\<forall>m. (s (m+n),t (m+n)) \<in> ?P \<inter> set Cs"
      by auto
    from CP_all have CP: "\<And>m. (s (m+n),t (m+n)) \<in> ?P \<inter> set Cs"
      by auto
    let ?tail = "\<lambda>m. ch (m+n)"
    have tail_step: "\<And>m. (?tail m,?tail (Suc m)) \<in>
      (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
      muterm_min_typed_pair_step Sharp (mu_of \<mu>) (set R)
        (?P \<inter> set Cs) (set S) O
      (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
    proof -
      fix m
      have singleton: "{(s (m+n),t (m+n))} \<subseteq> ?P \<inter> set Cs"
        using CP[of m] by auto
      have mono: "muterm_min_typed_pair_step Sharp (mu_of \<mu>) (set R)
          {(s (m+n),t (m+n))} (set S)
        \<subseteq> muterm_min_typed_pair_step Sharp (mu_of \<mu>) (set R)
          (?P \<inter> set Cs) (set S)"
        by (rule muterm_min_typed_pair_step_mono[OF singleton])
      have suc_add: "Suc m+n = Suc (m+n)" by simp
      have inc: "(csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
          muterm_min_typed_pair_step Sharp (mu_of \<mu>) (set R)
            {(s (m+n),t (m+n))} (set S) O
          (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* \<subseteq>
          (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
          muterm_min_typed_pair_step Sharp (mu_of \<mu>) (set R)
            (?P \<inter> set Cs) (set S) O
          (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
        by (meson relcomp_mono mono subset_refl)
      from typed[of "m+n"] inc show "(?tail m,?tail (Suc m)) \<in>
          (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
          muterm_min_typed_pair_step Sharp (mu_of \<mu>) (set R)
            (?P \<inter> set Cs) (set S) O
          (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
        unfolding suc_add
        by blast
    qed
    have tail_sn: "SN ((csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
      muterm_min_typed_pair_step Sharp (mu_of \<mu>) (set R)
        (?P \<inter> set Cs) (set S) O
      (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*)"
      using fin[OF mem]
      unfolding finite_muterm_min_typed_dpp_def SN_rel_on_def .
    have tail_is_chain: "chain
      ((csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
       muterm_min_typed_pair_step Sharp (mu_of \<mu>) (set R)
         (?P \<inter> set Cs) (set S) O
       (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*) ?tail"
      using tail_step by simp
    have not_tail_sn: "\<not> SN ((csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
      muterm_min_typed_pair_step Sharp (mu_of \<mu>) (set R)
        (?P \<inter> set Cs) (set S) O
      (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*)"
      by (rule not_SN_onI[of ?tail], simp, rule tail_is_chain)
    from not_tail_sn tail_sn show False ..
  qed
qed


end
