(*
Author:  Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Minimal_CSDP_Proofs
  imports
    CSR_Checker_Core.CSR_Checker
    CSR_Improved_CSDP_Proofs
begin

lemma sharp_csdp_step_imp_csnrstep:
  fixes shp :: "'f::{showl, compare_order} \<Rightarrow> 'f"
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (shp f, n)"
    and marked_inj: "inj shp"
    and step: "(sharp_term shp s, v) \<in> csdp_step shp \<mu> R"
  shows "\<exists>t. v = sharp_term shp t \<and> (s, t) \<in> csnrstep \<mu> R"
proof (cases s)
  case (Var x)
  from step obtain p lr \<sigma> where
    rewrite: "(sharp_term shp s, v) \<in> rstep_r_p_s R lr p \<sigma>"
    unfolding csdp_step_def csdp_step_p_def by auto
  have rewrite': "(Var x, v) \<in> rstep_r_p_s R lr p \<sigma>"
    using rewrite unfolding Var by simp
  from rewrite' have "p = []"
    unfolding rstep_r_p_s_def' by (cases p, auto)
  with rewrite' have lr: "lr \<in> R" and lhs: "fst lr \<cdot> \<sigma> = Var x"
    unfolding rstep_r_p_s_def' by auto
  from wf lr have "\<exists>g ts. fst lr = Fun g ts"
    unfolding wf_trs_def by (cases lr, auto)
  then obtain g ts where l: "fst lr = Fun g ts"
    by blast
  with lhs show ?thesis by simp
next
  case (Fun f ss)
  from step obtain p lr \<sigma> where
    rewrite0: "(sharp_term shp s, v) \<in> rstep_r_p_s R lr p \<sigma>"
    and cond0: "csdp_step_cond shp \<mu> p (sharp_term shp s)"
    unfolding csdp_step_def csdp_step_p_def by auto
  have rewrite: "(Fun (shp f) ss, v) \<in> rstep_r_p_s R lr p \<sigma>"
    using rewrite0 unfolding Fun by simp
  have cond: "csdp_step_cond shp \<mu> p (Fun (shp f) ss)"
    using cond0 unfolding Fun by simp
  have p_ne: "p \<noteq> []"
  proof
    assume "p = []"
    with rewrite have lr: "lr \<in> R"
      and lhs: "fst lr \<cdot> \<sigma> = Fun (shp f) ss"
      unfolding rstep_r_p_s_def' by auto
    from wf lr have "\<exists>g ts. fst lr = Fun g ts"
      unfolding wf_trs_def by (cases lr, auto)
    then obtain g ts where l: "fst lr = Fun g ts"
      by blast
    from lhs l have g: "g = shp f" and len: "length ts = length ss"
      by auto
    from lr l g len have "defined R (shp f, length ss)"
      unfolding defined_def by (cases "lr", auto)
    with fresh show False by contradiction
  qed
  then obtain i q where p: "p = i # q"
    by (cases p, auto)
  let ?t = "replace_at (Fun f ss) p (snd lr \<cdot> \<sigma>)"
  have rewrite': "(Fun f ss, ?t) \<in> rstep_r_p_s R lr p \<sigma>"
    using rewrite p unfolding rstep_r_p_s_def' by auto
  have v: "v = sharp_term shp ?t"
    using rewrite p unfolding rstep_r_p_s_def' by auto
  have cond': "csstep_cond \<mu> p (Fun f ss)"
  proof (unfold csstep_cond_def, intro allI impI)
    fix p1 j p2
    assume A: "p = p1 @ j # p2 \<and> p \<in> poss (Fun f ss)"
    show "\<exists>g us. Fun f ss |_ p1 = Fun g us \<and> j \<in> \<mu> (g, length us)"
    proof (cases p1)
      case Nil
      from cond[unfolded csdp_step_cond_def, rule_format,
          of "[]" j p2] A Nil
      show ?thesis using injD[OF marked_inj] by auto
    next
      case (Cons k qs)
      from cond[unfolded csdp_step_cond_def, rule_format,
          of p1 j p2] A Cons
      show ?thesis by auto
    qed
  qed
  have "(Fun f ss, ?t) \<in> csnrstep \<mu> R"
    unfolding csnrstep_def csstep_p_def
    using p rewrite' cond' by (cases lr, blast)
  with v Fun show ?thesis by auto
qed

lemma inj_Sharp: "inj Sharp"
  by (rule injI, simp)

lemma sharp_term_Sharp_inject:
  "sharp_term Sharp s = sharp_term Sharp t \<longleftrightarrow> s = t"
  by (cases s; cases t; auto)

lemma mu_Tinf_imp_SN_sharp_csdp:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f, n)"
    and Tinf: "t \<in> mu_Tinf \<mu> (csstep \<mu> R)"
  shows "SN_on (csdp_step Sharp \<mu> R) {sharp_term Sharp t}"
proof -
  from mu_Tinf_imp_SN_csnr_first_csrstep[OF wf Tinf]
  have SN: "SN_on (csnrstep \<mu> R) {t}"
    by blast
  show ?thesis
  proof (unfold SN_on_def, intro notI)
    assume "\<exists>ts. ts 0 \<in> {sharp_term Sharp t} \<and>
      (\<forall>i. (ts i, ts (Suc i)) \<in> csdp_step Sharp \<mu> R)"
    then obtain ts where init: "ts 0 = sharp_term Sharp t"
      and steps: "\<And>i. (ts i, ts (Suc i)) \<in> csdp_step Sharp \<mu> R"
      by auto
    have shaped: "\<And>i. \<exists>s. ts i = sharp_term Sharp s"
    proof -
      fix i
      show "\<exists>s. ts i = sharp_term Sharp s"
      proof (induct i)
        case 0
        show ?case using init by blast
      next
        case (Suc i)
        then obtain s where tsi: "ts i = sharp_term Sharp s"
          by blast
        from sharp_csdp_step_imp_csnrstep[OF wf fresh inj_Sharp,
            of s "ts (Suc i)"]
          steps[of i] tsi
        show ?case by auto
      qed
    qed
    have all_shaped: "\<forall>i. \<exists>s. ts i = sharp_term Sharp s"
      using shaped by blast
    from choice[OF all_shaped]
    obtain ss where shape: "\<And>i. ts i = sharp_term Sharp (ss i)"
      by blast
    have ss0: "ss 0 = t"
    proof (rule iffD1[OF sharp_term_Sharp_inject])
      show "sharp_term Sharp (ss 0) = sharp_term Sharp t"
        using init shape[of 0] by simp
    qed
    have ss_steps: "\<And>i. (ss i, ss (Suc i)) \<in> csnrstep \<mu> R"
    proof -
      fix i
      from sharp_csdp_step_imp_csnrstep[OF wf fresh inj_Sharp,
          of "ss i" "ts (Suc i)"] steps[of i] shape[of i]
      obtain u where u: "ts (Suc i) = sharp_term Sharp u"
        and step: "(ss i, u) \<in> csnrstep \<mu> R"
        by auto
      have "u = ss (Suc i)"
      proof (rule iffD1[OF sharp_term_Sharp_inject])
        show "sharp_term Sharp u = sharp_term Sharp (ss (Suc i))"
          using u shape[of "Suc i"] by simp
      qed
      with step show "(ss i, ss (Suc i)) \<in> csnrstep \<mu> R"
        by simp
    qed
    from SN ss0 ss_steps show False
      unfolding SN_on_def by blast
  qed
qed

definition csr_min_pair_step where
  "csr_min_pair_step shp \<mu> P R =
    (rrstep P \<inter> {(s, t). SN_on (csdp_step shp \<mu> R) {t}})"

definition finite_min_csr_dpp where
  "finite_min_csr_dpp shp \<mu> P R \<longleftrightarrow>
    SN_rel (csr_min_pair_step shp \<mu> P R) (csdp_step shp \<mu> R)"

lemma finite_csr_dpp_imp_finite_min_csr_dpp:
  assumes "finite_csr_dpp shp \<mu> P R"
  shows "finite_min_csr_dpp shp \<mu> P R"
proof -
  from assms have fin: "SN_rel (rrstep P) (csdp_step shp \<mu> R)"
    unfolding finite_csr_dpp_def .
  show ?thesis
    unfolding finite_min_csr_dpp_def csr_min_pair_step_def
    by (rule SN_rel_mono[OF _ subset_refl fin]) auto
qed

lemma finite_min_csr_dpp_mono_pairs:
  assumes sub: "P' \<subseteq> P"
    and fin: "finite_min_csr_dpp shp \<mu> P R"
  shows "finite_min_csr_dpp shp \<mu> P' R"
proof -
  have pair: "csr_min_pair_step shp \<mu> P' R \<subseteq>
      csr_min_pair_step shp \<mu> P R"
    using sub unfolding csr_min_pair_step_def rrstep_def' by blast
  from fin show ?thesis
    unfolding finite_min_csr_dpp_def
    by (rule SN_rel_mono[OF pair subset_refl])
qed

lemma finite_min_csr_dpp_imp_SN_csstep_if_mu_Tinf_progress:
  assumes progress: "\<And>t. t \<in> mu_Tinf \<mu> (csstep \<mu> R) \<Longrightarrow>
      \<exists>u. u \<in> mu_Tinf \<mu> (csstep \<mu> R) \<and>
        (sharp_term Sharp t, sharp_term Sharp u) \<in>
          (csdp_step Sharp \<mu> R)\<^sup>* O
          csr_min_pair_step Sharp \<mu> P R O
          (csdp_step Sharp \<mu> R)\<^sup>*"
    and fin: "finite_min_csr_dpp Sharp \<mu> P R"
  shows "SN (csstep \<mu> R)"
proof (rule ccontr)
  assume "\<not> SN (csstep \<mu> R)"
  from not_SN_imp_Tinf[OF this]
  obtain t0 where t0_T: "t0 \<in> Tinf (csstep \<mu> R)"
    by blast
  from Tinf_imp_mu_Tinf[OF t0_T]
  have t0: "t0 \<in> mu_Tinf \<mu> (csstep \<mu> R)" .
  let ?T = "csstep \<mu> R"
  let ?S = "csdp_step Sharp \<mu> R"
  let ?P = "csr_min_pair_step Sharp \<mu> P R"
  let ?rel = "?S\<^sup>* O ?P O ?S\<^sup>*"
  have all_ex: "\<forall>t. \<exists>u. t \<in> mu_Tinf \<mu> ?T \<longrightarrow>
    u \<in> mu_Tinf \<mu> ?T \<and>
      (sharp_term Sharp t, sharp_term Sharp u) \<in> ?rel"
    using progress by blast
  from choice[OF all_ex]
  obtain nxt where nxt: "\<And>t. t \<in> mu_Tinf \<mu> ?T \<Longrightarrow>
    nxt t \<in> mu_Tinf \<mu> ?T \<and>
      (sharp_term Sharp t, sharp_term Sharp (nxt t)) \<in> ?rel"
    by blast
  define ts where "ts = rec_nat t0 (\<lambda>n t. nxt t)"
  have ts_T: "ts n \<in> mu_Tinf \<mu> ?T" for n
  proof (induct n)
    case 0
    show ?case unfolding ts_def using t0 by simp
  next
    case (Suc n)
    from nxt[OF Suc.hyps] have "nxt (ts n) \<in> mu_Tinf \<mu> ?T"
      by simp
    then show ?case unfolding ts_def by simp
  qed
  have ts_step:
    "(sharp_term Sharp (ts n), sharp_term Sharp (ts (Suc n))) \<in> ?rel"
    for n
  proof -
    from nxt[OF ts_T[of n]]
    have step:
      "(sharp_term Sharp (ts n), sharp_term Sharp (nxt (ts n))) \<in> ?rel"
      by simp
    show ?thesis using step unfolding ts_def by simp
  qed
  define f where "f n = sharp_term Sharp (ts n)" for n
  have chain: "\<And>n. (f n, f (Suc n)) \<in> ?rel"
    unfolding f_def using ts_step by simp
  have "\<not> SN_rel ?P ?S"
    unfolding SN_rel_on_def SN_defs
    using chain by blast
  moreover from fin have "SN_rel ?P ?S"
    unfolding finite_min_csr_dpp_def .
  ultimately show False by contradiction
qed

lemma mu_Tinf_imp_mu_CSDP_min_csdp_relstep:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f, n)"
    and Tinf: "t \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and vc: "rhs_mu_vars_condition \<mu> R"
    and D: "{f. defined R f} \<subseteq> D"
  shows "\<exists>u. u \<in> mu_Tinf \<mu> (csstep \<mu> R) \<and>
    (sharp_term Sharp t, sharp_term Sharp u) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>* O
      csr_min_pair_step Sharp \<mu> (mu_CSDP_on Sharp \<mu> D R) R O
      (csdp_step Sharp \<mu> R)\<^sup>*"
proof -
  from mu_Tinf_imp_SN_csnr_first_csrstep[OF wf Tinf]
  obtain s v where pref: "(t, s) \<in> (csnrstep \<mu> R)\<^sup>*"
    and root: "(s, v) \<in> csrstep \<mu> R"
    and notSN_v: "\<not> SN_on (csstep \<mu> R) {v}"
    by auto
  have sv: "(s, v) \<in> csstep \<mu> R"
    using root unfolding csstep_root_nonroot by auto
  have notSN_s: "\<not> SN_on (csstep \<mu> R) {s}"
    by (rule step_notSN_on_source[OF sv notSN_v])
  have sT: "s \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    by (rule csnrsteps_mu_Tinf_preserve[OF wf pref Tinf notSN_s])
  from csrstep_mu_Tinf_rhs_imp_rrstep_mu_CSDP_on[
      OF wf root sT notSN_v vc D, where shp = Sharp]
  obtain u where uT: "u \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and dp: "(sharp_term Sharp s, sharp_term Sharp u) \<in>
      rrstep (mu_CSDP_on Sharp \<mu> D R)"
    by blast
  have target_SN:
    "SN_on (csdp_step Sharp \<mu> R) {sharp_term Sharp u}"
    by (rule mu_Tinf_imp_SN_sharp_csdp[OF wf fresh uT])
  have dp':
    "(sharp_term Sharp s, sharp_term Sharp u) \<in>
      csr_min_pair_step Sharp \<mu> (mu_CSDP_on Sharp \<mu> D R) R"
    using dp target_SN unfolding csr_min_pair_step_def by auto
  have left:
    "(sharp_term Sharp t, sharp_term Sharp s) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>*"
    by (rule csnrsteps_imp_sharp_csdp_steps[OF pref, where shp = Sharp])
  have right:
    "(sharp_term Sharp u, sharp_term Sharp u) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>*"
    by simp
  have "(sharp_term Sharp t, sharp_term Sharp u) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>* O
      csr_min_pair_step Sharp \<mu> (mu_CSDP_on Sharp \<mu> D R) R O
      (csdp_step Sharp \<mu> R)\<^sup>*"
    using left dp' right by auto
  with uT show ?thesis by blast
qed

theorem finite_min_csr_mu_CSDP_on_imp_SN_csstep:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f, n)"
    and vc: "rhs_mu_vars_condition \<mu> R"
    and D: "{f. defined R f} \<subseteq> D"
    and fin: "finite_min_csr_dpp Sharp \<mu>
      (mu_CSDP_on Sharp \<mu> D R) R"
  shows "SN (csstep \<mu> R)"
  by (rule finite_min_csr_dpp_imp_SN_csstep_if_mu_Tinf_progress[OF _ fin],
      rule mu_Tinf_imp_mu_CSDP_min_csdp_relstep[OF wf fresh _ vc D])

fun qcs_ur_closed_term where
  "qcs_ur_closed_term R U \<mu> (Var x) = (R \<subseteq> U)"
| "qcs_ur_closed_term R U \<mu> (Fun f ts) =
    ((\<forall>lr\<in>R. root (fst lr) = Some (f, length ts) \<longrightarrow> lr \<in> U) \<and>
     (\<forall>i<length ts. i \<in> \<mu> (f, length ts) \<longrightarrow>
       qcs_ur_closed_term R U \<mu> (ts ! i)))"

definition qcs_ur_closed where
  "qcs_ur_closed R U \<mu> P \<longleftrightarrow>
    (\<forall>lr\<in>U. qcs_ur_closed_term R U \<mu> (snd lr)) \<and>
    (\<forall>dp\<in>P. qcs_ur_closed_term R U \<mu> (snd dp))"

lemma qcs_ur_closed_term_all:
  assumes "R \<subseteq> U"
  shows "qcs_ur_closed_term R U \<mu> t"
  using assms by (induct t) auto

lemma qcs_ur_closed_term_subst:
  assumes closed: "qcs_ur_closed_term R U \<mu> t"
  shows "qcs_ur_closed_term R U \<mu> (t \<cdot> \<sigma>)"
  using closed
proof (induct t)
  case (Var x)
  then show ?case
    by (simp add: qcs_ur_closed_term_all)
next
  case (Fun f ts)
  from Fun.prems have roots:
    "\<forall>lr\<in>R. root (fst lr) = Some (f, length ts) \<longrightarrow> lr \<in> U"
    and args: "\<forall>i<length ts. i \<in> \<mu> (f, length ts) \<longrightarrow>
      qcs_ur_closed_term R U \<mu> (ts ! i)"
    by auto
  show ?case
    using roots args Fun.hyps by auto
qed

lemma csstep_FunI:
  assumes i: "i < length ss"
    and active: "i \<in> \<mu> (f, length ss)"
    and step: "(ss ! i, u) \<in> csstep \<mu> R"
  shows "(Fun f ss, Fun f (ss[i := u])) \<in> csnrstep \<mu> R"
proof -
  from step obtain p lr \<sigma> where
    rewrite: "(ss ! i, u) \<in> rstep_r_p_s R lr p \<sigma>"
    and cond: "csstep_cond \<mu> p (ss ! i)"
    unfolding csstep_def csstep_p_def by auto
  have rewrite':
    "(Fun f ss, Fun f (ss[i := u])) \<in> rstep_r_p_s R lr (i # p) \<sigma>"
    using rewrite i unfolding rstep_r_p_s_def'
    by (auto simp: upd_conv_take_nth_drop)
  have cond': "csstep_cond \<mu> (i # p) (Fun f ss)"
    unfolding csstep_cond_def
  proof (intro allI impI)
    fix p1 j p2
    assume A: "i # p = p1 @ j # p2 \<and> i # p \<in> poss (Fun f ss)"
    show "\<exists>g ts. Fun f ss |_ p1 = Fun g ts \<and>
      j \<in> \<mu> (g, length ts)"
    proof (cases p1)
      case Nil
      with A active show ?thesis by auto
    next
      case (Cons k qs)
      from A Cons have k: "k = i" and p: "p = qs @ j # p2"
        by auto
      from rewrite i have p_pos: "p \<in> poss (ss ! i)"
        unfolding rstep_r_p_s_def' by auto
      from cond[unfolded csstep_cond_def, rule_format, of qs j p2]
        p p_pos
      obtain g ts where sub: "ss ! i |_ qs = Fun g ts"
        and active': "j \<in> \<mu> (g, length ts)"
        by auto
      with Cons k i show ?thesis by auto
    qed
  qed
  show ?thesis
    unfolding csnrstep_def csstep_p_def
    using rewrite' cond' by (cases lr, blast)
qed

lemma cssteps_Fun_updateI:
  assumes i: "i < length ss"
    and active: "i \<in> \<mu> (f, length ss)"
    and steps: "(ss ! i, u) \<in> (csstep \<mu> R)\<^sup>*"
  shows "(Fun f ss, Fun f (ss[i := u])) \<in> (csstep \<mu> R)\<^sup>*"
  using steps
proof (induct rule: rtrancl_induct)
  case base
  then show ?case
    using i by simp
next
  case (step y z)
  have len: "i < length (ss[i := y])"
    using i by simp
  have active': "i \<in> \<mu> (f, length (ss[i := y]))"
    using active by simp
  have sub: "((ss[i := y]) ! i, z) \<in> csstep \<mu> R"
    using step.hyps(2) i by simp
  from csstep_FunI[OF len active' sub]
  have whole:
    "(Fun f (ss[i := y]), Fun f ((ss[i := y])[i := z]))
      \<in> csstep \<mu> R"
    unfolding csstep_root_nonroot by auto
  from rtrancl_into_rtrancl[OF step.hyps(3) whole]
  show ?case
    using i by simp
qed

lemma cssteps_FunI:
  assumes len: "length ss = length ts"
    and args:
      "\<And>i. i < length ss \<Longrightarrow>
        (if i \<in> \<mu> (f, length ss)
         then (ss ! i, ts ! i) \<in> (csstep \<mu> R)\<^sup>*
         else ts ! i = ss ! i)"
  shows "(Fun f ss, Fun f ts) \<in> (csstep \<mu> R)\<^sup>*"
proof -
  let ?mix = "\<lambda>i. take i ts @ drop i ss"
  have mix_len: "length (?mix i) = length ss" for i
    using len by simp
  have one:
    "(Fun f (?mix i), Fun f (?mix (Suc i)))
      \<in> (csstep \<mu> R)\<^sup>*"
    if i: "i < length ss" for i
  proof (cases "i \<in> \<mu> (f, length ss)")
    case True
    have i_ss: "i < length ss"
      using i len by simp
    have i_ts: "i < length ts"
      using i len by simp
    have take_len: "length (take i ts) = i"
      using i len by simp
    have drop_nth: "drop i ss ! 0 = ss ! i"
      using i_ss by simp
    have nth: "?mix i ! i = ss ! i"
      using take_len drop_nth
      by (simp add: nth_append)
    have update: "(?mix i)[i := ts ! i] = ?mix (Suc i)"
      using take_drop_update_first[OF i_ts len] .
    have sub: "(?mix i ! i, ts ! i) \<in> (csstep \<mu> R)\<^sup>*"
      using args[OF i] True
      by (simp add: nth)
    have i_mix: "i < length (?mix i)"
      using i_ss mix_len by simp
    have active_mix: "i \<in> \<mu> (f, length (?mix i))"
      using True mix_len by simp
    from cssteps_Fun_updateI[OF i_mix active_mix sub]
    show ?thesis
      using i True mix_len update by simp
  next
    case False
    have same: "ts ! i = ss ! i"
      using args[OF i] False by simp
    have i_ts: "i < length ts"
      using i len by simp
    have i_mix: "i < length (?mix i)"
      using i mix_len by simp
    have take_len: "length (take i ts) = i"
      using i len by simp
    have drop_nth: "drop i ss ! 0 = ss ! i"
      using i by simp
    have nth: "?mix i ! i = ss ! i"
      using take_len drop_nth
      by (simp add: nth_append)
    have update: "(?mix i)[i := ts ! i] = ?mix (Suc i)"
      using take_drop_update_first[OF i_ts len] .
    have same_nth: "ts ! i = ?mix i ! i"
      using same nth by simp
    have update_id: "(?mix i)[i := ts ! i] = ?mix i"
      unfolding same_nth
      by (rule list_update_id)
    have "?mix (Suc i) = ?mix i"
      using update update_id by simp
    then show ?thesis
      by simp
  qed
  have prefix:
    "(Fun f ss, Fun f (?mix i)) \<in> (csstep \<mu> R)\<^sup>*"
    if i: "i \<le> length ss" for i
    using i
  proof (induct i)
    case 0
    then show ?case by simp
  next
    case (Suc i)
    then have i: "i < length ss"
      by simp
    have prefix_i:
      "(Fun f ss, Fun f (?mix i)) \<in> (csstep \<mu> R)\<^sup>*"
      by (rule Suc.hyps[OF less_imp_le[OF i]])
    from rtrancl_trans[OF prefix_i one[OF i]]
    show ?case .
  qed
  from prefix[of "length ss"] len
  show ?thesis
    by simp
qed

lemma csstep_rules_mono:
  assumes "R \<subseteq> S"
  shows "csstep \<mu> R \<subseteq> csstep \<mu> S"
  using assms
  unfolding csstep_def csstep_p_def rstep_r_p_s_def'
  by auto

lemma qcs_ur_closed_csstep:
  assumes wf: "wf_trs R"
    and U_closed: "\<And>lr. lr \<in> U \<Longrightarrow>
      qcs_ur_closed_term R U \<mu> (snd lr)"
    and closed: "qcs_ur_closed_term R U \<mu> t"
    and step: "(t, u) \<in> csstep \<mu> R"
  shows "(t, u) \<in> csstep \<mu> U \<and>
    qcs_ur_closed_term R U \<mu> u"
  using closed step
proof (induct t arbitrary: u)
  case (Var x)
  from csstep_Var_empty_wf[OF wf, of x u \<mu>] Var.prems(2)
  show ?case by contradiction
next
  case (Fun f ss)
  from Fun.prems(2) have step':
    "(Fun f ss, u) \<in> csrstep \<mu> R \<or>
     (Fun f ss, u) \<in> csnrstep \<mu> R"
    unfolding csstep_root_nonroot by auto
  from step' show ?case
  proof
    assume root: "(Fun f ss, u) \<in> csrstep \<mu> R"
    from root obtain l r \<sigma> where lr: "(l, r) \<in> R"
      and lhs: "Fun f ss = l \<cdot> \<sigma>" and rhs: "u = r \<cdot> \<sigma>"
      by (elim csrstepE)
    from wf lr obtain g ts where l: "l = Fun g ts"
      unfolding wf_trs_def by (cases l, auto)
    from lhs l have gf: "g = f" and len: "length ts = length ss"
      by auto
    have root_l: "root l = Some (f, length ss)"
      unfolding l using gf len by simp
    from Fun.prems(1) lr root_l have lrU: "(l, r) \<in> U"
      by auto
    have root_U: "(Fun f ss, u) \<in> csrstep \<mu> U"
      unfolding csrstep_iff_rstep_root rstep_r_p_s_def'
      using lrU lhs rhs by force
    from U_closed[OF lrU]
    have closed_r: "qcs_ur_closed_term R U \<mu> r"
      by simp
    from qcs_ur_closed_term_subst[OF closed_r, of \<sigma>]
    have "qcs_ur_closed_term R U \<mu> (r \<cdot> \<sigma>)" .
    then have closed_u: "qcs_ur_closed_term R U \<mu> u"
      using rhs by simp
    show ?thesis
      using root_U closed_u unfolding csstep_root_nonroot by auto
  next
    assume nonroot: "(Fun f ss, u) \<in> csnrstep \<mu> R"
    from nonroot have "\<exists>i ts. i < length ss \<and>
      i \<in> \<mu> (f, length ss) \<and> u = Fun f ts \<and>
      length ts = length ss \<and>
      (ss ! i, ts ! i) \<in> csstep \<mu> R \<and>
      (\<forall>j<length ss. j \<noteq> i \<longrightarrow> ts ! j = ss ! j)"
      by (elim csnrstep_FunE, blast)
    then obtain i ts where i: "i < length ss"
      and active: "i \<in> \<mu> (f, length ss)"
      and u: "u = Fun f ts" and len: "length ts = length ss"
      and substep: "(ss ! i, ts ! i) \<in> csstep \<mu> R"
      and same: "\<And>j. j < length ss \<Longrightarrow> j \<noteq> i \<Longrightarrow>
        ts ! j = ss ! j"
      by blast
    from Fun.prems(1) i active
    have closed_i: "qcs_ur_closed_term R U \<mu> (ss ! i)"
      by auto
    from i have mem: "ss ! i \<in> set ss" by auto
    from Fun.hyps[OF mem, of "ts ! i"] closed_i substep
    have substep_U: "(ss ! i, ts ! i) \<in> csstep \<mu> U"
      and closed_i': "qcs_ur_closed_term R U \<mu> (ts ! i)"
      by auto
    have ts_update: "ts = ss[i := ts ! i]"
    proof (rule nth_equalityI)
      show "length ts = length (ss[i := ts ! i])"
        using len by simp
      fix j
      assume j: "j < length ts"
      show "ts ! j = (ss[i := ts ! i]) ! j"
      proof (cases "j = i")
        case True
        with i show ?thesis by simp
      next
        case False
        from j len have "j < length ss" by simp
        from same[OF this False] False i show ?thesis by simp
      qed
    qed
    have update_nr_U:
      "(Fun f ss, Fun f (ss[i := ts ! i])) \<in> csnrstep \<mu> U"
      by (rule csstep_FunI[OF i active substep_U])
    from update_nr_U have update_U:
      "(Fun f ss, Fun f (ss[i := ts ! i])) \<in> csstep \<mu> U"
      unfolding csstep_root_nonroot by auto
    from update_U ts_update
    have whole_U: "(Fun f ss, Fun f ts) \<in> csstep \<mu> U"
      by simp
    have closed_update:
      "qcs_ur_closed_term R U \<mu> (Fun f (ss[i := ts ! i]))"
      using Fun.prems(1) i closed_i'
      by (auto simp: nth_list_update)
    from closed_update ts_update
    have closed_u: "qcs_ur_closed_term R U \<mu> (Fun f ts)"
      by simp
    show ?thesis
      using whole_U closed_u u by simp
  qed
qed

fun qcs_ur_closed_below_root where
  "qcs_ur_closed_below_root R U \<mu> (Var x) = False"
| "qcs_ur_closed_below_root R U \<mu> (Fun f ts) =
    (\<forall>i<length ts. i \<in> \<mu> (f, length ts) \<longrightarrow>
      qcs_ur_closed_term R U \<mu> (ts ! i))"

lemma qcs_ur_closed_csnrstep:
  assumes wf: "wf_trs R"
    and U_closed: "\<And>lr. lr \<in> U \<Longrightarrow>
      qcs_ur_closed_term R U \<mu> (snd lr)"
    and closed: "qcs_ur_closed_below_root R U \<mu> t"
    and step: "(t, u) \<in> csnrstep \<mu> R"
  shows "(t, u) \<in> csnrstep \<mu> U \<and>
    qcs_ur_closed_below_root R U \<mu> u"
proof (cases t)
  case (Var x)
  from step[unfolded Var] have "(Var x, u) \<in> csnrstep \<mu> R" .
  with csnrstep_Var_empty[of x u \<mu> R] show ?thesis by contradiction
next
  case (Fun f ss)
  from step[unfolded Fun] have step': "(Fun f ss, u) \<in> csnrstep \<mu> R" .
  from step' have "\<exists>i ts. i < length ss \<and>
    i \<in> \<mu> (f, length ss) \<and> u = Fun f ts \<and>
    length ts = length ss \<and>
    (ss ! i, ts ! i) \<in> csstep \<mu> R \<and>
    (\<forall>j<length ss. j \<noteq> i \<longrightarrow> ts ! j = ss ! j)"
    by (elim csnrstep_FunE, blast)
  then obtain i ts where i: "i < length ss"
    and active: "i \<in> \<mu> (f, length ss)"
    and u: "u = Fun f ts" and len: "length ts = length ss"
    and substep: "(ss ! i, ts ! i) \<in> csstep \<mu> R"
    and same: "\<And>j. j < length ss \<Longrightarrow> j \<noteq> i \<Longrightarrow>
      ts ! j = ss ! j"
    by blast
  from closed[unfolded Fun] i active
  have closed_i: "qcs_ur_closed_term R U \<mu> (ss ! i)"
    by auto
  from qcs_ur_closed_csstep[OF wf U_closed closed_i substep]
  have substep_U: "(ss ! i, ts ! i) \<in> csstep \<mu> U"
    and closed_i': "qcs_ur_closed_term R U \<mu> (ts ! i)"
    by auto
  have ts_update: "ts = ss[i := ts ! i]"
  proof (rule nth_equalityI)
    show "length ts = length (ss[i := ts ! i])"
      using len by simp
    fix j
    assume j: "j < length ts"
    show "ts ! j = (ss[i := ts ! i]) ! j"
    proof (cases "j = i")
      case True
      with i show ?thesis by simp
    next
      case False
      from j len have "j < length ss" by simp
      from same[OF this False] False i show ?thesis by simp
    qed
  qed
  have update_nr_U:
    "(Fun f ss, Fun f (ss[i := ts ! i])) \<in> csnrstep \<mu> U"
    by (rule csstep_FunI[OF i active substep_U])
  from update_nr_U ts_update
  have whole_nr_U: "(Fun f ss, Fun f ts) \<in> csnrstep \<mu> U"
    by simp
  have closed_update:
    "qcs_ur_closed_below_root R U \<mu> (Fun f (ss[i := ts ! i]))"
    using closed[unfolded Fun] i closed_i'
    by (auto simp: nth_list_update)
  from closed_update ts_update
  have closed_ts: "qcs_ur_closed_below_root R U \<mu> (Fun f ts)"
    by simp
  show ?thesis
    using whole_nr_U closed_ts Fun u by simp
qed

fun qcs_ur_closed_dp_rhs ::
  "((('f, 'l) lab), 'v) trs \<Rightarrow>
   ((('f, 'l) lab), 'v) trs \<Rightarrow>
   (('f, 'l) lab) mu \<Rightarrow>
   ((('f, 'l) lab), 'v) term \<Rightarrow> bool"
where
  "qcs_ur_closed_dp_rhs R U \<mu> (Var x) = False"
| "qcs_ur_closed_dp_rhs R U \<mu> (Fun (Sharp f) ts) =
    (\<forall>i<length ts. i \<in> \<mu> (f, length ts) \<longrightarrow>
      qcs_ur_closed_term R U \<mu> (ts ! i))"
| "qcs_ur_closed_dp_rhs R U \<mu> (Fun f ts) = False"

definition qcs_csr_ur_closed where
  "qcs_csr_ur_closed R U \<mu> P \<longleftrightarrow>
    U \<subseteq> R \<and>
    (\<forall>lr\<in>U. qcs_ur_closed_term R U \<mu> (snd lr)) \<and>
    (\<forall>dp\<in>P. qcs_ur_closed_dp_rhs R U \<mu> (snd dp))"

lemma qcs_ur_closed_dp_rhs_subst:
  assumes closed: "qcs_ur_closed_dp_rhs R U \<mu> t"
  shows "qcs_ur_closed_dp_rhs R U \<mu> (t \<cdot> \<sigma>)"
  using closed
proof (cases t)
  case (Var x)
  then show ?thesis using closed by simp
next
  case (Fun f ts)
  from Fun closed obtain g where f: "f = Sharp g"
    by (cases f, auto)
  from Fun f closed have args:
    "\<And>i. i < length ts \<Longrightarrow> i \<in> \<mu> (g, length ts) \<Longrightarrow>
      qcs_ur_closed_term R U \<mu> (ts ! i)"
    by auto
  show ?thesis
    unfolding Fun f by auto
      (rule qcs_ur_closed_term_subst[OF args])
qed

lemma qcs_ur_closed_dp_rhs_sharp:
  "qcs_ur_closed_dp_rhs R U \<mu> (sharp_term Sharp t) =
    qcs_ur_closed_below_root R U \<mu> t"
  by (cases t) auto

lemma qcs_ur_closed_csdp_step:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f, n)"
    and U_closed: "\<And>lr. lr \<in> U \<Longrightarrow>
      qcs_ur_closed_term R U \<mu> (snd lr)"
    and closed: "qcs_ur_closed_dp_rhs R U \<mu> (sharp_term Sharp t)"
    and step: "(sharp_term Sharp t, v) \<in> csdp_step Sharp \<mu> R"
  shows "(sharp_term Sharp t, v) \<in> csdp_step Sharp \<mu> U \<and>
    qcs_ur_closed_dp_rhs R U \<mu> v"
proof -
  from sharp_csdp_step_imp_csnrstep[OF wf fresh inj_Sharp step]
  obtain u where v: "v = sharp_term Sharp u"
    and nonroot: "(t, u) \<in> csnrstep \<mu> R"
    by blast
  from closed have below: "qcs_ur_closed_below_root R U \<mu> t"
    unfolding qcs_ur_closed_dp_rhs_sharp .
  from qcs_ur_closed_csnrstep[OF wf U_closed below nonroot]
  have nonroot_U: "(t, u) \<in> csnrstep \<mu> U"
    and below_u: "qcs_ur_closed_below_root R U \<mu> u"
    by auto
  have step_U:
    "(sharp_term Sharp t, sharp_term Sharp u) \<in> csdp_step Sharp \<mu> U"
    by (rule sharp_csnrstep_imp_csdp_step[OF nonroot_U, where shp = Sharp])
  have closed_u:
    "qcs_ur_closed_dp_rhs R U \<mu> (sharp_term Sharp u)"
    using below_u unfolding qcs_ur_closed_dp_rhs_sharp .
  show ?thesis
    using step_U closed_u v by simp
qed

lemma qcs_ur_closed_dp_rhs_shape:
  assumes "qcs_ur_closed_dp_rhs R U \<mu> s"
  shows "\<exists>t. s = sharp_term Sharp t"
  using assms
proof (cases s)
  case (Var x)
  then show ?thesis using assms by simp
next
  case (Fun f ts)
  from Fun assms obtain g where "f = Sharp g"
    by (cases f, auto)
  with Fun show ?thesis
    by (intro exI[of _ "Fun g ts"], simp)
qed

lemma qcs_ur_closed_csdp_steps:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f, n)"
    and U_closed: "\<And>lr. lr \<in> U \<Longrightarrow>
      qcs_ur_closed_term R U \<mu> (snd lr)"
    and closed: "qcs_ur_closed_dp_rhs R U \<mu> s"
    and steps: "(s, t) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "(s, t) \<in> (csdp_step Sharp \<mu> U)\<^sup>* \<and>
    qcs_ur_closed_dp_rhs R U \<mu> t"
  using steps closed
proof (induct rule: rtrancl_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  from step.hyps(3)[OF step.prems]
  have prefix: "(s, y) \<in> (csdp_step Sharp \<mu> U)\<^sup>*"
    and closed_y: "qcs_ur_closed_dp_rhs R U \<mu> y"
    by auto
  from qcs_ur_closed_dp_rhs_shape[OF closed_y]
  obtain u where y: "y = sharp_term Sharp u"
    by blast
  have closed_u:
    "qcs_ur_closed_dp_rhs R U \<mu> (sharp_term Sharp u)"
    using closed_y y by simp
  have step_uz:
    "(sharp_term Sharp u, z) \<in> csdp_step Sharp \<mu> R"
    using step.hyps(2) y by simp
  from qcs_ur_closed_csdp_step[OF wf fresh U_closed closed_u step_uz]
  have yz: "(y, z) \<in> csdp_step Sharp \<mu> U"
    and closed_z: "qcs_ur_closed_dp_rhs R U \<mu> z"
    using y by auto
  from prefix yz closed_z show ?case by auto
qed

lemma qcs_ur_closed_rrstep_target:
  assumes P_closed: "\<And>dp. dp \<in> P \<Longrightarrow>
      qcs_ur_closed_dp_rhs R U \<mu> (snd dp)"
    and step: "(s, t) \<in> rrstep P"
  shows "qcs_ur_closed_dp_rhs R U \<mu> t"
proof -
  from step obtain l r \<sigma> where pair: "(l, r) \<in> P"
    and t: "t = r \<cdot> \<sigma>"
    unfolding rrstep_def' by auto
  from P_closed[OF pair]
  have "qcs_ur_closed_dp_rhs R U \<mu> r"
    by simp
  from qcs_ur_closed_dp_rhs_subst[OF this, of \<sigma>]
  show ?thesis unfolding t .
qed

lemma csr_min_pair_step_usable_mono:
  assumes subset: "U \<subseteq> R"
  shows "csr_min_pair_step Sharp \<mu> P R \<subseteq>
    csr_min_pair_step Sharp \<mu> P U"
proof
  fix s t
  assume pair: "(s, t) \<in> csr_min_pair_step Sharp \<mu> P R"
  then have rr: "(s, t) \<in> rrstep P"
    and SN: "SN_on (csdp_step Sharp \<mu> R) {t}"
    unfolding csr_min_pair_step_def by auto
  have step_subset:
    "csdp_step Sharp \<mu> U \<subseteq> csdp_step Sharp \<mu> R"
    by (rule csdp_step_mono[OF subset, where shp = Sharp])
  from SN_on_mono[OF SN step_subset]
  have "SN_on (csdp_step Sharp \<mu> U) {t}" .
  with rr show "(s, t) \<in> csr_min_pair_step Sharp \<mu> P U"
    unfolding csr_min_pair_step_def by auto
qed

lemma qcs_csr_relto_target_closed:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f, n)"
    and closed: "qcs_csr_ur_closed R U \<mu> P"
    and step: "(s, t) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>* O
      csr_min_pair_step Sharp \<mu> P R O
      (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "qcs_ur_closed_dp_rhs R U \<mu> t"
proof -
  from closed have U_closed: "\<And>lr. lr \<in> U \<Longrightarrow>
      qcs_ur_closed_term R U \<mu> (snd lr)"
    and P_closed: "\<And>dp. dp \<in> P \<Longrightarrow>
      qcs_ur_closed_dp_rhs R U \<mu> (snd dp)"
    unfolding qcs_csr_ur_closed_def by auto
  from step obtain a b where pair:
    "(a, b) \<in> csr_min_pair_step Sharp \<mu> P R"
    and suffix: "(b, t) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
    by auto
  from pair have rr: "(a, b) \<in> rrstep P"
    unfolding csr_min_pair_step_def by auto
  from qcs_ur_closed_rrstep_target[OF P_closed rr]
  have closed_b: "qcs_ur_closed_dp_rhs R U \<mu> b" .
  from qcs_ur_closed_csdp_steps[OF wf fresh U_closed closed_b suffix]
  show ?thesis by auto
qed

lemma qcs_csr_relto_transfer:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f, n)"
    and closed: "qcs_csr_ur_closed R U \<mu> P"
    and closed_s: "qcs_ur_closed_dp_rhs R U \<mu> s"
    and step: "(s, t) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>* O
      csr_min_pair_step Sharp \<mu> P R O
      (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "(s, t) \<in>
      (csdp_step Sharp \<mu> U)\<^sup>* O
      csr_min_pair_step Sharp \<mu> P U O
      (csdp_step Sharp \<mu> U)\<^sup>* \<and>
    qcs_ur_closed_dp_rhs R U \<mu> t"
proof -
  from closed have subset: "U \<subseteq> R"
    and U_closed: "\<And>lr. lr \<in> U \<Longrightarrow>
      qcs_ur_closed_term R U \<mu> (snd lr)"
    and P_closed: "\<And>dp. dp \<in> P \<Longrightarrow>
      qcs_ur_closed_dp_rhs R U \<mu> (snd dp)"
    unfolding qcs_csr_ur_closed_def by auto
  from step obtain a b where prefix:
    "(s, a) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
    and pair: "(a, b) \<in> csr_min_pair_step Sharp \<mu> P R"
    and suffix: "(b, t) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
    by auto
  from qcs_ur_closed_csdp_steps[OF wf fresh U_closed closed_s prefix]
  have prefix_U: "(s, a) \<in> (csdp_step Sharp \<mu> U)\<^sup>*"
    by auto
  from csr_min_pair_step_usable_mono[OF subset] pair
  have pair_U: "(a, b) \<in> csr_min_pair_step Sharp \<mu> P U"
    by auto
  from pair have rr: "(a, b) \<in> rrstep P"
    unfolding csr_min_pair_step_def by auto
  from qcs_ur_closed_rrstep_target[OF P_closed rr]
  have closed_b: "qcs_ur_closed_dp_rhs R U \<mu> b" .
  from qcs_ur_closed_csdp_steps[OF wf fresh U_closed closed_b suffix]
  have suffix_U: "(b, t) \<in> (csdp_step Sharp \<mu> U)\<^sup>*"
    and closed_t: "qcs_ur_closed_dp_rhs R U \<mu> t"
    by auto
  show ?thesis
    using prefix_U pair_U suffix_U closed_t by auto
qed

theorem finite_min_csr_dpp_qcs_usable_rules:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f, n)"
    and closed: "qcs_csr_ur_closed R U \<mu> P"
    and fin: "finite_min_csr_dpp Sharp \<mu> P U"
  shows "finite_min_csr_dpp Sharp \<mu> P R"
proof (rule ccontr)
  assume not_fin: "\<not> finite_min_csr_dpp Sharp \<mu> P R"
  let ?PR = "csr_min_pair_step Sharp \<mu> P R"
  let ?SR = "csdp_step Sharp \<mu> R"
  let ?PU = "csr_min_pair_step Sharp \<mu> P U"
  let ?SU = "csdp_step Sharp \<mu> U"
  from not_fin have not_SN_R: "\<not> SN_on (?SR\<^sup>* O ?PR O ?SR\<^sup>*) UNIV"
    unfolding finite_min_csr_dpp_def SN_rel_on_def .
  from not_SN_R obtain f where chain:
    "\<And>n. (f n, f (Suc n)) \<in>
      ?SR\<^sup>* O ?PR O ?SR\<^sup>*"
    unfolding SN_on_def by auto
  from qcs_csr_relto_target_closed[OF wf fresh closed chain[of 0]]
  have closed_1: "qcs_ur_closed_dp_rhs R U \<mu> (f (Suc 0))" .
  let ?g = "\<lambda>n. f (Suc n)"
  have closed_g: "qcs_ur_closed_dp_rhs R U \<mu> (?g n)" for n
  proof (induct n)
    case 0
    show ?case using closed_1 by simp
  next
    case (Suc n)
    from qcs_csr_relto_transfer[OF wf fresh closed Suc.hyps
        chain[of "Suc n"]]
    show ?case by auto
  qed
  have g_step: "(?g n, ?g (Suc n)) \<in>
    ?SU\<^sup>* O ?PU O ?SU\<^sup>*" for n
    using qcs_csr_relto_transfer[OF wf fresh closed closed_g[of n]
      chain[of "Suc n"]]
    by auto
  have g_chain: "chain (?SU\<^sup>* O ?PU O ?SU\<^sup>*) ?g"
    using g_step by simp
  have not_SN_U: "\<not> SN_on (?SU\<^sup>* O ?PU O ?SU\<^sup>*) UNIV"
    by (rule not_SN_onI[OF _ g_chain], simp)
  from fin have "SN_on (?SU\<^sup>* O ?PU O ?SU\<^sup>*) UNIV"
    unfolding finite_min_csr_dpp_def SN_rel_on_def .
  with not_SN_U show False by contradiction
qed

text \<open>
  The context-sensitive usable rules @{term "U\<^sub>3"} from Definition 18 of
  Alarcón et al. (LPAR 2008) use a different closure from ordinary usable
  rules.  The seeds are all symbols in DP right-hand sides, symbols at inactive
  positions in DP left-hand sides, and symbols at inactive positions in rule
  right-hand sides.  A selected root depends on every symbol at an inactive
  position of its rule left-hand sides and every symbol in their right-hand
  sides.

  The executable predicate below checks a (possibly proper) superset of this
  least closure.  Checking a superset is useful for certificates and avoids
  making the checker compute a fixed point.
\<close>

definition csr_u3_root_rules_check where
  "csr_u3_root_rules_check R U t ps =
    list_all (\<lambda>p. case root (t |_ p) of
      None \<Rightarrow> True
    | Some f \<Rightarrow> list_all
        (\<lambda>lr. root (fst lr) \<noteq> Some f \<or> lr \<in> set U) R) ps"

definition csr_u3_inactive_root_rules_check where
  "csr_u3_inactive_root_rules_check R U \<mu> t =
    csr_u3_root_rules_check R U t
      (filter (\<lambda>p. p \<notin> set (mu_fun_poss_list \<mu> t))
        (fun_poss_list t))"

definition csr_u3_all_root_rules_check where
  "csr_u3_all_root_rules_check R U t =
    csr_u3_root_rules_check R U t (fun_poss_list t)"

definition csr_u3_usable_rules_check where
  "csr_u3_usable_rules_check R U \<mu> P =
    (list_all (\<lambda>lr. lr \<in> set R) U \<and>
     list_all (\<lambda>dp.
       csr_u3_inactive_root_rules_check R U \<mu> (fst dp) \<and>
       csr_u3_all_root_rules_check R U (snd dp)) P \<and>
     list_all (\<lambda>lr.
       csr_u3_inactive_root_rules_check R U \<mu> (snd lr)) R \<and>
     list_all (\<lambda>lr.
       csr_u3_inactive_root_rules_check R U \<mu> (fst lr) \<and>
       csr_u3_all_root_rules_check R U (snd lr)) U)"

definition csr_u3_root_rules_closed where
  "csr_u3_root_rules_closed R U t A \<longleftrightarrow>
    (\<forall>p\<in>A. \<forall>f. root (t |_ p) = Some f \<longrightarrow>
      (\<forall>lr\<in>R. root (fst lr) = Some f \<longrightarrow> lr \<in> U))"

definition csr_u3_usable_rules_closed where
  "csr_u3_usable_rules_closed R U \<mu> P \<longleftrightarrow>
    U \<subseteq> R \<and>
    (\<forall>dp\<in>P.
      csr_u3_root_rules_closed R U (fst dp)
        {p\<in>fun_poss (fst dp). p \<notin> mu_fun_poss \<mu> (fst dp)} \<and>
      csr_u3_root_rules_closed R U (snd dp) (fun_poss (snd dp))) \<and>
    (\<forall>lr\<in>R. csr_u3_root_rules_closed R U (snd lr)
      {p\<in>fun_poss (snd lr). p \<notin> mu_fun_poss \<mu> (snd lr)}) \<and>
    (\<forall>lr\<in>U.
      csr_u3_root_rules_closed R U (fst lr)
        {p\<in>fun_poss (fst lr). p \<notin> mu_fun_poss \<mu> (fst lr)} \<and>
      csr_u3_root_rules_closed R U (snd lr) (fun_poss (snd lr)))"

definition csr_u3_delta where
  "csr_u3_delta R U =
    {f. \<forall>lr\<in>R. root (fst lr) = Some f \<longrightarrow> lr \<in> U}"

definition csr_inactive_funas where
  "csr_inactive_funas \<mu> t =
    {f. \<exists>p\<in>fun_poss t - mu_fun_poss \<mu> t.
      root (t |_ p) = Some f}"

lemma csr_u3_root_rules_closed_delta:
  assumes closed: "csr_u3_root_rules_closed R U t A"
    and p: "p \<in> A"
    and root: "root (t |_ p) = Some f"
  shows "f \<in> csr_u3_delta R U"
  using closed p root
  unfolding csr_u3_root_rules_closed_def csr_u3_delta_def
  by blast

lemma csr_u3_closed_inactive_rhs_delta:
  assumes closed: "csr_u3_usable_rules_closed R U \<mu> P"
    and lr: "lr \<in> R"
  shows "csr_inactive_funas \<mu> (snd lr) \<subseteq> csr_u3_delta R U"
proof
  fix f
  assume "f \<in> csr_inactive_funas \<mu> (snd lr)"
  then obtain p where
    p: "p \<in> fun_poss (snd lr) - mu_fun_poss \<mu> (snd lr)"
    and root: "root (snd lr |_ p) = Some f"
    unfolding csr_inactive_funas_def by blast
  from closed lr have roots:
    "csr_u3_root_rules_closed R U (snd lr)
      {p\<in>fun_poss (snd lr). p \<notin> mu_fun_poss \<mu> (snd lr)}"
    unfolding csr_u3_usable_rules_closed_def by blast
  show "f \<in> csr_u3_delta R U"
    by (rule csr_u3_root_rules_closed_delta[OF roots _ root], use p in auto)
qed

lemma csr_u3_closed_selected_rule:
  assumes root_delta: "f \<in> csr_u3_delta R U"
    and lr: "lr \<in> R"
    and root: "root (fst lr) = Some f"
  shows "lr \<in> U"
  using root_delta lr root unfolding csr_u3_delta_def by blast

lemma csr_u3_closed_selected_rhs_delta:
  assumes closed: "csr_u3_usable_rules_closed R U \<mu> P"
    and lr: "lr \<in> R"
    and root_delta: "the (root (fst lr)) \<in> csr_u3_delta R U"
    and root_some: "root (fst lr) \<noteq> None"
  shows "{f. \<exists>p\<in>fun_poss (snd lr). root (snd lr |_ p) = Some f}
    \<subseteq> csr_u3_delta R U"
proof -
  from root_some obtain f where root: "root (fst lr) = Some f"
    by (cases "root (fst lr)", auto)
  from root root_delta have f_delta: "f \<in> csr_u3_delta R U"
    by simp
  from csr_u3_closed_selected_rule[OF f_delta lr root]
  have lrU: "lr \<in> U" .
  from closed lrU have roots:
    "csr_u3_root_rules_closed R U (snd lr) (fun_poss (snd lr))"
    unfolding csr_u3_usable_rules_closed_def by blast
  show ?thesis
    using roots unfolding csr_u3_root_rules_closed_def csr_u3_delta_def
    by blast
qed

lemma csr_u3_closed_selected_lhs_inactive_delta:
  assumes closed: "csr_u3_usable_rules_closed R U \<mu> P"
    and lr: "lr \<in> R"
    and root_delta: "the (root (fst lr)) \<in> csr_u3_delta R U"
    and root_some: "root (fst lr) \<noteq> None"
  shows "csr_inactive_funas \<mu> (fst lr) \<subseteq> csr_u3_delta R U"
proof -
  from root_some obtain f where root: "root (fst lr) = Some f"
    by (cases "root (fst lr)", auto)
  from root root_delta have f_delta: "f \<in> csr_u3_delta R U"
    by simp
  from csr_u3_closed_selected_rule[OF f_delta lr root]
  have lrU: "lr \<in> U" .
  from closed lrU have roots:
    "csr_u3_root_rules_closed R U (fst lr)
      {p\<in>fun_poss (fst lr). p \<notin> mu_fun_poss \<mu> (fst lr)}"
    unfolding csr_u3_usable_rules_closed_def by blast
  show ?thesis
    using roots
    unfolding csr_inactive_funas_def csr_u3_root_rules_closed_def
      csr_u3_delta_def
    by blast
qed

lemma csr_u3_closed_inactive_subterm_delta:
  assumes closed:
      "csr_u3_root_rules_closed R U t
        {p\<in>fun_poss t. p \<notin> mu_fun_poss \<mu> t}"
    and p_fun: "p \<in> fun_poss t"
    and p_inactive: "p \<notin> mu_fun_poss \<mu> t"
  shows "funas_term (t |_ p) \<subseteq> csr_u3_delta R U"
proof
  fix f
  assume "f \<in> funas_term (t |_ p)"
  then obtain q g ts where
    f: "f = (g, length ts)"
    and q: "q \<in> poss (t |_ p)"
    and sub: "(t |_ p) |_ q = Fun g ts"
    unfolding funas_term_poss_conv by blast
  from p_fun have p_poss: "p \<in> poss t"
    by (rule fun_poss_imp_poss)
  from q p_poss have pq_poss: "p @ q \<in> poss t"
    unfolding poss_append_poss by simp
  from sub p_poss have whole_sub: "t |_ (p @ q) = Fun g ts"
    by (simp add: subt_at_append)
  have pq_fun: "p @ q \<in> fun_poss t"
    by (rule poss_is_Fun_fun_poss[OF pq_poss],
        use whole_sub in simp)
  have pq_inactive: "p @ q \<notin> mu_fun_poss \<mu> t"
  proof
    assume "p @ q \<in> mu_fun_poss \<mu> t"
    then have p_active: "p \<in> mu_poss \<mu> t"
      by (rule mu_fun_poss_append_prefix)
    have "p \<in> mu_fun_poss \<mu> t"
      by (rule mu_poss_fun_poss_imp_mu_fun_poss[OF p_active p_fun])
    with p_inactive show False by contradiction
  qed
  show "f \<in> csr_u3_delta R U"
    unfolding f
    by (rule csr_u3_root_rules_closed_delta[
        OF closed _ _], use pq_fun pq_inactive whole_sub in auto)
qed

lemma csr_u3_closed_pair_lhs_inactive_delta:
  assumes closed: "csr_u3_usable_rules_closed R U \<mu> P"
    and dp: "dp \<in> P"
    and p_fun: "p \<in> fun_poss (fst dp)"
    and p_inactive: "p \<notin> mu_fun_poss \<mu> (fst dp)"
  shows "funas_term (fst dp |_ p) \<subseteq> csr_u3_delta R U"
proof -
  from closed dp have roots:
    "csr_u3_root_rules_closed R U (fst dp)
      {p\<in>fun_poss (fst dp). p \<notin> mu_fun_poss \<mu> (fst dp)}"
    unfolding csr_u3_usable_rules_closed_def by blast
  show ?thesis
    by (rule csr_u3_closed_inactive_subterm_delta[
        OF roots p_fun p_inactive])
qed

lemma csr_u3_closed_pair_rhs_delta:
  assumes closed: "csr_u3_usable_rules_closed R U \<mu> P"
    and dp: "dp \<in> P"
  shows "funas_term (snd dp) \<subseteq> csr_u3_delta R U"
proof
  fix f
  assume "f \<in> funas_term (snd dp)"
  then obtain p g ts where
    f: "f = (g, length ts)"
    and p: "p \<in> poss (snd dp)"
    and sub: "snd dp |_ p = Fun g ts"
    unfolding funas_term_poss_conv by blast
  have p_fun: "p \<in> fun_poss (snd dp)"
    by (rule poss_is_Fun_fun_poss[OF p],
        use sub in simp)
  from closed dp have roots:
    "csr_u3_root_rules_closed R U (snd dp) (fun_poss (snd dp))"
    unfolding csr_u3_usable_rules_closed_def by blast
  show "f \<in> csr_u3_delta R U"
    unfolding f
    by (rule csr_u3_root_rules_closed_delta[OF roots p_fun],
      use sub in simp)
qed

definition mu_supt_rel where
  "mu_supt_rel \<mu> = {(s, t). mu_supt \<mu> s t}"

lemma csr_u3_post_step_nondelta_subterm_active:
  assumes wf: "wf_trs R"
    and closed: "csr_u3_usable_rules_closed R U \<mu> P"
    and step: "(u, v) \<in> csstep \<mu> R"
    and sub: "v \<rhd> s"
    and new: "\<not> u \<rhd> s"
    and s_fun: "is_Fun s"
    and nondelta: "the (root s) \<notin> csr_u3_delta R U"
  shows "mu_supt \<mu> v s"
proof (rule ccontr)
  assume inactive: "\<not> mu_supt \<mu> v s"
  obtain l r \<sigma> p q where
    lr: "(l, r) \<in> R"
    and q: "q \<in> fun_poss r"
    and q_inactive: "q \<notin> mu_fun_poss \<mu> r"
    and s: "s = (r |_ q) \<cdot> \<sigma>"
    by (rule csstep_new_inactive_subterm_rhs[
        OF wf step sub inactive new s_fun])
  from fun_poss_fun_conv[OF q]
  obtain f ts where rq: "r |_ q = Fun f ts"
    by auto
  have f_inactive: "(f, length ts) \<in> csr_inactive_funas \<mu> r"
    unfolding csr_inactive_funas_def
  proof
    show "\<exists>p\<in>fun_poss r - mu_fun_poss \<mu> r.
      root (r |_ p) = Some (f, length ts)"
      by (rule bexI[of _ q], use q q_inactive rq in auto)
  qed
  have inactive_subset:
    "csr_inactive_funas \<mu> r \<subseteq> csr_u3_delta R U"
    using csr_u3_closed_inactive_rhs_delta[OF closed lr] by simp
  have f_delta: "(f, length ts) \<in> csr_u3_delta R U"
    by (rule subsetD[OF inactive_subset f_inactive])
  have root_s: "root s = Some (f, length ts)"
    unfolding s rq by simp
  have f_nondelta: "(f, length ts) \<notin> csr_u3_delta R U"
    using nondelta root_s by simp
  from f_delta f_nondelta show False by contradiction
qed

lemma csr_u3_post_step_nondelta_supteq:
  assumes wf: "wf_trs R"
    and closed: "csr_u3_usable_rules_closed R U \<mu> P"
    and step: "(u, v) \<in> csstep \<mu> R"
    and sub: "v \<unrhd> s"
    and new: "\<not> u \<rhd> s"
    and s_fun: "is_Fun s"
    and nondelta: "the (root s) \<notin> csr_u3_delta R U"
  shows "(v, s) \<in> Id \<union> mu_supt_rel \<mu>"
proof (cases "v = s")
  case True
  then show ?thesis by simp
next
  case False
  with sub have "v \<rhd> s"
    unfolding supt_supteq_conv by auto
  from csr_u3_post_step_nondelta_subterm_active[
      OF wf closed step this new s_fun nondelta]
  show ?thesis
    unfolding mu_supt_rel_def by auto
qed

lemma csr_u3_rewrite_source_classification:
  assumes wf: "wf_trs R"
    and closed: "csr_u3_usable_rules_closed R U \<mu> P"
    and step: "(u, v) \<in> csstep \<mu> R"
    and sub: "v \<unrhd> s"
    and s_fun: "is_Fun s"
    and nondelta: "the (root s) \<notin> csr_u3_delta R U"
  shows "u \<rhd> s \<or>
    ((u, v) \<in> csstep \<mu> R \<and>
      (v, s) \<in> Id \<union> mu_supt_rel \<mu>)"
proof (cases "u \<rhd> s")
  case True
  then show ?thesis by simp
next
  case False
  from csr_u3_post_step_nondelta_supteq[
      OF wf closed step sub False s_fun nondelta]
  show ?thesis
    using step by blast
qed

lemma csr_u3_usable_rules_check_subset:
  assumes "csr_u3_usable_rules_check R U \<mu> P"
  shows "set U \<subseteq> set R"
  using assms unfolding csr_u3_usable_rules_check_def
  by (auto simp: list_all_iff)

lemma csr_u3_root_rules_check_sound:
  assumes "csr_u3_root_rules_check R U t ps"
  shows "csr_u3_root_rules_closed (set R) (set U) t (set ps)"
  using assms
  unfolding csr_u3_root_rules_check_def csr_u3_root_rules_closed_def
  by (auto simp: list_all_iff split: option.splits)

lemma set_csr_u3_inactive_fun_poss [simp]:
  "set (filter (\<lambda>p. p \<notin> set (mu_fun_poss_list \<mu> t))
      (fun_poss_list t)) =
    fun_poss t - mu_fun_poss (mu_of \<mu>) t"
  by auto

lemma csr_u3_inactive_root_rules_check_sound:
  assumes "csr_u3_inactive_root_rules_check R U \<mu> t"
  shows "csr_u3_root_rules_closed (set R) (set U) t
    {p\<in>fun_poss t. p \<notin> mu_fun_poss (mu_of \<mu>) t}"
  using csr_u3_root_rules_check_sound[OF assms[
    unfolded csr_u3_inactive_root_rules_check_def]]
  by simp

lemma csr_u3_all_root_rules_check_sound:
  assumes "csr_u3_all_root_rules_check R U t"
  shows "csr_u3_root_rules_closed (set R) (set U) t (fun_poss t)"
  using csr_u3_root_rules_check_sound[OF assms[
    unfolded csr_u3_all_root_rules_check_def]]
  by simp

lemma csr_u3_usable_rules_check_sound:
  assumes "csr_u3_usable_rules_check R U \<mu> P"
  shows "csr_u3_usable_rules_closed (set R) (set U) (mu_of \<mu>) (set P)"
  using assms
  unfolding csr_u3_usable_rules_check_def
    csr_u3_usable_rules_closed_def
  by (auto simp: list_all_iff
    intro: csr_u3_inactive_root_rules_check_sound
      csr_u3_all_root_rules_check_sound)

definition csrewrite where
  "csrewrite \<mu> R t =
    filter (\<lambda>u. (t, u) \<in> csstep \<mu> (set R)) (rewrite R t)"

lemma csrewrite_sound:
  assumes "u \<in> set (csrewrite \<mu> R t)"
  shows "(t, u) \<in> csstep \<mu> (set R)"
  using assms unfolding csrewrite_def by auto

lemma csrewrite_complete:
  assumes wf: "wf_trs (set R)"
    and step: "(t, u) \<in> csstep \<mu> (set R)"
  shows "u \<in> set (csrewrite \<mu> R t)"
proof -
  from wf have vars:
    "\<And>l r. (l, r) \<in> set R \<Longrightarrow> vars_term r \<subseteq> vars_term l"
    unfolding wf_trs_def by auto
  from step csstep_subset_rstep have "(t, u) \<in> rstep (set R)"
    by blast
  moreover have "set (rewrite R t) = {v. (t, v) \<in> rstep (set R)}"
    by (rule rewrite[OF vars])
  ultimately have "u \<in> set (rewrite R t)"
    by simp
  with step show ?thesis
    unfolding csrewrite_def by simp
qed

lemma set_csrewrite:
  assumes "wf_trs (set R)"
  shows "set (csrewrite \<mu> R t) = csstep \<mu> (set R) `` {t}"
  using csrewrite_sound csrewrite_complete[OF assms]
  by auto

lemma finite_csstep_image:
  assumes "finite R" and "wf_trs R"
  shows "finite (csstep \<mu> R `` {t})"
proof -
  from finite_list[OF assms(1)] obtain Rs where R: "R = set Rs"
    by auto
  have "csstep \<mu> R `` {t} = set (csrewrite \<mu> Rs t)"
    using set_csrewrite[of Rs \<mu> t] assms(2) unfolding R by simp
  then show ?thesis by simp
qed

definition csr_i1_struct_call where
  "csr_i1_struct_call =
    {(Fun f ts, t) |f ts t. t \<in> set ts}"

definition csr_i1_rewrite_call where
  "csr_i1_rewrite_call R \<mu> \<Delta> =
    {(t, u). SN_on (csstep \<mu> R) {t} \<and>
      the (root t) \<notin> \<Delta> \<and> (t, u) \<in> csstep \<mu> R}"

definition csr_i1_call where
  "csr_i1_call R \<mu> \<Delta> =
    csr_i1_struct_call \<union> csr_i1_rewrite_call R \<mu> \<Delta>"

lemma csr_i1_struct_call_supt:
  "csr_i1_struct_call \<subseteq> {\<rhd>}"
  unfolding csr_i1_struct_call_def
  by (auto intro: supt.arg)

lemma SN_csr_i1_struct_call:
  "SN csr_i1_struct_call"
  by (rule SN_subset[OF SN_supt csr_i1_struct_call_supt])

lemma csr_i1_rewrite_callD:
  assumes "(t, u) \<in> csr_i1_rewrite_call R \<mu> \<Delta>"
  shows "SN_on (csstep \<mu> R) {t}"
    "the (root t) \<notin> \<Delta>"
    "(t, u) \<in> csstep \<mu> R"
  using assms unfolding csr_i1_rewrite_call_def by auto

lemma csr_i1_rewrite_call_finite:
  assumes "finite R" and "wf_trs R"
  shows "finite (csr_i1_rewrite_call R \<mu> \<Delta> `` {t})"
proof -
  have subset: "csr_i1_rewrite_call R \<mu> \<Delta> `` {t}
      \<subseteq> csstep \<mu> R `` {t}"
    unfolding csr_i1_rewrite_call_def by auto
  from finite_csstep_image[OF assms, of \<mu> t]
  show ?thesis
    by (rule finite_subset[OF subset])
qed

lemma csr_i1_call_finite:
  assumes "finite R" and "wf_trs R"
  shows "finite (csr_i1_call R \<mu> \<Delta> `` {t})"
proof -
  have struct:
    "csr_i1_struct_call `` {t} \<subseteq> set (args t)"
    unfolding csr_i1_struct_call_def
    by (cases t, auto)
  have finite_struct: "finite (csr_i1_struct_call `` {t})"
    by (rule finite_subset[OF struct], simp)
  have finite_rewrite:
    "finite (csr_i1_rewrite_call R \<mu> \<Delta> `` {t})"
    by (rule csr_i1_rewrite_call_finite[OF assms])
  have image:
    "csr_i1_call R \<mu> \<Delta> `` {t} =
      csr_i1_struct_call `` {t} \<union>
      csr_i1_rewrite_call R \<mu> \<Delta> `` {t}"
    unfolding csr_i1_call_def by blast
  show ?thesis
    unfolding image
    by (rule finite_UnI[OF finite_struct finite_rewrite])
qed

lemma ce_trs_sound_csstep:
  assumes "t \<in> set ts"
  shows "(comb cn ts, t) \<in> (csstep \<mu> (ce_trs cn))\<^sup>+"
  using assms
proof (induct ts)
  case Nil
  then show ?case by simp
next
  case (Cons s ss)
  obtain c n where cn: "cn = (c, n)"
    by force
  have root_step:
    "\<And>u v. (u, v) \<in> ce_trs cn \<Longrightarrow>
      (u, v) \<in> csstep \<mu> (ce_trs cn)"
  proof -
    fix u v
    assume rule: "(u, v) \<in> ce_trs cn"
    have "(u, v) \<in> rstep_r_p_s (ce_trs cn) (u, v) [] Var"
      using rule unfolding rstep_r_p_s_def' by simp
    then have "(u, v) \<in> csrstep \<mu> (ce_trs cn)"
      unfolding csrstep_iff_rstep_root by blast
    then show "(u, v) \<in> csstep \<mu> (ce_trs cn)"
      unfolding csstep_root_nonroot by simp
  qed
  show ?case
  proof (cases "s = t")
    case True
    with cn have "(comb cn (s # ss), s) \<in> ce_trs cn"
      by (simp add: ce_trs.simps comb.simps)
    from root_step[OF this] True show ?thesis
      by force
  next
    case False
    with Cons have ind:
      "(comb cn ss, t) \<in> (csstep \<mu> (ce_trs cn))\<^sup>+"
      by auto
    from cn have "(comb cn (s # ss), comb cn ss) \<in> ce_trs cn"
      by (simp add: ce_trs.simps comb.simps)
    from root_step[OF this] ind show ?thesis
      by auto
  qed
qed

fun qcs_ur_closed_term_check where
  "qcs_ur_closed_term_check R U \<mu> (Var x) =
    list_all (\<lambda>lr. lr \<in> set U) R"
| "qcs_ur_closed_term_check R U \<mu> (Fun f ts) =
    (list_all (\<lambda>lr. root (fst lr) \<noteq> Some (f, length ts) \<or>
        lr \<in> set U) R \<and>
     list_all (\<lambda>(i, t). i \<notin> mu_of \<mu> (f, length ts) \<or>
        qcs_ur_closed_term_check R U \<mu> t)
       (zip [0..<length ts] ts))"

fun qcs_ur_closed_dp_rhs_check where
  "qcs_ur_closed_dp_rhs_check R U \<mu> (Var x) = False"
| "qcs_ur_closed_dp_rhs_check R U \<mu> (Fun (Sharp f) ts) =
    list_all (\<lambda>(i, t). i \<notin> mu_of \<mu> (f, length ts) \<or>
      qcs_ur_closed_term_check R U \<mu> t)
      (zip [0..<length ts] ts)"
| "qcs_ur_closed_dp_rhs_check R U \<mu> (Fun f ts) = False"

definition qcs_csr_ur_closed_check where
  "qcs_csr_ur_closed_check R U \<mu> P =
    (list_all (\<lambda>lr. lr \<in> set R) U \<and>
     list_all (\<lambda>lr. qcs_ur_closed_term_check R U \<mu> (snd lr)) U \<and>
     list_all (\<lambda>dp. qcs_ur_closed_dp_rhs_check R U \<mu> (snd dp)) P)"

lemma list_all_zip_upt_nth:
  assumes all: "list_all (\<lambda>(i, t). Q i t)
      (zip [0..<length ts] ts)"
    and i: "i < length ts"
  shows "Q i (ts ! i)"
proof -
  from i have i': "i < length (zip [0..<length ts] ts)"
    by simp
  from nth_mem[OF i']
  have "(zip [0..<length ts] ts) ! i \<in>
    set (zip [0..<length ts] ts)" .
  with i have "(i, ts ! i) \<in> set (zip [0..<length ts] ts)"
    by simp
  with all show ?thesis
    by (auto simp: list_all_iff)
qed

lemma qcs_ur_closed_term_check_sound:
  assumes "qcs_ur_closed_term_check R U \<mu> t"
  shows "qcs_ur_closed_term (set R) (set U) (mu_of \<mu>) t"
  using assms
proof (induct t)
  case (Var x)
  then show ?case by (auto simp: list_all_iff)
next
  case (Fun f ts)
  from Fun.prems have roots:
    "\<And>lr. lr \<in> set R \<Longrightarrow>
      root (fst lr) = Some (f, length ts) \<Longrightarrow> lr \<in> set U"
    and args: "list_all (\<lambda>(i, t).
      i \<notin> mu_of \<mu> (f, length ts) \<or>
      qcs_ur_closed_term_check R U \<mu> t)
      (zip [0..<length ts] ts)"
    by (auto simp: list_all_iff)
  have roots_sem: "\<forall>lr\<in>set R.
    root (fst lr) = Some (f, length ts) \<longrightarrow> lr \<in> set U"
    using roots by auto
  have args_sem: "\<forall>i<length ts.
    i \<in> mu_of \<mu> (f, length ts) \<longrightarrow>
    qcs_ur_closed_term (set R) (set U) (mu_of \<mu>) (ts ! i)"
    using args Fun.hyps
    by (metis list_all_zip_upt_nth nth_mem)
  show ?case using roots_sem args_sem by simp
qed

lemma qcs_ur_closed_dp_rhs_check_sound:
  assumes "qcs_ur_closed_dp_rhs_check R U \<mu> t"
  shows "qcs_ur_closed_dp_rhs (set R) (set U) (mu_of \<mu>) t"
  using assms
proof (cases t)
  case (Var x)
  then show ?thesis using assms by simp
next
  case (Fun f ts)
  from Fun assms obtain g where f: "f = Sharp g"
    by (cases f, auto)
  from Fun f assms have args: "list_all (\<lambda>(i, t).
    i \<notin> mu_of \<mu> (g, length ts) \<or>
    qcs_ur_closed_term_check R U \<mu> t)
    (zip [0..<length ts] ts)"
    by simp
  have args_sem: "\<forall>i<length ts.
    i \<in> mu_of \<mu> (g, length ts) \<longrightarrow>
    qcs_ur_closed_term (set R) (set U) (mu_of \<mu>) (ts ! i)"
    using args qcs_ur_closed_term_check_sound
    by (metis list_all_zip_upt_nth)
  show ?thesis unfolding Fun f using args_sem by simp
qed

lemma qcs_csr_ur_closed_check_sound:
  assumes "qcs_csr_ur_closed_check R U \<mu> P"
  shows "qcs_csr_ur_closed (set R) (set U) (mu_of \<mu>) (set P)"
proof -
  from assms have subset: "set U \<subseteq> set R"
    and U: "\<And>lr. lr \<in> set U \<Longrightarrow>
      qcs_ur_closed_term_check R U \<mu> (snd lr)"
    and P: "\<And>dp. dp \<in> set P \<Longrightarrow>
      qcs_ur_closed_dp_rhs_check R U \<mu> (snd dp)"
    unfolding qcs_csr_ur_closed_check_def
    by (auto simp: list_all_iff)
  show ?thesis
    unfolding qcs_csr_ur_closed_def
  proof (intro conjI ballI)
    show "set U \<subseteq> set R" by (rule subset)
    fix lr
    assume "lr \<in> set U"
    from qcs_ur_closed_term_check_sound[OF U[OF this]]
    show "qcs_ur_closed_term (set R) (set U) (mu_of \<mu>) (snd lr)" .
  next
    fix dp
    assume "dp \<in> set P"
    from qcs_ur_closed_dp_rhs_check_sound[OF P[OF this]]
    show "qcs_ur_closed_dp_rhs (set R) (set U) (mu_of \<mu>) (snd dp)" .
  qed
qed

definition csr_qcs_usable_rules_proc ::
  "('dpp, ('f::{showl, compare_order}, 'l::{showl, compare_order}) lab, 'v::{showl, compare_order}) dpp_ops \<Rightarrow>
   (('f, 'l) lab) muL \<Rightarrow> ((('f, 'l) lab), 'v) rules \<Rightarrow> 'dpp proc"
where
  "csr_qcs_usable_rules_proc J \<mu> U dpp =
    check_return (do {
      check (qcs_csr_ur_closed_check
        (dpp_ops.rules J dpp) U \<mu> (dpp_ops.pairs J dpp))
        (showsl_lit (STR ''error when checking QCS usable-rule closure''))
    }) (dpp_ops.intersect_rules J dpp U)"

lemma csr_qcs_usable_rules_proc_sound:
  assumes J: "dpp_spec J"
    and proc: "csr_qcs_usable_rules_proc J \<mu> U dpp = return dpp'"
  shows "dpp' = dpp_ops.intersect_rules J dpp U"
    and "qcs_csr_ur_closed (set (dpp_ops.rules J dpp)) (set U) (mu_of \<mu>)
      (set (dpp_ops.pairs J dpp))"
proof -
  from proc[unfolded csr_qcs_usable_rules_proc_def]
  have dpp': "dpp' = dpp_ops.intersect_rules J dpp U"
    and closed: "qcs_csr_ur_closed_check
      (dpp_ops.rules J dpp) U \<mu> (dpp_ops.pairs J dpp)"
    by (auto simp: isOK_check)
  show "dpp' = dpp_ops.intersect_rules J dpp U"
    by (rule dpp')
  show "qcs_csr_ur_closed (set (dpp_ops.rules J dpp)) (set U) (mu_of \<mu>)
      (set (dpp_ops.pairs J dpp))"
    by (rule qcs_csr_ur_closed_check_sound[OF closed])
qed

lemma sharp_csdp_step_active_arg:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f, n)"
    and i: "i < length ts"
    and active: "i \<in> \<mu> (f, length ts)"
    and step: "(Fun (Sharp f) ts, v) \<in> csdp_step Sharp \<mu> R"
  shows "\<exists>us. v = Fun (Sharp f) us \<and> length us = length ts \<and>
    (ts ! i, us ! i) \<in> (csstep \<mu> R)\<^sup>*"
proof -
  have sharp: "Fun (Sharp f) ts = sharp_term Sharp (Fun f ts)"
    by simp
  from sharp_csdp_step_imp_csnrstep[OF wf fresh inj_Sharp,
      of "Fun f ts" v]
    step[unfolded sharp]
  obtain u where v: "v = sharp_term Sharp u"
    and nr: "(Fun f ts, u) \<in> csnrstep \<mu> R"
    by blast
  from nr obtain j us where j: "j < length ts"
    and u: "u = Fun f us" and len: "length us = length ts"
    and sub: "(ts ! j, us ! j) \<in> csstep \<mu> R"
    and same: "\<And>k. k < length ts \<Longrightarrow> k \<noteq> j \<Longrightarrow>
      us ! k = ts ! k"
    by (elim csnrstep_FunE, blast)
  have arg: "(ts ! i, us ! i) \<in> (csstep \<mu> R)\<^sup>*"
  proof (cases "i = j")
    case True
    with sub show ?thesis by simp
  next
    case False
    from same[OF i False] show ?thesis by simp
  qed
  show ?thesis
    using v u len arg by simp
qed

lemma sharp_csdp_steps_active_arg:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f, n)"
    and i: "i < length ts"
    and active: "i \<in> \<mu> (f, length ts)"
    and steps: "(Fun (Sharp f) ts, v) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "\<exists>us. v = Fun (Sharp f) us \<and> length us = length ts \<and>
    (ts ! i, us ! i) \<in> (csstep \<mu> R)\<^sup>*"
  using steps
proof (induct rule: rtrancl_induct)
  case base
  show ?case
    using i by auto
next
  case (step y z)
  from step.hyps(3)
  obtain ys where y: "y = Fun (Sharp f) ys"
    and len: "length ys = length ts"
    and args: "(ts ! i, ys ! i) \<in> (csstep \<mu> R)\<^sup>*"
    by metis
  have i': "i < length ys"
    using i len by simp
  have active': "i \<in> \<mu> (f, length ys)"
    using active len by simp
  from sharp_csdp_step_active_arg[OF wf fresh i' active'
      step.hyps(2)[unfolded y]]
  obtain zs where z: "z = Fun (Sharp f) zs"
    and zlen: "length zs = length ys"
    and arg: "(ys ! i, zs ! i) \<in> (csstep \<mu> R)\<^sup>*"
    by metis
  have total: "(ts ! i, zs ! i) \<in> (csstep \<mu> R)\<^sup>*"
    by (rule rtrancl_trans[OF args arg])
  show ?case
    using z zlen len total by auto
qed

lemma SN_sharp_csdp_imp_SN_active_arg:
  fixes shp :: "'f::{showl, compare_order} \<Rightarrow> 'f"
  assumes i: "i < length ts"
    and active: "i \<in> \<mu> (f, length ts)"
    and SN: "SN_on (csdp_step shp \<mu> R) {Fun (shp f) ts}"
  shows "SN_on (csstep \<mu> R) {ts ! i}"
proof (unfold SN_on_def, intro notI)
  assume "\<exists>as. as 0 \<in> {ts ! i} \<and>
    (\<forall>n. (as n, as (Suc n)) \<in> csstep \<mu> R)"
  then obtain as where init: "as 0 = ts ! i"
    and step: "\<And>n. (as n, as (Suc n)) \<in> csstep \<mu> R"
    by auto
  let ?whole = "\<lambda>n. Fun (shp f) (ts[i := as n])"
  have whole0: "?whole 0 = Fun (shp f) ts"
    using init i by simp
  have whole_step:
    "(?whole n, ?whole (Suc n)) \<in> csdp_step shp \<mu> R" for n
  proof -
    have len: "i < length (ts[i := as n])"
      using i by simp
    have active': "i \<in> \<mu> (f, length (ts[i := as n]))"
      using active by simp
    have sub:
      "((ts[i := as n]) ! i, as (Suc n)) \<in> csstep \<mu> R"
      using step[of n] i by simp
    from csstep_FunI[OF len active' sub]
    have nr:
      "(Fun f (ts[i := as n]),
        Fun f ((ts[i := as n])[i := as (Suc n)])) \<in> csnrstep \<mu> R" .
    from sharp_csnrstep_imp_csdp_step[OF nr, where shp = shp]
    show ?thesis
      using i by simp
  qed
  have bad:
    "\<exists>ws. ws 0 \<in> {Fun (shp f) ts} \<and>
      (\<forall>n. (ws n, ws (Suc n)) \<in> csdp_step shp \<mu> R)"
  proof (intro exI[of _ ?whole] conjI)
    show "?whole 0 \<in> {Fun (shp f) ts}"
      using whole0 by simp
    show "\<forall>n. (?whole n, ?whole (Suc n)) \<in> csdp_step shp \<mu> R"
      using whole_step by simp
  qed
  from SN bad show False
    unfolding SN_on_def by contradiction
qed

fun csr_sct_active_index where
  "csr_sct_active_index \<mu> (Fun (Sharp f) ts) (Suc i) =
    (i < length ts \<and> i \<in> \<mu> (f, length ts))"
| "csr_sct_active_index \<mu> t i = False"

fun csr_sct_index where
  "csr_sct_index (Fun (Sharp f) ts) (Suc i) = (i < length ts)"
| "csr_sct_index t i = False"

lemma csr_sct_indexE:
  assumes index: "csr_sct_index t i"
  obtains f ts j where "t = Fun (Sharp f) ts" "i = Suc j"
    "j < length ts"
proof (cases t)
  case (Var x)
  with index show thesis by simp
next
  case (Fun g us)
  show thesis
  proof (cases i)
    case 0
    with index Fun show thesis by simp
  next
    case (Suc j)
    show thesis
    proof (cases g)
      case (Sharp f)
      with index Fun Suc have "j < length us" by simp
      with that[of f us j] Fun Suc Sharp show thesis by simp
    qed (use index Fun Suc in auto)
  qed
qed

lemma csr_sct_active_indexE:
  assumes active: "csr_sct_active_index \<mu> t i"
  obtains f ts j where "t = Fun (Sharp f) ts" "i = Suc j"
    "j < length ts" "j \<in> \<mu> (f, length ts)"
proof (cases t)
  case (Var x)
  with active show thesis by simp
next
  case (Fun g us)
  show thesis
  proof (cases i)
    case 0
    with active Fun show thesis by simp
  next
    case (Suc j)
    show thesis
    proof (cases g)
      case (Sharp f)
      with active Fun Suc have "j < length us"
        "j \<in> \<mu> (f, length us)"
        by auto
      with that[of f us j] Fun Suc Sharp show thesis
        by simp
    qed (use active Fun Suc in auto)
  qed
qed

lemma csr_sct_active_index_bound:
  assumes "csr_sct_active_index \<mu> t i"
  shows "0 < i \<and> i \<le> length (args t)"
proof -
  from csr_sct_active_indexE[OF assms]
  obtain f ts j where t: "t = Fun (Sharp f) ts" and i: "i = Suc j"
    and j: "j < length ts"
    by metis
  show ?thesis
    using t i j by simp
qed

lemma csr_sct_active_index_subst_SN:
  assumes active: "csr_sct_active_index \<mu> t i"
    and SN: "SN_on (csdp_step Sharp \<mu> R) {t \<cdot> \<sigma>}"
  shows "SN_on (csstep \<mu> R) {get_arg t i \<cdot> \<sigma>}"
proof (cases t)
  case (Var x)
  then show ?thesis
    using active by simp
next
  case (Fun g ts)
  show ?thesis
  proof (cases i)
    case 0
    then show ?thesis
      using active Fun by simp
  next
    case (Suc j)
    show ?thesis
    proof (cases g)
      case (Sharp f)
      from active Fun Suc Sharp have j: "j < length ts"
        and act: "j \<in> \<mu> (f, length ts)"
        by auto
      have SN':
        "SN_on (csdp_step Sharp \<mu> R)
          {Fun (Sharp f) (map (\<lambda>u. u \<cdot> \<sigma>) ts)}"
        using SN Fun Sharp by simp
      have j': "j < length (map (\<lambda>u. u \<cdot> \<sigma>) ts)"
        using j by simp
      have act': "j \<in> \<mu> (f, length (map (\<lambda>u. u \<cdot> \<sigma>) ts))"
        using act by simp
      from SN_sharp_csdp_imp_SN_active_arg[OF j' act' SN']
      show ?thesis
        using Fun Suc Sharp j by simp
    qed (use active Fun Suc in auto)
  qed
qed

lemma csr_sct_active_get_arg_steps:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f, n)"
    and active_t: "csr_sct_active_index \<mu> t i"
    and active_s: "csr_sct_active_index \<mu> s i"
    and steps: "(t \<cdot> \<sigma>, s \<cdot> \<tau>) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "(get_arg t i \<cdot> \<sigma>, get_arg s i \<cdot> \<tau>) \<in>
    (csstep \<mu> R)\<^sup>*"
proof (cases t)
  case (Var x)
  then show ?thesis
    using active_t by simp
next
  case (Fun g ts)
  show ?thesis
  proof (cases i)
    case 0
    then show ?thesis
      using active_t Fun by simp
  next
    case (Suc j)
    show ?thesis
    proof (cases g)
      case (Sharp f)
      from active_t Fun Suc Sharp have j: "j < length ts"
        and act: "j \<in> \<mu> (f, length ts)"
        by auto
      from csr_sct_active_indexE[OF active_s]
      obtain h ss k where s: "s = Fun (Sharp h) ss"
        and i': "i = Suc k" and k_s: "k < length ss"
        and k_act: "k \<in> \<mu> (h, length ss)"
        by auto
      from i' Suc have k: "k = j"
        by simp
      have j_s: "j < length ss"
        using k_s k by simp
      have steps':
        "(Fun (Sharp f) (map (\<lambda>u. u \<cdot> \<sigma>) ts), s \<cdot> \<tau>) \<in>
          (csdp_step Sharp \<mu> R)\<^sup>*"
        using steps Fun Sharp by simp
      have j': "j < length (map (\<lambda>u. u \<cdot> \<sigma>) ts)"
        using j by simp
      have act': "j \<in> \<mu> (f, length (map (\<lambda>u. u \<cdot> \<sigma>) ts))"
        using act by simp
      from sharp_csdp_steps_active_arg[OF wf fresh j' act' steps']
      obtain us where end_term:
          "s \<cdot> \<tau> = Fun (Sharp f) us"
        and len: "length us = length ts"
        and arg0:
          "(map (\<lambda>u. u \<cdot> \<sigma>) ts ! j, us ! j) \<in>
            (csstep \<mu> R)\<^sup>*"
        by auto
      have arg:
        "(ts ! j \<cdot> \<sigma>, us ! j) \<in> (csstep \<mu> R)\<^sup>*"
        using arg0 j by simp
      from end_term s have us: "us = map (\<lambda>u. u \<cdot> \<tau>) ss"
        by auto
      show ?thesis
        using Fun Suc Sharp s j j_s arg us by simp
    qed (use active_t Fun Suc in auto)
  qed
qed

lemma csr_sct_get_arg_transition:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f, n)"
    and index_t: "csr_sct_index t i"
    and index_s: "csr_sct_index s i"
    and target_SN: "SN_on (csdp_step Sharp \<mu> R) {t \<cdot> \<sigma>}"
    and steps: "(t \<cdot> \<sigma>, s \<cdot> \<tau>) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "(get_arg t i \<cdot> \<sigma>, get_arg s i \<cdot> \<tau>) \<in>
    restrict_SN ((csstep \<mu> R)\<^sup>*) (csstep \<mu> R) \<union> Id"
proof -
  from csr_sct_indexE[OF index_t]
  obtain f ts j where t: "t = Fun (Sharp f) ts"
    and i: "i = Suc j" and j: "j < length ts" .
  from csr_sct_indexE[OF index_s]
  obtain h ss k where s: "s = Fun (Sharp h) ss"
    and i': "i = Suc k" and k: "k < length ss" .
  from i i' have kj: "k = j" by simp
  have steps':
    "(Fun (Sharp f) (map (\<lambda>u. u \<cdot> \<sigma>) ts), s \<cdot> \<tau>) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>*"
    using steps t by simp
  have undef:
    "\<not> defined R
      (Sharp f, length (map (\<lambda>u. u \<cdot> \<sigma>) ts))"
    by (rule fresh)
  from cssteps_Fun_undefined_root_preserved[OF wf undef steps']
  obtain us where finish:
      "s \<cdot> \<tau> = Fun (Sharp f) us"
    and len_us:
      "length us = length (map (\<lambda>u. u \<cdot> \<sigma>) ts)"
    by blast
  from finish s have hf: "h = f"
    and maps: "map (\<lambda>u. u \<cdot> \<tau>) ss = us"
    by auto
  have len: "length ss = length ts"
    using arg_cong[OF maps, of length] len_us by simp
  have j_ss: "j < length ss"
    using j len by simp
  show ?thesis
  proof (cases "j \<in> \<mu> (f, length ts)")
    case True
    have active_t: "csr_sct_active_index \<mu> t i"
      using t i j True by simp
    have active_s: "csr_sct_active_index \<mu> s i"
      using s i kj k hf len True by simp
    have arg_steps:
      "(get_arg t i \<cdot> \<sigma>, get_arg s i \<cdot> \<tau>) \<in>
        (csstep \<mu> R)\<^sup>*"
      by (rule csr_sct_active_get_arg_steps[
        OF wf fresh active_t active_s steps])
    have arg_SN:
      "SN_on (csstep \<mu> R) {get_arg t i \<cdot> \<sigma>}"
      by (rule csr_sct_active_index_subst_SN[OF active_t target_SN])
    show ?thesis
      using arg_steps arg_SN unfolding restrict_SN_def by auto
  next
    case False
    have inactive:
      "j \<notin> csr_dp_root_mu \<mu>
        (Sharp f, length (map (\<lambda>u. u \<cdot> \<sigma>) ts))"
      using False by simp
    have j_map: "j < length (map (\<lambda>u. u \<cdot> \<sigma>) ts)"
      using j by simp
    from cssteps_Fun_inactive_arg_preserved[
      OF wf undef j_map inactive steps']
    obtain vs where finish':
        "s \<cdot> \<tau> = Fun (Sharp f) vs"
      and same:
        "vs ! j = map (\<lambda>u. u \<cdot> \<sigma>) ts ! j"
      by blast
    from finish finish' have vs_us: "vs = us" by simp
    have left: "get_arg t i \<cdot> \<sigma> = us ! j"
      using same j t i vs_us by simp
    have maps_j: "map (\<lambda>u. u \<cdot> \<tau>) ss ! j = us ! j"
      by (rule arg_cong[OF maps])
    have right: "get_arg s i \<cdot> \<tau> = us ! j"
      using maps_j j_ss s i kj by simp
    have eq:
      "get_arg t i \<cdot> \<sigma> = get_arg s i \<cdot> \<tau>"
      using left right by simp
    with eq show ?thesis by auto
  qed
qed

lemma csr_sct_index_steps:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f, n)"
    and index_t: "csr_sct_index t i"
    and shape_s: "\<exists>g ss. s = Fun (Sharp g) ss"
    and steps: "(t \<cdot> \<sigma>, s \<cdot> \<tau>) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "csr_sct_index s i"
proof -
  from csr_sct_indexE[OF index_t]
  obtain f ts j where t: "t = Fun (Sharp f) ts"
    and i: "i = Suc j" and j: "j < length ts" .
  from shape_s obtain g ss where s: "s = Fun (Sharp g) ss"
    by auto
  have start:
    "t \<cdot> \<sigma> = Fun (Sharp f) (map (\<lambda>u. u \<cdot> \<sigma>) ts)"
    using t by simp
  have undef:
    "\<not> defined R
      (Sharp f, length (map (\<lambda>u. u \<cdot> \<sigma>) ts))"
    by (rule fresh)
  from cssteps_Fun_undefined_root_preserved[
    OF wf undef steps[unfolded start]]
  obtain us where finish:
      "s \<cdot> \<tau> = Fun (Sharp f) us"
    and len_us:
      "length us = length (map (\<lambda>u. u \<cdot> \<sigma>) ts)"
    by blast
  from finish s have gf: "g = f"
    and maps: "map (\<lambda>u. u \<cdot> \<tau>) ss = us"
    by auto
  have "length ss = length ts"
    using arg_cong[OF maps, of length] len_us by simp
  with s i j show ?thesis by simp
qed

lemma mu_poss_replace_at_root:
  assumes p: "p \<in> mu_fun_poss \<mu> t"
  shows "p \<in> mu_poss \<mu> (replace_at t p u)"
  using p
proof (induct t arbitrary: p)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  show ?case
  proof (cases p)
    case Nil
    then show ?thesis
      by (cases u, auto)
  next
    case (Cons i q)
    with Fun.prems have i: "i \<in> \<mu> (f, length ts)" "i < length ts"
      and q: "q \<in> mu_fun_poss \<mu> (ts ! i)"
      by auto
    from Fun.hyps[OF nth_mem[OF i(2)] q]
    have rec: "q \<in> mu_poss \<mu> (replace_at (ts ! i) q u)" .
    show ?thesis
      using i rec Cons by (simp add: nth_append)
  qed
qed

lemma mu_poss_Fun_subterm_imp_mu_fun_poss:
  assumes p: "p \<in> mu_poss \<mu> t"
    and sub: "t |_ p = Fun f ts"
  shows "p \<in> mu_fun_poss \<mu> t"
  using p sub
proof (induct t arbitrary: p)
  case (Var x)
  then show ?case by simp
next
  case (Fun g us)
  show ?case
  proof (cases p)
    case Nil
    then show ?thesis by simp
  next
    case (Cons i q)
    with Fun.prems have i: "i \<in> \<mu> (g, length us)" "i < length us"
      and q: "q \<in> mu_poss \<mu> (us ! i)"
      and sub: "us ! i |_ q = Fun f ts"
      by auto
    from Fun.hyps[OF nth_mem[OF i(2)] q sub]
    have "q \<in> mu_fun_poss \<mu> (us ! i)" .
    with i Cons show ?thesis by auto
  qed
qed

lemma mu_supt_csstep_commute:
  assumes wf: "wf_trs R"
    and sub: "mu_supt \<mu> x y"
    and step: "(y, z) \<in> csstep \<mu> R"
  shows "\<exists>w. (x, w) \<in> csstep \<mu> R \<and> mu_supt \<mu> w z"
proof -
  from sub obtain i p where pos: "i # p \<in> mu_poss \<mu> x"
    and y: "x |_ (i # p) = y"
    unfolding mu_supt_def by auto
  from step have y_fun: "is_Fun y"
  proof (cases y)
    case (Var v)
    from step[unfolded Var] csstep_Var_empty_wf[OF wf, of v z \<mu>]
    show ?thesis by contradiction
  qed simp
  then obtain f ts where yf: "y = Fun f ts"
    by (cases y, auto)
  have sub_fun: "x |_ (i # p) = Fun f ts"
    using y yf by simp
  have pfun: "i # p \<in> mu_fun_poss \<mu> x"
    by (rule mu_poss_Fun_subterm_imp_mu_fun_poss[OF pos sub_fun])
  let ?w = "replace_at x (i # p) z"
  have xw: "(x, ?w) \<in> csstep \<mu> R"
    by (rule csstep_mu_subterm_lift[OF wf pfun], unfold y, rule step)
  have pposs: "i # p \<in> poss x"
    using pos mu_poss_imp_poss by blast
  have pos_w: "i # p \<in> mu_poss \<mu> ?w"
    by (rule mu_poss_replace_at_root[OF pfun])
  have sub_w: "?w |_ (i # p) = z"
    by (rule replace_at_subt_at[OF pposs])
  have "mu_supt \<mu> ?w z"
    unfolding mu_supt_def using pos_w sub_w by blast
  with xw show ?thesis by blast
qed

lemma SN_restrict_SN_mu_supt_csstep:
  assumes wf: "wf_trs R"
  shows "SN (restrict_SN (csstep \<mu> R) (csstep \<mu> R) \<union>
    restrict_SN (mu_supt_rel \<mu>) (csstep \<mu> R))"
proof -
  let ?A = "restrict_SN (csstep \<mu> R) (csstep \<mu> R)"
  let ?B = "restrict_SN (mu_supt_rel \<mu>) (csstep \<mu> R)"
  have sn_A: "SN ?A"
    by (rule SN_restrict_SN_idemp)
  have B_sub: "?B \<subseteq> {\<rhd>}"
    unfolding restrict_SN_def mu_supt_rel_def
    using mu_supt_imp_supt by auto
  have sn_B: "SN ?B"
    by (rule SN_subset[OF SN_supt B_sub])
  have commute: "quasi_commute ?A ?B"
    unfolding quasi_commute_def
  proof (rule subrelI)
    fix x z
    assume "(x, z) \<in> ?B O ?A"
    then obtain y where xy: "(x, y) \<in> ?B"
      and yz: "(y, z) \<in> ?A"
      by auto
    from xy have sub: "mu_supt \<mu> x y"
      and sn_x: "SN_on (csstep \<mu> R) {x}"
      unfolding restrict_SN_def mu_supt_rel_def by auto
    from yz have step: "(y, z) \<in> csstep \<mu> R"
      unfolding restrict_SN_def by auto
    from mu_supt_csstep_commute[OF wf sub step]
    obtain w where xw: "(x, w) \<in> csstep \<mu> R"
      and wz: "mu_supt \<mu> w z"
      by auto
    have sn_w: "SN_on (csstep \<mu> R) {w}"
      by (rule step_preserves_SN_on[OF xw sn_x])
    have xw_A: "(x, w) \<in> ?A"
      using xw sn_x unfolding restrict_SN_def by auto
    have wz_B: "(w, z) \<in> ?B"
      using wz sn_w unfolding restrict_SN_def mu_supt_rel_def by auto
    have "(w, z) \<in> (?A \<union> ?B)\<^sup>*"
      using wz_B by auto
    with xw_A show "(x, z) \<in> ?A O (?A \<union> ?B)\<^sup>*"
      by auto
  qed
  show ?thesis
    by (rule quasi_commute_imp_SN[OF sn_A sn_B commute])
qed

lemma SN_on_csstep_imp_SN_on_mu_supt_union:
  assumes wf: "wf_trs R"
    and SN: "SN_on (csstep \<mu> R) T"
  shows "SN_on (mu_supt_rel \<mu> \<union> csstep \<mu> R) T"
proof (rule ccontr)
  let ?S = "mu_supt_rel \<mu> \<union> csstep \<mu> R"
  assume "\<not> SN_on ?S T"
  then obtain f where init: "f 0 \<in> T"
    and chain: "\<And>i. (f i, f (Suc i)) \<in> ?S"
    unfolding SN_on_def by auto
  have all_SN: "SN_on (csstep \<mu> R) {f i}" for i
  proof (induct i)
    case 0
    show ?case
      by (rule SN_on_subset2[of "{f 0}" T],
        use init SN in auto)
  next
    case (Suc i)
    from chain[of i] show ?case
    proof
      assume "(f i, f (Suc i)) \<in> mu_supt_rel \<mu>"
      then obtain j p where p: "j # p \<in> mu_poss \<mu> (f i)"
        and sub: "f i |_ (j # p) = f (Suc i)"
        unfolding mu_supt_rel_def mu_supt_def by auto
      from SN_on_mu_pos[OF wf p Suc]
      show ?case
        unfolding sub .
    next
      assume "(f i, f (Suc i)) \<in> csstep \<mu> R"
      then show ?case
        by (rule step_preserves_SN_on[OF _ Suc])
    qed
  qed
  let ?A = "restrict_SN (csstep \<mu> R) (csstep \<mu> R)"
  let ?B = "restrict_SN (mu_supt_rel \<mu>) (csstep \<mu> R)"
  have restricted: "(f i, f (Suc i)) \<in> ?A \<union> ?B" for i
    using chain[of i] all_SN[of i]
    unfolding restrict_SN_def by auto
  from SN_restrict_SN_mu_supt_csstep[OF wf]
  show False
    unfolding SN_defs using restricted by blast
qed

theorem wf_csr_i1_call:
  assumes fin: "finite R"
    and wf: "wf_trs R"
    and closed: "csr_u3_usable_rules_closed R U \<mu> P"
  shows "wf ((csr_i1_call R \<mu> (csr_u3_delta R U))\<inverse>)"
proof (rule ccontr)
  let ?C = "csr_i1_call R \<mu> (csr_u3_delta R U)"
  let ?Bad = "UNIV - Wellfounded.acc (?C\<inverse>)"
  assume not_wf: "\<not> wf (?C\<inverse>)"
  have acc_ne: "Wellfounded.acc (?C\<inverse>) \<noteq> UNIV"
  proof
    assume acc_all: "Wellfounded.acc (?C\<inverse>) = UNIV"
    have all_acc: "\<forall>x. x \<in> Wellfounded.acc (?C\<inverse>)"
      using acc_all by simp
    have "wf (?C\<inverse>)"
      by (rule wf_iff_acc[THEN iffD2, OF all_acc])
    with not_wf show False
      by contradiction
  qed
  have "?Bad \<noteq> {}"
    using acc_ne by auto
  then obtain a where bad_a: "a \<in> ?Bad"
    by auto
  have wf_sub: "wf {\<lhd>}"
    using SN_supt unfolding SN_iff_wf .
  obtain t where bad_t: "t \<in> ?Bad"
    and min_t_raw:
      "\<And>s. (s, t) \<in> {\<lhd>} \<Longrightarrow>
        s \<notin> ?Bad"
  proof (rule wfE_min[OF wf_sub bad_a])
    fix z
    assume z_bad: "z \<in> ?Bad"
      and z_min: "\<And>y. (y, z) \<in> {\<lhd>} \<Longrightarrow>
        y \<notin> ?Bad"
    show thesis
      by (rule that[OF z_bad z_min])
  qed
  have min_t: "\<And>s. t \<rhd> s \<Longrightarrow> s \<notin> ?Bad"
  proof -
    fix s
    assume ts: "t \<rhd> s"
    have "(s, t) \<in> {\<lhd>}"
      using ts by simp
    then show "s \<notin> ?Bad"
      by (rule min_t_raw)
  qed
  let ?M = "{x. x \<in> ?Bad \<and> (\<forall>y. x \<rhd> y \<longrightarrow> y \<notin> ?Bad)}"
  have tM: "t \<in> ?M"
    using bad_t min_t by simp

  have bad_rewrite:
    "\<And>x. x \<in> ?M \<Longrightarrow>
      \<exists>u. u \<in> ?Bad \<and>
        (x, u) \<in> csr_i1_rewrite_call R \<mu> (csr_u3_delta R U)"
  proof -
    fix x
    assume xM: "x \<in> ?M"
    then have x_bad: "x \<notin> Wellfounded.acc (?C\<inverse>)"
      by simp
    from not_acc_down[OF x_bad]
    obtain u where call: "(u, x) \<in> ?C\<inverse>"
      and u_bad: "u \<notin> Wellfounded.acc (?C\<inverse>)" .
    have xu: "(x, u) \<in> ?C"
      using call by simp
    show "\<exists>u. u \<in> ?Bad \<and>
      (x, u) \<in> csr_i1_rewrite_call R \<mu> (csr_u3_delta R U)"
    proof (rule exI[of _ u], intro conjI)
      show "u \<in> ?Bad"
        using u_bad by simp
      have xu_cases:
        "(x, u) \<in> csr_i1_struct_call \<or>
          (x, u) \<in>
            csr_i1_rewrite_call R \<mu> (csr_u3_delta R U)"
        using xu unfolding csr_i1_call_def by simp
      from xu_cases show
        "(x, u) \<in> csr_i1_rewrite_call R \<mu> (csr_u3_delta R U)"
      proof
        assume "(x, u) \<in> csr_i1_struct_call"
        then have xu_sub: "x \<rhd> u"
          by (rule subsetD[OF csr_i1_struct_call_supt])
        from xM have no_bad_sub:
          "\<forall>y. x \<rhd> y \<longrightarrow> y \<notin> ?Bad"
          by simp
        have "u \<in> ?Bad"
          using u_bad by simp
        moreover from no_bad_sub xu_sub have "u \<notin> ?Bad"
          by simp
        ultimately show ?thesis
          by contradiction
      next
        assume "(x, u) \<in>
          csr_i1_rewrite_call R \<mu> (csr_u3_delta R U)"
        then show ?thesis .
      qed
    qed
  qed

  have minimal_bad_below:
    "\<And>u. u \<in> ?Bad \<Longrightarrow>
      \<exists>s. s \<in> ?M \<and> u \<unrhd> s"
  proof -
    fix u
    assume u_bad: "u \<in> ?Bad"
    let ?Q = "{s. s \<in> ?Bad \<and> u \<unrhd> s}"
    have uQ: "u \<in> ?Q"
      using u_bad by simp
    obtain s where sQ: "s \<in> ?Q"
      and min_s_raw:
        "\<And>y. (y, s) \<in> {\<lhd>} \<Longrightarrow>
          y \<notin> ?Q"
    proof (rule wfE_min[OF wf_sub uQ])
      fix z
      assume zQ: "z \<in> ?Q"
        and z_min: "\<And>y. (y, z) \<in> {\<lhd>} \<Longrightarrow>
          y \<notin> ?Q"
      show thesis
        by (rule that[OF zQ z_min])
    qed
    have min_s: "\<And>y. s \<rhd> y \<Longrightarrow> y \<notin> ?Q"
    proof -
      fix y
      assume sy: "s \<rhd> y"
      have "(y, s) \<in> {\<lhd>}"
        using sy by simp
      then show "y \<notin> ?Q"
        by (rule min_s_raw)
    qed
    have sM: "s \<in> ?M"
    proof (simp only: mem_Collect_eq, intro conjI allI impI)
      show "s \<in> ?Bad"
        using sQ by simp
    next
      fix y
      assume sy: "s \<rhd> y"
      show "y \<notin> ?Bad"
      proof
        assume y_bad: "y \<in> ?Bad"
        from sQ have us: "u \<unrhd> s"
          by simp
        have "u \<rhd> y"
          by (rule supteq_supt_trans[OF us sy])
        then have "u \<unrhd> y"
          by (rule supt_imp_supteq)
        with y_bad have "y \<in> ?Q"
          by simp
        with min_s[OF sy] show False
          by contradiction
      qed
    qed
    show "\<exists>s. s \<in> ?M \<and> u \<unrhd> s"
    proof (rule exI[of _ s], intro conjI)
      show "s \<in> ?M"
        by (rule sM)
      show "u \<unrhd> s"
        using sQ by simp
    qed
  qed

  let ?G =
    "csstep \<mu> R O (Id \<union> mu_supt_rel \<mu>)"
  have progress:
    "\<And>x. x \<in> ?M \<Longrightarrow> \<exists>s. s \<in> ?M \<and> (x, s) \<in> ?G"
  proof -
    fix x
    assume xM: "x \<in> ?M"
    from bad_rewrite[OF xM]
    obtain u where u_bad: "u \<in> ?Bad"
      and xu_call:
        "(x, u) \<in> csr_i1_rewrite_call R \<mu> (csr_u3_delta R U)"
      by auto
    from minimal_bad_below[OF u_bad]
    obtain s where sM: "s \<in> ?M" and us: "u \<unrhd> s"
      by auto
    from bad_rewrite[OF sM]
    obtain z where
      sz_call:
        "(s, z) \<in> csr_i1_rewrite_call R \<mu> (csr_u3_delta R U)"
      by auto
    have xu: "(x, u) \<in> csstep \<mu> R"
      by (rule csr_i1_rewrite_callD(3)[OF xu_call])
    have s_nondelta:
        "the (root s) \<notin> csr_u3_delta R U"
      by (rule csr_i1_rewrite_callD(2)[OF sz_call])
    have sz: "(s, z) \<in> csstep \<mu> R"
      by (rule csr_i1_rewrite_callD(3)[OF sz_call])
    have s_fun: "is_Fun s"
    proof (cases s)
      case (Var v)
      from csstep_Var_empty_wf[OF wf, of v z \<mu>]
        sz[unfolded Var]
      show ?thesis by contradiction
    next
      case (Fun f ts)
      then show ?thesis by simp
    qed
    have not_xs: "\<not> x \<rhd> s"
    proof
      assume xs: "x \<rhd> s"
      from xM have no_bad_sub:
        "\<forall>y. x \<rhd> y \<longrightarrow> y \<notin> ?Bad"
        by simp
      from no_bad_sub xs have "s \<notin> ?Bad"
        by simp
      moreover from sM have "s \<in> ?Bad"
        by simp
      ultimately show False
        by contradiction
    qed
    from csr_u3_post_step_nondelta_supteq[
        OF wf closed xu us not_xs s_fun s_nondelta]
    have "(u, s) \<in> Id \<union> mu_supt_rel \<mu>" .
    with xu have "(x, s) \<in> ?G"
      by auto
    with sM show "\<exists>s. s \<in> ?M \<and> (x, s) \<in> ?G"
      by (intro exI[of _ s] conjI)
  qed

  have G_sub:
    "?G \<subseteq> (mu_supt_rel \<mu> \<union> csstep \<mu> R)\<^sup>+"
  proof
    fix x y
    assume "(x, y) \<in> ?G"
    then obtain z where xz: "(x, z) \<in> csstep \<mu> R"
      and zy: "(z, y) \<in> Id \<union> mu_supt_rel \<mu>"
      by auto
    from zy show
      "(x, y) \<in> (mu_supt_rel \<mu> \<union> csstep \<mu> R)\<^sup>+"
    proof
      assume "(z, y) \<in> Id"
      then have "z = y"
        by simp
      with xz have xy: "(x, y) \<in> csstep \<mu> R"
        by simp
      have "(x, y) \<in> mu_supt_rel \<mu> \<union> csstep \<mu> R"
        by (rule UnI2[OF xy])
      then show ?thesis
        by (rule trancl.r_into_trancl)
    next
      assume zy_mu: "(z, y) \<in> mu_supt_rel \<mu>"
      have xz_step:
        "(x, z) \<in> (mu_supt_rel \<mu> \<union> csstep \<mu> R)\<^sup>+"
        by (intro trancl.r_into_trancl UnI2 xz)
      have zy_step:
        "(z, y) \<in> mu_supt_rel \<mu> \<union> csstep \<mu> R"
        by (rule UnI1[OF zy_mu])
      show ?thesis
        by (rule trancl_into_trancl[OF xz_step zy_step])
    qed
  qed
  from bad_rewrite[OF tM]
  obtain u where
    tu_call:
      "(t, u) \<in> csr_i1_rewrite_call R \<mu> (csr_u3_delta R U)"
    by auto
  have sn_t: "SN_on (csstep \<mu> R) {t}"
    by (rule csr_i1_rewrite_callD(1)[OF tu_call])
  from SN_on_csstep_imp_SN_on_mu_supt_union[OF wf sn_t]
  have sn_active:
    "SN_on ((mu_supt_rel \<mu> \<union> csstep \<mu> R)\<^sup>+) {t}"
    by (rule SN_on_trancl)
  have sn_G: "SN_on ?G {t}"
    by (rule SN_on_subset1[OF sn_active G_sub])
  have "t \<notin> ?M"
  proof (rule SN_on_induct_acc_style[
      where R="?G" and P="\<lambda>x. x \<notin> ?M", OF sn_G])
    fix x
    assume sn_x: "SN_on ?G {x}"
      and IH: "\<And>y. (x, y) \<in> ?G \<Longrightarrow> y \<notin> ?M"
    show "x \<notin> ?M"
    proof
      assume xM: "x \<in> ?M"
      from progress[OF xM]
      obtain y where yM: "y \<in> ?M" and xy: "(x, y) \<in> ?G"
        by auto
      from IH[OF xy] yM show False
        by contradiction
    qed
  qed
  with tM show False
    by contradiction
qed

locale csr_u3_i1 =
  fixes Rs :: "('f::{showl, compare_order}, 'v) rules"
    and U :: "('f, 'v) trs"
    and \<mu> :: "('f \<times> nat) \<Rightarrow> nat set"
    and P :: "('f, 'v) trs"
    and cn :: "'f \<times> nat"
  assumes wf: "wf_trs (set Rs)"
    and closed:
      "csr_u3_usable_rules_closed (set Rs) U \<mu> P"
begin

abbreviation \<Delta> where
  "\<Delta> \<equiv> csr_u3_delta (set Rs) U"

function i1 :: "('f, 'v) term \<Rightarrow> ('f, 'v) term" where
  "i1 (Var x) = Var x"
| "i1 (Fun f ts) =
    (if (f, length ts) \<in> \<Delta> \<or>
        \<not> SN_on (csstep \<mu> (set Rs)) {Fun f ts}
      then Fun f (map i1 ts)
      else comb cn
        (Fun f (map i1 ts) # map i1 (csrewrite \<mu> Rs (Fun f ts))))"
  by pat_completeness auto

termination i1
  apply (relation "(csr_i1_call (set Rs) \<mu> \<Delta>)\<inverse>")
    apply (rule wf_csr_i1_call[OF finite_set wf closed])
   apply (auto simp: csr_i1_call_def csr_i1_struct_call_def)
  apply (auto simp: csr_i1_call_def csr_i1_rewrite_call_def
    intro: csrewrite_sound)
  done

abbreviation i1_subst :: "('f, 'v) subst \<Rightarrow> ('f, 'v) subst" where
  "i1_subst \<sigma> \<equiv> \<lambda>x. i1 (\<sigma> x)"

lemma i1_delta_subst:
  assumes delta: "funas_term t \<subseteq> \<Delta>"
  shows "i1 (t \<cdot> \<sigma>) = t \<cdot> i1_subst \<sigma>"
  using delta
proof (induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  have root_delta: "(f, length ts) \<in> \<Delta>"
    using Fun.prems by simp
  have args_delta: "\<And>t. t \<in> set ts \<Longrightarrow> funas_term t \<subseteq> \<Delta>"
    using Fun.prems by auto
  have IH:
    "\<And>t. t \<in> set ts \<Longrightarrow>
      i1 (t \<cdot> \<sigma>) = t \<cdot> i1_subst \<sigma>"
    using Fun(1) args_delta by blast
  show ?case
    using root_delta IH by simp
qed

lemma i1_pattern_subst:
  assumes inactive:
    "\<And>p. p \<in> fun_poss t \<Longrightarrow>
      p \<notin> mu_fun_poss \<mu> t \<Longrightarrow>
      funas_term (t |_ p) \<subseteq> \<Delta>"
  shows "(i1 (t \<cdot> \<sigma>), t \<cdot> i1_subst \<sigma>)
    \<in> (csstep \<mu> (ce_trs cn))\<^sup>*"
  using inactive
proof (induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  let ?ss = "map (\<lambda>s. i1 (s \<cdot> \<sigma>)) ts"
  let ?us = "map (\<lambda>s. s \<cdot> i1_subst \<sigma>) ts"
  have len: "length ?ss = length ?us"
    by simp
  have arg:
    "\<And>i. i < length ?ss \<Longrightarrow>
      (if i \<in> \<mu> (f, length ?ss)
       then (?ss ! i, ?us ! i)
         \<in> (csstep \<mu> (ce_trs cn))\<^sup>*
       else ?us ! i = ?ss ! i)"
  proof -
    fix i
    assume i: "i < length ?ss"
    then have i_ts: "i < length ts"
      by simp
    show "(if i \<in> \<mu> (f, length ?ss)
      then (?ss ! i, ?us ! i)
        \<in> (csstep \<mu> (ce_trs cn))\<^sup>*
      else ?us ! i = ?ss ! i)"
    proof (cases "i \<in> \<mu> (f, length ts)")
      case True
      have inherited:
        "\<And>p. p \<in> fun_poss (ts ! i) \<Longrightarrow>
          p \<notin> mu_fun_poss \<mu> (ts ! i) \<Longrightarrow>
          funas_term (ts ! i |_ p) \<subseteq> \<Delta>"
      proof -
        fix p
        assume p_fun: "p \<in> fun_poss (ts ! i)"
          and p_inactive: "p \<notin> mu_fun_poss \<mu> (ts ! i)"
        have ip_fun: "i # p \<in> fun_poss (Fun f ts)"
          using i_ts p_fun by simp
        have ip_inactive: "i # p \<notin> mu_fun_poss \<mu> (Fun f ts)"
          using i_ts True p_inactive by simp
        show "funas_term (ts ! i |_ p) \<subseteq> \<Delta>"
          using Fun.prems[OF ip_fun ip_inactive] i_ts p_fun
          by simp
      qed
      have sub:
        "(i1 ((ts ! i) \<cdot> \<sigma>),
          (ts ! i) \<cdot> i1_subst \<sigma>)
          \<in> (csstep \<mu> (ce_trs cn))\<^sup>*"
        by (rule Fun.hyps[OF nth_mem[OF i_ts] inherited])
      show ?thesis
        using True i_ts sub by simp
    next
      case False
      have delta: "funas_term (ts ! i) \<subseteq> \<Delta>"
      proof (cases "ts ! i")
        case (Var x)
        then show ?thesis by simp
      next
        case (Fun g us)
        have pos: "[i] \<in> fun_poss (Fun f ts)"
          using i_ts Fun by simp
        have not_mu: "[i] \<notin> mu_fun_poss \<mu> (Fun f ts)"
          using i_ts False by simp
        from Fun.prems[OF pos not_mu]
        show ?thesis
          using i_ts Fun by simp
      qed
      from i1_delta_subst[OF delta, of \<sigma>]
      show ?thesis
        using False i_ts by simp
    qed
  qed
  have base:
    "(Fun f ?ss, Fun f ?us) \<in> (csstep \<mu> (ce_trs cn))\<^sup>*"
    by (rule cssteps_FunI[OF len arg])
  have ss_comp:
    "map (i1 \<circ> (\<lambda>s. s \<cdot> \<sigma>)) ts = ?ss"
    by (rule map_cong, auto)
  have base_comp:
    "(Fun f (map (i1 \<circ> (\<lambda>s. s \<cdot> \<sigma>)) ts), Fun f ?us)
      \<in> (csstep \<mu> (ce_trs cn))\<^sup>*"
    by (subst ss_comp, rule base)
  show ?case
  proof (cases "(f, length ts) \<in> \<Delta> \<or>
      \<not> SN_on (csstep \<mu> (set Rs)) {Fun f (map (\<lambda>s. s \<cdot> \<sigma>) ts)}")
    case True
    then show ?thesis
      using base_comp by simp
  next
    case False
    let ?xs =
      "Fun f ?ss #
        map i1 (csrewrite \<mu> Rs (Fun f (map (\<lambda>s. s \<cdot> \<sigma>) ts)))"
    have member: "Fun f ?ss \<in> set ?xs"
      by simp
    from ce_trs_sound_csstep[OF member, where \<mu>=\<mu>]
    have project:
      "(comb cn ?xs, Fun f ?ss)
        \<in> (csstep \<mu> (ce_trs cn))\<^sup>+" .
    have first:
      "(comb cn ?xs, Fun f ?ss)
        \<in> (csstep \<mu> (ce_trs cn))\<^sup>*"
      by (rule trancl_into_rtrancl[OF project])
    have total:
      "(comb cn ?xs, Fun f ?us)
        \<in> (csstep \<mu> (ce_trs cn))\<^sup>*"
      by (rule rtrancl_trans[OF first base])
    have total_comp:
      "(comb cn
          (Fun f (map (i1 \<circ> (\<lambda>s. s \<cdot> \<sigma>)) ts) #
           map i1
             (csrewrite \<mu> Rs
               (Fun f (map (\<lambda>s. s \<cdot> \<sigma>) ts)))),
        Fun f ?us) \<in> (csstep \<mu> (ce_trs cn))\<^sup>*"
      by (subst ss_comp, rule total)
    show ?thesis
      using False total_comp by simp
  qed
qed

lemma i1_root_csstep:
  assumes SN: "SN_on (csstep \<mu> (set Rs)) {s}"
    and step: "(s, t) \<in> csrstep \<mu> (set Rs)"
  shows "(i1 s, i1 t)
    \<in> (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*"
proof -
  from step obtain l r \<sigma> where lr: "(l, r) \<in> set Rs"
    and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
    by (elim csrstepE)
  from wf lr obtain f ls where l: "l = Fun f ls"
    unfolding wf_trs_def by (cases l, auto)
  have root_l: "root l = Some (f, length ls)"
    unfolding l by simp
  have root_s: "root s = Some (f, length ls)"
    unfolding s l by simp
  show ?thesis
  proof (cases "(f, length ls) \<in> \<Delta>")
    case True
    from True have selected:
      "\<And>lr. lr \<in> set Rs \<Longrightarrow>
        root (fst lr) = Some (f, length ls) \<Longrightarrow> lr \<in> U"
      unfolding csr_u3_delta_def by auto
    have lrU: "(l, r) \<in> U"
      by (rule selected[OF lr], use root_l in simp)
    from closed have selected_closed:
      "\<And>lr. lr \<in> U \<Longrightarrow>
        csr_u3_root_rules_closed (set Rs) U (fst lr)
          {p\<in>fun_poss (fst lr). p \<notin> mu_fun_poss \<mu> (fst lr)} \<and>
        csr_u3_root_rules_closed (set Rs) U (snd lr)
          (fun_poss (snd lr))"
      unfolding csr_u3_usable_rules_closed_def by auto
    have lhs_closed:
      "csr_u3_root_rules_closed (set Rs) U l
        {p\<in>fun_poss l. p \<notin> mu_fun_poss \<mu> l}"
      using selected_closed[OF lrU] by simp
    have lhs_inactive:
      "\<And>p. p \<in> fun_poss l \<Longrightarrow>
        p \<notin> mu_fun_poss \<mu> l \<Longrightarrow>
        funas_term (l |_ p) \<subseteq> \<Delta>"
      by (rule csr_u3_closed_inactive_subterm_delta[OF lhs_closed])
    from i1_pattern_subst[OF lhs_inactive, of \<sigma>]
    have lhs_project:
      "(i1 (l \<cdot> \<sigma>), l \<cdot> i1_subst \<sigma>)
        \<in> (csstep \<mu> (ce_trs cn))\<^sup>*" .
    have C_subset:
      "csstep \<mu> (ce_trs cn) \<subseteq>
        csstep \<mu> (U \<union> ce_trs cn)"
      by (rule csstep_rules_mono, simp)
    have lhs_project':
      "(i1 (l \<cdot> \<sigma>), l \<cdot> i1_subst \<sigma>)
        \<in> (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*"
      by (rule subsetD[OF rtrancl_mono[OF C_subset] lhs_project])
    have root_U:
      "(l \<cdot> i1_subst \<sigma>, r \<cdot> i1_subst \<sigma>)
        \<in> csrstep \<mu> U"
      unfolding csrstep_iff_rstep_root rstep_r_p_s_def'
      using lrU by force
    have root_union:
      "(l \<cdot> i1_subst \<sigma>, r \<cdot> i1_subst \<sigma>)
        \<in> csstep \<mu> (U \<union> ce_trs cn)"
      using root_U csstep_rules_mono[of U "U \<union> ce_trs cn"]
      unfolding csstep_root_nonroot by auto
    have root_the:
      "the (root (fst (l, r))) \<in> \<Delta>"
      using True root_l by simp
    have root_some: "root (fst (l, r)) \<noteq> None"
      using root_l by simp
    have rhs_roots:
      "{g. \<exists>p\<in>fun_poss r. root (r |_ p) = Some g}
        \<subseteq> \<Delta>"
      by (rule csr_u3_closed_selected_rhs_delta[
          OF closed lr root_the root_some, simplified])
    have rhs_delta: "funas_term r \<subseteq> \<Delta>"
    proof
      fix g
      assume "g \<in> funas_term r"
      then obtain p h us where
        g: "g = (h, length us)"
        and p: "p \<in> poss r"
        and sub: "r |_ p = Fun h us"
        unfolding funas_term_poss_conv by blast
      have p_fun: "p \<in> fun_poss r"
        by (rule poss_is_Fun_fun_poss[OF p], use sub in simp)
      have "g \<in> {g. \<exists>p\<in>fun_poss r. root (r |_ p) = Some g}"
      proof
        show "\<exists>q\<in>fun_poss r. root (r |_ q) = Some g"
          by (rule bexI[of _ p], use g p_fun sub in simp_all)
      qed
      then show "g \<in> \<Delta>"
        by (rule subsetD[OF rhs_roots])
    qed
    from i1_delta_subst[OF rhs_delta, of \<sigma>]
    have rhs_I: "i1 (r \<cdot> \<sigma>) = r \<cdot> i1_subst \<sigma>" .
    from rtrancl_into_rtrancl[OF lhs_project' root_union]
    show ?thesis
      unfolding s t rhs_I .
  next
    case False
    have cs: "(s, t) \<in> csstep \<mu> (set Rs)"
      using step unfolding csstep_root_nonroot by auto
    from csrewrite_complete[OF wf cs]
    have member:
      "i1 t \<in>
        set (Fun f (map i1 (map (\<lambda>x. x \<cdot> \<sigma>) ls)) #
          map i1 (csrewrite \<mu> Rs s))"
      using s l t by simp
    from ce_trs_sound_csstep[OF member, where \<mu>=\<mu>]
    have project:
      "(comb cn
          (Fun f (map i1 (map (\<lambda>x. x \<cdot> \<sigma>) ls)) #
            map i1 (csrewrite \<mu> Rs s)),
        i1 t) \<in> (csstep \<mu> (ce_trs cn))\<^sup>+" .
    have source_I:
      "i1 s =
        comb cn
          (Fun f (map i1 (map (\<lambda>x. x \<cdot> \<sigma>) ls)) #
            map i1 (csrewrite \<mu> Rs s))"
      using False SN root_s s l by (simp add: comp_def)
    have C_subset:
      "csstep \<mu> (ce_trs cn) \<subseteq>
        csstep \<mu> (U \<union> ce_trs cn)"
      by (rule csstep_rules_mono, simp)
    have project':
      "(i1 s, i1 t) \<in>
        (csstep \<mu> (U \<union> ce_trs cn))\<^sup>+"
      unfolding source_I
      by (rule trancl_mono[OF project C_subset])
    show ?thesis
      by (rule trancl_into_rtrancl[OF project'])
  qed
qed

lemma i1_csstep:
  assumes SN: "SN_on (csstep \<mu> (set Rs)) {s}"
    and step: "(s, t) \<in> csstep \<mu> (set Rs)"
  shows "(i1 s, i1 t)
    \<in> (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*"
  using SN step
proof (induct s arbitrary: t)
  case (Var x)
  from csstep_Var_empty_wf[OF wf, of x t \<mu>] Var.prems(2)
  show ?case by contradiction
next
  case (Fun f ss)
  let ?A = "csstep \<mu> (U \<union> ce_trs cn)"
  show ?case
  proof (cases "(f, length ss) \<in> \<Delta>")
    case False
    from csrewrite_complete[OF wf Fun.prems(2)]
    have member:
      "i1 t \<in> set
        (Fun f (map i1 ss) #
          map i1 (csrewrite \<mu> Rs (Fun f ss)))"
      by simp
    from ce_trs_sound_csstep[OF member, where \<mu>=\<mu>]
    have project:
      "(comb cn
          (Fun f (map i1 ss) #
            map i1 (csrewrite \<mu> Rs (Fun f ss))),
        i1 t) \<in> (csstep \<mu> (ce_trs cn))\<^sup>+" .
    have source_I:
      "i1 (Fun f ss) =
        comb cn
          (Fun f (map i1 ss) #
            map i1 (csrewrite \<mu> Rs (Fun f ss)))"
      using False Fun.prems(1) by simp
    have subset:
      "csstep \<mu> (ce_trs cn) \<subseteq> ?A"
      by (rule csstep_rules_mono, simp)
    have "(i1 (Fun f ss), i1 t) \<in> ?A\<^sup>+"
      unfolding source_I
      by (rule trancl_mono[OF project subset])
    then show ?thesis
      by (rule trancl_into_rtrancl)
  next
    case True
    from Fun.prems(2) have cases:
      "(Fun f ss, t) \<in> csrstep \<mu> (set Rs) \<or>
       (Fun f ss, t) \<in> csnrstep \<mu> (set Rs)"
      unfolding csstep_root_nonroot by auto
    from cases show ?thesis
    proof
      assume root: "(Fun f ss, t) \<in> csrstep \<mu> (set Rs)"
      show ?thesis
        by (rule i1_root_csstep[OF Fun.prems(1) root])
    next
      assume nonroot: "(Fun f ss, t) \<in> csnrstep \<mu> (set Rs)"
      from nonroot obtain i ts where
        i: "i < length ss"
        and active: "i \<in> \<mu> (f, length ss)"
        and t: "t = Fun f ts"
        and len: "length ts = length ss"
        and substep: "(ss ! i, ts ! i) \<in> csstep \<mu> (set Rs)"
        and same: "\<And>j. j < length ss \<Longrightarrow> j \<noteq> i \<Longrightarrow>
          ts ! j = ss ! j"
        by (elim csnrstep_FunE, blast)
      have sub_fun: "\<exists>g us. ss ! i = Fun g us"
      proof (cases "ss ! i")
        case (Var x)
        from csstep_Var_empty_wf[OF wf, of x "ts ! i" \<mu>]
          substep[unfolded Var]
        show ?thesis by contradiction
      next
        case (Fun g us)
        then show ?thesis by blast
      qed
      have pos: "[i] \<in> mu_poss \<mu> (Fun f ss)"
        using i active sub_fun by auto
      from SN_on_mu_pos[OF wf pos Fun.prems(1)]
      have sub_SN: "SN_on (csstep \<mu> (set Rs)) {ss ! i}"
        using i by simp
      from Fun.hyps[OF nth_mem[OF i], of "ts ! i",
          OF sub_SN substep]
      have sub_I: "(i1 (ss ! i), i1 (ts ! i)) \<in> ?A\<^sup>*" .
      have ts_update: "ts = ss[i := ts ! i]"
      proof (rule nth_equalityI)
        show "length ts = length (ss[i := ts ! i])"
          using len by simp
        fix j
        assume j: "j < length ts"
        show "ts ! j = (ss[i := ts ! i]) ! j"
        proof (cases "j = i")
          case True
          with i show ?thesis by simp
        next
          case False
          from j len have "j < length ss" by simp
          from same[OF this False] False i show ?thesis by simp
        qed
      qed
      have i_map: "i < length (map i1 ss)"
        using i by simp
      have active_map: "i \<in> \<mu> (f, length (map i1 ss))"
        using active by simp
      have sub_map:
        "((map i1 ss) ! i, i1 (ts ! i)) \<in> ?A\<^sup>*"
        using sub_I i by simp
      have whole:
        "(Fun f (map i1 ss),
          Fun f ((map i1 ss)[i := i1 (ts ! i)])) \<in> ?A\<^sup>*"
        by (rule cssteps_Fun_updateI[OF i_map active_map sub_map])
      have target_delta: "(f, length ts) \<in> \<Delta>"
        using True len by simp
      have map_update:
        "map i1 ts = (map i1 ss)[i := i1 (ts ! i)]"
        apply (subst (1) ts_update)
        apply (rule nth_equalityI)
         apply simp
        using i
        apply (auto simp: nth_list_update)
        done
      show ?thesis
        using True target_delta whole t map_update by simp
    qed
  qed
qed

lemma i1_sharp_csdp_step:
  fixes shp :: "'f \<Rightarrow> 'f"
  assumes fresh: "\<And>g n. \<not> defined (set Rs) (shp g, n)"
    and marked_inj: "inj shp"
    and marked_mu:
      "\<mu> (f, length ss) \<subseteq> \<mu> (shp f, length ss)"
    and SN:
      "SN_on (csdp_step shp \<mu> (set Rs)) {Fun (shp f) ss}"
    and step:
      "(Fun (shp f) ss, t) \<in> csdp_step shp \<mu> (set Rs)"
  shows "(i1 (Fun (shp f) ss), i1 t)
    \<in> (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*"
proof -
  have step':
    "(sharp_term shp (Fun f ss), t)
      \<in> csdp_step shp \<mu> (set Rs)"
    using step by simp
  have converted:
    "\<exists>u. t = sharp_term shp u \<and>
      (Fun f ss, u) \<in> csnrstep \<mu> (set Rs)"
    apply (rule sharp_csdp_step_imp_csnrstep)
      apply (rule wf)
     apply (rule fresh)
    apply (rule marked_inj)
    apply (rule step')
    done
  from converted
  obtain u where t0: "t = sharp_term shp u"
    and nonroot: "(Fun f ss, u) \<in> csnrstep \<mu> (set Rs)"
    by blast
  from nonroot obtain i us where
    i: "i < length ss"
    and active: "i \<in> \<mu> (f, length ss)"
    and u: "u = Fun f us"
    and len: "length us = length ss"
    and substep: "(ss ! i, us ! i) \<in> csstep \<mu> (set Rs)"
    and same: "\<And>j. j < length ss \<Longrightarrow> j \<noteq> i \<Longrightarrow>
      us ! j = ss ! j"
    by (elim csnrstep_FunE, blast)
  have t: "t = Fun (shp f) us"
    using t0 u by simp
  from SN_sharp_csdp_imp_SN_active_arg[OF i active SN]
  have sub_SN: "SN_on (csstep \<mu> (set Rs)) {ss ! i}" .
  from i1_csstep[OF sub_SN substep]
  have sub_I:
    "(i1 (ss ! i), i1 (us ! i))
      \<in> (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*" .
  have sharp_delta: "(shp f, length ss) \<in> \<Delta>"
  proof (unfold csr_u3_delta_def, intro CollectI ballI impI)
    fix lr
    assume mem: "lr \<in> set Rs"
      and root: "root (fst lr) = Some (shp f, length ss)"
    from mem root have "defined (set Rs) (shp f, length ss)"
      unfolding defined_def
      by (intro exI[of _ "fst lr"] exI[of _ "snd lr"], simp)
    with fresh[of f "length ss"] show "lr \<in> U"
      by contradiction
  qed
  have target_delta: "(shp f, length us) \<in> \<Delta>"
    using sharp_delta len by simp
  have us_update: "us = ss[i := us ! i]"
  proof (rule nth_equalityI)
    show "length us = length (ss[i := us ! i])"
      using len by simp
    fix j
    assume j: "j < length us"
    show "us ! j = (ss[i := us ! i]) ! j"
    proof (cases "j = i")
      case True
      with i show ?thesis by simp
    next
      case False
      from j len have "j < length ss" by simp
      from same[OF this False] False i show ?thesis by simp
    qed
  qed
  have sub_map:
    "((map i1 ss) ! i, i1 (us ! i))
      \<in> (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*"
    using sub_I i by simp
  have marked_active: "i \<in> \<mu> (shp f, length (map i1 ss))"
    using active marked_mu by auto
  have whole:
    "(Fun (shp f) (map i1 ss),
      Fun (shp f) ((map i1 ss)[i := i1 (us ! i)]))
      \<in> (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*"
    by (rule cssteps_Fun_updateI,
      use i marked_active sub_map in simp_all)
  have map_update:
    "map i1 us = (map i1 ss)[i := i1 (us ! i)]"
    apply (subst (1) us_update)
    apply (rule nth_equalityI)
     apply simp
    using i
    apply (auto simp: nth_list_update)
    done
  show ?thesis
    using sharp_delta target_delta whole t map_update by simp
qed

end

lemma mu_supt_subst:
  assumes "mu_supt \<mu> s t"
  shows "mu_supt \<mu> (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)"
proof -
  from assms obtain i p where pos: "i # p \<in> mu_poss \<mu> s"
    and sub: "s |_ (i # p) = t"
    unfolding mu_supt_def by auto
  have pos': "i # p \<in> mu_poss \<mu> (s \<cdot> \<sigma>)"
    by (rule mu_poss_subst_lift[OF pos])
  have "(s \<cdot> \<sigma>) |_ (i # p) = t \<cdot> \<sigma>"
    using mu_poss_imp_poss[OF pos] sub by simp
  with pos' show ?thesis
    unfolding mu_supt_def by blast
qed

lemma csr_sct_with_active_subterm:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f, n)"
    and pair: "\<And>k. (s k, t k) \<in> P"
    and pair_shape: "\<forall>(u, v)\<in>P.
      (\<exists>f us. u = Fun (Sharp f) us) \<and>
      (\<exists>g vs. v = Fun (Sharp g) vs)"
    and target_SN: "\<And>k. SN_on (csdp_step Sharp \<mu> R) {t k \<cdot> \<sigma> k}"
    and steps: "\<And>k. (t k \<cdot> \<sigma> k, s (Suc k) \<cdot> \<sigma> (Suc k)) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>*"
    and graphs: "\<forall>(u, v)\<in>P. \<exists>stri nstri.
      Scg (info (u, v)) (info (u, v))
        (remdups_sort stri) (remdups_sort nstri) \<in> set Gs \<and>
      (\<forall>(i, j)\<in>set stri.
        csr_sct_active_index \<mu> u i \<and>
        csr_sct_index v j \<and>
        mu_supt \<mu> (get_arg u i) (get_arg v j)) \<and>
      (\<forall>(i, j)\<in>set nstri.
        csr_sct_index u i \<and> csr_sct_index v j \<and>
        (get_arg u i = get_arg v j \<or>
          (csr_sct_active_index \<mu> u i \<and>
            mu_supt \<mu> (get_arg u i) (get_arg v j))))"
    and edge: "\<And>k. edg (info (s k, t k)) (info (s (Suc k), t (Suc k)))"
    and check: "check_SCT edg Gs"
  shows False
proof -
  let ?entry = "\<lambda>k. info (s (Suc k), t (Suc k))"
  let ?ss = "\<lambda>k. s (Suc k)"
  let ?tt = "\<lambda>k. t (Suc k)"
  let ?subst = "\<lambda>k. \<sigma> (Suc k)"
  let ?step = "csstep \<mu> R"
  let ?msupt = "mu_supt_rel \<mu>"
  let ?supt = "restrict_SN ((?msupt \<union> ?step)\<^sup>+) ?step"
  let ?supteq = "restrict_SN (?step\<^sup>*) ?step \<union> Id"
  let ?vals = "\<lambda>k. (?entry k,
    (\<lambda>j. get_arg (?ss k) j \<cdot> ?subst k))"
  let ?rel = "{(?vals k, ?vals (Suc k)) | k. True}"
  let ?strict = "(?supteq \<union> ?supt)\<^sup>* O ?supt O
    (?supteq \<union> ?supt)\<^sup>*"
  let ?nonstrict = "(?supteq \<union> ?supt)\<^sup>*"
  have semantics: "sct_semantics ?supt ?supteq"
  proof
    show "SN ?supt"
    proof -
      have "\<forall>u. SN_on ?supt {u}"
      proof (rule ccontr)
        assume "\<not> (\<forall>u. SN_on ?supt {u})"
        then obtain u where not_sn: "\<not> SN_on ?supt {u}"
          by auto
        then obtain us where init: "us 0 = u"
          and chain: "\<forall>i. (us i, us (Suc i)) \<in> ?supt"
          unfolding SN_defs by auto
        from chain have all_sn: "\<forall>i. SN_on ?step {us i}"
          unfolding restrict_SN_def by auto
        from all_sn have "SN_on ?step {us 0}" by simp
        then have "SN_on (?msupt \<union> ?step) {u}"
          unfolding init by (rule SN_on_csstep_imp_SN_on_mu_supt_union[OF wf])
        then have "SN_on ((?msupt \<union> ?step)\<^sup>+) {u}"
          by (rule SN_on_trancl)
        moreover have "?supt \<subseteq> (?msupt \<union> ?step)\<^sup>+"
          by (rule restrict_SN_subset)
        ultimately have "SN_on ?supt {u}"
          by (rule SN_on_subset1)
        with not_sn show False by contradiction
      qed
      then show ?thesis
        unfolding SN_defs by simp
    qed
  next
    show "?supteq O ?supt \<subseteq> ?supt"
    proof (rule subrelI)
      fix u w
      assume "(u, w) \<in> ?supteq O ?supt"
      then obtain v where uv: "(u, v) \<in> ?supteq"
        and vw: "(v, w) \<in> ?supt"
        by auto
      show "(u, w) \<in> ?supt"
      proof (cases "(u, v) \<in> Id")
        case True
        with vw show ?thesis by simp
      next
        case False
        with uv have uv': "(u, v) \<in> restrict_SN (?step\<^sup>*) ?step"
          by auto
        from uv' have uv_steps: "(u, v) \<in> ?step\<^sup>*"
          and sn_u: "SN_on ?step {u}"
          unfolding restrict_SN_def by auto
        from vw have vw_steps: "(v, w) \<in> (?msupt \<union> ?step)\<^sup>+"
          unfolding restrict_SN_def by auto
        show "(u, w) \<in> ?supt"
          using uv_steps sn_u vw_steps
        proof (induct)
          case base
          then show ?case
            unfolding restrict_SN_def by simp
        next
          case (step x y)
          from step.hyps(2) have xy:
            "(x, y) \<in> (?msupt \<union> ?step)\<^sup>+"
            by auto
          from xy step.prems(2) have xw:
            "(x, w) \<in> (?msupt \<union> ?step)\<^sup>+"
            by simp
          from step.hyps(1) have ux:
            "(u, x) \<in> (?msupt \<union> ?step)\<^sup>*"
            using rtrancl_mono[of ?step "?msupt \<union> ?step"]
            by auto
          have "(u, w) \<in> (?msupt \<union> ?step)\<^sup>+"
            by (rule rtrancl_trancl_trancl[OF ux xw])
          with step.prems(1) show ?case
            unfolding restrict_SN_def by simp
        qed
      qed
    qed
  qed
  {
    fix k
    have inP: "(?ss k, ?tt k) \<in> P"
      using pair[of "Suc k"] by simp
    have inP_next: "(?ss (Suc k), ?tt (Suc k)) \<in> P"
      using pair[of "Suc (Suc k)"] by simp
    from graphs inP obtain stri nstri where graph:
      "Scg (?entry k) (?entry k)
        (remdups_sort stri) (remdups_sort nstri) \<in> set Gs"
      and strict_edges:
        "\<forall>(i, j)\<in>set stri.
          csr_sct_active_index \<mu> (?ss k) i \<and>
          csr_sct_index (?tt k) j \<and>
          mu_supt \<mu> (get_arg (?ss k) i) (get_arg (?tt k) j)"
      and nonstrict_edges:
        "\<forall>(i, j)\<in>set nstri.
          csr_sct_index (?ss k) i \<and>
          csr_sct_index (?tt k) j \<and>
          (get_arg (?ss k) i = get_arg (?tt k) j \<or>
            (csr_sct_active_index \<mu> (?ss k) i \<and>
              mu_supt \<mu> (get_arg (?ss k) i) (get_arg (?tt k) j)))"
      by auto
    have whole_source_SN:
      "SN_on (csdp_step Sharp \<mu> R) {?ss k \<cdot> ?subst k}"
    proof -
      have prev:
        "(t k \<cdot> \<sigma> k, ?ss k \<cdot> ?subst k) \<in>
          (csdp_step Sharp \<mu> R)\<^sup>*"
        using steps[of k] by simp
      show ?thesis
        by (rule steps_preserve_SN_on[OF prev target_SN[of k]])
    qed
    have between:
      "(?tt k \<cdot> ?subst k, ?ss (Suc k) \<cdot> ?subst (Suc k)) \<in>
        (csdp_step Sharp \<mu> R)\<^sup>*"
      using steps[of "Suc k"] by simp
    let ?g = "Scg (?entry k) (?entry k)
      (remdups_sort stri) (remdups_sort nstri)"
    let ?holds = "\<lambda>g. ((?entry k,
      (\<lambda>j. get_arg (?ss k) j \<cdot> ?subst k)),
      (?entry (Suc k),
      (\<lambda>j. get_arg (?ss (Suc k)) j \<cdot> ?subst (Suc k))))
      \<in> sct_semantics.steps ?supt ?supteq edg g"
    have holds_g: "?holds ?g"
    proof (simp add: sct_semantics.steps.simps semantics
        edge[of "Suc k"], intro conjI)
      show "\<forall>ij\<in>set nstri.
        (case ij of (i, j) \<Rightarrow>
          (get_arg (?ss k) i \<cdot> ?subst k,
           get_arg (?ss (Suc k)) j \<cdot> ?subst (Suc k))
          \<in> ?nonstrict)"
      proof clarify
        fix i j
        assume ij: "(i, j) \<in> set nstri"
        from nonstrict_edges ij have index_i:
          "csr_sct_index (?ss k) i"
          and index_j: "csr_sct_index (?tt k) j"
          and sub: "get_arg (?ss k) i = get_arg (?tt k) j \<or>
            (csr_sct_active_index \<mu> (?ss k) i \<and>
              mu_supt \<mu> (get_arg (?ss k) i) (get_arg (?tt k) j))"
          by auto
        from pair_shape inP_next have shape_next:
          "\<exists>f us. ?ss (Suc k) = Fun (Sharp f) us"
          by auto
        have index_j_next: "csr_sct_index (?ss (Suc k)) j"
          by (rule csr_sct_index_steps[
            OF wf fresh index_j shape_next between])
        have arg_steps_ns:
          "(get_arg (?tt k) j \<cdot> ?subst k,
            get_arg (?ss (Suc k)) j \<cdot> ?subst (Suc k))
            \<in> ?supteq"
          by (rule csr_sct_get_arg_transition[
            OF wf fresh index_j index_j_next
              target_SN[of "Suc k", simplified] between])
        have first:
          "(get_arg (?ss k) i \<cdot> ?subst k,
            get_arg (?tt k) j \<cdot> ?subst k) \<in> ?supteq \<union> ?supt"
        using sub
        proof
          assume 1:
            "get_arg (?ss k) i = get_arg (?tt k) j"
          then show ?thesis
            by auto
        next
          assume 2:
            "csr_sct_active_index \<mu> (?ss k) i \<and>
              mu_supt \<mu> (get_arg (?ss k) i) (get_arg (?tt k) j)"
          from 2 have source_arg_SN:
            "SN_on ?step {get_arg (?ss k) i \<cdot> ?subst k}"
            by (intro csr_sct_active_index_subst_SN[OF _ whole_source_SN],
              auto)
          from 2 have sub_inst:
            "mu_supt \<mu> (get_arg (?ss k) i \<cdot> ?subst k)
              (get_arg (?tt k) j \<cdot> ?subst k)"
            by (auto intro: mu_supt_subst)
          have "(get_arg (?ss k) i \<cdot> ?subst k,
              get_arg (?tt k) j \<cdot> ?subst k) \<in>
              (?msupt \<union> ?step)\<^sup>+"
            using sub_inst unfolding mu_supt_rel_def by auto
          with source_arg_SN show ?thesis
            unfolding restrict_SN_def by auto
        qed
        have total:
          "(get_arg (?ss k) i \<cdot> ?subst k,
            get_arg (?ss (Suc k)) j \<cdot> ?subst (Suc k))
            \<in> ?nonstrict"
        proof -
          have first': "(get_arg (?ss k) i \<cdot> ?subst k,
              get_arg (?tt k) j \<cdot> ?subst k) \<in> ?nonstrict"
            using first by auto
          have second': "(get_arg (?tt k) j \<cdot> ?subst k,
              get_arg (?ss (Suc k)) j \<cdot> ?subst (Suc k))
              \<in> ?nonstrict"
            using arg_steps_ns by auto
          show ?thesis
            by (rule rtrancl_trans[OF first' second'])
        qed
        show "(get_arg (?ss k) i \<cdot> ?subst k,
          get_arg (?ss (Suc k)) j \<cdot> ?subst (Suc k))
          \<in> ?nonstrict"
          by (rule total)
      qed
    next
      show "\<forall>ij\<in>set stri.
        (case ij of (i, j) \<Rightarrow>
          (get_arg (?ss k) i \<cdot> ?subst k,
           get_arg (?ss (Suc k)) j \<cdot> ?subst (Suc k))
          \<in> ?strict)"
      proof clarify
        fix i j
        assume ij: "(i, j) \<in> set stri"
        from strict_edges ij have active_i:
          "csr_sct_active_index \<mu> (?ss k) i"
          and index_j: "csr_sct_index (?tt k) j"
          and sub: "mu_supt \<mu>
            (get_arg (?ss k) i) (get_arg (?tt k) j)"
          by auto
        from pair_shape inP_next have shape_next:
          "\<exists>f us. ?ss (Suc k) = Fun (Sharp f) us"
          by auto
        have index_j_next: "csr_sct_index (?ss (Suc k)) j"
          by (rule csr_sct_index_steps[
            OF wf fresh index_j shape_next between])
        have arg_steps_ns:
          "(get_arg (?tt k) j \<cdot> ?subst k,
            get_arg (?ss (Suc k)) j \<cdot> ?subst (Suc k))
            \<in> ?supteq"
          by (rule csr_sct_get_arg_transition[
            OF wf fresh index_j index_j_next
              target_SN[of "Suc k", simplified] between])
        have source_arg_SN:
          "SN_on ?step {get_arg (?ss k) i \<cdot> ?subst k}"
          by (rule csr_sct_active_index_subst_SN[
            OF active_i whole_source_SN])
        have sub_inst:
          "mu_supt \<mu> (get_arg (?ss k) i \<cdot> ?subst k)
            (get_arg (?tt k) j \<cdot> ?subst k)"
          by (rule mu_supt_subst[OF sub])
        have first:
          "(get_arg (?ss k) i \<cdot> ?subst k,
            get_arg (?tt k) j \<cdot> ?subst k) \<in> ?supt"
        proof -
          have edge:
            "(get_arg (?ss k) i \<cdot> ?subst k,
              get_arg (?tt k) j \<cdot> ?subst k) \<in>
              (?msupt \<union> ?step)\<^sup>+"
            using sub_inst unfolding mu_supt_rel_def by auto
          show ?thesis
            using edge source_arg_SN unfolding restrict_SN_def by auto
        qed
        have total:
          "(get_arg (?ss k) i \<cdot> ?subst k,
            get_arg (?ss (Suc k)) j \<cdot> ?subst (Suc k))
            \<in> ?strict"
        proof -
          have refl:
            "(get_arg (?ss k) i \<cdot> ?subst k,
              get_arg (?ss k) i \<cdot> ?subst k) \<in> ?nonstrict"
            by simp
          have right:
            "(get_arg (?tt k) j \<cdot> ?subst k,
              get_arg (?ss (Suc k)) j \<cdot> ?subst (Suc k))
              \<in> ?nonstrict"
            by (rule r_into_rtrancl, rule UnI1, rule arg_steps_ns)
          have tail:
            "(get_arg (?ss k) i \<cdot> ?subst k,
              get_arg (?ss (Suc k)) j \<cdot> ?subst (Suc k))
              \<in> ?supt O ?nonstrict"
            by (rule relcompI[OF first right])
          show ?thesis
            by (rule relcompI[OF refl tail])
        qed
        show "(get_arg (?ss k) i \<cdot> ?subst k,
          get_arg (?ss (Suc k)) j \<cdot> ?subst (Suc k))
          \<in> ?strict"
          by (rule total)
      qed
    qed
    have "\<exists>g\<in>set Gs. ?holds g"
    proof (rule bexI[where x = ?g])
      show "?holds ?g" by (rule holds_g)
      show "?g \<in> set Gs" by (rule graph)
    qed
  } note holds = this
  have subset:
    "?rel \<subseteq> (\<Union>G\<in>set Gs.
      sct_semantics.steps ?supt ?supteq edg G)"
  proof
    fix x
    assume x_mem: "x \<in> ?rel"
    have "\<exists>k. x = (?vals k, ?vals (Suc k))"
      using x_mem by simp
    then obtain k where x:
      "x = (?vals k, ?vals (Suc k))"
      by (rule exE)
    from holds[of k] obtain g where g: "g \<in> set Gs"
      and step:
        "(?vals k, ?vals (Suc k)) \<in>
          sct_semantics.steps ?supt ?supteq edg g"
      by (rule bexE)
    have x_step:
      "x \<in> sct_semantics.steps ?supt ?supteq edg g"
      using x step by simp
    show "x \<in> (\<Union>G\<in>set Gs.
      sct_semantics.steps ?supt ?supteq edg G)"
    proof (rule UN_I[where a = g])
      show "g \<in> set Gs" by (rule g)
      show "x \<in> sct_semantics.steps ?supt ?supteq edg g"
        by (rule x_step)
    qed
  qed
  have "SN ?rel"
    by (rule sct_semantics.SCT_correctness2[
      where S = ?supt and NS = ?supteq],
      rule semantics, rule subset, rule check)
  have infinite: "chain ?rel ?vals"
  proof
    fix i
    show "(?vals i, ?vals (Suc i)) \<in> ?rel"
      by (rule CollectI, rule exI[where x = i], simp)
  qed
  have witness:
    "\<exists>f. f 0 \<in> UNIV \<and> chain ?rel f"
  proof (rule exI[where x = ?vals], intro conjI)
    show "?vals 0 \<in> UNIV" by simp
    show "chain ?rel ?vals" by (rule infinite)
  qed
  have "\<not> SN ?rel"
    unfolding SN_on_def
    using witness by simp
  then show False using \<open>SN ?rel\<close> by contradiction
qed

lemma not_finite_min_csr_dpp_obtain_chain:
  assumes not_fin: "\<not> finite_min_csr_dpp Sharp \<mu> P R"
  shows "\<exists>s t \<sigma>.
    (\<forall>k. (s k, t k) \<in> P) \<and>
    (\<forall>k. SN_on (csdp_step Sharp \<mu> R) {t k \<cdot> \<sigma> k}) \<and>
    (\<forall>k. (t k \<cdot> \<sigma> k, s (Suc k) \<cdot> \<sigma> (Suc k)) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>*)"
proof -
  let ?S = "csdp_step Sharp \<mu> R"
  let ?M = "csr_min_pair_step Sharp \<mu> P R"
  from not_fin obtain f where chain:
    "\<And>k. (f k, f (Suc k)) \<in> ?S\<^sup>* O ?M O ?S\<^sup>*"
    unfolding finite_min_csr_dpp_def SN_rel_on_def SN_on_def
    by auto
  have witnesses:
    "\<forall>k. \<exists>l r \<tau>.
      (l, r) \<in> P \<and>
      SN_on ?S {r \<cdot> \<tau>} \<and>
      (f k, l \<cdot> \<tau>) \<in> ?S\<^sup>* \<and>
      (r \<cdot> \<tau>, f (Suc k)) \<in> ?S\<^sup>*"
  proof
    fix k
    from chain[of k] obtain a b where
      prefix: "(f k, a) \<in> ?S\<^sup>*"
      and pair: "(a, b) \<in> ?M"
      and suffix: "(b, f (Suc k)) \<in> ?S\<^sup>*"
      by auto
    from pair have rr: "(a, b) \<in> rrstep P"
      and min: "SN_on ?S {b}"
      unfolding csr_min_pair_step_def by auto
    from rr obtain l r \<tau> where lr: "(l, r) \<in> P"
      and a: "a = l \<cdot> \<tau>" and b: "b = r \<cdot> \<tau>"
      unfolding rrstep_def' by auto
    show "\<exists>l r \<tau>.
      (l, r) \<in> P \<and>
      SN_on ?S {r \<cdot> \<tau>} \<and>
      (f k, l \<cdot> \<tau>) \<in> ?S\<^sup>* \<and>
      (r \<cdot> \<tau>, f (Suc k)) \<in> ?S\<^sup>*"
      by (intro exI[of _ l] exI[of _ r] exI[of _ \<tau>],
        use lr min prefix suffix a b in auto)
  qed
  from choice[OF witnesses]
  obtain s where s:
    "\<forall>k. \<exists>r \<tau>.
      (s k, r) \<in> P \<and>
      SN_on ?S {r \<cdot> \<tau>} \<and>
      (f k, s k \<cdot> \<tau>) \<in> ?S\<^sup>* \<and>
      (r \<cdot> \<tau>, f (Suc k)) \<in> ?S\<^sup>*"
    by auto
  from choice[OF s]
  obtain t where t:
    "\<forall>k. \<exists>\<tau>.
      (s k, t k) \<in> P \<and>
      SN_on ?S {t k \<cdot> \<tau>} \<and>
      (f k, s k \<cdot> \<tau>) \<in> ?S\<^sup>* \<and>
      (t k \<cdot> \<tau>, f (Suc k)) \<in> ?S\<^sup>*"
    by auto
  from choice[OF t]
  obtain \<sigma> where data:
    "\<And>k. (s k, t k) \<in> P"
    "\<And>k. SN_on ?S {t k \<cdot> \<sigma> k}"
    "\<And>k. (f k, s k \<cdot> \<sigma> k) \<in> ?S\<^sup>*"
    "\<And>k. (t k \<cdot> \<sigma> k, f (Suc k)) \<in> ?S\<^sup>*"
    by auto
  have between:
    "(t k \<cdot> \<sigma> k, s (Suc k) \<cdot> \<sigma> (Suc k)) \<in> ?S\<^sup>*"
    for k
    by (rule rtrancl_trans[OF data(4) data(3)])
  show ?thesis
    by (intro exI[of _ s] exI[of _ t] exI[of _ \<sigma>] conjI allI,
      rule data(1), rule data(2), rule between)
qed

lemma csr_u3_interpretation_steps:
  assumes refl: "refl NS"
    and trans: "trans NS"
    and step_I:
      "\<And>x y. SN_on (csdp_step Sharp \<mu> R) {x} \<Longrightarrow>
        (x, y) \<in> csdp_step Sharp \<mu> R \<Longrightarrow>
        (I x, I y) \<in> NS"
    and SN: "SN_on (csdp_step Sharp \<mu> R) {x}"
    and steps: "(x, y) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "(I x, I y) \<in> NS"
  using steps SN
proof (induct rule: rtrancl_induct)
  case base
  show ?case using refl unfolding refl_on_def by auto
next
  case (step y z)
  from step.hyps(1) step.prems have SN_y:
    "SN_on (csdp_step Sharp \<mu> R) {y}"
    by (rule steps_preserve_SN_on)
  have "(I x, I y) \<in> NS"
    by (rule step.hyps(3)[OF step.prems])
  moreover have "(I y, I z) \<in> NS"
    by (rule step_I[OF SN_y step.hyps(2)])
  ultimately show ?case
    using trans unfolding trans_def by blast
qed

lemma csr_u3_interpretation_steps_marked:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f, n)"
    and refl: "refl NS"
    and trans: "trans NS"
    and step_I:
      "\<And>f ts y. SN_on (csdp_step Sharp \<mu> R) {Fun (Sharp f) ts} \<Longrightarrow>
        (Fun (Sharp f) ts, y) \<in> csdp_step Sharp \<mu> R \<Longrightarrow>
        (I (Fun (Sharp f) ts), I y) \<in> NS"
    and shape: "\<exists>f ts. x = Fun (Sharp f) ts"
    and SN: "SN_on (csdp_step Sharp \<mu> R) {x}"
    and steps: "(x, y) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "(I x, I y) \<in> NS \<and> (\<exists>f ts. y = Fun (Sharp f) ts)"
  using steps SN shape
proof (induct rule: rtrancl_induct)
  case base
  have "(I x, I x) \<in> NS"
    using refl unfolding refl_on_def by auto
  then show ?case
    using base.prems by blast
next
  case (step y z)
  from step.hyps(1) step.prems(1)
  have SN_y: "SN_on (csdp_step Sharp \<mu> R) {y}"
    by (rule steps_preserve_SN_on)
  from step.hyps(3)[OF step.prems]
  have prefix: "(I x, I y) \<in> NS"
    and y_shape: "\<exists>f ts. y = Fun (Sharp f) ts"
    by auto
  then obtain f ts where y: "y = Fun (Sharp f) ts"
    by blast
  have last: "(I y, I z) \<in> NS"
    unfolding y
    by (rule step_I[OF SN_y[unfolded y] step.hyps(2)[unfolded y]])
  have last_step:
    "(sharp_term Sharp (Fun f ts), z) \<in> csdp_step Sharp \<mu> R"
    using step.hyps(2) unfolding y by simp
  have converted:
    "\<exists>u. z = sharp_term Sharp u \<and>
      (Fun f ts, u) \<in> csnrstep \<mu> R"
    apply (rule sharp_csdp_step_imp_csnrstep)
       apply (rule wf)
      apply (rule fresh)
     apply (rule inj_Sharp)
    apply (rule last_step)
    done
  from converted
  obtain u where z: "z = sharp_term Sharp u"
    and nr: "(Fun f ts, u) \<in> csnrstep \<mu> R"
    by auto
  from nr obtain us where u: "u = Fun f us"
    by (elim csnrstep_FunE, blast)
  have z_shape: "\<exists>g vs. z = Fun (Sharp g) vs"
    using z u by auto
  have "(I x, I z) \<in> NS"
    using prefix last trans unfolding trans_def by blast
  then show ?case
    using z_shape by blast
qed

lemma csr_u3_unhiding_csdp_step_empty:
  fixes U :: "(('f::{showl, compare_order}, 'l::{showl, compare_order}) lab)"
  assumes wf: "wf_trs R"
    and fresh: "\<And>n. \<not> defined R (U, n)"
    and unsharp: "\<not> is_sharp_lab U"
  shows "(Fun U ts, y) \<notin> csdp_step Sharp \<mu> R"
proof
  assume step: "(Fun U ts, y) \<in> csdp_step Sharp \<mu> R"
  then obtain p lr \<sigma> where
    rewrite: "(Fun U ts, y) \<in> rstep_r_p_s R lr p \<sigma>"
    and cond: "csdp_step_cond Sharp \<mu> p (Fun U ts)"
    unfolding csdp_step_def csdp_step_p_def by auto
  show False
  proof (cases p)
    case Nil
    from rewrite Nil have lr: "lr \<in> R"
      and lhs: "fst lr \<cdot> \<sigma> = Fun U ts"
      unfolding rstep_r_p_s_def' by auto
    from wf lr have "\<exists>f ss. fst lr = Fun f ss"
      unfolding wf_trs_def by (cases lr, auto)
    then obtain f ss where l: "fst lr = Fun f ss"
      by blast
    from lhs l have f: "f = U" and len: "length ss = length ts"
      by auto
    from lr l f len have "defined R (U, length ts)"
      unfolding defined_def by (cases lr, auto)
    with fresh show False by contradiction
  next
    case (Cons i q)
    from rewrite Cons have pos: "i # q \<in> poss (Fun U ts)"
      unfolding rstep_r_p_s_def' by auto
    from cond[unfolded csdp_step_cond_def, rule_format,
        of "[]" i q] Cons pos
    obtain f where "U = Sharp f"
      by auto
    with unsharp show False by simp
  qed
qed

lemma csr_u3_unhiding_csdp_steps_identity:
  fixes U :: "(('f::{showl, compare_order}, 'l::{showl, compare_order}) lab)"
  assumes wf: "wf_trs R"
    and fresh: "\<And>n. \<not> defined R (U, n)"
    and unsharp: "\<not> is_sharp_lab U"
    and steps: "(Fun U ts, y) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "y = Fun U ts"
  using steps
proof (induct rule: rtrancl_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  from step.hyps(3) have "y = Fun U ts" .
  from csr_u3_unhiding_csdp_step_empty[
      OF wf fresh unsharp, of ts z]
    step.hyps(2)[unfolded this]
  show ?case by contradiction
qed

definition csr_u3_mixed_term_shape where
  "csr_u3_mixed_term_shape U t \<longleftrightarrow>
    (\<exists>f ts. t = Fun (Sharp f) ts) \<or> (\<exists>ts. t = Fun U ts)"

lemma csr_u3_mixed_term_shape_subst:
  assumes "csr_u3_mixed_term_shape U t"
  shows "csr_u3_mixed_term_shape U (t \<cdot> \<sigma>)"
  using assms unfolding csr_u3_mixed_term_shape_def by auto

lemma csr_u3_interpretation_steps_mixed:
  fixes U :: "(('f::{showl, compare_order}, 'l::{showl, compare_order}) lab)"
  assumes wf: "wf_trs R"
    and fresh_sharp: "\<And>f n. \<not> defined R (Sharp f, n)"
    and fresh_U: "\<And>n. \<not> defined R (U, n)"
    and unsharp: "\<not> is_sharp_lab U"
    and refl: "refl NS"
    and trans: "trans NS"
    and step_I:
      "\<And>f ts y. SN_on (csdp_step Sharp \<mu> R) {Fun (Sharp f) ts} \<Longrightarrow>
        (Fun (Sharp f) ts, y) \<in> csdp_step Sharp \<mu> R \<Longrightarrow>
        (I (Fun (Sharp f) ts), I y) \<in> NS"
    and shape: "csr_u3_mixed_term_shape U x"
    and SN: "SN_on (csdp_step Sharp \<mu> R) {x}"
    and steps: "(x, y) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "(I x, I y) \<in> NS \<and> csr_u3_mixed_term_shape U y"
proof -
  consider (marked) f ts where "x = Fun (Sharp f) ts"
    | (hidden) ts where "x = Fun U ts"
    using shape unfolding csr_u3_mixed_term_shape_def by blast
  then show ?thesis
  proof cases
    case (marked f ts)
    have marked_shape: "\<exists>g us. x = Fun (Sharp g) us"
      using marked by blast
    from csr_u3_interpretation_steps_marked[
        where R=R and \<mu>=\<mu> and NS=NS and I=I and x=x and y=y,
        OF wf fresh_sharp refl trans step_I marked_shape SN steps]
    have sim: "(I x, I y) \<in> NS"
      and y_marked: "\<exists>f ts. y = Fun (Sharp f) ts"
      by auto
    show ?thesis
      using sim y_marked by (simp add: csr_u3_mixed_term_shape_def)
  next
    case (hidden ts)
    from csr_u3_unhiding_csdp_steps_identity[
        OF wf fresh_U unsharp steps[unfolded hidden]]
    have y: "y = Fun U ts" .
    have "(I x, I y) \<in> NS"
      unfolding hidden y using refl unfolding refl_on_def by auto
    moreover have "(\<exists>f us. y = Fun (Sharp f) us) \<or> (\<exists>us. y = Fun U us)"
      unfolding y by blast
    ultimately show ?thesis
      unfolding csr_u3_mixed_term_shape_def by blast
  qed
qed

lemma csr_u3_chain_simulation_from_interpretation:
  assumes refl: "refl NS"
    and trans: "trans NS"
    and pair: "\<And>k. (s k, t k) \<in> P"
    and target_SN:
      "\<And>k. SN_on (csdp_step Sharp \<mu> R) {t k \<cdot> \<sigma> k}"
    and steps:
      "\<And>k. (t k \<cdot> \<sigma> k, s (Suc k) \<cdot> \<sigma> (Suc k)) \<in>
        (csdp_step Sharp \<mu> R)\<^sup>*"
    and rhs_I:
      "\<And>dp \<rho>. dp \<in> P \<Longrightarrow>
        I (snd dp \<cdot> \<rho>) = snd dp \<cdot> (\<lambda>x. I (\<rho> x))"
    and lhs_I:
      "\<And>dp \<rho>. dp \<in> P \<Longrightarrow>
        (I (fst dp \<cdot> \<rho>),
          fst dp \<cdot> (\<lambda>x. I (\<rho> x))) \<in> NS"
    and step_I:
      "\<And>x y. SN_on (csdp_step Sharp \<mu> R) {x} \<Longrightarrow>
        (x, y) \<in> csdp_step Sharp \<mu> R \<Longrightarrow>
        (I x, I y) \<in> NS"
  shows "\<exists>\<tau>. \<forall>k.
    (t k \<cdot> \<tau> k, s (Suc k) \<cdot> \<tau> (Suc k)) \<in> NS"
proof -
  let ?\<tau> = "\<lambda>k x. I (\<sigma> k x)"
  have rhs:
    "t k \<cdot> ?\<tau> k = I (t k \<cdot> \<sigma> k)" for k
    using rhs_I[OF pair[of k], of "\<sigma> k"] by simp
  have between:
    "(I (t k \<cdot> \<sigma> k),
      I (s (Suc k) \<cdot> \<sigma> (Suc k))) \<in> NS" for k
    by (rule csr_u3_interpretation_steps[
        OF refl trans step_I target_SN steps])
  have lhs:
    "(I (s (Suc k) \<cdot> \<sigma> (Suc k)),
      s (Suc k) \<cdot> ?\<tau> (Suc k)) \<in> NS" for k
    using lhs_I[OF pair[of "Suc k"], of "\<sigma> (Suc k)"] by simp
  have sim:
    "(t k \<cdot> ?\<tau> k, s (Suc k) \<cdot> ?\<tau> (Suc k)) \<in> NS"
    for k
    unfolding rhs[of k]
    using between[of k] lhs[of k] trans unfolding trans_def by blast
  show ?thesis
  proof (rule exI[of _ ?\<tau>], intro allI)
    fix k
    show "(t k \<cdot> ?\<tau> k, s (Suc k) \<cdot> ?\<tau> (Suc k)) \<in> NS"
      by (rule sim)
  qed
qed

lemma csr_u3_chain_simulation_from_marked_interpretation:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f, n)"
    and refl: "refl NS"
    and trans: "trans NS"
    and pair: "\<And>k. (s k, t k) \<in> P"
    and pair_shape: "\<forall>(u, v)\<in>P.
      (\<exists>f us. u = Fun (Sharp f) us) \<and>
      (\<exists>g vs. v = Fun (Sharp g) vs)"
    and target_SN:
      "\<And>k. SN_on (csdp_step Sharp \<mu> R) {t k \<cdot> \<sigma> k}"
    and steps:
      "\<And>k. (t k \<cdot> \<sigma> k, s (Suc k) \<cdot> \<sigma> (Suc k)) \<in>
        (csdp_step Sharp \<mu> R)\<^sup>*"
    and rhs_I:
      "\<And>dp \<rho>. dp \<in> P \<Longrightarrow>
        I (snd dp \<cdot> \<rho>) = snd dp \<cdot> (\<lambda>x. I (\<rho> x))"
    and lhs_I:
      "\<And>dp \<rho>. dp \<in> P \<Longrightarrow>
        (I (fst dp \<cdot> \<rho>),
          fst dp \<cdot> (\<lambda>x. I (\<rho> x))) \<in> NS"
    and step_I:
      "\<And>f ts y. SN_on (csdp_step Sharp \<mu> R) {Fun (Sharp f) ts} \<Longrightarrow>
        (Fun (Sharp f) ts, y) \<in> csdp_step Sharp \<mu> R \<Longrightarrow>
        (I (Fun (Sharp f) ts), I y) \<in> NS"
  shows "\<exists>\<tau>. \<forall>k.
    (t k \<cdot> \<tau> k, s (Suc k) \<cdot> \<tau> (Suc k)) \<in> NS"
proof -
  let ?\<tau> = "\<lambda>k x. I (\<sigma> k x)"
  have rhs:
    "t k \<cdot> ?\<tau> k = I (t k \<cdot> \<sigma> k)" for k
    using rhs_I[OF pair[of k], of "\<sigma> k"] by simp
  have start_shape:
    "\<exists>f us. t k \<cdot> \<sigma> k = Fun (Sharp f) us" for k
  proof -
    from pair_shape pair[of k]
    obtain f us where t: "t k = Fun (Sharp f) us"
      by auto
    show ?thesis
      unfolding t by auto
  qed
  have between:
    "(I (t k \<cdot> \<sigma> k),
      I (s (Suc k) \<cdot> \<sigma> (Suc k))) \<in> NS" for k
  proof -
    have both:
      "(I (t k \<cdot> \<sigma> k),
          I (s (Suc k) \<cdot> \<sigma> (Suc k))) \<in> NS \<and>
        (\<exists>f ts. s (Suc k) \<cdot> \<sigma> (Suc k) = Fun (Sharp f) ts)"
      apply (rule csr_u3_interpretation_steps_marked[
          where x="t k \<cdot> \<sigma> k"
            and y="s (Suc k) \<cdot> \<sigma> (Suc k)"
            and I=I and NS=NS and R=R and \<mu>=\<mu>])
             apply (rule wf)
            apply (rule fresh)
           apply (rule refl)
         apply (rule trans)
         apply (rule step_I)
          apply assumption
         apply assumption
        apply (rule start_shape)
       apply (rule target_SN)
      apply (rule steps)
      done
    show ?thesis
      using both by simp
  qed
  have lhs:
    "(I (s (Suc k) \<cdot> \<sigma> (Suc k)),
      s (Suc k) \<cdot> ?\<tau> (Suc k)) \<in> NS" for k
    using lhs_I[OF pair[of "Suc k"], of "\<sigma> (Suc k)"] by simp
  have sim:
    "(t k \<cdot> ?\<tau> k, s (Suc k) \<cdot> ?\<tau> (Suc k)) \<in> NS"
    for k
    unfolding rhs[of k]
    using between[of k] lhs[of k] trans unfolding trans_def by blast
  show ?thesis
    by (rule exI[of _ ?\<tau>], use sim in blast)
qed

lemma csr_u3_chain_simulation_from_mixed_interpretation:
  fixes U :: "(('f::{showl, compare_order}, 'l::{showl, compare_order}) lab)"
  assumes wf: "wf_trs R"
    and fresh_sharp: "\<And>f n. \<not> defined R (Sharp f, n)"
    and fresh_U: "\<And>n. \<not> defined R (U, n)"
    and unsharp: "\<not> is_sharp_lab U"
    and refl: "refl NS"
    and trans: "trans NS"
    and pair: "\<And>k. (s k, t k) \<in> P"
    and pair_shape: "\<forall>(u, v)\<in>P.
      csr_u3_mixed_term_shape U u \<and> csr_u3_mixed_term_shape U v"
    and target_SN:
      "\<And>k. SN_on (csdp_step Sharp \<mu> R) {t k \<cdot> \<sigma> k}"
    and steps:
      "\<And>k. (t k \<cdot> \<sigma> k, s (Suc k) \<cdot> \<sigma> (Suc k)) \<in>
        (csdp_step Sharp \<mu> R)\<^sup>*"
    and rhs_I:
      "\<And>dp \<rho>. dp \<in> P \<Longrightarrow>
        I (snd dp \<cdot> \<rho>) = snd dp \<cdot> (\<lambda>x. I (\<rho> x))"
    and lhs_I:
      "\<And>dp \<rho>. dp \<in> P \<Longrightarrow>
        (I (fst dp \<cdot> \<rho>),
          fst dp \<cdot> (\<lambda>x. I (\<rho> x))) \<in> NS"
    and step_I:
      "\<And>f ts y. SN_on (csdp_step Sharp \<mu> R) {Fun (Sharp f) ts} \<Longrightarrow>
        (Fun (Sharp f) ts, y) \<in> csdp_step Sharp \<mu> R \<Longrightarrow>
        (I (Fun (Sharp f) ts), I y) \<in> NS"
  shows "\<exists>\<tau>. \<forall>k.
    (t k \<cdot> \<tau> k, s (Suc k) \<cdot> \<tau> (Suc k)) \<in> NS"
proof -
  let ?\<tau> = "\<lambda>k x. I (\<sigma> k x)"
  have rhs:
    "t k \<cdot> ?\<tau> k = I (t k \<cdot> \<sigma> k)" for k
    using rhs_I[OF pair[of k], of "\<sigma> k"] by simp
  have start_shape:
    "csr_u3_mixed_term_shape U (t k \<cdot> \<sigma> k)" for k
  proof -
    from pair_shape pair[of k]
    have "csr_u3_mixed_term_shape U (t k)" by auto
    then show ?thesis by (rule csr_u3_mixed_term_shape_subst)
  qed
  have between:
    "(I (t k \<cdot> \<sigma> k),
      I (s (Suc k) \<cdot> \<sigma> (Suc k))) \<in> NS" for k
  proof -
    from csr_u3_interpretation_steps_mixed[
        where x="t k \<cdot> \<sigma> k"
          and y="s (Suc k) \<cdot> \<sigma> (Suc k)"
          and U=U and I=I and NS=NS and R=R and \<mu>=\<mu>,
        OF wf fresh_sharp fresh_U unsharp refl trans step_I
          start_shape target_SN steps]
    show ?thesis by simp
  qed
  have lhs:
    "(I (s (Suc k) \<cdot> \<sigma> (Suc k)),
      s (Suc k) \<cdot> ?\<tau> (Suc k)) \<in> NS" for k
    using lhs_I[OF pair[of "Suc k"], of "\<sigma> (Suc k)"] by simp
  have sim:
    "(t k \<cdot> ?\<tau> k, s (Suc k) \<cdot> ?\<tau> (Suc k)) \<in> NS"
    for k
    unfolding rhs[of k]
    using between[of k] lhs[of k] trans unfolding trans_def by blast
  show ?thesis
    by (rule exI[of _ ?\<tau>], use sim in blast)
qed

theorem finite_min_csr_dpp_redpair_simulation:
  assumes redpair: "compat_redpair_order S NS"
    and orient: "P \<subseteq> S \<union> NS"
    and simulation:
      "\<And>s t \<sigma>.
        (\<And>k. (s k, t k) \<in> P) \<Longrightarrow>
        (\<And>k. SN_on (csdp_step Sharp \<mu> R) {t k \<cdot> \<sigma> k}) \<Longrightarrow>
        (\<And>k. (t k \<cdot> \<sigma> k, s (Suc k) \<cdot> \<sigma> (Suc k)) \<in>
          (csdp_step Sharp \<mu> R)\<^sup>*) \<Longrightarrow>
        \<exists>\<tau>. \<forall>k. (t k \<cdot> \<tau> k, s (Suc k) \<cdot> \<tau> (Suc k)) \<in> NS"
    and fin: "finite_min_csr_dpp Sharp \<mu> (P - S) R"
  shows "finite_min_csr_dpp Sharp \<mu> P R"
proof (rule ccontr)
  interpret compat_redpair_order S NS by (rule redpair)
  assume not_fin: "\<not> finite_min_csr_dpp Sharp \<mu> P R"
  from not_finite_min_csr_dpp_obtain_chain[OF not_fin]
  obtain s t \<sigma> where
    pair: "\<And>k. (s k, t k) \<in> P"
    and target_SN:
      "\<And>k. SN_on (csdp_step Sharp \<mu> R) {t k \<cdot> \<sigma> k}"
    and steps:
      "\<And>k. (t k \<cdot> \<sigma> k, s (Suc k) \<cdot> \<sigma> (Suc k)) \<in>
        (csdp_step Sharp \<mu> R)\<^sup>*"
    by blast
  from simulation[of s t \<sigma>, OF pair target_SN steps]
  obtain \<tau> where sim:
    "\<And>k. (t k \<cdot> \<tau> k, s (Suc k) \<cdot> \<tau> (Suc k)) \<in> NS"
    by blast
  let ?x = "\<lambda>k. s k \<cdot> \<tau> k"
  let ?y = "\<lambda>k. t k \<cdot> \<tau> k"
  have pair_ord: "(?x k, ?y k) \<in> S \<union> NS" for k
  proof -
    from orient pair[of k] have "(s k, t k) \<in> S \<union> NS"
      by blast
    then show ?thesis
      using subst_S subst_NS by (auto simp: subst.closed_def)
  qed
  have x_step: "(?x k, ?x (Suc k)) \<in> S \<union> NS" for k
  proof (cases "(?x k, ?y k) \<in> S")
    case True
    from compat_S_NS True sim[of k]
    have "(?x k, ?x (Suc k)) \<in> S" by blast
    then show ?thesis by simp
  next
    case False
    with pair_ord[of k] have "(?x k, ?y k) \<in> NS" by blast
    from trans_NS_point[OF this sim[of k]]
    show ?thesis by simp
  qed
  have x_chain: "chain (NS \<union> S) ?x"
    using x_step by (simp add: Un_commute)
  have sn_x0: "SN_on S {?x 0}"
    using SN unfolding SN_on_def by auto
  from non_strict_ending[OF x_chain compat_NS_S sn_x0]
  obtain j where tail: "\<And>k. k \<ge> j \<Longrightarrow>
    (?x k, ?x (Suc k)) \<in> NS - S"
    by auto
  have pair_tail: "(s (k + j), t (k + j)) \<in> P - S" for k
  proof (rule DiffI)
    show "(s (k + j), t (k + j)) \<in> P"
      by (rule pair)
    show "(s (k + j), t (k + j)) \<notin> S"
    proof (rule ccontr)
      assume "\<not> (s (k + j), t (k + j)) \<notin> S"
      then have rule_S: "(s (k + j), t (k + j)) \<in> S" by simp
      from subst.closedD[OF subst_S rule_S]
      have inst_S: "(?x (k + j), ?y (k + j)) \<in> S" .
      from compat_S_NS inst_S sim[of "k + j"]
      have "(?x (k + j), ?x (Suc (k + j))) \<in> S" by blast
      moreover from tail[of "k + j"] have
        "(?x (k + j), ?x (Suc (k + j))) \<notin> S" by auto
      ultimately show False by contradiction
    qed
  qed
  let ?ss = "shift s j"
  let ?tt = "shift t j"
  let ?\<sigma>\<sigma> = "shift \<sigma> j"
  let ?RS = "csdp_step Sharp \<mu> R"
  let ?RP = "csr_min_pair_step Sharp \<mu> (P - S) R"
  let ?rel = "?RS\<^sup>* O ?RP O ?RS\<^sup>*"
  let ?vals = "\<lambda>k. ?ss k \<cdot> ?\<sigma>\<sigma> k"
  have rel_step: "(?vals k, ?vals (Suc k)) \<in> ?rel" for k
  proof -
    have pair_k: "(?ss k, ?tt k) \<in> P - S"
      using pair_tail[of k] by simp
    have rr_k:
      "(?ss k \<cdot> ?\<sigma>\<sigma> k, ?tt k \<cdot> ?\<sigma>\<sigma> k) \<in>
        rrstep (P - S)"
      unfolding rrstep_def'
      apply (rule Quasi_Order.mem_rel_ofI)
      apply (rule exI[where x = "?ss k"])
      apply (rule exI[where x = "?tt k"])
      apply (rule exI[where x = "?\<sigma>\<sigma> k"])
      using pair_k
      apply simp
      done
    have sn_k:
      "SN_on ?RS {?tt k \<cdot> ?\<sigma>\<sigma> k}"
      using target_SN[of "k + j"] by simp
    have min_k:
      "(?ss k \<cdot> ?\<sigma>\<sigma> k, ?tt k \<cdot> ?\<sigma>\<sigma> k) \<in> ?RP"
      unfolding csr_min_pair_step_def
    proof (rule IntI)
      show "(?ss k \<cdot> ?\<sigma>\<sigma> k, ?tt k \<cdot> ?\<sigma>\<sigma> k) \<in>
        rrstep (P - S)"
        by (rule rr_k)
      show "(?ss k \<cdot> ?\<sigma>\<sigma> k, ?tt k \<cdot> ?\<sigma>\<sigma> k) \<in>
        {(u, v). SN_on ?RS {v}}"
        using sn_k by simp
    qed
    have steps_k:
      "(?tt k \<cdot> ?\<sigma>\<sigma> k, ?ss (Suc k) \<cdot> ?\<sigma>\<sigma> (Suc k)) \<in>
        ?RS\<^sup>*"
      using steps[of "k + j"] by simp
    have prefix:
      "(?vals k, ?vals k) \<in> ?RS\<^sup>*"
      by simp
    have pair_and_suffix:
      "(?vals k, ?vals (Suc k)) \<in> ?RP O ?RS\<^sup>*"
      by (rule relcompI[OF min_k steps_k])
    show ?thesis
      by (rule relcompI[OF prefix pair_and_suffix])
  qed
  have vals_chain: "chain ?rel ?vals"
    using rel_step by simp
  have "\<not> SN_on ?rel UNIV"
    by (rule not_SN_onI[OF _ vals_chain], simp)
  moreover from fin have "SN_on ?rel UNIV"
    unfolding finite_min_csr_dpp_def SN_rel_on_def .
  ultimately show False by contradiction
qed

theorem finite_min_csr_dpp_redpair_interpretation:
  assumes redpair: "compat_redpair_order S NS"
    and orient: "P \<subseteq> S \<union> NS"
    and rhs_I:
      "\<And>dp \<rho>. dp \<in> P \<Longrightarrow>
        I (snd dp \<cdot> \<rho>) = snd dp \<cdot> (\<lambda>x. I (\<rho> x))"
    and lhs_I:
      "\<And>dp \<rho>. dp \<in> P \<Longrightarrow>
        (I (fst dp \<cdot> \<rho>),
          fst dp \<cdot> (\<lambda>x. I (\<rho> x))) \<in> NS"
    and step_I:
      "\<And>x y. SN_on (csdp_step Sharp \<mu> R) {x} \<Longrightarrow>
        (x, y) \<in> csdp_step Sharp \<mu> R \<Longrightarrow>
        (I x, I y) \<in> NS"
    and fin: "finite_min_csr_dpp Sharp \<mu> (P - S) R"
  shows "finite_min_csr_dpp Sharp \<mu> P R"
proof -
  interpret compat_redpair_order S NS by (rule redpair)
  show ?thesis
  proof (rule finite_min_csr_dpp_redpair_simulation[
      OF redpair orient _ fin])
    fix s t \<sigma>
    assume pair: "\<And>k. (s k, t k) \<in> P"
      and target_SN:
        "\<And>k. SN_on (csdp_step Sharp \<mu> R) {t k \<cdot> \<sigma> k}"
      and steps:
        "\<And>k. (t k \<cdot> \<sigma> k,
          s (Suc k) \<cdot> \<sigma> (Suc k)) \<in>
          (csdp_step Sharp \<mu> R)\<^sup>*"
    show "\<exists>\<tau>. \<forall>k.
      (t k \<cdot> \<tau> k, s (Suc k) \<cdot> \<tau> (Suc k)) \<in> NS"
      apply (rule csr_u3_chain_simulation_from_interpretation[
          where NS=NS and P=P and I=I and \<mu>=\<mu> and R=R
            and s=s and t=t and \<sigma>=\<sigma>])
      using refl_NS trans_NS pair target_SN steps rhs_I lhs_I step_I
      apply blast+
      done
  qed
qed

theorem finite_min_csr_dpp_redpair_marked_interpretation:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f, n)"
    and redpair: "compat_redpair_order S NS"
    and orient: "P \<subseteq> S \<union> NS"
    and pair_shape: "\<forall>(u, v)\<in>P.
      (\<exists>f us. u = Fun (Sharp f) us) \<and>
      (\<exists>g vs. v = Fun (Sharp g) vs)"
    and rhs_I:
      "\<And>dp \<rho>. dp \<in> P \<Longrightarrow>
        I (snd dp \<cdot> \<rho>) = snd dp \<cdot> (\<lambda>x. I (\<rho> x))"
    and lhs_I:
      "\<And>dp \<rho>. dp \<in> P \<Longrightarrow>
        (I (fst dp \<cdot> \<rho>),
          fst dp \<cdot> (\<lambda>x. I (\<rho> x))) \<in> NS"
    and step_I:
      "\<And>f ts y. SN_on (csdp_step Sharp \<mu> R) {Fun (Sharp f) ts} \<Longrightarrow>
        (Fun (Sharp f) ts, y) \<in> csdp_step Sharp \<mu> R \<Longrightarrow>
        (I (Fun (Sharp f) ts), I y) \<in> NS"
    and fin: "finite_min_csr_dpp Sharp \<mu> (P - S) R"
  shows "finite_min_csr_dpp Sharp \<mu> P R"
proof -
  interpret compat_redpair_order S NS by (rule redpair)
  show ?thesis
  proof (rule finite_min_csr_dpp_redpair_simulation[
      OF redpair orient _ fin])
    fix s t \<sigma>
    assume pair: "\<And>k. (s k, t k) \<in> P"
      and target_SN:
        "\<And>k. SN_on (csdp_step Sharp \<mu> R) {t k \<cdot> \<sigma> k}"
      and steps:
        "\<And>k. (t k \<cdot> \<sigma> k,
          s (Suc k) \<cdot> \<sigma> (Suc k)) \<in>
          (csdp_step Sharp \<mu> R)\<^sup>*"
    show "\<exists>\<tau>. \<forall>k.
      (t k \<cdot> \<tau> k, s (Suc k) \<cdot> \<tau> (Suc k)) \<in> NS"
      apply (rule csr_u3_chain_simulation_from_marked_interpretation[
          where s=s and t=t and \<sigma>=\<sigma> and P=P and I=I
            and NS=NS and R=R and \<mu>=\<mu>])
                apply (rule wf)
               apply (rule fresh)
              apply (rule refl_NS)
             apply (rule trans_NS)
            apply (rule pair)
           apply (rule pair_shape)
          apply (rule target_SN)
         apply (rule steps)
        apply (rule rhs_I)
        apply assumption
       apply (rule lhs_I)
       apply assumption
      apply (rule step_I)
       apply assumption
      apply assumption
      done
  qed
qed

theorem finite_min_csr_dpp_redpair_mixed_interpretation:
  fixes U :: "(('f::{showl, compare_order}, 'l::{showl, compare_order}) lab)"
  assumes wf: "wf_trs R"
    and fresh_sharp: "\<And>f n. \<not> defined R (Sharp f, n)"
    and fresh_U: "\<And>n. \<not> defined R (U, n)"
    and unsharp: "\<not> is_sharp_lab U"
    and redpair: "compat_redpair_order S NS"
    and orient: "P \<subseteq> S \<union> NS"
    and pair_shape: "\<forall>(u, v)\<in>P.
      csr_u3_mixed_term_shape U u \<and> csr_u3_mixed_term_shape U v"
    and rhs_I:
      "\<And>dp \<rho>. dp \<in> P \<Longrightarrow>
        I (snd dp \<cdot> \<rho>) = snd dp \<cdot> (\<lambda>x. I (\<rho> x))"
    and lhs_I:
      "\<And>dp \<rho>. dp \<in> P \<Longrightarrow>
        (I (fst dp \<cdot> \<rho>),
          fst dp \<cdot> (\<lambda>x. I (\<rho> x))) \<in> NS"
    and step_I:
      "\<And>f ts y. SN_on (csdp_step Sharp \<mu> R) {Fun (Sharp f) ts} \<Longrightarrow>
        (Fun (Sharp f) ts, y) \<in> csdp_step Sharp \<mu> R \<Longrightarrow>
        (I (Fun (Sharp f) ts), I y) \<in> NS"
    and fin: "finite_min_csr_dpp Sharp \<mu> (P - S) R"
  shows "finite_min_csr_dpp Sharp \<mu> P R"
proof -
  interpret compat_redpair_order S NS by (rule redpair)
  show ?thesis
  proof (rule finite_min_csr_dpp_redpair_simulation[
      OF redpair orient _ fin])
    fix s t \<sigma>
    assume pair: "\<And>k. (s k, t k) \<in> P"
      and target_SN:
        "\<And>k. SN_on (csdp_step Sharp \<mu> R) {t k \<cdot> \<sigma> k}"
      and steps:
        "\<And>k. (t k \<cdot> \<sigma> k,
          s (Suc k) \<cdot> \<sigma> (Suc k)) \<in>
          (csdp_step Sharp \<mu> R)\<^sup>*"
    show "\<exists>\<tau>. \<forall>k.
      (t k \<cdot> \<tau> k, s (Suc k) \<cdot> \<tau> (Suc k)) \<in> NS"
      apply (rule csr_u3_chain_simulation_from_mixed_interpretation[
          where s=s and t=t and \<sigma>=\<sigma> and P=P and I=I
            and NS=NS and R=R and \<mu>=\<mu> and U=U])
                 apply (rule wf)
                apply (rule fresh_sharp)
               apply (rule fresh_U)
              apply (rule unsharp)
             apply (rule refl_NS)
            apply (rule trans_NS)
           apply (rule pair)
          apply (rule pair_shape)
         apply (rule target_SN)
        apply (rule steps)
       apply (rule rhs_I)
       apply assumption
      apply (rule lhs_I)
      apply assumption
     apply (rule step_I)
      apply assumption
     apply assumption
      done
  qed
qed

locale csr_u3_i1_lab =
  fixes Rs :: "((('f::{showl, compare_order},
      'l::{showl, compare_order}) lab), 'v) rules"
    and U :: "((('f, 'l) lab), 'v) trs"
    and \<mu>\<^sub>0 :: "(('f, 'l) lab) mu"
    and P :: "((('f, 'l) lab), 'v) trs"
    and cn :: "(('f, 'l) lab) \<times> nat"
  assumes wf: "wf_trs (set Rs)"
    and closed:
      "csr_u3_usable_rules_closed (set Rs) U \<mu>\<^sub>0 P"
begin

sublocale I: csr_u3_i1 Rs U \<mu>\<^sub>0 P cn
  by (unfold_locales, rule wf, rule closed)

theorem finite_min_csr_dpp_u3_redpair:
  assumes fresh:
      "\<And>f n. \<not> defined (set Rs) (Sharp f, n)"
    and marked_mu:
      "\<And>f n. \<mu>\<^sub>0 (f, n) \<subseteq> \<mu>\<^sub>0 (Sharp f, n)"
    and redpair: "compat_redpair_order S NS"
    and orient: "P \<subseteq> S \<union> NS"
    and pair_shape: "\<forall>(u, v)\<in>P.
      (\<exists>f us. u = Fun (Sharp f) us) \<and>
      (\<exists>g vs. v = Fun (Sharp g) vs)"
    and rewrite_NS:
      "csstep \<mu>\<^sub>0 (U \<union> ce_trs cn) \<subseteq> NS"
    and fin:
      "finite_min_csr_dpp Sharp \<mu>\<^sub>0
        (P - S) (set Rs)"
  shows "finite_min_csr_dpp Sharp \<mu>\<^sub>0 P (set Rs)"
proof -
  interpret compat_redpair_order S NS by (rule redpair)
  let ?A = "csstep \<mu>\<^sub>0 (U \<union> ce_trs cn)"
  have closure_NS: "?A\<^sup>* \<subseteq> NS"
  proof
    fix p
    assume p: "p \<in> ?A\<^sup>*"
    from subsetD[OF rtrancl_mono[OF rewrite_NS] p]
    have "p \<in> NS\<^sup>*" .
    then show "p \<in> NS"
      using refl_NS trans_NS trans_refl_imp_rtrancl_id by auto
  qed
  have rhs_I:
    "\<And>dp \<rho>. dp \<in> P \<Longrightarrow>
      I.i1 (snd dp \<cdot> \<rho>) =
        snd dp \<cdot> (\<lambda>x. I.i1 (\<rho> x))"
  proof -
    fix dp \<rho>
    assume dp: "dp \<in> P"
    from csr_u3_closed_pair_rhs_delta[OF closed dp]
    show "I.i1 (snd dp \<cdot> \<rho>) =
      snd dp \<cdot> (\<lambda>x. I.i1 (\<rho> x))"
      by (rule I.i1_delta_subst)
  qed
  have lhs_I:
    "\<And>dp \<rho>. dp \<in> P \<Longrightarrow>
      (I.i1 (fst dp \<cdot> \<rho>),
        fst dp \<cdot> (\<lambda>x. I.i1 (\<rho> x))) \<in> NS"
  proof -
    fix dp \<rho>
    assume dp: "dp \<in> P"
    have inactive:
      "\<And>p. p \<in> fun_poss (fst dp) \<Longrightarrow>
        p \<notin> mu_fun_poss \<mu>\<^sub>0 (fst dp) \<Longrightarrow>
        funas_term (fst dp |_ p) \<subseteq>
          csr_u3_delta (set Rs) U"
      by (rule csr_u3_closed_pair_lhs_inactive_delta[OF closed dp])
    from I.i1_pattern_subst[OF inactive, of \<rho>]
    have project:
      "(I.i1 (fst dp \<cdot> \<rho>),
        fst dp \<cdot> (\<lambda>x. I.i1 (\<rho> x))) \<in>
        (csstep \<mu>\<^sub>0 (ce_trs cn))\<^sup>*" .
    have C_subset:
      "csstep \<mu>\<^sub>0 (ce_trs cn) \<subseteq> ?A"
      by (rule csstep_rules_mono, simp)
    have project':
      "(I.i1 (fst dp \<cdot> \<rho>),
        fst dp \<cdot> (\<lambda>x. I.i1 (\<rho> x))) \<in> ?A\<^sup>*"
      by (rule subsetD[OF rtrancl_mono[OF C_subset] project])
    show "(I.i1 (fst dp \<cdot> \<rho>),
      fst dp \<cdot> (\<lambda>x. I.i1 (\<rho> x))) \<in> NS"
      by (rule subsetD[OF closure_NS project'])
  qed
  have step_I:
    "\<And>f ts y.
      SN_on (csdp_step Sharp \<mu>\<^sub>0 (set Rs))
        {Fun (Sharp f) ts} \<Longrightarrow>
      (Fun (Sharp f) ts, y) \<in>
        csdp_step Sharp \<mu>\<^sub>0 (set Rs) \<Longrightarrow>
      (I.i1 (Fun (Sharp f) ts), I.i1 y) \<in> NS"
  proof -
    fix f ts y
    assume SN:
      "SN_on (csdp_step Sharp \<mu>\<^sub>0 (set Rs))
        {Fun (Sharp f) ts}"
      and step:
      "(Fun (Sharp f) ts, y) \<in>
        csdp_step Sharp \<mu>\<^sub>0 (set Rs)"
    from I.i1_sharp_csdp_step[
        OF fresh inj_Sharp marked_mu[of f "length ts"] SN step]
    show "(I.i1 (Fun (Sharp f) ts), I.i1 y) \<in> NS"
      by (rule subsetD[OF closure_NS])
  qed
  show ?thesis
    by (rule finite_min_csr_dpp_redpair_marked_interpretation[
        OF wf fresh redpair orient pair_shape rhs_I lhs_I step_I fin])
qed

theorem finite_min_csr_dpp_mixed_u3_redpair:
  fixes H :: "(('f, 'l) lab)"
  assumes fresh_sharp:
      "\<And>f n. \<not> defined (set Rs) (Sharp f, n)"
    and fresh_H: "\<And>n. \<not> defined (set Rs) (H, n)"
    and unsharp: "\<not> is_sharp_lab H"
    and marked_mu:
      "\<And>f n. \<mu>\<^sub>0 (f, n) \<subseteq> \<mu>\<^sub>0 (Sharp f, n)"
    and redpair: "compat_redpair_order S NS"
    and orient: "P \<subseteq> S \<union> NS"
    and pair_shape: "\<forall>(u, v)\<in>P.
      csr_u3_mixed_term_shape H u \<and> csr_u3_mixed_term_shape H v"
    and rewrite_NS:
      "csstep \<mu>\<^sub>0 (U \<union> ce_trs cn) \<subseteq> NS"
    and fin:
      "finite_min_csr_dpp Sharp \<mu>\<^sub>0
        (P - S) (set Rs)"
  shows "finite_min_csr_dpp Sharp \<mu>\<^sub>0 P (set Rs)"
proof -
  interpret compat_redpair_order S NS by (rule redpair)
  let ?A = "csstep \<mu>\<^sub>0 (U \<union> ce_trs cn)"
  have closure_NS: "?A\<^sup>* \<subseteq> NS"
  proof
    fix p
    assume p: "p \<in> ?A\<^sup>*"
    from subsetD[OF rtrancl_mono[OF rewrite_NS] p]
    have "p \<in> NS\<^sup>*" .
    then show "p \<in> NS"
      using refl_NS trans_NS trans_refl_imp_rtrancl_id by auto
  qed
  have rhs_I:
    "\<And>dp \<rho>. dp \<in> P \<Longrightarrow>
      I.i1 (snd dp \<cdot> \<rho>) =
        snd dp \<cdot> (\<lambda>x. I.i1 (\<rho> x))"
  proof -
    fix dp \<rho>
    assume dp: "dp \<in> P"
    from csr_u3_closed_pair_rhs_delta[OF closed dp]
    show "I.i1 (snd dp \<cdot> \<rho>) =
      snd dp \<cdot> (\<lambda>x. I.i1 (\<rho> x))"
      by (rule I.i1_delta_subst)
  qed
  have lhs_I:
    "\<And>dp \<rho>. dp \<in> P \<Longrightarrow>
      (I.i1 (fst dp \<cdot> \<rho>),
        fst dp \<cdot> (\<lambda>x. I.i1 (\<rho> x))) \<in> NS"
  proof -
    fix dp \<rho>
    assume dp: "dp \<in> P"
    have inactive:
      "\<And>p. p \<in> fun_poss (fst dp) \<Longrightarrow>
        p \<notin> mu_fun_poss \<mu>\<^sub>0 (fst dp) \<Longrightarrow>
        funas_term (fst dp |_ p) \<subseteq>
          csr_u3_delta (set Rs) U"
      by (rule csr_u3_closed_pair_lhs_inactive_delta[OF closed dp])
    from I.i1_pattern_subst[OF inactive, of \<rho>]
    have project:
      "(I.i1 (fst dp \<cdot> \<rho>),
        fst dp \<cdot> (\<lambda>x. I.i1 (\<rho> x))) \<in>
        (csstep \<mu>\<^sub>0 (ce_trs cn))\<^sup>*" .
    have C_subset:
      "csstep \<mu>\<^sub>0 (ce_trs cn) \<subseteq> ?A"
      by (rule csstep_rules_mono, simp)
    have project':
      "(I.i1 (fst dp \<cdot> \<rho>),
        fst dp \<cdot> (\<lambda>x. I.i1 (\<rho> x))) \<in> ?A\<^sup>*"
      by (rule subsetD[OF rtrancl_mono[OF C_subset] project])
    show "(I.i1 (fst dp \<cdot> \<rho>),
      fst dp \<cdot> (\<lambda>x. I.i1 (\<rho> x))) \<in> NS"
      by (rule subsetD[OF closure_NS project'])
  qed
  have step_I:
    "\<And>f ts y.
      SN_on (csdp_step Sharp \<mu>\<^sub>0 (set Rs))
        {Fun (Sharp f) ts} \<Longrightarrow>
      (Fun (Sharp f) ts, y) \<in>
        csdp_step Sharp \<mu>\<^sub>0 (set Rs) \<Longrightarrow>
      (I.i1 (Fun (Sharp f) ts), I.i1 y) \<in> NS"
  proof -
    fix f ts y
    assume SN:
      "SN_on (csdp_step Sharp \<mu>\<^sub>0 (set Rs))
        {Fun (Sharp f) ts}"
      and step:
      "(Fun (Sharp f) ts, y) \<in>
        csdp_step Sharp \<mu>\<^sub>0 (set Rs)"
    from I.i1_sharp_csdp_step[
        OF fresh_sharp inj_Sharp marked_mu[of f "length ts"] SN step]
    show "(I.i1 (Fun (Sharp f) ts), I.i1 y) \<in> NS"
      by (rule subsetD[OF closure_NS])
  qed
  show ?thesis
    by (rule finite_min_csr_dpp_redpair_mixed_interpretation[
        OF wf fresh_sharp fresh_H unsharp redpair orient pair_shape
          rhs_I lhs_I step_I fin])
qed

end

theorem finite_min_csr_dpp_u3_redpair:
  fixes Rs :: "((('f::{showl, compare_order},
      'l::{showl, compare_order}) lab), 'v) rules"
    and U :: "((('f, 'l) lab), 'v) trs"
    and \<mu>\<^sub>0 :: "(('f, 'l) lab) mu"
    and P :: "((('f, 'l) lab), 'v) trs"
  assumes wf: "wf_trs (set Rs)"
    and closed:
      "csr_u3_usable_rules_closed (set Rs) U
        \<mu>\<^sub>0 P"
    and fresh:
      "\<And>f n. \<not> defined (set Rs) (Sharp f, n)"
    and marked_mu:
      "\<And>f n. \<mu>\<^sub>0 (f, n) \<subseteq> \<mu>\<^sub>0 (Sharp f, n)"
    and redpair: "compat_redpair_order S NS"
    and orient: "P \<subseteq> S \<union> NS"
    and pair_shape: "\<forall>(u, v)\<in>P.
      (\<exists>f us. u = Fun (Sharp f) us) \<and>
      (\<exists>g vs. v = Fun (Sharp g) vs)"
    and U_NS: "U \<subseteq> NS"
    and ce: "ce_compatible NS"
    and fin:
      "finite_min_csr_dpp Sharp \<mu>\<^sub>0
        (P - S) (set Rs)"
  shows "finite_min_csr_dpp Sharp \<mu>\<^sub>0 P (set Rs)"
proof (cases "P = {}")
  case True
  have diff: "P - S = P"
    using True by simp
  from fin show ?thesis
    unfolding diff .
next
  case False
  then obtain dp where dp: "dp \<in> P"
    by blast
  from pair_shape dp obtain f us where lhs: "fst dp = Fun (Sharp f) us"
    by (cases dp, auto)
  obtain n where ce_bound:
    "\<And>c m. m \<ge> n \<Longrightarrow> ce_trs (c, m) \<subseteq> NS"
  proof (rule ce_compatibleE[OF ce])
    fix n
    assume bound: "\<And>c m. m \<ge> n \<Longrightarrow> ce_trs (c, m) \<subseteq> NS"
    show thesis
      by (rule that[OF bound])
  qed
  have ce_NS: "ce_trs (Sharp f, n) \<subseteq> NS"
    by (rule ce_bound, simp)
  let ?cn = "(Sharp f, n)"
  interpret rp: compat_redpair_order S NS by (rule redpair)
  have rules_NS: "U \<union> ce_trs ?cn \<subseteq> NS"
    using U_NS ce_NS by auto
  have rewrite_NS:
    "csstep \<mu>\<^sub>0 (U \<union> ce_trs ?cn) \<subseteq> NS"
  proof (rule subset_trans[OF csstep_subset_rstep])
    have "rstep (U \<union> ce_trs ?cn) \<subseteq> rstep NS"
      by (rule rstep_mono[OF rules_NS])
    also have "... \<subseteq> NS"
      by (rule rp.rstep_NS)
    finally show "rstep (U \<union> ce_trs ?cn) \<subseteq> NS" .
  qed
  interpret L: csr_u3_i1_lab Rs U \<mu>\<^sub>0 P ?cn
    by (unfold_locales, rule wf, rule closed)
  show ?thesis
    by (rule L.finite_min_csr_dpp_u3_redpair[
        OF fresh marked_mu redpair orient pair_shape rewrite_NS fin])
qed

theorem finite_min_csr_dpp_mixed_u3_redpair:
  fixes Rs :: "((('f::{showl, compare_order},
      'l::{showl, compare_order}) lab), 'v) rules"
    and Ur :: "((('f, 'l) lab), 'v) trs"
    and H :: "(('f, 'l) lab)"
    and \<mu>\<^sub>0 :: "(('f, 'l) lab) mu"
    and P :: "((('f, 'l) lab), 'v) trs"
  assumes wf: "wf_trs (set Rs)"
    and closed:
      "csr_u3_usable_rules_closed (set Rs) Ur
        \<mu>\<^sub>0 P"
    and fresh_sharp:
      "\<And>f n. \<not> defined (set Rs) (Sharp f, n)"
    and fresh_H: "\<And>n. \<not> defined (set Rs) (H, n)"
    and unsharp: "\<not> is_sharp_lab H"
    and marked_mu:
      "\<And>f n. \<mu>\<^sub>0 (f, n) \<subseteq> \<mu>\<^sub>0 (Sharp f, n)"
    and redpair: "compat_redpair_order S NS"
    and orient: "P \<subseteq> S \<union> NS"
    and pair_shape: "\<forall>(u, v)\<in>P.
      csr_u3_mixed_term_shape H u \<and> csr_u3_mixed_term_shape H v"
    and Ur_NS: "Ur \<subseteq> NS"
    and ce: "ce_compatible NS"
    and fin:
      "finite_min_csr_dpp Sharp \<mu>\<^sub>0
        (P - S) (set Rs)"
  shows "finite_min_csr_dpp Sharp \<mu>\<^sub>0 P (set Rs)"
proof -
  obtain n where ce_bound:
    "\<And>c m. m \<ge> n \<Longrightarrow> ce_trs (c, m) \<subseteq> NS"
  proof (rule ce_compatibleE[OF ce])
    fix n
    assume bound: "\<And>c m. m \<ge> n \<Longrightarrow> ce_trs (c, m) \<subseteq> NS"
    show thesis
      by (rule that[OF bound])
  qed
  have ce_NS: "ce_trs (H, n) \<subseteq> NS"
    by (rule ce_bound, simp)
  let ?cn = "(H, n)"
  interpret rp: compat_redpair_order S NS by (rule redpair)
  have rules_NS: "Ur \<union> ce_trs ?cn \<subseteq> NS"
    using Ur_NS ce_NS by auto
  have rewrite_NS:
    "csstep \<mu>\<^sub>0 (Ur \<union> ce_trs ?cn) \<subseteq> NS"
  proof (rule subset_trans[OF csstep_subset_rstep])
    have "rstep (Ur \<union> ce_trs ?cn) \<subseteq> rstep NS"
      by (rule rstep_mono[OF rules_NS])
    also have "... \<subseteq> NS"
      by (rule rp.rstep_NS)
    finally show "rstep (Ur \<union> ce_trs ?cn) \<subseteq> NS" .
  qed
  interpret L: csr_u3_i1_lab Rs Ur \<mu>\<^sub>0 P ?cn
    by (unfold_locales, rule wf, rule closed)
  show ?thesis
    by (rule L.finite_min_csr_dpp_mixed_u3_redpair[
        OF fresh_sharp fresh_H unsharp marked_mu redpair orient
          pair_shape rewrite_NS fin])
qed

definition csr_sharp_pairs_check where
  "csr_sharp_pairs_check P = list_all (\<lambda>(l, r).
    (case root l of Some (Sharp f, n) \<Rightarrow> True | _ \<Rightarrow> False) \<and>
    (case root r of Some (Sharp f, n) \<Rightarrow> True | _ \<Rightarrow> False)) P"

lemma csr_sharp_pairs_check_sound:
  assumes "csr_sharp_pairs_check P"
  shows "\<forall>(u, v)\<in>set P.
    (\<exists>f us. u = Fun (Sharp f) us) \<and>
    (\<exists>g vs. v = Fun (Sharp g) vs)"
proof (intro ballI, clarify)
  fix u v
  assume mem: "(u, v) \<in> set P"
  from assms mem have checks:
    "(case root u of Some (Sharp f, n) \<Rightarrow> True | _ \<Rightarrow> False) \<and>
     (case root v of Some (Sharp f, n) \<Rightarrow> True | _ \<Rightarrow> False)"
    unfolding csr_sharp_pairs_check_def by (auto simp: list_all_iff)
  from checks obtain f n where uroot: "root u = Some (Sharp f, n)"
    by (cases "root u"; auto split: lab.splits)
  then obtain us where u: "u = Fun (Sharp f) us"
    by (cases u, auto)
  from checks obtain g m where vroot: "root v = Some (Sharp g, m)"
    by (cases "root v"; auto split: lab.splits)
  then obtain vs where v: "v = Fun (Sharp g) vs"
    by (cases v, auto)
  show "(\<exists>f us. u = Fun (Sharp f) us) \<and>
      (\<exists>g vs. v = Fun (Sharp g) vs)"
    using u v by blast
qed

fun csr_u3_mixed_term_check where
  "csr_u3_mixed_term_check H (Var x) = False"
| "csr_u3_mixed_term_check H (Fun f ts) =
    (is_sharp_lab f \<or> f = H)"

definition csr_u3_mixed_pairs_check where
  "csr_u3_mixed_pairs_check R P = list_ex (\<lambda>H.
    \<not> is_sharp_lab H \<and>
    list_all (\<lambda>(f, n). f \<noteq> H) (funas_trs_list R) \<and>
    list_all (\<lambda>(l, r). csr_u3_mixed_term_check H l \<and>
      csr_u3_mixed_term_check H r) P)
    (map fst (funas_trs_list P))"

lemma csr_u3_mixed_term_check_sound:
  assumes "csr_u3_mixed_term_check H t"
  shows "csr_u3_mixed_term_shape H t"
proof (cases t)
  case (Var x)
  with assms show ?thesis by simp
next
  case (Fun f ts)
  with assms show ?thesis
    by (cases f; auto simp: csr_u3_mixed_term_shape_def)
qed

lemma csr_u3_mixed_pairs_check_sound:
  assumes "csr_u3_mixed_pairs_check R P"
  shows "\<exists>H. (\<forall>n. \<not> defined (set R) (H, n)) \<and>
    \<not> is_sharp_lab H \<and>
    (\<forall>(u, v)\<in>set P.
      csr_u3_mixed_term_shape H u \<and> csr_u3_mixed_term_shape H v)"
proof -
  from assms obtain H where unsharp: "\<not> is_sharp_lab H"
    and fresh: "list_all (\<lambda>(f, n). f \<noteq> H) (funas_trs_list R)"
    and shape: "list_all (\<lambda>(l, r).
      csr_u3_mixed_term_check H l \<and>
      csr_u3_mixed_term_check H r) P"
    unfolding csr_u3_mixed_pairs_check_def
    by (auto simp: list_ex_iff)
  have fresh_sem: "\<And>n. \<not> defined (set R) (H, n)"
  proof
    fix n
    assume "defined (set R) (H, n)"
    then have "(H, n) \<in> funas_trs (set R)"
      by (rule defined_funas_trs)
    then have "(H, n) \<in> set (funas_trs_list R)"
      by simp
    with fresh show False
      by (auto simp: list_all_iff)
  qed
  have shape_sem: "\<forall>(u, v)\<in>set P.
      csr_u3_mixed_term_shape H u \<and> csr_u3_mixed_term_shape H v"
    using shape
    by (auto simp: list_all_iff intro: csr_u3_mixed_term_check_sound)
  show ?thesis using fresh_sem unsharp shape_sem by blast
qed

definition csr_u3_redpair_proc where
  "csr_u3_redpair_proc J \<mu> rp Premove U dpp = check_return (do {
    rel_impl_redpair rp;
    csr_sharp_mu_check \<mu>;
    let (ps, pns) = dpp_ops.split_pairs J dpp Premove;
    check (csr_sharp_pairs_check (dpp_ops.pairs J dpp) \<or>
        csr_u3_mixed_pairs_check (dpp_ops.rules J dpp)
          (dpp_ops.pairs J dpp))
      (showsl_lit (STR ''U3 reduction pair requires marked or fresh-unhiding CS-DPs''));
    check (csr_u3_usable_rules_check
        (dpp_ops.rules J dpp) U \<mu> (dpp_ops.pairs J dpp))
      (showsl_lit (STR ''supplied rules are not a closed U3 set''));
    rel_impl.ce_compat rp
      <+? (\<lambda>s. showsl_lit
        (STR ''U3 reduction pair requires C-epsilon compatibility\<newline>'') \<circ> s);
    rel_impl_ns rp (U @ pns)
      <+? (\<lambda>s. showsl_lit
        (STR ''problem weakly orienting U3 rules or retained CS-DPs\<newline>'') \<circ> s);
    rel_impl_s rp ps
      <+? (\<lambda>s. showsl_lit
        (STR ''problem strictly orienting removed CS-DPs\<newline>'') \<circ> s)
  }) (dpp_spec.delete_pairs J dpp Premove)"

lemma csr_u3_redpair_proc_sound:
  fixes J :: "('dpp, ('f::{showl, compare_order},
      'l::{showl, compare_order}) lab, string) dpp_ops"
    and \<mu> :: "(('f, 'l) lab) muL"
    and rp :: "(('f, 'l) lab, string) rel_impl"
  assumes J: "dpp_spec J" and rp: "rel_impl rp"
    and proc: "csr_u3_redpair_proc J \<mu> rp Premove U dpp = return dpp'"
    and wf: "wf_trs (set (dpp_ops.rules J dpp))"
    and fresh: "\<And>f n. \<not> defined (set (dpp_ops.rules J dpp)) (Sharp f, n)"
    and fin: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (dpp_ops.pairs J dpp')) (set (dpp_ops.rules J dpp'))"
  shows "finite_min_csr_dpp Sharp (mu_of \<mu>)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
proof -
  interpret dpp_spec J by fact
  obtain ps pns where split: "split_pairs dpp Premove = (ps, pns)"
    by force
  from split_pairs_sound[OF split]
  have ps: "set ps = set (pairs dpp) \<inter> set Premove"
    and pns: "set pns = set (pairs dpp) - set Premove"
    by auto
  from proc[unfolded csr_u3_redpair_proc_def Let_def split, simplified]
  have valid: "isOK (rel_impl_redpair rp)"
    and sharp_mu: "isOK (csr_sharp_mu_check \<mu>)"
    and shape: "csr_sharp_pairs_check (pairs dpp) \<or>
      csr_u3_mixed_pairs_check (rules dpp) (pairs dpp)"
    and closed: "csr_u3_usable_rules_check (rules dpp) U \<mu> (pairs dpp)"
    and ce: "isOK (rel_impl.ce_compat rp)"
    and weak: "isOK (rel_impl_ns rp (U @ pns))"
    and strict: "isOK (rel_impl_s rp ps)"
    and dpp': "dpp' = delete_pairs dpp Premove"
    by (auto simp: isOK_check rel_impl_list)
  from valid[unfolded rel_impl_redpair_def, simplified]
  have impl_valid: "isOK (rel_impl.valid rp)"
    and standard: "isOK (rel_impl.standard rp)"
    and sn: "isOK (rel_impl.SN rp)"
    and subst: "isOK (rel_impl.subst_s rp)"
    by auto
  let ?all = "ps @ U @ pns"
  from rp[unfolded rel_impl_def] impl_valid
  have all_rel: "\<forall>V. \<exists>S NS NST. rel_impl_prop rp V S NS NST"
    by blast
  have all_rel': "\<exists>S NS NST. rel_impl_prop rp ?all S NS NST"
    by (rule spec[OF all_rel])
  obtain S NS NST where rel_prop: "rel_impl_prop rp ?all S NS NST"
    using all_rel' by presburger
  from rel_prop strict weak subst sn standard
  have strict_S: "set ps \<subseteq> S"
    and U_NS: "set U \<subseteq> NS"
    and pns_NS: "set pns \<subseteq> NS"
    and S_NS: "S \<subseteq> NS"
    and S_NS_comp: "S O NS \<subseteq> S"
    and NS_S_comp: "NS O S \<subseteq> S"
    and ctxt_NS: "ctxt.closed NS"
    and trans_NS: "trans NS"
    and refl_NS: "refl NS"
    and subst_NS: "subst.closed NS"
    and trans_S: "trans S"
    and irrefl_S: "irrefl S"
    and subst_S: "subst.closed S"
    and SN_S: "SN S"
    and ce_NS: "ce_compatible NS"
    using ce by (auto simp: rel_impl_list)
  have redpair: "compat_redpair_order S NS"
    by (unfold_locales; fact)
  have orient: "set (pairs dpp) \<subseteq> S \<union> NS"
    using strict_S pns_NS unfolding ps pns by auto
  have closed_sem: "csr_u3_usable_rules_closed
      (set (rules dpp)) (set U) (mu_of \<mu>) (set (pairs dpp))"
    by (rule csr_u3_usable_rules_check_sound[OF closed])
  have marked_mu:
      "\<And>f n. mu_of \<mu> (f, n) \<subseteq> mu_of \<mu> (Sharp f, n)"
    by (rule csr_sharp_mu_check_sound[OF sharp_mu])
  have pairs': "set (pairs dpp') = set (pairs dpp) - set Premove"
    using dpp' delete_P_Pw_sound[of dpp Premove Premove]
      pairs_sound[of dpp'] by auto
  have rules': "set (rules dpp') = set (rules dpp)"
    using dpp' delete_P_Pw_sound[of dpp Premove Premove]
      rules_sound[of dpp'] by auto
  have sub: "set (pairs dpp) - S \<subseteq>
      set (pairs dpp) - set Premove"
    using strict_S unfolding ps by auto
  have fin_S: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (pairs dpp) - S) (set (rules dpp))"
    by (rule finite_min_csr_dpp_mono_pairs[OF sub fin[unfolded pairs' rules']])
  show ?thesis
  proof (cases "csr_sharp_pairs_check (pairs dpp)")
    case True
    have shape_sem: "\<forall>(u, v)\<in>set (pairs dpp).
        (\<exists>f us. u = Fun (Sharp f) us) \<and>
        (\<exists>g vs. v = Fun (Sharp g) vs)"
      by (rule csr_sharp_pairs_check_sound[OF True])
    show ?thesis
      by (rule finite_min_csr_dpp_u3_redpair[
          OF wf closed_sem fresh marked_mu redpair orient shape_sem
            U_NS ce_NS fin_S])
  next
    case False
    with shape have mixed: "csr_u3_mixed_pairs_check
        (rules dpp) (pairs dpp)"
      by simp
    from csr_u3_mixed_pairs_check_sound[OF mixed]
    obtain H where fresh_H: "\<And>n. \<not> defined (set (rules dpp)) (H, n)"
      and unsharp: "\<not> is_sharp_lab H"
      and shape_sem: "\<forall>(u, v)\<in>set (pairs dpp).
        csr_u3_mixed_term_shape H u \<and>
        csr_u3_mixed_term_shape H v"
      by blast
    show ?thesis
      by (rule finite_min_csr_dpp_mixed_u3_redpair[
          OF wf closed_sem fresh fresh_H unsharp marked_mu redpair orient
            shape_sem U_NS ce_NS fin_S])
  qed
qed

theorem finite_min_csr_dpp_sct_active_subterm:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f, n)"
    and pair_shape: "\<forall>(u, v)\<in>P.
      (\<exists>f us. u = Fun (Sharp f) us) \<and>
      (\<exists>g vs. v = Fun (Sharp g) vs)"
    and graphs: "\<forall>(u, v)\<in>P. \<exists>stri nstri.
      Scg (info (u, v)) (info (u, v))
        (remdups_sort stri) (remdups_sort nstri) \<in> set Gs \<and>
      (\<forall>(i, j)\<in>set stri.
        csr_sct_active_index \<mu> u i \<and>
        csr_sct_index v j \<and>
        mu_supt \<mu> (get_arg u i) (get_arg v j)) \<and>
      (\<forall>(i, j)\<in>set nstri.
        csr_sct_index u i \<and> csr_sct_index v j \<and>
        (get_arg u i = get_arg v j \<or>
          (csr_sct_active_index \<mu> u i \<and>
            mu_supt \<mu> (get_arg u i) (get_arg v j))))"
    and edge: "\<And>s t \<sigma> u v \<tau>.
      (s, t) \<in> P \<Longrightarrow> (u, v) \<in> P \<Longrightarrow>
      (t \<cdot> \<sigma>, u \<cdot> \<tau>) \<in> (csdp_step Sharp \<mu> R)\<^sup>* \<Longrightarrow>
      edg (info (s, t)) (info (u, v))"
    and check: "check_SCT edg Gs"
  shows "finite_min_csr_dpp Sharp \<mu> P R"
proof (rule ccontr)
  assume not_fin: "\<not> finite_min_csr_dpp Sharp \<mu> P R"
  from not_finite_min_csr_dpp_obtain_chain[OF not_fin]
  obtain s t \<sigma> where pair: "\<forall>k. (s k, t k) \<in> P"
    and target_SN:
      "\<forall>k. SN_on (csdp_step Sharp \<mu> R) {t k \<cdot> \<sigma> k}"
    and steps:
      "\<forall>k. (t k \<cdot> \<sigma> k, s (Suc k) \<cdot> \<sigma> (Suc k)) \<in>
        (csdp_step Sharp \<mu> R)\<^sup>*"
    by auto
  have chain_edge:
    "edg (info (s k, t k)) (info (s (Suc k), t (Suc k)))"
    for k
    by (rule edge[OF pair[rule_format] pair[rule_format] steps[rule_format]])
  show False
  proof (rule csr_sct_with_active_subterm[
      where s = s and t = t and \<sigma> = \<sigma> and P = P and R = R
        and \<mu> = \<mu> and info = info and Gs = Gs and edg = edg])
    show "wf_trs R" by (rule wf)
    show "\<And>f n. \<not> defined R (Sharp f, n)" by (rule fresh)
    show "\<And>k. (s k, t k) \<in> P" by (rule pair[rule_format])
    show "\<forall>(u, v)\<in>P.
      (\<exists>f us. u = Fun (Sharp f) us) \<and>
      (\<exists>g vs. v = Fun (Sharp g) vs)"
      by (rule pair_shape)
    show "\<And>k. SN_on (csdp_step Sharp \<mu> R) {t k \<cdot> \<sigma> k}"
      by (rule target_SN[rule_format])
    show "\<And>k. (t k \<cdot> \<sigma> k, s (Suc k) \<cdot> \<sigma> (Suc k)) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>*"
      by (rule steps[rule_format])
    show "\<forall>(u, v)\<in>P. \<exists>stri nstri.
      Scg (info (u, v)) (info (u, v))
        (remdups_sort stri) (remdups_sort nstri) \<in> set Gs \<and>
      (\<forall>(i, j)\<in>set stri.
        csr_sct_active_index \<mu> u i \<and>
        csr_sct_index v j \<and>
        mu_supt \<mu> (get_arg u i) (get_arg v j)) \<and>
      (\<forall>(i, j)\<in>set nstri.
        csr_sct_index u i \<and> csr_sct_index v j \<and>
        (get_arg u i = get_arg v j \<or>
          (csr_sct_active_index \<mu> u i \<and>
            mu_supt \<mu> (get_arg u i) (get_arg v j))))"
      by (rule graphs)
    show "\<And>k. edg (info (s k, t k))
      (info (s (Suc k), t (Suc k)))"
      by (rule chain_edge)
    show "check_SCT edg Gs" by (rule check)
  qed
qed

lemma csr_dep_graph_edge_check_steps:
  fixes R :: "((('f::{showl, compare_order}, 'l::{showl, compare_order}) lab),
    'v::compare_order) rules"
  assumes wf: "wf_trs (set R)"
    and steps: "(t \<cdot> \<sigma>, u \<cdot> \<tau>) \<in>
      (csdp_step Sharp \<mu> (set R))\<^sup>*"
  shows "csr_dep_graph_edge_check (csr_dp_root_mu \<mu>) R
    ((((s, t), ()), ((u, v), ())))"
proof (simp, intro conjI notI)
  assume no: "csr_inactive_arg_no_edge (csr_dp_root_mu \<mu>) R t u"
  from csr_inactive_arg_no_edge_sound[OF wf no, of \<sigma> \<tau>] steps
  show False by contradiction
next
  assume no: "csr_frozen_root_no_edge (csr_dp_root_mu \<mu>) R t u"
  from csr_frozen_root_no_edge_sound[OF wf no, of \<sigma> \<tau>] steps
  show False by contradiction
next
  assume no: "csr_tcap_no_edge R t u"
  from csr_tcap_no_edge_sound[OF no, of \<sigma> \<tau>] steps
  show False by contradiction
next
  assume no: "csr_reverse_tcap_no_edge R t u"
  from csr_reverse_tcap_no_edge_sound[OF no, of \<sigma> \<tau>] steps
  show False by contradiction
next
  assume no: "csr_root_tcap_no_edge (csr_dp_root_mu \<mu>) R t u"
  from csr_root_tcap_no_edge_sound[OF wf no, of \<sigma> \<tau>] steps
  show False by contradiction
next
  assume no:
    "csr_shared_inactive_arg_no_edge (csr_dp_root_mu \<mu>) R t u"
  from csr_shared_inactive_arg_no_edge_sound[OF wf no, of \<sigma> \<tau>] steps
  show False by contradiction
next
  assume no:
    "csr_shared_source_inactive_arg_no_edge
      (csr_dp_root_mu \<mu>) R t u"
  from csr_shared_source_inactive_arg_no_edge_sound[
    OF wf no, of \<sigma> \<tau>] steps
  show False by contradiction
qed

fun csr_sct_sharp_term where
  "csr_sct_sharp_term (Fun (Sharp f) ts) = True"
| "csr_sct_sharp_term t = False"

fun csr_sct_active_index_check where
  "csr_sct_active_index_check \<mu> (Fun (Sharp f) ts) i =
    (0 < i \<and> i \<le> length ts \<and>
      i - 1 \<in> mu_of \<mu> (f, length ts))"
| "csr_sct_active_index_check \<mu> t i = False"

fun csr_sct_index_check where
  "csr_sct_index_check (Fun (Sharp f) ts) i =
    (0 < i \<and> i \<le> length ts)"
| "csr_sct_index_check t i = False"

lemma csr_sct_index_check_iff [simp]:
  "csr_sct_index_check t i = csr_sct_index t i"
proof (cases t)
  case (Var x)
  then show ?thesis by simp
next
  case (Fun f ts)
  show ?thesis
  proof (cases f)
    case (Sharp g)
    then show ?thesis using Fun by (cases i, auto)
  qed (use Fun in auto)
qed

lemma csr_sct_active_index_check_iff [simp]:
  "csr_sct_active_index_check \<mu> t i =
    csr_sct_active_index (mu_of \<mu>) t i"
proof (cases t)
  case (Var x)
  then show ?thesis by simp
next
  case (Fun f ts)
  show ?thesis
  proof (cases f)
    case (Sharp g)
    then show ?thesis
      using Fun by (cases i, auto)
  qed (use Fun in auto)
qed

lemma csr_sct_sharp_term_iff [simp]:
  "csr_sct_sharp_term t \<longleftrightarrow> (\<exists>f ts. t = Fun (Sharp f) ts)"
proof (cases t)
  case (Var x)
  then show ?thesis by simp
next
  case (Fun f ts)
  then show ?thesis by (cases f, auto)
qed

definition csr_sct_active_subterm_proc ::
  "('dpp, (('f::{showl, compare_order}, 'l::{showl, compare_order}) lab),
      string) dpp_ops \<Rightarrow>
   (('f, 'l) lab) muL \<Rightarrow>
   (((('f, 'l) lab), string) rule \<times>
      ((nat \<times> nat) list \<times> (nat \<times> nat) list)) list \<Rightarrow>
   'dpp \<Rightarrow> showsl check"
where
  "csr_sct_active_subterm_proc J \<mu> Gs dpp = do {
    let P = dpp_ops.pairs J dpp;
    let R = dpp_ops.rules J dpp;
    check_subseteq P (map fst Gs)
      <+? (\<lambda>st. showsl_lit
        (STR ''there is no CSR size-change graph for pair '')
        \<circ> showsl_rule st);
    let GGs = filter (\<lambda>G. fst G \<in> set P) Gs;
    check_allm (\<lambda>((s, t), (stri, nstri)). do {
      check (csr_sct_sharp_term s \<and> csr_sct_sharp_term t)
        (showsl_lit (STR ''CSR size-change pair is not sharp-rooted''));
      check_allm (\<lambda>(i, j). check
        (csr_sct_active_index_check \<mu> s i \<and>
         csr_sct_index_check t j \<and>
         get_arg t j \<in> set (mu_supt_list \<mu> (get_arg s i)))
        (showsl_lit (STR ''invalid strict CSR size-change edge''))) stri;
      check_allm (\<lambda>(i, j). check
        (csr_sct_index_check s i \<and> csr_sct_index_check t j \<and>
         (get_arg s i = get_arg t j \<or>
          (csr_sct_active_index_check \<mu> s i \<and>
           get_arg t j \<in> set (mu_supt_list \<mu> (get_arg s i)))))
        (showsl_lit (STR ''invalid non-strict CSR size-change edge'')))
        nstri
    }) GGs;
    let conn = (\<lambda>st uv. csr_dep_graph_edge_check
      (csr_dp_root_mu (mu_of \<mu>)) R ((st, ()), (uv, ())));
    check (check_SCT conn
      (map (\<lambda>(st, (stri, nstri)).
        Scg st st (remdups_sort stri) (remdups_sort nstri)) GGs))
      (showsl_lit (STR ''CSR size-change analysis failed''))
  }"

lemma csr_sct_active_subterm_proc_sound:
  assumes J: "dpp_spec J"
    and wf: "wf_trs (set (dpp_ops.rules J dpp))"
    and fresh: "\<And>f n.
      \<not> defined (set (dpp_ops.rules J dpp)) (Sharp f, n)"
    and ok: "isOK (csr_sct_active_subterm_proc J \<mu> Gs dpp)"
  shows "finite_min_csr_dpp Sharp (mu_of \<mu>)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
proof -
  interpret dpp_spec J by fact
  let ?P = "set (pairs dpp)"
  let ?RL = "rules dpp"
  let ?R = "set ?RL"
  define GGs where "GGs = filter (\<lambda>G. fst G \<in> ?P) Gs"
  let ?conn = "\<lambda>st uv. csr_dep_graph_edge_check
    (csr_dp_root_mu (mu_of \<mu>)) ?RL ((st, ()), (uv, ()))"
  let ?SGs = "map (\<lambda>(st, (stri, nstri)).
    Scg st st (remdups_sort stri) (remdups_sort nstri)) GGs"
  let ?validate = "\<lambda>((s, t), (stri, nstri)). do {
    check (csr_sct_sharp_term s \<and> csr_sct_sharp_term t)
      (showsl_lit (STR ''CSR size-change pair is not sharp-rooted''));
    check_allm (\<lambda>(i, j). check
      (csr_sct_active_index_check \<mu> s i \<and>
       csr_sct_index_check t j \<and>
       get_arg t j \<in> set (mu_supt_list \<mu> (get_arg s i)))
      (showsl_lit (STR ''invalid strict CSR size-change edge''))) stri;
    check_allm (\<lambda>(i, j). check
      (csr_sct_index_check s i \<and> csr_sct_index_check t j \<and>
       (get_arg s i = get_arg t j \<or>
        (csr_sct_active_index_check \<mu> s i \<and>
         get_arg t j \<in> set (mu_supt_list \<mu> (get_arg s i)))))
      (showsl_lit (STR ''invalid non-strict CSR size-change edge'')))
      nstri
  }"
  note ok' = ok[unfolded csr_sct_active_subterm_proc_def Let_def,
    folded GGs_def]
  from ok' have cover: "?P \<subseteq> set (map fst Gs)"
    by auto
  from ok' have valid_ok: "isOK (check_allm ?validate GGs)"
    by auto
  have valid_one:
    "csr_sct_sharp_term s \<and> csr_sct_sharp_term t \<and>
      (\<forall>(i, j)\<in>set stri.
        csr_sct_active_index (mu_of \<mu>) s i \<and>
        csr_sct_index t j \<and>
        mu_supt (mu_of \<mu>) (get_arg s i) (get_arg t j)) \<and>
      (\<forall>(i, j)\<in>set nstri.
        csr_sct_index s i \<and> csr_sct_index t j \<and>
        (get_arg s i = get_arg t j \<or>
         (csr_sct_active_index (mu_of \<mu>) s i \<and>
          mu_supt (mu_of \<mu>) (get_arg s i) (get_arg t j))))"
    if mem: "((s, t), (stri, nstri)) \<in> set GGs"
    for s t stri nstri
  proof -
    from valid_ok have all:
      "\<forall>x\<in>set GGs. isOK (?validate x)"
      by (rule iffD1[OF isOK_check_allm])
    have one: "isOK (?validate ((s, t), (stri, nstri)))"
      by (rule all[rule_format, OF mem])
    from one show ?thesis
      by (simp add: isOK_check_allm isOK_check)
  qed
  have valid:
      "\<forall>((s, t), (stri, nstri))\<in>set GGs.
        csr_sct_sharp_term s \<and> csr_sct_sharp_term t \<and>
        (\<forall>(i, j)\<in>set stri.
          csr_sct_active_index (mu_of \<mu>) s i \<and>
          csr_sct_index t j \<and>
          mu_supt (mu_of \<mu>) (get_arg s i) (get_arg t j)) \<and>
        (\<forall>(i, j)\<in>set nstri.
          csr_sct_index s i \<and> csr_sct_index t j \<and>
          (get_arg s i = get_arg t j \<or>
           (csr_sct_active_index (mu_of \<mu>) s i \<and>
            mu_supt (mu_of \<mu>) (get_arg s i) (get_arg t j))))"
    using valid_one by blast
  from ok' have sct: "check_SCT ?conn ?SGs"
    by auto
  have shape: "\<forall>(u, v)\<in>?P.
    (\<exists>f us. u = Fun (Sharp f) us) \<and>
    (\<exists>g vs. v = Fun (Sharp g) vs)"
  proof clarify
    fix u v
    assume uv: "(u, v) \<in> ?P"
    from cover uv obtain stri nstri where
      mem: "((u, v), (stri, nstri)) \<in> set Gs"
      by auto
    have mem': "((u, v), (stri, nstri)) \<in> set GGs"
      using mem uv unfolding GGs_def by simp
    from valid[rule_format, OF mem']
    show "(\<exists>f us. u = Fun (Sharp f) us) \<and>
      (\<exists>g vs. v = Fun (Sharp g) vs)"
      by simp
  qed
  have graph: "\<forall>(u, v)\<in>?P. \<exists>stri nstri.
    Scg (u, v) (u, v)
      (remdups_sort stri) (remdups_sort nstri) \<in> set ?SGs \<and>
    (\<forall>(i, j)\<in>set stri.
      csr_sct_active_index (mu_of \<mu>) u i \<and>
      csr_sct_index v j \<and>
      mu_supt (mu_of \<mu>) (get_arg u i) (get_arg v j)) \<and>
    (\<forall>(i, j)\<in>set nstri.
      csr_sct_index u i \<and> csr_sct_index v j \<and>
      (get_arg u i = get_arg v j \<or>
       (csr_sct_active_index (mu_of \<mu>) u i \<and>
        mu_supt (mu_of \<mu>) (get_arg u i) (get_arg v j))))"
  proof clarify
    fix u v
    assume uv: "(u, v) \<in> ?P"
    from cover uv obtain stri nstri where
      mem: "((u, v), (stri, nstri)) \<in> set Gs"
      by auto
    have mem': "((u, v), (stri, nstri)) \<in> set GGs"
      using mem uv unfolding GGs_def by simp
    have graph_mem:
      "Scg (u, v) (u, v) (remdups_sort stri) (remdups_sort nstri)
        \<in> set ?SGs"
      using mem' by force
    from valid[rule_format, OF mem']
    have strict:
      "\<forall>(i, j)\<in>set stri.
        csr_sct_active_index (mu_of \<mu>) u i \<and>
        csr_sct_index v j \<and>
        mu_supt (mu_of \<mu>) (get_arg u i) (get_arg v j)"
      and nonstrict:
      "\<forall>(i, j)\<in>set nstri.
        csr_sct_index u i \<and> csr_sct_index v j \<and>
        (get_arg u i = get_arg v j \<or>
         (csr_sct_active_index (mu_of \<mu>) u i \<and>
          mu_supt (mu_of \<mu>) (get_arg u i) (get_arg v j)))"
      by auto
    show "\<exists>stri nstri.
      Scg (u, v) (u, v)
        (remdups_sort stri) (remdups_sort nstri) \<in> set ?SGs \<and>
      (\<forall>(i, j)\<in>set stri.
        csr_sct_active_index (mu_of \<mu>) u i \<and>
        csr_sct_index v j \<and>
        mu_supt (mu_of \<mu>) (get_arg u i) (get_arg v j)) \<and>
      (\<forall>(i, j)\<in>set nstri.
        csr_sct_index u i \<and> csr_sct_index v j \<and>
        (get_arg u i = get_arg v j \<or>
         (csr_sct_active_index (mu_of \<mu>) u i \<and>
          mu_supt (mu_of \<mu>) (get_arg u i) (get_arg v j))))"
      by (intro exI[of _ stri] exI[of _ nstri],
        use graph_mem strict nonstrict in auto)
  qed
  have edge: "?conn (s, t) (u, v)"
    if "(s, t) \<in> ?P" "(u, v) \<in> ?P"
      "(t \<cdot> \<sigma>, u \<cdot> \<tau>) \<in>
        (csdp_step Sharp (mu_of \<mu>) ?R)\<^sup>*"
    for s t u v \<sigma> \<tau>
    unfolding Let_def
    by (rule csr_dep_graph_edge_check_steps[OF wf that(3)])
  show ?thesis
    by (rule finite_min_csr_dpp_sct_active_subterm[
      where info = "\<lambda>x. x" and Gs = ?SGs and edg = ?conn,
      OF wf fresh shape graph edge sct])
qed

lemma check_csr_dep_graph_proc_min_sound:
  assumes J: "dpp_spec J"
    and plain: "plain_csr_dpp J dpp"
    and check: "isOK (check_csr_dep_graph_proc J \<mu> dpp edps)"
    and fin: "\<And>prf C. (Some prf, C) \<in> set edps \<Longrightarrow>
      finite_min_csr_dpp Sharp (mu_of \<mu>)
        (set (dpp_ops.pairs J dpp) \<inter> set C)
        (set (dpp_ops.rules J dpp))"
  shows "finite_min_csr_dpp Sharp (mu_of \<mu>)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
proof (rule ccontr)
  interpret dpp_spec J by fact
  let ?P = "set (pairs dpp)"
  let ?RL = "rules dpp"
  let ?R = "set ?RL"
  let ?S = "csdp_step Sharp (mu_of \<mu>) ?R"
  let ?echeck = "csr_dep_graph_edge_check (csr_dp_root_mu (mu_of \<mu>)) ?RL"
  let ?conv = "\<lambda>(real, Cs).
    (real \<noteq> None, map (\<lambda>(s,t). ((s,t), ())) Cs)"
  assume not_fin: "\<not> finite_min_csr_dpp Sharp (mu_of \<mu>) ?P ?R"
  from not_finite_min_csr_dpp_obtain_chain[OF not_fin]
  obtain s t \<sigma> where pair: "\<And>i. (s i, t i) \<in> ?P"
    and target_SN: "\<And>i. SN_on ?S {t i \<cdot> \<sigma> i}"
    and steps: "\<And>i. (t i \<cdot> \<sigma> i,
      s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?S\<^sup>*"
    by blast
  from check have wf: "wf_trs ?R"
    and subset: "?P \<subseteq> set (concat (map snd edps))"
    and scc: "isOK (check_graph_decomp (showsl \<circ> fst)
      (Multi_Map.empty (root o fst o fst))
      graph_approx_csr_rt Multi_Map.insert ?echeck (map ?conv edps))"
    unfolding check_csr_dep_graph_proc_def
    by (auto simp: Let_def)
  let ?p = "\<lambda>i. ((s i, t i), ())"
  have path: "\<And>i. ?echeck (?p i, ?p (Suc i))"
    by (rule csr_dep_graph_edge_check_steps[OF wf steps])
  have lift_node: "\<And>l r.
      (l, r) \<in> set (concat (map snd edps)) \<Longrightarrow>
      ((l, r), ()) \<in> set (concat (map snd (map ?conv edps)))"
  proof -
    fix l r
    assume lr: "(l, r) \<in> set (concat (map snd edps))"
    then obtain x where x: "x \<in> set edps"
      and lrx: "(l, r) \<in> set (snd x)"
      by auto
    obtain real Cs where xeq: "x = (real, Cs)"
      by (cases x, auto)
    have node: "((l, r), ()) \<in>
      set (map (\<lambda>(s,t). ((s,t), ())) Cs)"
      using lrx xeq by force
    have conv_mem: "?conv (real, Cs) \<in> set (map ?conv edps)"
      using x xeq by (auto split: prod.splits)
    have comp_mem: "snd (?conv (real, Cs)) \<in>
      set (map snd (map ?conv edps))"
      using conv_mem unfolding set_map by blast
    have node': "((l, r), ()) \<in> set (snd (?conv (real, Cs)))"
      using node by simp
    show "((l, r), ()) \<in> set (concat (map snd (map ?conv edps)))"
      using comp_mem node' unfolding set_concat by blast
  qed
  have nodes: "path_nodes ?p \<subseteq>
      set (concat (map snd (map ?conv edps)))"
  proof
    fix x
    assume "x \<in> path_nodes ?p"
    then obtain i where x: "x = ?p i"
      unfolding path_nodes_def by auto
    from pair[of i] subset
    have "(s i, t i) \<in> set (concat (map snd edps))"
      by auto
    then show "x \<in> set (concat (map snd (map ?conv edps)))"
      unfolding x by (rule lift_node)
  qed
  have key_insert: "\<And>x m.
      Multi_Map.key_fun m = root \<circ> fst \<circ> fst \<Longrightarrow>
      Multi_Map.key_fun (Multi_Map.insert x m) = root \<circ> fst \<circ> fst"
    by simp
  have approx: "\<And>m a b.
      Multi_Map.key_fun m = root \<circ> fst \<circ> fst \<Longrightarrow>
      ?echeck (a, b) \<Longrightarrow> b \<in> set (Multi_Map.values m) \<Longrightarrow>
      b \<in> set (graph_approx_csr_rt m a)"
    unfolding graph_approx_csr_rt.simps by simp
  have component:
    "\<exists>q C. ?p =\<dots> q \<and>
      C \<in> set (map snd (filter fst (map ?conv edps))) \<and>
      path_nodes q \<subseteq> set C"
    by (rule check_graph_decomp_sound[
      of "\<lambda>m. set (Multi_Map.values m)",
      OF values_empty values_insert,
      of "\<lambda>m. Multi_Map.key_fun m = (root o fst o fst)",
      OF key_fun_empty key_insert approx scc path nodes])
  from component obtain q C where suffix: "?p =\<dots> q"
    and ending: "path_nodes q \<subseteq> set C"
    and component_mem:
      "C \<in> set (map snd (filter fst (map ?conv edps)))"
    by blast
  from component_mem obtain p0 Cs where
    mem: "(Some p0, Cs) \<in> set edps"
    and C: "C = map (\<lambda>(s,t). ((s,t), ())) Cs"
    by force
  from suffix obtain n where pq: "\<And>m. ?p (m + n) = q m"
    unfolding Graph.suffix_def by blast
  have CP: "\<And>m. (s (m + n), t (m + n)) \<in> ?P \<inter> set Cs"
  proof -
    fix m
    have "?p (m + n) \<in> path_nodes q"
      using pq[of m] unfolding path_nodes_def by blast
    with ending C pair[of "m + n"]
    show "(s (m + n), t (m + n)) \<in> ?P \<inter> set Cs"
      by force
  qed
  let ?tail = "\<lambda>m. s (m + n) \<cdot> \<sigma> (m + n)"
  let ?A = "csr_min_pair_step Sharp (mu_of \<mu>) (?P \<inter> set Cs) ?R"
  have tail_chain: "\<And>m. (?tail m, ?tail (Suc m)) \<in>
      ?S\<^sup>* O ?A O ?S\<^sup>*"
  proof -
    fix m
    have rr: "(s (m + n) \<cdot> \<sigma> (m + n),
        t (m + n) \<cdot> \<sigma> (m + n)) \<in>
        rrstep (?P \<inter> set Cs)"
      by (rule rrstepI[OF CP[of m] refl refl])
    have strict: "(s (m + n) \<cdot> \<sigma> (m + n),
        t (m + n) \<cdot> \<sigma> (m + n)) \<in> ?A"
      using rr target_SN[of "m + n"]
      unfolding csr_min_pair_step_def by auto
    have suc_add: "Suc m + n = Suc (m + n)"
      by simp
    show "(?tail m, ?tail (Suc m)) \<in> ?S\<^sup>* O ?A O ?S\<^sup>*"
      using strict steps[of "m + n"] unfolding suc_add by auto
  qed
  have tail_is_chain: "chain (?S\<^sup>* O ?A O ?S\<^sup>*) ?tail"
    using tail_chain by simp
  have tail_sn: "SN (?S\<^sup>* O ?A O ?S\<^sup>*)"
    using fin[OF mem]
    unfolding finite_min_csr_dpp_def SN_rel_on_def .
  have "\<not> SN (?S\<^sup>* O ?A O ?S\<^sup>*)"
    by (rule not_SN_onI[of ?tail], simp, rule tail_is_chain)
  with tail_sn show False by contradiction
qed

fun csr_instantiation_cap where
  "csr_instantiation_cap \<mu> R (Var x) = GCHole"
| "csr_instantiation_cap \<mu> R (Fun f ts) =
    csr_root_tcap (csr_dp_root_mu \<mu>) R (Fun f ts)"

lemma csr_instantiation_cap_steps:
  fixes R :: "((('f::{showl, compare_order}, 'l::{showl, compare_order}) lab), string) rules"
  assumes wf: "wf_trs (set R)"
    and undef: "case root v of None \<Rightarrow> True
      | Some fn \<Rightarrow> fn \<notin> set (defined_list R)"
    and steps: "(v \<cdot> \<sigma>, s \<cdot> \<tau>) \<in>
      (csdp_step Sharp \<mu> (set R))\<^sup>*"
  shows "s \<cdot> \<tau> \<in> Ground_Context.equiv_class
    (csr_instantiation_cap \<mu> R v)"
proof (cases v)
  case (Var x)
  then show ?thesis by simp
next
  case (Fun f ts)
  from undef Fun have undef':
    "\<not> defined (set R) (f, length ts)"
    using set_defined_list by force
  from csr_root_tcap_steps[
    where R = R and f = f and ts = ts and \<sigma> = \<sigma>
      and u = s and \<tau> = \<tau> and \<mu> = \<mu>,
    OF wf undef' steps[unfolded Fun]]
  show ?thesis unfolding Fun by simp
qed

theorem finite_min_csr_dpp_csr_instantiation:
  fixes P R sts :: "((('f::{showl, compare_order}, 'l::{showl, compare_order}) lab), string) trs"
    and RL :: "((('f, 'l) lab), string) rules"
  assumes wf: "wf_trs R"
    and rules: "set RL = R"
    and undef: "\<And>u v. (u,v) \<in> P \<Longrightarrow>
      (case root v of None \<Rightarrow> True
       | Some fn \<Rightarrow> \<not> defined R fn)"
    and instances: "\<And>st'. st' \<in> sts \<Longrightarrow> instance_rule st' (s,t)"
    and cover: "\<And>u v \<gamma>. (u,v) \<in> P \<Longrightarrow>
      gc_matcher (csr_instantiation_cap \<mu> RL v) s =
        Some \<gamma> \<Longrightarrow>
      \<exists>st'\<in>sts. instance_rule (s \<cdot> \<gamma>, t \<cdot> \<gamma>) st'"
    and fin: "finite_min_csr_dpp Sharp \<mu> (replace (s,t) sts P) R"
  shows "finite_min_csr_dpp Sharp \<mu> P R"
proof (rule ccontr)
  assume not_fin: "\<not> finite_min_csr_dpp Sharp \<mu> P R"
  from not_finite_min_csr_dpp_obtain_chain[OF not_fin]
  obtain si ti \<sigma> where
    pair: "\<And>k. (si k, ti k) \<in> P"
    and target_SN: "\<And>k. SN_on (csdp_step Sharp \<mu> R) {ti k \<cdot> \<sigma> k}"
    and steps: "\<And>k. (ti k \<cdot> \<sigma> k,
      si (Suc k) \<cdot> \<sigma> (Suc k)) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>*"
    by blast
  let ?RL = "RL"
  have replacement:
    "\<forall>k. \<exists>s' t' \<tau>.
      (s',t') \<in> replace (s,t) sts P \<and>
      si (Suc k) \<cdot> \<sigma> (Suc k) = s' \<cdot> \<tau> \<and>
      ti (Suc k) \<cdot> \<sigma> (Suc k) = t' \<cdot> \<tau>"
  proof
    fix k
    show "\<exists>s' t' \<tau>.
      (s',t') \<in> replace (s,t) sts P \<and>
      si (Suc k) \<cdot> \<sigma> (Suc k) = s' \<cdot> \<tau> \<and>
      ti (Suc k) \<cdot> \<sigma> (Suc k) = t' \<cdot> \<tau>"
    proof (cases "(si (Suc k), ti (Suc k)) = (s,t)")
      case False
      have neq: "(si (Suc k), ti (Suc k)) \<noteq> (s,t)"
        by fact
      have not_singleton: "(si (Suc k), ti (Suc k)) \<notin> {(s,t)}"
        using neq by simp
      show ?thesis
      proof (intro exI conjI)
        show "(si (Suc k), ti (Suc k)) \<in> replace (s,t) sts P"
        proof (cases "(s,t) \<in> P")
          case True
          note selected_mem = True
          have in_diff:
            "(si (Suc k), ti (Suc k)) \<in> P - {(s,t)}"
            using pair[of "Suc k"] not_singleton by blast
          have rep: "replace (s,t) sts P = P - {(s,t)} \<union> sts"
            unfolding Util.replace_def
            apply (rule if_P)
            apply (rule selected_mem)
            done
          show ?thesis
            unfolding rep by (rule UnI1[OF in_diff])
        next
          case False
          with pair[of "Suc k"] show ?thesis
            unfolding Util.replace_def by simp
        qed
      qed simp_all
    next
      case True
      then have si: "si (Suc k) = s" and ti: "ti (Suc k) = t"
        by auto
      have set_RL: "set ?RL = R"
        by (rule rules)
      have undef_k:
        "case root (ti k) of None \<Rightarrow> True
         | Some fn \<Rightarrow> fn \<notin> set (defined_list ?RL)"
      proof (cases "root (ti k)")
        case None
        then show ?thesis by simp
      next
        case (Some fn)
        from undef[OF pair[of k]] Some
        have "\<not> defined R fn"
          by simp
        with Some set_RL show ?thesis
          by simp
      qed
      have wf_RL: "wf_trs (set ?RL)"
        using wf set_RL by simp
      have steps_k:
        "(ti k \<cdot> \<sigma> k, s \<cdot> \<sigma> (Suc k)) \<in>
          (csdp_step Sharp \<mu> (set ?RL))\<^sup>*"
        using steps[of k] unfolding si set_RL .
      from csr_instantiation_cap_steps[
        where R = ?RL and v = "ti k" and \<sigma> = "\<sigma> k"
          and s = s and \<tau> = "\<sigma> (Suc k)" and \<mu> = \<mu>,
        OF wf_RL undef_k steps_k]
      have cap_mem:
        "s \<cdot> \<sigma> (Suc k) \<in> Ground_Context.equiv_class
          (csr_instantiation_cap \<mu> ?RL (ti k))"
        .
      from gc_matcher_complete[OF cap_mem]
      obtain \<gamma> \<delta> where
        matcher:
          "gc_matcher (csr_instantiation_cap \<mu> ?RL (ti k)) s =
            Some \<gamma>"
        and sigma: "\<sigma> (Suc k) = \<gamma> \<circ>\<^sub>s \<delta>"
        by blast
      from cover[OF pair[of k] matcher]
      obtain s' t' where st': "(s',t') \<in> sts"
        and covered: "instance_rule (s \<cdot> \<gamma>, t \<cdot> \<gamma>) (s',t')"
        by auto
      from covered[unfolded instance_rule_def]
      obtain \<rho> where rho:
        "s \<cdot> \<gamma> = s' \<cdot> \<rho>" "t \<cdot> \<gamma> = t' \<cdot> \<rho>"
        by auto
      have selected_mem: "(s,t) \<in> P"
        using pair[of "Suc k"] True by simp
      have member: "(s',t') \<in> replace (s,t) sts P"
        using st' selected_mem unfolding Util.replace_def by simp
      have eq_s: "si (Suc k) \<cdot> \<sigma> (Suc k) =
          s' \<cdot> (\<rho> \<circ>\<^sub>s \<delta>)"
        using rho(1) unfolding si sigma by simp
      have eq_t: "ti (Suc k) \<cdot> \<sigma> (Suc k) =
          t' \<cdot> (\<rho> \<circ>\<^sub>s \<delta>)"
        using rho(2) unfolding ti sigma by simp
      show ?thesis
        using member eq_s eq_t by blast
    qed
  qed
  from choice[OF replacement]
  obtain si' where one:
    "\<forall>k. \<exists>t' \<tau>.
      (si' k,t') \<in> replace (s,t) sts P \<and>
      si (Suc k) \<cdot> \<sigma> (Suc k) = si' k \<cdot> \<tau> \<and>
      ti (Suc k) \<cdot> \<sigma> (Suc k) = t' \<cdot> \<tau>"
    by auto
  from choice[OF one]
  obtain ti' where two:
    "\<forall>k. \<exists>\<tau>.
      (si' k,ti' k) \<in> replace (s,t) sts P \<and>
      si (Suc k) \<cdot> \<sigma> (Suc k) = si' k \<cdot> \<tau> \<and>
      ti (Suc k) \<cdot> \<sigma> (Suc k) = ti' k \<cdot> \<tau>"
    by auto
  from choice[OF two]
  obtain \<tau> where transformed:
    "\<And>k. (si' k,ti' k) \<in> replace (s,t) sts P"
    "\<And>k. si (Suc k) \<cdot> \<sigma> (Suc k) = si' k \<cdot> \<tau> k"
    "\<And>k. ti (Suc k) \<cdot> \<sigma> (Suc k) = ti' k \<cdot> \<tau> k"
    by auto
  let ?S = "csdp_step Sharp \<mu> R"
  let ?M = "csr_min_pair_step Sharp \<mu> (replace (s,t) sts P) R"
  let ?g = "\<lambda>k. si' k \<cdot> \<tau> k"
  have min_pair: "(si' k \<cdot> \<tau> k, ti' k \<cdot> \<tau> k) \<in> ?M"
    for k
    unfolding csr_min_pair_step_def rrstep_def'
    using transformed(1)[of k] target_SN[of "Suc k"] transformed(3)[of k]
    by auto
  have bridge: "(ti' k \<cdot> \<tau> k, si' (Suc k) \<cdot> \<tau> (Suc k))
      \<in> ?S\<^sup>*"
    for k
    using steps[of "Suc k"] transformed(3)[of k]
      transformed(2)[of "Suc k"] by auto
  have g_step: "(?g k, ?g (Suc k)) \<in> ?S\<^sup>* O ?M O ?S\<^sup>*"
    for k
    using min_pair[of k] bridge[of k] by auto
  have g_chain: "chain (?S\<^sup>* O ?M O ?S\<^sup>*) ?g"
    using g_step by simp
  have not_SN': "\<not> SN_on (?S\<^sup>* O ?M O ?S\<^sup>*) UNIV"
    by (rule not_SN_onI[OF _ g_chain], simp)
  from fin have "SN_on (?S\<^sup>* O ?M O ?S\<^sup>*) UNIV"
    unfolding finite_min_csr_dpp_def SN_rel_on_def .
  with not_SN' show False by contradiction
qed

definition csr_instantiation_proc ::
  "('dpp, ('f::{showl, compare_order}, 'l::{showl, compare_order}) lab, string) dpp_ops \<Rightarrow>
   (('f, 'l) lab) muL \<Rightarrow>
   ((('f, 'l) lab), string) rule \<Rightarrow>
   ((('f, 'l) lab), string) rules \<Rightarrow> 'dpp proc"
where
  "csr_instantiation_proc J \<mu> st sts dpp =
    check_return (do {
      check (st \<in> set (dpp_ops.pairs J dpp))
        (showsl_lit (STR ''selected CS-DP is not present''));
      check_allm (\<lambda>st'. check (instance_rule st' st)
        (showsl_lit (STR ''supplied CS-DP is not an instance of the selected pair'') \<circ>
          showsl_rule st')) sts;
      let (s, t) = st;
      check_allm (\<lambda>(u, v).
        do {
          check (case root v of None \<Rightarrow> True
            | Some fn \<Rightarrow> fn \<notin> set (defined_list (dpp_ops.rules J dpp)))
            (showsl_lit (STR ''predecessor right-hand side has a defined root''));
          case gc_matcher
              (csr_instantiation_cap (mu_of \<mu>) (dpp_ops.rules J dpp) v) s of
            None \<Rightarrow> succeed
          | Some \<sigma> \<Rightarrow>
              check (\<exists>st'\<in>set sts.
                instance_rule (s \<cdot> \<sigma>, t \<cdot> \<sigma>) st')
                (showsl_lit (STR ''missing replacement-map-aware instance of pair '') \<circ>
                  showsl_rule (s \<cdot> \<sigma>, t \<cdot> \<sigma>))
        }) (dpp_ops.pairs J dpp)
    }) (dpp_ops.replace_pair J dpp st sts)"

lemma csr_instantiation_proc_sound:
  assumes proc: "csr_instantiation_proc J \<mu> st sts dpp = return dpp'"
  shows "dpp' = dpp_ops.replace_pair J dpp st sts"
    and "st \<in> set (dpp_ops.pairs J dpp)"
    and "\<And>st'. st' \<in> set sts \<Longrightarrow> instance_rule st' st"
    and "\<And>u v. (u,v) \<in> set (dpp_ops.pairs J dpp) \<Longrightarrow>
      (case root v of None \<Rightarrow> True
       | Some fn \<Rightarrow> fn \<notin> set (defined_list (dpp_ops.rules J dpp)))"
    and "\<And>s t u v \<sigma>. st = (s,t) \<Longrightarrow>
      (u,v) \<in> set (dpp_ops.pairs J dpp) \<Longrightarrow>
      gc_matcher
        (csr_instantiation_cap (mu_of \<mu>) (dpp_ops.rules J dpp) v) s =
          Some \<sigma> \<Longrightarrow>
      \<exists>st'\<in>set sts. instance_rule (s \<cdot> \<sigma>, t \<cdot> \<sigma>) st'"
proof -
  obtain s t where st: "st = (s,t)"
    by (cases st)
  let ?pred_check = "\<lambda>(u, v). do {
    check (case root v of None \<Rightarrow> True
      | Some fn \<Rightarrow> fn \<notin> set (defined_list (dpp_ops.rules J dpp)))
      (showsl_lit (STR ''predecessor right-hand side has a defined root''));
    case gc_matcher
        (csr_instantiation_cap (mu_of \<mu>) (dpp_ops.rules J dpp) v) s of
      None \<Rightarrow> succeed
    | Some \<sigma> \<Rightarrow>
        check (\<exists>st'\<in>set sts.
          instance_rule (s \<cdot> \<sigma>, t \<cdot> \<sigma>) st')
          (showsl_lit (STR ''missing replacement-map-aware instance of pair '') \<circ>
            showsl_rule (s \<cdot> \<sigma>, t \<cdot> \<sigma>))
  }"
  from proc[unfolded csr_instantiation_proc_def st]
  have result: "dpp' = dpp_ops.replace_pair J dpp (s,t) sts"
    and selected: "(s,t) \<in> set (dpp_ops.pairs J dpp)"
    and instances_ok: "isOK (check_allm (\<lambda>st'. check
      (instance_rule st' (s,t))
      (showsl_lit (STR ''supplied CS-DP is not an instance of the selected pair'') \<circ>
        showsl_rule st')) sts)"
    and predecessors_ok:
      "isOK (check_allm ?pred_check (dpp_ops.pairs J dpp))"
    by auto
  show "dpp' = dpp_ops.replace_pair J dpp st sts"
    using result st by simp
  show "st \<in> set (dpp_ops.pairs J dpp)"
    using selected st by simp
  show "\<And>st'. st' \<in> set sts \<Longrightarrow> instance_rule st' st"
    using instances_ok st
    by (auto simp: isOK_check_allm isOK_check)
  {
    fix u v
    assume mem: "(u,v) \<in> set (dpp_ops.pairs J dpp)"
    from predecessors_ok mem
    have one: "isOK (?pred_check (u,v))"
      by (auto simp: isOK_check_allm)
    have undef:
      "case root v of None \<Rightarrow> True
       | Some fn \<Rightarrow> fn \<notin> set (defined_list (dpp_ops.rules J dpp))"
      using one by (cases "root v"; simp add: isOK_check)
    show "case root v of None \<Rightarrow> True
       | Some fn \<Rightarrow> fn \<notin> set (defined_list (dpp_ops.rules J dpp))"
      by (rule undef)
    fix s' t' \<sigma>
    assume st': "st = (s',t')"
      and matcher:
        "gc_matcher
          (csr_instantiation_cap (mu_of \<mu>) (dpp_ops.rules J dpp) v) s' =
            Some \<sigma>"
    from st st' have s': "s' = s" and t': "t' = t"
      by auto
    from one undef matcher
    show "\<exists>st'\<in>set sts.
      instance_rule (s' \<cdot> \<sigma>, t' \<cdot> \<sigma>) st'"
      unfolding s' t'
      by (cases "root v"; simp add: isOK_check split: option.splits)
  }
qed

fun check_csr_dp_ordinary_min ::
  "('tp, ('f::{showl, compare_order,countable}, label_type) lab, string) tp_ops \<Rightarrow>
   ('dpp, ('f, label_type) lab, string) dpp_ops \<Rightarrow>
   (('f, label_type) lab) muL \<Rightarrow> bool \<Rightarrow>
   showsl \<Rightarrow> 'dpp \<Rightarrow>
   ('f, label_type, string) dp_termination_proof \<Rightarrow> showsl check"
where
  "check_csr_dp_ordinary_min I J \<mu> a i dpp prf =
    (case prf of
      Redpair_UR_Proc redp Pr U subprf \<Rightarrow>
        debug i (STR ''CSR U3 reduction pair'') (do {
          dpp' \<leftarrow> csr_u3_redpair_proc J \<mu> (get_rel_impl redp) Pr U dpp
            <+? (\<lambda>s. i \<circ> showsl_lit
              (STR '': error when applying CSR U3 reduction pair\<newline>'') \<circ> s);
          check_csr_dp_termination_proof_core I J \<mu> a (add_index i 1) dpp'
            (CSR_DP_Ordinary_Proof subprf)
            <+? (\<lambda>s. i \<circ> showsl_lit
              (STR '': error below CSR U3 reduction pair\<newline>'') \<circ> s)
        })
    | _ \<Rightarrow> check_csr_dp_termination_proof_core I J \<mu> a i dpp
        (CSR_DP_Ordinary_Proof prf))"

lemma check_csr_dp_ordinary_min_Redpair_UR_Proc:
  "check_csr_dp_ordinary_min I J \<mu> a i dpp
      (Redpair_UR_Proc redp Pr U subprf) =
    debug i (STR ''CSR U3 reduction pair'') (do {
      dpp' \<leftarrow> csr_u3_redpair_proc J \<mu> (get_rel_impl redp) Pr U dpp
        <+? (\<lambda>s. i \<circ> showsl_lit
          (STR '': error when applying CSR U3 reduction pair\<newline>'') \<circ> s);
      check_csr_dp_termination_proof_core I J \<mu> a (add_index i 1) dpp'
        (CSR_DP_Ordinary_Proof subprf)
        <+? (\<lambda>s. i \<circ> showsl_lit
          (STR '': error below CSR U3 reduction pair\<newline>'') \<circ> s)
    })"
  by (subst check_csr_dp_ordinary_min.simps, simp)

declare check_csr_dp_ordinary_min.simps[simp del]

fun check_csr_dp_termination_proof_min ::
  "('tp, ('f::{showl, compare_order,countable}, label_type) lab, string) tp_ops \<Rightarrow>
   ('dpp, ('f, label_type) lab, string) dpp_ops \<Rightarrow>
   (('f, label_type) lab) muL \<Rightarrow> bool \<Rightarrow>
   showsl \<Rightarrow> 'dpp \<Rightarrow>
   ('f, label_type, string) csr_dp_termination_proof \<Rightarrow> showsl check"
and check_csr_dp_graph_components_min ::
  "('tp, ('f::{showl, compare_order,countable}, label_type) lab, string) tp_ops \<Rightarrow>
   ('dpp, ('f, label_type) lab, string) dpp_ops \<Rightarrow>
   (('f, label_type) lab) muL \<Rightarrow> bool \<Rightarrow>
   showsl \<Rightarrow> 'dpp \<Rightarrow>
   (('f, label_type, string) csr_dp_termination_proof option \<times>
    ('f, label_type, string) trsLL) list \<Rightarrow> showsl check"
where
  "check_csr_dp_termination_proof_min I J \<mu> a i dpp CSR_DP_P_is_Empty =
    check_csr_dp_termination_proof_core I J \<mu> a i dpp CSR_DP_P_is_Empty"
| "check_csr_dp_termination_proof_min I J \<mu> a i dpp
    (CSR_DP_Ordinary_Proof prf) =
    check_csr_dp_ordinary_min I J \<mu> a i dpp prf"
| "check_csr_dp_termination_proof_min I J \<mu> a i dpp
    (CSR_DP_Subterm_Criterion_Proc p rseq Pr prf) =
    check_csr_dp_termination_proof_core I J \<mu> a i dpp
      (CSR_DP_Subterm_Criterion_Proc p rseq Pr prf)"
| "check_csr_dp_termination_proof_min I J \<mu> a i dpp
    (CSR_DP_Gen_Subterm_Criterion_Proc p Pr prf) =
    check_csr_dp_termination_proof_core I J \<mu> a i dpp
      (CSR_DP_Gen_Subterm_Criterion_Proc p Pr prf)"
| "check_csr_dp_termination_proof_min I J \<mu> a i dpp
    (CSR_DP_Usable_Rules_Proc U prf) =
    debug i (STR ''QCS usable rules'') (do {
      dpp' \<leftarrow> csr_qcs_usable_rules_proc J \<mu> U dpp
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying QCS usable rules\<newline>'') \<circ> s);
      check_csr_dp_termination_proof_min I J \<mu> a (add_index i 1) dpp' prf
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below QCS usable rules\<newline>'') \<circ> s)
    })"
| "check_csr_dp_termination_proof_min I J \<mu> a i dpp
    (CSR_DP_Dep_Graph_Proc edpts) =
    debug i (STR ''minimal CSR-DP dependency graph'') (do {
      _ \<leftarrow> check_csr_dep_graph_proc J \<mu> dpp edpts
        <+? (\<lambda>s. i \<circ> showsl_lit
          (STR '': error when applying minimal CSR dependency graph\<newline>'') \<circ> s);
      check_csr_dp_graph_components_min I J \<mu> a i dpp edpts
        <+? (\<lambda>s. i \<circ> showsl_lit
          (STR '': error below minimal CSR dependency graph\<newline>'') \<circ> s)
    })"
| "check_csr_dp_termination_proof_min I J \<mu> a i dpp
    (CSR_DP_Instantiation_Proc st sts prf) =
    error (i \<circ> showsl_lit
      (STR '': context-sensitive instantiation requires improved CS-DPs''))"
| "check_csr_dp_termination_proof_min I J \<mu> a i dpp
    (CSR_DP_Size_Change_Subterm_Proc graphs) =
    (if isOK (csr_sct_active_subterm_proc J \<mu> graphs dpp)
     then debug i (STR ''active CSR size-change'') succeed
     else check_csr_dp_termination_proof_core I J \<mu> a i dpp
       (CSR_DP_Size_Change_Subterm_Proc graphs))"
| "check_csr_dp_graph_components_min I J \<mu> a i dpp [] = succeed"
| "check_csr_dp_graph_components_min I J \<mu> a i dpp
    ((None, P) # rest) =
    check_csr_dp_graph_components_min I J \<mu> a (add_index i 1) dpp rest"
| "check_csr_dp_graph_components_min I J \<mu> a i dpp
    ((Some prf, P) # rest) = do {
      check_csr_dp_termination_proof_min I J \<mu> a (add_index i 1)
        (dpp_ops.intersect_pairs J dpp P) prf;
      check_csr_dp_graph_components_min I J \<mu> a (add_index i 1) dpp rest
    }"

lemma check_csr_dp_graph_components_min_member:
  assumes ok:
      "isOK (check_csr_dp_graph_components_min I J \<mu> a i dpp edps)"
    and mem: "(Some prf, P) \<in> set edps"
  shows "\<exists>j. isOK (check_csr_dp_termination_proof_min I J \<mu> a
    j (dpp_ops.intersect_pairs J dpp P) prf)"
  using ok mem
proof (induct edps arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons head rest)
  obtain po C where head: "head = (po, C)"
    by (cases head)
  show ?case
  proof (cases po)
    case None
    from Cons.prems head None show ?thesis
      by (auto intro: Cons.hyps)
  next
    case (Some p)
    show ?thesis
    proof (cases "(Some prf, P) = head")
      case True
      with Cons.prems head Some show ?thesis by auto
    next
      case False
      from Cons.prems head Some False show ?thesis
        by (auto intro: Cons.hyps)
    qed
  qed
qed

lemma plain_csr_dpp_delete_pairs:
  assumes J: "dpp_spec J" and plain: "plain_csr_dpp J dpp"
  shows "plain_csr_dpp J (dpp_spec.delete_pairs J dpp Pr)"
proof -
  interpret dpp_spec J by fact
  let ?d = "delete_pairs dpp Pr"
  have sem: "dpp_ops.dpp J ?d =
    (NFS dpp, M dpp, set (P dpp) - set Pr,
      set (Pw dpp) - set Pr, set (Q dpp), set (R dpp), set (Rw dpp))"
    by (rule delete_P_Pw_sound)
  have sem': "dpp_ops.dpp J ?d =
    (NFS ?d, M ?d, set (P ?d), set (Pw ?d),
      set (Q ?d), set (R ?d), set (Rw ?d))"
    by (rule dpp_sound)
  from plain sem sem' show ?thesis
    unfolding plain_csr_dpp_def by auto
qed

lemma check_csr_dp_ordinary_min_fallback_sound:
  assumes eq: "check_csr_dp_ordinary_min I J \<mu> a i dpp prf =
      check_csr_dp_termination_proof_core I J \<mu> a i dpp
        (CSR_DP_Ordinary_Proof prf)"
    and I: "tp_spec I" and J: "dpp_spec J"
    and plain: "plain_csr_dpp J dpp"
    and mode: "a = False"
    and ok: "isOK (check_csr_dp_ordinary_min I J \<mu> a i dpp prf)"
  shows "finite_min_csr_dpp Sharp (mu_of \<mu>)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
proof -
  from eq mode ok have core:
    "isOK (check_csr_dp_termination_proof_core I J \<mu> False i dpp
      (CSR_DP_Ordinary_Proof prf))"
    by simp
  from check_csr_dp_termination_proof_core_sound[OF I J plain core]
  show ?thesis by (rule finite_csr_dpp_imp_finite_min_csr_dpp)
qed

lemma check_csr_dp_ordinary_min_fallback_eq:
  assumes nr: "\<And>redp Pr U subprf.
    prf \<noteq> Redpair_UR_Proc redp Pr U subprf"
  shows "check_csr_dp_ordinary_min I J \<mu> a i dpp prf =
    check_csr_dp_termination_proof_core I J \<mu> a i dpp
      (CSR_DP_Ordinary_Proof prf)"
  using nr
  by (cases "prf"; simp add: check_csr_dp_ordinary_min.simps)

lemma check_csr_dp_ordinary_min_non_u3_sound:
  assumes nr: "\<And>redp Pr U subprf.
      prf \<noteq> Redpair_UR_Proc redp Pr U subprf"
    and I: "tp_spec I" and J: "dpp_spec J"
    and plain: "plain_csr_dpp J dpp"
    and mode: "a = False"
    and ok: "isOK (check_csr_dp_ordinary_min I J \<mu> a i dpp prf)"
  shows "finite_min_csr_dpp Sharp (mu_of \<mu>)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
  apply (rule check_csr_dp_ordinary_min_fallback_sound)
       apply (rule check_csr_dp_ordinary_min_fallback_eq)
       apply (rule nr)
      apply (rule I)
     apply (rule J)
    apply (rule plain)
   apply (rule mode)
  apply (rule ok)
  done

lemma check_csr_dp_ordinary_min_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and plain: "plain_csr_dpp J dpp"
    and wf: "wf_trs (set (dpp_ops.rules J dpp))"
    and fresh: "\<And>f n. \<not> defined (set (dpp_ops.rules J dpp)) (Sharp f, n)"
    and mode: "a = False"
    and ok: "isOK (check_csr_dp_ordinary_min I J \<mu> a i dpp prf)"
  shows "finite_min_csr_dpp Sharp (mu_of \<mu>)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
proof (cases "\<exists>redp Pr U subprf.
    prf = Redpair_UR_Proc redp Pr U subprf")
  case True
  then obtain redp Pr U subprf where
    Redpair_UR_Proc: "prf = Redpair_UR_Proc redp Pr U subprf"
    by blast
  from ok mode Redpair_UR_Proc obtain dpp' where
    proc: "csr_u3_redpair_proc J \<mu> (get_rel_impl redp) Pr U dpp = return dpp'"
    and core: "isOK (check_csr_dp_termination_proof_core I J \<mu> False
      (add_index i 1) dpp' (CSR_DP_Ordinary_Proof subprf))"
    by (auto simp add: check_csr_dp_ordinary_min_Redpair_UR_Proc)
  have dpp': "dpp' = dpp_spec.delete_pairs J dpp Pr"
    using proc unfolding csr_u3_redpair_proc_def by auto
  have plain': "plain_csr_dpp J dpp'"
    unfolding dpp'
    by (rule plain_csr_dpp_delete_pairs[OF J plain])
  interpret dpp_spec J by (rule J)
  have rules': "set (rules dpp') = set (rules dpp)"
    using dpp' delete_P_Pw_sound[of dpp Pr Pr] rules_sound[of dpp']
    by auto
  from check_csr_dp_termination_proof_core_sound[OF I J plain' core]
  have fin': "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (pairs dpp')) (set (rules dpp'))"
    by (rule finite_csr_dpp_imp_finite_min_csr_dpp)
  show ?thesis
    apply (rule csr_u3_redpair_proc_sound)
         apply (rule J)
        apply (rule get_rel_impl)
       apply (rule proc)
      apply (rule wf)
     apply (rule fresh)
    apply (rule fin')
    done
next
  case False
  have nr: "\<And>redp Pr U subprf.
      prf \<noteq> Redpair_UR_Proc redp Pr U subprf"
    using False by blast
  from check_csr_dp_ordinary_min_non_u3_sound[
    OF nr I J plain mode ok]
  show ?thesis .
qed

lemma check_csr_dp_termination_proof_min_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and plain: "plain_csr_dpp J dpp"
    and wf: "wf_trs (set (dpp_ops.rules J dpp))"
    and fresh: "\<And>f n. \<not> defined (set (dpp_ops.rules J dpp)) (Sharp f, n)"
    and ok: "isOK (check_csr_dp_termination_proof_min I J \<mu> False i dpp prf)"
  shows "finite_min_csr_dpp Sharp (mu_of \<mu>)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
  using ok plain wf fresh
proof (induct "prf" arbitrary: dpp i)
  case CSR_DP_P_is_Empty
  then have core: "isOK (check_csr_dp_termination_proof_core I J \<mu> False i dpp
      CSR_DP_P_is_Empty)"
    by simp
  from check_csr_dp_termination_proof_core_sound[OF I J CSR_DP_P_is_Empty.prems(2) core]
  show ?case by (rule finite_csr_dpp_imp_finite_min_csr_dpp)
next
  case (CSR_DP_Ordinary_Proof x)
  from CSR_DP_Ordinary_Proof.prems(1) have ordinary_ok:
    "isOK (check_csr_dp_ordinary_min I J \<mu> False i dpp x)"
    by simp
  show ?case
    apply (rule check_csr_dp_ordinary_min_sound)
          apply (rule I)
         apply (rule J)
        apply (rule CSR_DP_Ordinary_Proof.prems(2))
       apply (rule CSR_DP_Ordinary_Proof.prems(3))
      apply (rule CSR_DP_Ordinary_Proof.prems(4))
     apply (rule refl)
    apply (rule ordinary_ok)
    done
next
  case (CSR_DP_Subterm_Criterion_Proc p rseq Pr subprf)
  then have core: "isOK (check_csr_dp_termination_proof_core I J \<mu> False i dpp
      (CSR_DP_Subterm_Criterion_Proc p rseq Pr subprf))"
    by simp
  from check_csr_dp_termination_proof_core_sound[
      OF I J CSR_DP_Subterm_Criterion_Proc.prems(2) core]
  show ?case by (rule finite_csr_dpp_imp_finite_min_csr_dpp)
next
  case (CSR_DP_Gen_Subterm_Criterion_Proc p Pr subprf)
  then have core: "isOK (check_csr_dp_termination_proof_core I J \<mu> False i dpp
      (CSR_DP_Gen_Subterm_Criterion_Proc p Pr subprf))"
    by simp
  from check_csr_dp_termination_proof_core_sound[
      OF I J CSR_DP_Gen_Subterm_Criterion_Proc.prems(2) core]
  show ?case by (rule finite_csr_dpp_imp_finite_min_csr_dpp)
next
  case (CSR_DP_Usable_Rules_Proc U subprf)
  from CSR_DP_Usable_Rules_Proc.prems(1)
  obtain dpp' where proc: "csr_qcs_usable_rules_proc J \<mu> U dpp = return dpp'"
    and rec: "isOK (check_csr_dp_termination_proof_min I J \<mu> False
      (add_index i 1) dpp' subprf)"
    by auto
  from csr_qcs_usable_rules_proc_sound[OF J proc]
  have dpp': "dpp' = dpp_ops.intersect_rules J dpp U"
    and closed: "qcs_csr_ur_closed (set (dpp_ops.rules J dpp)) (set U)
      (mu_of \<mu>) (set (dpp_ops.pairs J dpp))"
    by auto
  interpret dpp_spec J by fact
  have sem: "dpp_ops.dpp J dpp' =
    (NFS dpp, M dpp, set (P dpp), set (Pw dpp), set (Q dpp),
      set (R dpp) \<inter> set U, set (Rw dpp) \<inter> set U)"
    unfolding dpp' by (rule intersect_rules_sound)
  have sem': "dpp_ops.dpp J dpp' =
    (NFS dpp', M dpp', set (P dpp'), set (Pw dpp'), set (Q dpp'),
      set (R dpp'), set (Rw dpp'))"
    by (rule dpp_sound)
  from closed have subset: "set U \<subseteq> set (rules dpp)"
    unfolding qcs_csr_ur_closed_def by auto
  have P': "set (pairs dpp') = set (pairs dpp)"
    using sem sem' pairs_sound[of dpp] pairs_sound[of dpp'] by auto
  have R': "set (rules dpp') = set U"
    using sem sem' rules_sound[of dpp] rules_sound[of dpp'] subset by auto
  have plain': "plain_csr_dpp J dpp'"
    unfolding dpp' by (rule plain_csr_dpp_intersect_rules[
      OF J CSR_DP_Usable_Rules_Proc.prems(2)])
  have wf': "wf_trs (set (rules dpp'))"
    using CSR_DP_Usable_Rules_Proc.prems(3) subset
    unfolding R' wf_trs_def by auto
  have fresh': "\<And>f n. \<not> defined (set (rules dpp')) (Sharp f, n)"
    using CSR_DP_Usable_Rules_Proc.prems(4) subset
    unfolding R' defined_def by blast
  from CSR_DP_Usable_Rules_Proc.hyps[OF rec plain' wf' fresh']
  have fin': "finite_min_csr_dpp Sharp (mu_of \<mu>)
    (set (pairs dpp')) (set (rules dpp'))" .
  show ?case
    by (rule finite_min_csr_dpp_qcs_usable_rules[
      OF CSR_DP_Usable_Rules_Proc.prems(3) CSR_DP_Usable_Rules_Proc.prems(4)
        closed fin'[unfolded P' R']])
next
  case (CSR_DP_Dep_Graph_Proc edpts)
  from CSR_DP_Dep_Graph_Proc.prems(1) have graph_ok:
      "isOK (check_csr_dep_graph_proc J \<mu> dpp edpts)"
    and components_ok:
      "isOK (check_csr_dp_graph_components_min
        I J \<mu> False i dpp edpts)"
    by auto
  show ?case
  proof (rule check_csr_dep_graph_proc_min_sound[
      OF J CSR_DP_Dep_Graph_Proc.prems(2) graph_ok])
    fix p0 C
    assume mem: "(Some p0, C) \<in> set edpts"
    from check_csr_dp_graph_components_min_member[OF components_ok mem]
    obtain j where rec:
      "isOK (check_csr_dp_termination_proof_min I J \<mu> False
        j (dpp_ops.intersect_pairs J dpp C) p0)"
      by blast
    let ?d = "dpp_ops.intersect_pairs J dpp C"
    have plain': "plain_csr_dpp J ?d"
      by (rule plain_csr_dpp_intersect_pairs[
        OF J CSR_DP_Dep_Graph_Proc.prems(2)])
    interpret dpp_spec J by fact
    have sem: "dpp_ops.dpp J ?d =
      (NFS dpp, M dpp, set (P dpp) \<inter> set C,
        set (Pw dpp) \<inter> set C, set (Q dpp),
        set (R dpp), set (Rw dpp))"
      by (rule intersect_pairs_sound)
    have sem': "dpp_ops.dpp J ?d =
      (NFS ?d, M ?d, set (P ?d), set (Pw ?d), set (Q ?d),
        set (R ?d), set (Rw ?d))"
      by (rule dpp_sound)
    have pairs': "set (pairs ?d) = set (pairs dpp) \<inter> set C"
      using sem sem' pairs_sound[of dpp] pairs_sound[of ?d] by auto
    have rules': "set (rules ?d) = set (rules dpp)"
      using sem sem' rules_sound[of dpp] rules_sound[of ?d] by auto
    have wf': "wf_trs (set (dpp_ops.rules J ?d))"
      using CSR_DP_Dep_Graph_Proc.prems(3)
      unfolding rules' .
    have fresh': "\<And>f n.
      \<not> defined (set (dpp_ops.rules J ?d)) (Sharp f, n)"
      using CSR_DP_Dep_Graph_Proc.prems(4)
      unfolding rules' .
    have ih: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (dpp_ops.pairs J ?d)) (set (dpp_ops.rules J ?d))"
      apply (rule CSR_DP_Dep_Graph_Proc.hyps)
          apply (rule mem)
         apply simp
        apply simp
       apply (rule rec)
      apply (rule plain')
      apply (rule wf')
      apply (rule fresh')
      done
    show "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (dpp_ops.pairs J dpp) \<inter> set C)
      (set (dpp_ops.rules J dpp))"
      using ih unfolding pairs' rules' .
  qed
next
  case (CSR_DP_Instantiation_Proc st sts subprf)
  then show ?case by simp
next
  case (CSR_DP_Size_Change_Subterm_Proc graphs)
  show ?case
  proof (cases "isOK (csr_sct_active_subterm_proc J \<mu> graphs dpp)")
    case True
    show ?thesis
      by (rule csr_sct_active_subterm_proc_sound[
        OF J CSR_DP_Size_Change_Subterm_Proc.prems(3)
          CSR_DP_Size_Change_Subterm_Proc.prems(4) True])
  next
    case False
    from CSR_DP_Size_Change_Subterm_Proc.prems(1) False
    have core:
      "isOK (check_csr_dp_termination_proof_core I J \<mu> False i dpp
        (CSR_DP_Size_Change_Subterm_Proc graphs))"
      by simp
    from check_csr_dp_termination_proof_core_sound[
        OF I J CSR_DP_Size_Change_Subterm_Proc.prems(2) core]
    show ?thesis by (rule finite_csr_dpp_imp_finite_min_csr_dpp)
  qed
qed

definition csr_rules_sharp_fresh_check ::
  "((('f, 'l) lab), 'v) rules \<Rightarrow> showsl check"
where
  "csr_rules_sharp_fresh_check R =
    check_allm (\<lambda>(f, n). check (\<not> is_sharp_lab f)
      (showsl_lit (STR ''source CSR defines a sharp symbol''))) (defined_list R)"

lemma csr_rules_sharp_fresh_check_sound:
  assumes ok: "isOK (csr_rules_sharp_fresh_check R)"
  shows "\<And>f n. \<not> defined (set R) (Sharp f, n)"
proof
  fix f n
  assume def: "defined (set R) (Sharp f, n)"
  have mem: "(Sharp f, n) \<in> set (defined_list R)"
    using def by auto
  from ok mem show False
    unfolding csr_rules_sharp_fresh_check_def
    by (auto simp: isOK_check_allm isOK_check)
qed

lemma finite_min_csr_dpp_rename_vars:
  assumes fin: "finite_min_csr_dpp Sharp \<mu> P' R"
    and cover: "\<And>st. st \<in> P \<Longrightarrow> \<exists>st'. st' \<in> P' \<and> st =\<^sub>v st'"
  shows "finite_min_csr_dpp Sharp \<mu> P R"
proof -
  have rr: "rrstep P \<subseteq> rrstep P'"
  proof
    fix s t
    assume "(s, t) \<in> rrstep P"
    then obtain l r \<sigma> where lr: "(l, r) \<in> P"
      and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
      unfolding rrstep_def' by auto
    from cover[OF lr] obtain l' r' where lr': "(l', r') \<in> P'"
      and eq: "(l, r) =\<^sub>v (l', r')"
      by auto
    from eq_rule_mod_varsE[OF eq]
    obtain \<tau> where l: "l = l' \<cdot> \<tau>" and r: "r = r' \<cdot> \<tau>"
      by blast
    have step: "\<exists>la ra \<rho>. (la, ra) \<in> P' \<and>
      s = la \<cdot> \<rho> \<and> t = ra \<cdot> \<rho>"
      using lr' s t unfolding l r
      by (intro exI[of _ l'] exI[of _ r'] exI[of _ "\<tau> \<circ>\<^sub>s \<sigma>"], simp)
    show "(s, t) \<in> rrstep P'"
      unfolding rrstep_def' using step by auto
  qed
  have pair: "csr_min_pair_step Sharp \<mu> P R \<subseteq>
    csr_min_pair_step Sharp \<mu> P' R"
    using rr unfolding csr_min_pair_step_def by auto
  from fin show ?thesis
    unfolding finite_min_csr_dpp_def
    by (rule SN_rel_mono[OF pair subset_refl])
qed

primrec check_csr_termination_proof_min ::
  "('tp, ('f::{showl, compare_order,countable}, label_type) lab, string) tp_ops \<Rightarrow>
   ('dpp, ('f, label_type) lab, string) dpp_ops \<Rightarrow> bool \<Rightarrow>
   showsl \<Rightarrow> (('f, label_type) lab) muL \<Rightarrow>
   ('f, label_type, string) trsLL \<Rightarrow>
   ('f, label_type, string) csr_termination_proof \<Rightarrow> showsl check"
where
  "check_csr_termination_proof_min I J a i \<mu> R CSR_R_is_Empty =
    check_csr_termination_proof I J a i \<mu> R CSR_R_is_Empty"
| "check_csr_termination_proof_min I J a i \<mu> R
    (CSR_Rule_Removal redp Rr prf) =
    debug i (STR ''CSR rule removal'')
      (case csr_rule_removal_impl redp \<mu> Rr R of
        Inl e \<Rightarrow> Inl e
      | Inr R2 \<Rightarrow> check_csr_termination_proof_min I J a i \<mu> R2 prf)"
| "check_csr_termination_proof_min I J a i \<mu> R
    (CSR_Dependency_Pairs P prf) =
    debug i (STR ''minimal CSR dependency pairs'') (do {
      csr_sharp_mu_check \<mu>
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': invalid replacement map for CSR dependency pairs\<newline>'') \<circ> s);
      csr_rules_sharp_fresh_check R
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': invalid sharp symbol in source CSR\<newline>'') \<circ> s);
      (case mu_csr_dependency_pairs_tt Sharp J \<mu> R P of
        Inr dpp \<Rightarrow> check_csr_dp_termination_proof_min I J \<mu> False
          (add_index i 1) dpp prf
          <+? (\<lambda>s. i \<circ> showsl_lit
            (STR '': error below replacement-map-specific CSR dependency pairs\<newline>'') \<circ> s)
      | Inl e \<Rightarrow> do {
          dpp \<leftarrow> safe_csr_dependency_pairs_tt Sharp J \<mu> R P
            <+? (\<lambda>s. i \<circ> showsl_lit
              (STR '': error when switching from CSR to a safe CS-DP problem\<newline>'') \<circ> s);
          check_csr_dp_termination_proof I J False (add_index i 1) dpp prf
            <+? (\<lambda>s. i \<circ> showsl_lit
              (STR '': error below safe CSR dependency pairs\<newline>'') \<circ> s)
        })
    })"
| "check_csr_termination_proof_min I J a i \<mu> R
    (CSR_Safe_Dependency_Pairs P prf) =
    check_csr_termination_proof I J a i \<mu> R
      (CSR_Safe_Dependency_Pairs P prf)"

lemma check_csr_termination_proof_min_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_csr_termination_proof_min I J a i \<mu> R prf)"
  shows "SN (csstep (mu_of \<mu>) (set R))"
  using ok
proof (induct "prf" arbitrary: R)
  case CSR_R_is_Empty
  then show ?case
    using check_csr_termination_proof_sound[OF I J] by simp
next
  case (CSR_Rule_Removal redp Rr subprf)
  from CSR_Rule_Removal.prems obtain R2 where
    proc: "csr_rule_removal_impl redp \<mu> Rr R = return R2"
    and rec: "isOK (check_csr_termination_proof_min I J a i \<mu> R2 subprf)"
    by (auto split: sum.splits)
  have fin: "SN (csstep (mu_of \<mu>) (set R2))"
    by (rule CSR_Rule_Removal.hyps[OF rec])
  show ?case
    by (rule csr_rule_removal_impl[OF proc fin])
next
  case (CSR_Dependency_Pairs P dp_prf)
  let ?idx = "add_index i 1"
  from CSR_Dependency_Pairs.prems have sharp_rules:
    "isOK (csr_rules_sharp_fresh_check R)"
    by auto
  have fresh: "\<And>f n. \<not> defined (set R) (Sharp f, n)"
    by (rule csr_rules_sharp_fresh_check_sound[OF sharp_rules])
  show ?case
  proof (cases "mu_csr_dependency_pairs_tt Sharp J \<mu> R P")
    case (Inl e)
    from CSR_Dependency_Pairs.prems Inl
    have old: "isOK (check_csr_termination_proof I J a i \<mu> R
      (CSR_Dependency_Pairs P dp_prf))"
      by auto
    show ?thesis
      by (rule check_csr_termination_proof_sound[OF I J old])
  next
    case (Inr dpp)
    from CSR_Dependency_Pairs.prems Inr have rec:
      "isOK (check_csr_dp_termination_proof_min I J \<mu> False ?idx dpp dp_prf)"
      by auto
    have tt: "mu_csr_dependency_pairs_tt Sharp J \<mu> R P = return dpp"
      using Inr by simp
    note tt' = tt[unfolded mu_csr_dependency_pairs_tt_def Let_def, simplified]
    have wf: "wf_trs (set R)"
      using tt' by auto
    have vc: "rhs_mu_vars_condition (mu_of \<mu>) (set R)"
      by (rule rhs_mu_vars_condition_list_sound, insert tt', auto)
    have D: "{f. defined (set R) f} \<subseteq> set (defined_list R)"
      using tt' by auto
    interpret dpp_spec J by fact
    have dpp: "dpp = dpp_ops.mk J False False P [] [] [] R"
      using tt' by auto
    have sem: "dpp_ops.dpp J dpp =
      (False, False, set P, {}, {}, {}, set R)"
      using dpp unfolding dpp_spec.mk_sound[OF J] by simp
    have sem': "dpp_ops.dpp J dpp =
      (NFS dpp, M dpp, set (local.P dpp), set (Pw dpp), set (Q dpp),
        set (local.R dpp), set (Rw dpp))"
      by (rule dpp_sound)
    have plain: "plain_csr_dpp J dpp"
      using sem sem' unfolding plain_csr_dpp_def by auto
    have rules: "set (rules dpp) = set R"
      using sem sem' rules_sound[of dpp] by auto
    have pairs: "set (pairs dpp) = set P"
      using sem sem' pairs_sound[of dpp] by auto
    have wf_dpp: "wf_trs (set (rules dpp))"
      using wf rules by simp
    have fresh_dpp: "\<And>f n. \<not> defined (set (rules dpp)) (Sharp f, n)"
      using fresh rules by simp
    have fin_dpp: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (pairs dpp)) (set (rules dpp))"
      by (rule check_csr_dp_termination_proof_min_sound[
        OF I J plain wf_dpp fresh_dpp rec])
    have finP: "finite_min_csr_dpp Sharp (mu_of \<mu>) (set P) (set R)"
      using fin_dpp unfolding rules pairs .
    have cover: "\<And>dp. dp \<in> mu_CSDP_on Sharp (mu_of \<mu>)
        (set (defined_list R)) (set R) \<Longrightarrow>
      \<exists>dp'\<in>set P. dp =\<^sub>v dp'"
    proof -
      fix dp
      assume mem: "dp \<in> mu_CSDP_on Sharp (mu_of \<mu>)
        (set (defined_list R)) (set R)"
      have mem': "dp \<in> set (mu_CSDP_list Sharp R \<mu> (defined_list R))"
        using mem unfolding mu_CSDP_list by simp
      from tt' mem' show "\<exists>dp'\<in>set P. dp =\<^sub>v dp'"
        using eq_rule_mod_vars_refl[of dp] by blast
    qed
    have fin: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (mu_CSDP_on Sharp (mu_of \<mu>) (set (defined_list R)) (set R)) (set R)"
      apply (rule finite_min_csr_dpp_rename_vars[
        where P' = "set P" and
          P = "mu_CSDP_on Sharp (mu_of \<mu>) (set (defined_list R)) (set R)" and
          R = "set R"])
       apply (rule finP)
      subgoal for st
        using tt' eq_rule_mod_vars_refl[of st]
        unfolding mu_CSDP_list by blast
      done
    show ?thesis
      by (rule finite_min_csr_mu_CSDP_on_imp_SN_csstep[
        OF wf fresh vc D fin])
  qed
next
  case (CSR_Safe_Dependency_Pairs P dp_prf)
  from CSR_Safe_Dependency_Pairs.prems have old:
    "isOK (check_csr_termination_proof I J a i \<mu> R
      (CSR_Safe_Dependency_Pairs P dp_prf))"
    unfolding check_csr_termination_proof_min.simps .
  show ?case
    by (rule check_csr_termination_proof_sound[OF I J old])
qed

end
