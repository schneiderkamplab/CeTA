(*
Author:  Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Minimal_CSDP_Proofs
  imports CSR_Checker
begin

lemma sharp_csdp_step_imp_csnrstep:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f, n)"
    and step: "(sharp_term Sharp s, v) \<in> csdp_step Sharp \<mu> R"
  shows "\<exists>t. v = sharp_term Sharp t \<and> (s, t) \<in> csnrstep \<mu> R"
proof (cases s)
  case (Var x)
  from step obtain p lr \<sigma> where
    rewrite: "(sharp_term Sharp s, v) \<in> rstep_r_p_s R lr p \<sigma>"
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
    rewrite0: "(sharp_term Sharp s, v) \<in> rstep_r_p_s R lr p \<sigma>"
    and cond0: "csdp_step_cond Sharp \<mu> p (sharp_term Sharp s)"
    unfolding csdp_step_def csdp_step_p_def by auto
  have rewrite: "(Fun (Sharp f) ss, v) \<in> rstep_r_p_s R lr p \<sigma>"
    using rewrite0 unfolding Fun by simp
  have cond: "csdp_step_cond Sharp \<mu> p (Fun (Sharp f) ss)"
    using cond0 unfolding Fun by simp
  have p_ne: "p \<noteq> []"
  proof
    assume "p = []"
    with rewrite have lr: "lr \<in> R"
      and lhs: "fst lr \<cdot> \<sigma> = Fun (Sharp f) ss"
      unfolding rstep_r_p_s_def' by auto
    from wf lr have "\<exists>g ts. fst lr = Fun g ts"
      unfolding wf_trs_def by (cases lr, auto)
    then obtain g ts where l: "fst lr = Fun g ts"
      by blast
    from lhs l have g: "g = Sharp f" and len: "length ts = length ss"
      by auto
    from lr l g len have "defined R (Sharp f, length ss)"
      unfolding defined_def by (cases lr, auto)
    with fresh show False by contradiction
  qed
  then obtain i q where p: "p = i # q"
    by (cases p, auto)
  let ?t = "replace_at (Fun f ss) p (snd lr \<cdot> \<sigma>)"
  have rewrite': "(Fun f ss, ?t) \<in> rstep_r_p_s R lr p \<sigma>"
    using rewrite p unfolding rstep_r_p_s_def' by auto
  have v: "v = sharp_term Sharp ?t"
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
      show ?thesis by auto
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
        from sharp_csdp_step_imp_csnrstep[OF wf fresh, of s "ts (Suc i)"]
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
      from sharp_csdp_step_imp_csnrstep[OF wf fresh,
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
  from sharp_csdp_step_imp_csnrstep[OF wf fresh step]
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
  from sharp_csdp_step_imp_csnrstep[OF wf fresh, of "Fun f ts" v]
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
  assumes i: "i < length ts"
    and active: "i \<in> \<mu> (f, length ts)"
    and SN: "SN_on (csdp_step Sharp \<mu> R) {Fun (Sharp f) ts}"
  shows "SN_on (csstep \<mu> R) {ts ! i}"
proof (unfold SN_on_def, intro notI)
  assume "\<exists>as. as 0 \<in> {ts ! i} \<and>
    (\<forall>n. (as n, as (Suc n)) \<in> csstep \<mu> R)"
  then obtain as where init: "as 0 = ts ! i"
    and step: "\<And>n. (as n, as (Suc n)) \<in> csstep \<mu> R"
    by auto
  let ?whole = "\<lambda>n. Fun (Sharp f) (ts[i := as n])"
  have whole0: "?whole 0 = Fun (Sharp f) ts"
    using init i by simp
  have whole_step:
    "(?whole n, ?whole (Suc n)) \<in> csdp_step Sharp \<mu> R" for n
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
    from sharp_csnrstep_imp_csdp_step[OF nr, where shp = Sharp]
    show ?thesis
      using i by simp
  qed
  have bad:
    "\<exists>ws. ws 0 \<in> {Fun (Sharp f) ts} \<and>
      (\<forall>n. (ws n, ws (Suc n)) \<in> csdp_step Sharp \<mu> R)"
  proof (intro exI[of _ ?whole] conjI)
    show "?whole 0 \<in> {Fun (Sharp f) ts}"
      using whole0 by simp
    show "\<forall>n. (?whole n, ?whole (Suc n)) \<in> csdp_step Sharp \<mu> R"
      using whole_step by simp
  qed
  from SN bad show False
    unfolding SN_on_def by contradiction
qed

fun csr_sct_active_index where
  "csr_sct_active_index \<mu> (Fun (Sharp f) ts) (Suc i) =
    (i < length ts \<and> i \<in> \<mu> (f, length ts))"
| "csr_sct_active_index \<mu> t i = False"

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

definition mu_supt_rel where
  "mu_supt_rel \<mu> = {(s, t). mu_supt \<mu> s t}"

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
        csr_sct_active_index \<mu> v j \<and>
        mu_supt \<mu> (get_arg u i) (get_arg v j)) \<and>
      (\<forall>(i, j)\<in>set nstri.
        csr_sct_active_index \<mu> u i \<and>
        csr_sct_active_index \<mu> v j \<and>
        (get_arg u i = get_arg v j \<or>
          mu_supt \<mu> (get_arg u i) (get_arg v j)))"
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
  let ?supteq = "restrict_SN (?step\<^sup>*) ?step"
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
      from uv have uv_steps: "(u, v) \<in> ?step\<^sup>*"
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
          csr_sct_active_index \<mu> (?tt k) j \<and>
          mu_supt \<mu> (get_arg (?ss k) i) (get_arg (?tt k) j)"
      and nonstrict_edges:
        "\<forall>(i, j)\<in>set nstri.
          csr_sct_active_index \<mu> (?ss k) i \<and>
          csr_sct_active_index \<mu> (?tt k) j \<and>
          (get_arg (?ss k) i = get_arg (?tt k) j \<or>
            mu_supt \<mu> (get_arg (?ss k) i) (get_arg (?tt k) j))"
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
        from nonstrict_edges ij have active_i:
          "csr_sct_active_index \<mu> (?ss k) i"
          and active_j: "csr_sct_active_index \<mu> (?tt k) j"
          and sub: "get_arg (?ss k) i = get_arg (?tt k) j \<or>
            mu_supt \<mu> (get_arg (?ss k) i) (get_arg (?tt k) j)"
          by auto
        have active_j_next:
          "csr_sct_active_index \<mu> (?ss (Suc k)) j"
        proof -
          from csr_sct_active_indexE[OF active_j]
          obtain f us q where tt:
              "?tt k = Fun (Sharp f) us"
            and j: "j = Suc q" and q: "q < length us"
            and q_act: "q \<in> \<mu> (f, length us)"
            by auto
          from between tt obtain vs where source:
              "?ss (Suc k) = Fun (Sharp f) vs"
            and len: "length vs = length us"
          proof -
            have start:
              "?tt k \<cdot> ?subst k =
                Fun (Sharp f) (map (\<lambda>x. x \<cdot> ?subst k) us)"
              using tt by simp
            have q': "q < length (map (\<lambda>x. x \<cdot> ?subst k) us)"
              using q by simp
            have q_act':
              "q \<in> \<mu> (f, length (map (\<lambda>x. x \<cdot> ?subst k) us))"
              using q_act by simp
            have between':
              "(Fun (Sharp f) (map (\<lambda>x. x \<cdot> ?subst k) us),
                ?ss (Suc k) \<cdot> ?subst (Suc k)) \<in>
                (csdp_step Sharp \<mu> R)\<^sup>*"
              using between start by simp
            have undef:
              "\<not> defined R
                (Sharp f, length (map (\<lambda>x. x \<cdot> ?subst k) us))"
              by (rule fresh)
            have preserved:
              "\<exists>ws. ?ss (Suc k) \<cdot> ?subst (Suc k) =
                  Fun (Sharp f) ws \<and>
                length ws =
                  length (map (\<lambda>x. x \<cdot> ?subst k) us)"
            proof (rule cssteps_Fun_undefined_root_preserved)
              show "wf_trs R" by fact
              show "\<not> defined R
                (Sharp f, length (map (\<lambda>x. x \<cdot> ?subst k) us))"
                by fact
              show "(Fun (Sharp f) (map (\<lambda>x. x \<cdot> ?subst k) us),
                ?ss (Suc k) \<cdot> ?subst (Suc k)) \<in>
                (csdp_step Sharp \<mu> R)\<^sup>*"
                by fact
            qed
            from preserved obtain ws where finish:
                "?ss (Suc k) \<cdot> ?subst (Suc k) =
                  Fun (Sharp f) ws"
              and len_ws:
                "length ws = length (map (\<lambda>x. x \<cdot> ?subst k) us)"
              by auto
            from pair_shape inP_next obtain h vs where src0:
                "?ss (Suc k) = Fun (Sharp h) vs"
              by auto
            from finish src0 have hf: "h = f"
              by simp
            have src: "?ss (Suc k) = Fun (Sharp f) vs"
              using src0 hf by simp
            have maps:
              "map (\<lambda>x. x \<cdot> ?subst (Suc k)) vs = ws"
              using finish src by simp
            have vs_ws: "length vs = length ws"
              using arg_cong[OF maps, of length] by simp
            have "length vs = length us"
              using vs_ws len_ws by simp
            with that[OF src] show thesis .
          qed
          show ?thesis
            using source j q q_act len by simp
        qed
        have arg_steps:
          "(get_arg (?tt k) j \<cdot> ?subst k,
            get_arg (?ss (Suc k)) j \<cdot> ?subst (Suc k))
            \<in> ?step\<^sup>*"
          by (rule csr_sct_active_get_arg_steps[
            OF wf fresh active_j active_j_next between])
        have target_arg_SN:
          "SN_on ?step {get_arg (?tt k) j \<cdot> ?subst k}"
          by (rule csr_sct_active_index_subst_SN[
            OF active_j target_SN[of "Suc k", simplified]])
        have arg_steps_ns:
          "(get_arg (?tt k) j \<cdot> ?subst k,
            get_arg (?ss (Suc k)) j \<cdot> ?subst (Suc k))
            \<in> ?supteq"
          using arg_steps target_arg_SN
          unfolding restrict_SN_def by simp
        have source_arg_SN:
          "SN_on ?step {get_arg (?ss k) i \<cdot> ?subst k}"
          by (rule csr_sct_active_index_subst_SN[
            OF active_i whole_source_SN])
        have sub_inst:
          "get_arg (?ss k) i \<cdot> ?subst k =
              get_arg (?tt k) j \<cdot> ?subst k \<or>
            mu_supt \<mu> (get_arg (?ss k) i \<cdot> ?subst k)
              (get_arg (?tt k) j \<cdot> ?subst k)"
          using sub mu_supt_subst by auto
        have first:
          "(get_arg (?ss k) i \<cdot> ?subst k,
            get_arg (?tt k) j \<cdot> ?subst k) \<in> ?supteq \<union> ?supt"
        using sub_inst
        proof
          assume 1:
            "get_arg (?ss k) i \<cdot> ?subst k =
              get_arg (?tt k) j \<cdot> ?subst k"
          then show ?thesis
            using source_arg_SN unfolding restrict_SN_def by auto
        next
          assume 2:
            "mu_supt \<mu> (get_arg (?ss k) i \<cdot> ?subst k)
              (get_arg (?tt k) j \<cdot> ?subst k)"
          have "(get_arg (?ss k) i \<cdot> ?subst k,
              get_arg (?tt k) j \<cdot> ?subst k) \<in>
              (?msupt \<union> ?step)\<^sup>+"
            using 2 unfolding mu_supt_rel_def by auto
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
          and active_j: "csr_sct_active_index \<mu> (?tt k) j"
          and sub: "mu_supt \<mu>
            (get_arg (?ss k) i) (get_arg (?tt k) j)"
          by auto
        have active_j_next:
          "csr_sct_active_index \<mu> (?ss (Suc k)) j"
        proof -
          from csr_sct_active_indexE[OF active_j]
          obtain f us q where tt:
              "?tt k = Fun (Sharp f) us"
            and j: "j = Suc q" and q: "q < length us"
            and q_act: "q \<in> \<mu> (f, length us)"
            by auto
          have start:
            "?tt k \<cdot> ?subst k =
              Fun (Sharp f) (map (\<lambda>x. x \<cdot> ?subst k) us)"
            using tt by simp
          have q': "q < length (map (\<lambda>x. x \<cdot> ?subst k) us)"
            using q by simp
          have q_act':
            "q \<in> \<mu> (f, length (map (\<lambda>x. x \<cdot> ?subst k) us))"
            using q_act by simp
          have between':
            "(Fun (Sharp f) (map (\<lambda>x. x \<cdot> ?subst k) us),
              ?ss (Suc k) \<cdot> ?subst (Suc k)) \<in>
              (csdp_step Sharp \<mu> R)\<^sup>*"
            using between start by simp
          have undef:
            "\<not> defined R
              (Sharp f, length (map (\<lambda>x. x \<cdot> ?subst k) us))"
            by (rule fresh)
          have preserved:
            "\<exists>ws. ?ss (Suc k) \<cdot> ?subst (Suc k) =
                Fun (Sharp f) ws \<and>
              length ws =
                length (map (\<lambda>x. x \<cdot> ?subst k) us)"
          proof (rule cssteps_Fun_undefined_root_preserved)
            show "wf_trs R" by fact
            show "\<not> defined R
              (Sharp f, length (map (\<lambda>x. x \<cdot> ?subst k) us))"
              by fact
            show "(Fun (Sharp f) (map (\<lambda>x. x \<cdot> ?subst k) us),
              ?ss (Suc k) \<cdot> ?subst (Suc k)) \<in>
              (csdp_step Sharp \<mu> R)\<^sup>*"
              by fact
          qed
          from preserved obtain ws where finish:
              "?ss (Suc k) \<cdot> ?subst (Suc k) =
                Fun (Sharp f) ws"
            and len_ws:
              "length ws = length (map (\<lambda>x. x \<cdot> ?subst k) us)"
            by auto
          from pair_shape inP_next obtain h vs where source0:
              "?ss (Suc k) = Fun (Sharp h) vs"
            by auto
          from finish source0 have hf: "h = f"
            by simp
          have source: "?ss (Suc k) = Fun (Sharp f) vs"
            using source0 hf by simp
          have maps:
            "map (\<lambda>x. x \<cdot> ?subst (Suc k)) vs = ws"
            using finish source by simp
          have vs_ws: "length vs = length ws"
            using arg_cong[OF maps, of length] by simp
          have len: "length vs = length us"
            using vs_ws len_ws by simp
          show ?thesis
            using source j q q_act len by simp
        qed
        have arg_steps:
          "(get_arg (?tt k) j \<cdot> ?subst k,
            get_arg (?ss (Suc k)) j \<cdot> ?subst (Suc k))
            \<in> ?step\<^sup>*"
          by (rule csr_sct_active_get_arg_steps[
            OF wf fresh active_j active_j_next between])
        have target_arg_SN:
          "SN_on ?step {get_arg (?tt k) j \<cdot> ?subst k}"
          by (rule csr_sct_active_index_subst_SN[
            OF active_j target_SN[of "Suc k", simplified]])
        have arg_steps_ns:
          "(get_arg (?tt k) j \<cdot> ?subst k,
            get_arg (?ss (Suc k)) j \<cdot> ?subst (Suc k))
            \<in> ?supteq"
          using arg_steps target_arg_SN
          unfolding restrict_SN_def by simp
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
        csr_sct_active_index \<mu> v j \<and>
        mu_supt \<mu> (get_arg u i) (get_arg v j)) \<and>
      (\<forall>(i, j)\<in>set nstri.
        csr_sct_active_index \<mu> u i \<and>
        csr_sct_active_index \<mu> v j \<and>
        (get_arg u i = get_arg v j \<or>
          mu_supt \<mu> (get_arg u i) (get_arg v j)))"
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
        csr_sct_active_index \<mu> v j \<and>
        mu_supt \<mu> (get_arg u i) (get_arg v j)) \<and>
      (\<forall>(i, j)\<in>set nstri.
        csr_sct_active_index \<mu> u i \<and>
        csr_sct_active_index \<mu> v j \<and>
        (get_arg u i = get_arg v j \<or>
          mu_supt \<mu> (get_arg u i) (get_arg v j)))"
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
qed

fun csr_sct_sharp_term where
  "csr_sct_sharp_term (Fun (Sharp f) ts) = True"
| "csr_sct_sharp_term t = False"

fun csr_sct_active_index_check where
  "csr_sct_active_index_check \<mu> (Fun (Sharp f) ts) i =
    (0 < i \<and> i \<le> length ts \<and>
      i - 1 \<in> mu_of \<mu> (f, length ts))"
| "csr_sct_active_index_check \<mu> t i = False"

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
         csr_sct_active_index_check \<mu> t j \<and>
         get_arg t j \<in> set (mu_supt_list \<mu> (get_arg s i)))
        (showsl_lit (STR ''invalid strict active CSR size-change edge''))) stri;
      check_allm (\<lambda>(i, j). check
        (csr_sct_active_index_check \<mu> s i \<and>
         csr_sct_active_index_check \<mu> t j \<and>
         (get_arg s i = get_arg t j \<or>
          get_arg t j \<in> set (mu_supt_list \<mu> (get_arg s i))))
        (showsl_lit (STR ''invalid non-strict active CSR size-change edge'')))
        nstri
    }) GGs;
    let conn = (\<lambda>st uv. csr_dep_graph_edge_check
      (csr_dp_root_mu (mu_of \<mu>)) R ((st, ()), (uv, ())));
    check (check_SCT conn
      (map (\<lambda>(st, (stri, nstri)).
        Scg st st (remdups_sort stri) (remdups_sort nstri)) GGs))
      (showsl_lit (STR ''active CSR size-change analysis failed''))
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
       csr_sct_active_index_check \<mu> t j \<and>
       get_arg t j \<in> set (mu_supt_list \<mu> (get_arg s i)))
      (showsl_lit (STR ''invalid strict active CSR size-change edge''))) stri;
    check_allm (\<lambda>(i, j). check
      (csr_sct_active_index_check \<mu> s i \<and>
       csr_sct_active_index_check \<mu> t j \<and>
       (get_arg s i = get_arg t j \<or>
        get_arg t j \<in> set (mu_supt_list \<mu> (get_arg s i))))
      (showsl_lit (STR ''invalid non-strict active CSR size-change edge'')))
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
        csr_sct_active_index (mu_of \<mu>) t j \<and>
        mu_supt (mu_of \<mu>) (get_arg s i) (get_arg t j)) \<and>
      (\<forall>(i, j)\<in>set nstri.
        csr_sct_active_index (mu_of \<mu>) s i \<and>
        csr_sct_active_index (mu_of \<mu>) t j \<and>
        (get_arg s i = get_arg t j \<or>
         mu_supt (mu_of \<mu>) (get_arg s i) (get_arg t j)))"
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
          csr_sct_active_index (mu_of \<mu>) t j \<and>
          mu_supt (mu_of \<mu>) (get_arg s i) (get_arg t j)) \<and>
        (\<forall>(i, j)\<in>set nstri.
          csr_sct_active_index (mu_of \<mu>) s i \<and>
          csr_sct_active_index (mu_of \<mu>) t j \<and>
          (get_arg s i = get_arg t j \<or>
           mu_supt (mu_of \<mu>) (get_arg s i) (get_arg t j)))"
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
      csr_sct_active_index (mu_of \<mu>) v j \<and>
      mu_supt (mu_of \<mu>) (get_arg u i) (get_arg v j)) \<and>
    (\<forall>(i, j)\<in>set nstri.
      csr_sct_active_index (mu_of \<mu>) u i \<and>
      csr_sct_active_index (mu_of \<mu>) v j \<and>
      (get_arg u i = get_arg v j \<or>
       mu_supt (mu_of \<mu>) (get_arg u i) (get_arg v j)))"
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
        csr_sct_active_index (mu_of \<mu>) v j \<and>
        mu_supt (mu_of \<mu>) (get_arg u i) (get_arg v j)"
      and nonstrict:
      "\<forall>(i, j)\<in>set nstri.
        csr_sct_active_index (mu_of \<mu>) u i \<and>
        csr_sct_active_index (mu_of \<mu>) v j \<and>
        (get_arg u i = get_arg v j \<or>
         mu_supt (mu_of \<mu>) (get_arg u i) (get_arg v j))"
      by auto
    show "\<exists>stri nstri.
      Scg (u, v) (u, v)
        (remdups_sort stri) (remdups_sort nstri) \<in> set ?SGs \<and>
      (\<forall>(i, j)\<in>set stri.
        csr_sct_active_index (mu_of \<mu>) u i \<and>
        csr_sct_active_index (mu_of \<mu>) v j \<and>
        mu_supt (mu_of \<mu>) (get_arg u i) (get_arg v j)) \<and>
      (\<forall>(i, j)\<in>set nstri.
        csr_sct_active_index (mu_of \<mu>) u i \<and>
        csr_sct_active_index (mu_of \<mu>) v j \<and>
        (get_arg u i = get_arg v j \<or>
         mu_supt (mu_of \<mu>) (get_arg u i) (get_arg v j)))"
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

primrec check_csr_dp_termination_proof_min ::
  "('tp, ('f::{showl, compare_order,countable}, label_type) lab, string) tp_ops \<Rightarrow>
   ('dpp, ('f, label_type) lab, string) dpp_ops \<Rightarrow>
   (('f, label_type) lab) muL \<Rightarrow> bool \<Rightarrow>
   showsl \<Rightarrow> 'dpp \<Rightarrow>
   ('f, label_type, string) csr_dp_termination_proof \<Rightarrow> showsl check"
where
  "check_csr_dp_termination_proof_min I J \<mu> a i dpp CSR_DP_P_is_Empty =
    check_csr_dp_termination_proof_core I J \<mu> a i dpp CSR_DP_P_is_Empty"
| "check_csr_dp_termination_proof_min I J \<mu> a i dpp
    (CSR_DP_Ordinary_Proof prf) =
    check_csr_dp_termination_proof_core I J \<mu> a i dpp
      (CSR_DP_Ordinary_Proof prf)"
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
    check_csr_dp_termination_proof_core I J \<mu> a i dpp
      (CSR_DP_Dep_Graph_Proc edpts)"
| "check_csr_dp_termination_proof_min I J \<mu> a i dpp
    (CSR_DP_Size_Change_Subterm_Proc graphs) =
    (if isOK (csr_sct_active_subterm_proc J \<mu> graphs dpp)
     then debug i (STR ''active CSR size-change'') succeed
     else check_csr_dp_termination_proof_core I J \<mu> a i dpp
       (CSR_DP_Size_Change_Subterm_Proc graphs))"

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
  then have core: "isOK (check_csr_dp_termination_proof_core I J \<mu> False i dpp
      (CSR_DP_Ordinary_Proof x))"
    by simp
  from check_csr_dp_termination_proof_core_sound[OF I J CSR_DP_Ordinary_Proof.prems(2) core]
  show ?case by (rule finite_csr_dpp_imp_finite_min_csr_dpp)
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
  then have core: "isOK (check_csr_dp_termination_proof_core I J \<mu> False i dpp
      (CSR_DP_Dep_Graph_Proc edpts))"
    by simp
  from check_csr_dp_termination_proof_core_sound[
      OF I J CSR_DP_Dep_Graph_Proc.prems(2) core]
  show ?case by (rule finite_csr_dpp_imp_finite_min_csr_dpp)
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
