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
    check_csr_dp_termination_proof_core I J \<mu> a i dpp
      (CSR_DP_Size_Change_Subterm_Proc graphs)"

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
  then have core: "isOK (check_csr_dp_termination_proof_core I J \<mu> False i dpp
      (CSR_DP_Size_Change_Subterm_Proc graphs))"
    by simp
  from check_csr_dp_termination_proof_core_sound[
      OF I J CSR_DP_Size_Change_Subterm_Proc.prems(2) core]
  show ?case by (rule finite_csr_dpp_imp_finite_min_csr_dpp)
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
