(*
Author:  Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Minimal_SCT_Ext
  imports
    Proof_Checker.CSR_Minimal_CSDP_Proofs
begin

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
        (csr_sct_active_index (mu_of \<mu>) s i \<and>
         csr_sct_active_index (mu_of \<mu>) t j \<and>
         get_arg t j \<in> set (mu_supt_list \<mu> (get_arg s i)))
        (showsl_lit (STR ''invalid strict active CSR size-change edge''))) stri;
      check_allm (\<lambda>(i, j). check
        (csr_sct_active_index (mu_of \<mu>) s i \<and>
         csr_sct_active_index (mu_of \<mu>) t j \<and>
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
      (csr_sct_active_index (mu_of \<mu>) s i \<and>
       csr_sct_active_index (mu_of \<mu>) t j \<and>
       get_arg t j \<in> set (mu_supt_list \<mu> (get_arg s i)))
      (showsl_lit (STR ''invalid strict active CSR size-change edge''))) stri;
    check_allm (\<lambda>(i, j). check
      (csr_sct_active_index (mu_of \<mu>) s i \<and>
       csr_sct_active_index (mu_of \<mu>) t j \<and>
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

end
