(*
Author:  Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Checker
  imports
    Check_Termination
    TRS.Context_Sensitive_Impl
begin

hide_const NthRoot.root

lemma csstep_cond_imp_af_regarded_pos:
  assumes cond: "csstep_cond \<mu> p t"
    and poss: "p \<in> poss t"
  shows "af_regarded_pos \<mu> t p"
  using cond poss
proof (induct p arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons i p)
  then show ?case
  proof (cases t)
    case (Var x)
    with Cons.prems show ?thesis by simp
  next
    case (Fun f ts)
    from Cons.prems Fun have i: "i < length ts" and p: "p \<in> poss (ts ! i)"
      by auto
    from Cons.prems(1)[unfolded csstep_cond_def] Cons.prems(2) Fun
    have imu: "i \<in> \<mu> (f, length ts)"
      by (drule_tac x = "[]" in spec, drule_tac x = i in spec,
          drule_tac x = p in spec, auto)
    have cond': "csstep_cond \<mu> p (ts ! i)"
      unfolding csstep_cond_def
    proof (intro allI impI)
      fix p1 j p2
      assume a: "p = p1 @ j # p2 \<and> p \<in> poss (ts ! i)"
      from a have pp: "p \<in> poss (ts ! i)" by blast
      from a have "i # p = [i] @ p1 @ j # p2" by simp
      moreover from i pp Fun have "i # p \<in> poss t"
        by (simp only: poss_Cons_poss term.sel)
      ultimately obtain g us where
        "(t |_ ([i] @ p1)) = Fun g us \<and> j \<in> \<mu> (g, length us)"
        using Cons.prems(1)[unfolded csstep_cond_def, rule_format, of "[i] @ p1" j p2]
        by auto
      with Fun i show "\<exists>g us. (ts ! i) |_ p1 = Fun g us \<and> j \<in> \<mu> (g, length us)"
        by simp
    qed
    from Cons.hyps[OF cond' p] i imu Fun show ?thesis by simp
  qed
qed

lemma csstep_subset_order:
  assumes rules: "R \<subseteq> ord"
    and mono: "af_monotone \<mu> ord"
    and subst: "subst.closed ord"
  shows "csstep \<mu> R \<subseteq> ord"
proof
  fix s t
  assume st: "(s, t) \<in> csstep \<mu> R"
  then obtain p lr \<sigma> where
    step: "(s, t) \<in> rstep_r_p_s R lr p \<sigma>"
    and cond: "csstep_cond \<mu> p s"
    unfolding csstep_def csstep_p_def by auto
  from step[unfolded rstep_r_p_s_def'] have
    lr: "lr \<in> R" and p: "p \<in> poss s"
    and redex: "s |_ p = fst lr \<cdot> \<sigma>"
    and t: "t = replace_at s p (snd lr \<cdot> \<sigma>)"
    by auto
  let ?C = "ctxt_of_pos_term p s"
  have s: "s = ?C\<langle>fst lr \<cdot> \<sigma>\<rangle>"
    using ctxt_supt_id[OF p] redex by simp
  have t': "t = ?C\<langle>snd lr \<cdot> \<sigma>\<rangle>"
    using t by simp
  have lr_ord: "lr \<in> ord"
    using rules lr by auto
  have base: "(fst lr \<cdot> \<sigma>, snd lr \<cdot> \<sigma>) \<in> ord"
    using subst.closedD[OF subst] lr_ord by (cases lr, auto)
  have reg: "af_regarded_pos \<mu> s p"
    by (rule csstep_cond_imp_af_regarded_pos[OF cond p])
  have hp: "hole_pos ?C = p"
    using hole_pos_ctxt_of_pos_term[OF p] .
  have reg': "af_regarded_pos \<mu> (?C\<langle>fst lr \<cdot> \<sigma>\<rangle>) (hole_pos ?C)"
    using reg s hp by simp
  have "(?C\<langle>fst lr \<cdot> \<sigma>\<rangle>, ?C\<langle>snd lr \<cdot> \<sigma>\<rangle>) \<in> ord"
    by (rule af_monotone_af_regarded_posD[OF mono reg' base])
  then show "(s, t) \<in> ord"
    using s t' by simp
qed

lemma csr_af_rule_removal:
  assumes strict: "Rs \<subseteq> S"
    and weak: "Rr \<subseteq> NS"
    and mono_S: "af_monotone \<mu> S"
    and mono_NS: "af_monotone \<mu> NS"
    and subst_S: "subst.closed S"
    and subst_NS: "subst.closed NS"
    and compat_NS_S: "NS O S \<subseteq> S"
    and SN_S: "SN S"
    and rec: "SN (csstep \<mu> Rr)"
  shows "SN (csstep \<mu> (Rs \<union> Rr))"
proof -
  have s_sub: "csstep \<mu> Rs \<subseteq> S"
    by (rule csstep_subset_order[OF strict mono_S subst_S])
  have ns_sub: "csstep \<mu> Rr \<subseteq> NS"
    by (rule csstep_subset_order[OF weak mono_NS subst_NS])
  have rel: "SN_rel (csstep \<mu> Rs) (csstep \<mu> Rr)"
    by (rule SN_rel_mono[OF s_sub ns_sub],
        unfold SN_rel_defs,
        rule SN_subset[OF compatible_SN'[OF compat_NS_S SN_S]],
        regexp)
  have relto: "SN (relto (csstep \<mu> Rs) (csstep \<mu> Rr))"
    by (rule SN_rel_imp_SN_relto[OF rel])
  have "SN (csstep \<mu> Rs \<union> csstep \<mu> Rr)"
    using relto rec SN_on_Un[of "csstep \<mu> Rs" "csstep \<mu> Rr" UNIV]
    by simp
  moreover have "csstep \<mu> (Rs \<union> Rr) \<subseteq> csstep \<mu> Rs \<union> csstep \<mu> Rr"
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
  ultimately show ?thesis
    by (rule SN_subset)
qed

definition csr_rule_removal_tt ::
  "('f::{showl, compare_order}, 'v::{showl, compare_order}) rel_impl \<Rightarrow>
   'f muL \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> showsl + ('f, 'v) rules"
where
  "csr_rule_removal_tt rp \<mu> Rremove R = (let Rr = ceta_list_diff R Rremove in
    check_return (do {
      rel_impl_mono_redpair rp Rremove Rr;
      rel_impl_s rp Rremove
        <+? (\<lambda>s. showsl_lit (STR ''problem when orienting strict CSR rules\<newline>'') \<circ> s);
      rel_impl_ns rp Rr
        <+? (\<lambda>s. showsl_lit (STR ''problem when orienting remaining CSR rules\<newline>'') \<circ> s)
    } <+? (\<lambda>s. showsl_lit (STR ''could not apply the CSR rule removal processor with the following\<newline>'')
      \<circ> rel_impl.desc rp \<circ> showsl_nl \<circ> s))
    Rr)"

lemma csr_rule_removal_tt:
  assumes rp: "rel_impl rp"
    and ok: "csr_rule_removal_tt rp \<mu> Rremove R = return R'"
    and rec: "SN (csstep (mu_of \<mu>) (set R'))"
  shows "SN (csstep (mu_of \<mu>) (set R))"
proof -
  let ?Rr = "ceta_list_diff R Rremove"
  from ok[unfolded csr_rule_removal_tt_def Let_def, simplified] have
    valid: "isOK (rel_impl_mono_redpair rp Rremove ?Rr)"
    and orient: "isOK (rel_impl_s rp Rremove)" "isOK (rel_impl_ns rp ?Rr)"
    and R': "R' = ?Rr"
    by auto
  from rel_impl_mono_redpair[OF rp valid orient, of undefined undefined]
  obtain S NS NST where
    S: "set Rremove \<subseteq> S" and NS: "set ?Rr \<subseteq> NS"
    and rp': "mono_redtriple_order S NS NST"
    by auto
  interpret mono_redtriple_order S NS NST by fact
  have mono_S: "af_monotone (mu_of \<mu>) S"
    by (rule ctxt_closed_imp_af_monotone[OF ctxt_S])
  have mono_NS: "af_monotone (mu_of \<mu>) NS"
    by (rule ctxt_closed_imp_af_monotone[OF ctxt_NS])
  have rem: "set R - set Rremove = set R'"
    using R' by simp
  have "SN (csstep (mu_of \<mu>) ((set R \<inter> set Rremove) \<union> (set R - set Rremove)))"
    by (rule csr_af_rule_removal[OF _ _ mono_S mono_NS subst_S subst_NS compat_NS_S SN],
        insert S NS rec rem, auto)
  moreover have "(set R \<inter> set Rremove) \<union> (set R - set Rremove) = set R"
    by auto
  ultimately show ?thesis
    by simp
qed

definition csr_rule_removal_af_tt ::
  "('f::{showl, compare_order}, 'v::{showl, compare_order}) rel_impl \<Rightarrow>
   ('f \<times> nat) list \<Rightarrow> 'f muL \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> showsl + ('f, 'v) rules"
where
  "csr_rule_removal_af_tt rp fs \<mu> Rremove R = (let Rr = ceta_list_diff R Rremove in
    check_return (do {
      rel_impl_redpair rp;
      (check_allm (\<lambda> f. check (mu_of \<mu> f \<subseteq> rel_impl.mono_af rp f)
        (showsl_lit (STR ''error in CSR monotonicity: replacement map for '') \<circ> showsl f
        \<circ> showsl_lit (STR '' is '') \<circ> showsl_position_set f (mu_of \<mu> f)
        \<circ> showsl_lit (STR ''\<newline>but the order is monotone only in positions '')
        \<circ> showsl_position_set f (rel_impl.mono_af rp f))) fs);
      rel_impl_s rp Rremove
        <+? (\<lambda>s. showsl_lit (STR ''problem when orienting strict CSR rules\<newline>'') \<circ> s);
      rel_impl_ns rp Rr
        <+? (\<lambda>s. showsl_lit (STR ''problem when orienting remaining CSR rules\<newline>'') \<circ> s)
    } <+? (\<lambda>s. showsl_lit (STR ''could not apply the CSR rule removal processor with replacement-map monotonicity and the following\<newline>'')
      \<circ> rel_impl.desc rp \<circ> showsl_nl \<circ> s))
    Rr)"

lemma isOK_check_allm_checkD:
  assumes ok: "isOK (check_allm (\<lambda>x. check (P x) (E x)) xs)"
    and x: "x \<in> set xs"
  shows "P x"
  using ok x unfolding isOK_check_allm isOK_check by auto

definition csr_mu_mono_check ::
  "'f::{showl, compare_order} muL \<Rightarrow> ('f \<times> nat \<Rightarrow> nat set) \<Rightarrow> ('f \<times> nat) list \<Rightarrow> showsl check"
where
  "csr_mu_mono_check \<mu> monof fs = check_allm (\<lambda> f. check (mu_of \<mu> f \<subseteq> monof f)
    (showsl_lit (STR ''error in CSR monotonicity: replacement map for '') \<circ> showsl f
    \<circ> showsl_lit (STR '' is '') \<circ> showsl_position_set f (mu_of \<mu> f)
    \<circ> showsl_lit (STR ''\<newline>but the order is monotone only in positions '')
    \<circ> showsl_position_set f (monof f))) fs"

fun is_sharp_lab :: "('f, 'l) lab \<Rightarrow> bool"
where
  "is_sharp_lab (Sharp f) = True"
| "is_sharp_lab (UnLab f) = False"
| "is_sharp_lab (Lab f l) = False"
| "is_sharp_lab (FunLab f ls) = False"

definition csr_sharp_mu_entry_ok ::
  "((('f, 'l) lab \<times> nat) \<times> nat list) \<Rightarrow> bool"
where
  "csr_sharp_mu_entry_ok e = (case e of ((f, n), is) \<Rightarrow>
    \<not> is_sharp_lab f \<and> set is \<subseteq> {0..<n})"

definition csr_sharp_mu_check ::
  "(('f::{showl, compare_order}, 'l::showl) lab) muL \<Rightarrow> showsl check"
where
  "csr_sharp_mu_check \<mu> = check_allm (\<lambda>e.
    check (csr_sharp_mu_entry_ok e)
      (case e of ((f, n), is) \<Rightarrow>
        showsl_lit (STR ''invalid replacement map entry for CSR-DP sharp side steps: '')
        \<circ> showsl f \<circ> showsl_lit (STR ''/'') \<circ> showsl n)) \<mu>"

lemma csr_sharp_mu_check_sound:
  assumes ok: "isOK (csr_sharp_mu_check \<mu>)"
  shows "mu_of \<mu> (f, n) \<subseteq> mu_of \<mu> (Sharp f, n)"
proof -
  have valid: "\<And>g m is. ((g, m), is) \<in> set \<mu> \<Longrightarrow>
      \<not> is_sharp_lab g \<and> set is \<subseteq> {0..<m}"
    using isOK_check_allm_checkD[OF ok[unfolded csr_sharp_mu_check_def]]
    unfolding csr_sharp_mu_entry_ok_def by force
  have none: "map_of \<mu> (Sharp f, n) = None"
  proof (rule ccontr)
    assume "map_of \<mu> (Sharp f, n) \<noteq> None"
    then obtain js where some: "map_of \<mu> (Sharp f, n) = Some js"
      by auto
    from map_of_SomeD[OF some] valid
    show False by fastforce
  qed
  show ?thesis
  proof (cases "map_of \<mu> (f, n)")
    case None
    with none show ?thesis
      unfolding mu_of_def by simp
  next
    case (Some js)
    from valid[OF map_of_SomeD[OF Some]] Some none show ?thesis
      unfolding mu_of_def by simp
  qed
qed

definition csr_int_mu_mono_check ::
  "('f::{showl, compare_order}) itself \<Rightarrow>
   (('f, int) lpoly_interL) \<Rightarrow> 'f muL \<Rightarrow> showsl check"
where
  "csr_int_mu_mono_check _ I \<mu> =
    csr_mu_mono_check \<mu> (rel_impl.mono_af (int_rel_impl I)) (remdups (map fst I @ map fst \<mu>))"

lemma csr_rule_removal_af_tt:
  assumes rp: "rel_impl rp"
    and ok: "csr_rule_removal_af_tt rp fs \<mu> Rremove R = return R'"
    and af: "af_subset (mu_of \<mu>) (rel_impl.mono_af rp)"
    and rec: "SN (csstep (mu_of \<mu>) (set R'))"
  shows "SN (csstep (mu_of \<mu>) (set R))"
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
  have "SN (csstep (mu_of \<mu>) ((set R \<inter> set Rremove) \<union> (set R - set Rremove)))"
    by (rule csr_af_rule_removal[OF _ _ mono_S mono_NS subst_S subst_NS compat_NS_S SN],
        insert S NS rec rem, auto)
  moreover have "(set R \<inter> set Rremove) \<union> (set R - set Rremove) = set R"
    by auto
  ultimately show ?thesis
    by simp
qed

lemma int_carrier_mu_af_subset:
  assumes ok: "\<forall>f\<in>set fs. mu_of \<mu> f \<subseteq> rel_impl.mono_af (int_rel_impl I) f"
    and fs: "set (map fst I @ map fst \<mu>) \<subseteq> set fs"
  shows "af_subset (mu_of \<mu>) (rel_impl.mono_af (int_rel_impl I))"
  unfolding af_subset_def
proof
  fix f
  show "mu_of \<mu> f \<subseteq> rel_impl.mono_af (int_rel_impl I) f"
  proof (cases "f \<in> set fs")
    case True
    obtain g n where f: "f = (g, n)"
      by (cases f)
    show ?thesis
    proof
      fix x
      assume x: "x \<in> mu_of \<mu> f"
      have sub: "mu_of \<mu> f \<subseteq> rel_impl.mono_af (int_rel_impl I) f"
        using ok True
        unfolding Ball_def
        apply (drule_tac x=f in spec)
        apply (drule mp)
        apply assumption
        apply (simp add: create_poly_rel_impl_def Let_def)
        done
      from sub x show "x \<in> rel_impl.mono_af (int_rel_impl I) f"
        by (rule subsetD)
    qed
  next
    case False
    then have f_mu: "f \<notin> set (map fst \<mu>)" and f_i: "f \<notin> set (map fst I)"
      using fs by auto
    then have "map_of \<mu> f = None"
      by (simp add: map_of_eq_None_iff)
    moreover have "ceta_map_of I f = None"
      using f_i by (simp add: ceta_map_of map_of_eq_None_iff)
    ultimately show ?thesis
      unfolding mu_of_def create_poly_rel_impl_def create_mono_af_def Let_def
        fun_of_map_fun'.simps class_lpoly_order_def class_ordered_semiring_def
        class_semiring_def
      by auto
  qed
qed

definition csr_int_rule_removal_tt ::
  "(('f::{showl, compare_order}, int) lpoly_interL) \<Rightarrow>
   'f muL \<Rightarrow> ('f, 'v::{showl, compare_order}) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> showsl + ('f, 'v) rules"
where
  "csr_int_rule_removal_tt I \<mu> Rremove R = (let fs = remdups (map fst I @ map fst \<mu>); rp = int_rel_impl I in do {
    _ \<leftarrow> csr_int_mu_mono_check TYPE('f) TYPE('f) I \<mu>;
    csr_rule_removal_af_tt rp fs \<mu> Rremove R
  })"

lemma csr_int_rule_removal_tt:
  fixes I :: "(('f::{showl, compare_order}, int) lpoly_interL)"
    and \<mu> :: "'f muL"
  assumes ok: "csr_int_rule_removal_tt I \<mu> Rremove R = return R'"
    and rec: "SN (csstep (mu_of \<mu>) (set R'))"
  shows "SN (csstep (mu_of \<mu>) (set R))"
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
    by (rule csr_rule_removal_af_tt[OF int_rel_impl af_ok af rec])
qed

fun csr_rule_removal_impl ::
  "('f::{showl, compare_order}) redtriple_impl \<Rightarrow>
   'f muL \<Rightarrow> ('f, string) rules \<Rightarrow> ('f, string) rules \<Rightarrow> showsl + ('f, string) rules"
where
  "csr_rule_removal_impl (Int_carrier I) \<mu> Rremove R = csr_int_rule_removal_tt I \<mu> Rremove R"
| "csr_rule_removal_impl redp \<mu> Rremove R =
    error (showsl_lit (STR ''unsupported CSR rule-removal redpair''))"

lemma csr_rule_removal_get_rel_impl:
  assumes ok: "csr_rule_removal_tt (get_rel_impl redp) \<mu> Rremove R = return R'"
    and rec: "SN (csstep (mu_of \<mu>) (set R'))"
  shows "SN (csstep (mu_of \<mu>) (set R))"
  by (rule csr_rule_removal_tt[OF get_rel_impl ok rec])

lemma csr_rule_removal_impl:
  assumes ok: "csr_rule_removal_impl redp \<mu> Rremove R = return R'"
    and rec: "SN (csstep (mu_of \<mu>) (set R'))"
  shows "SN (csstep (mu_of \<mu>) (set R))"
  using ok rec
  by (cases redp; simp add: csr_int_rule_removal_tt)

lemma csstep_empty[simp]: "csstep \<mu> {} = {}"
  unfolding csstep_def csstep_p_def rstep_r_p_s_def by auto

lemma csstep_cond_Cons_FunD:
  assumes cond: "csstep_cond \<mu> (i # q) (Fun f ss)"
    and iq: "i # q \<in> poss (Fun f ss)"
  shows "i \<in> \<mu> (f, length ss)" "csstep_cond \<mu> q (ss ! i)"
proof -
  from iq have i: "i < length ss" and q: "q \<in> poss (ss ! i)"
    by auto
  show "i \<in> \<mu> (f, length ss)"
    using cond[unfolded csstep_cond_def, rule_format, of "[]" i q] iq by auto
  show "csstep_cond \<mu> q (ss ! i)"
    unfolding csstep_cond_def
  proof (intro allI impI)
    fix p1 j p2
    assume a: "q = p1 @ j # p2 \<and> q \<in> poss (ss ! i)"
    from cond[unfolded csstep_cond_def, rule_format, of "i # p1" j p2]
    obtain g us where "Fun f ss |_ (i # p1) = Fun g us" and "j \<in> \<mu> (g, length us)"
      using a i by auto
    with i show "\<exists>g us. ss ! i |_ p1 = Fun g us \<and> j \<in> \<mu> (g, length us)"
      by auto
  qed
qed

definition csrstep :: "'f mu \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) trs"
where
  "csrstep \<mu> R = csstep_p \<mu> R []"

definition csnrstep :: "'f mu \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) trs"
where
  "csnrstep \<mu> R = {(s, t). \<exists>p. p \<noteq> [] \<and> (s, t) \<in> csstep_p \<mu> R p}"

lemma csstep_root_nonroot:
  "csstep \<mu> R = csrstep \<mu> R \<union> csnrstep \<mu> R"
  unfolding csstep_def csrstep_def csnrstep_def
  by (auto, metis list.exhaust)

lemma csrstep_iff_rstep_root:
  "(s, t) \<in> csrstep \<mu> R \<longleftrightarrow> (\<exists>lr \<sigma>. (s, t) \<in> rstep_r_p_s R lr [] \<sigma>)"
  unfolding csrstep_def csstep_p_def csstep_cond_def by auto

lemma csnrstep_FunE:
  assumes step: "(Fun f ss, t) \<in> csnrstep \<mu> R"
  obtains i ts where "i < length ss" "i \<in> \<mu> (f, length ss)"
    "t = Fun f ts" "length ts = length ss"
    "(ss ! i, ts ! i) \<in> csstep \<mu> R"
    "\<And>j. j < length ss \<Longrightarrow> j \<noteq> i \<Longrightarrow> ts ! j = ss ! j"
proof -
  from step obtain p lr \<sigma> where p_ne: "p \<noteq> []"
    and rstep: "(Fun f ss, t) \<in> rstep_r_p_s R lr p \<sigma>"
    and cond: "csstep_cond \<mu> p (Fun f ss)"
    unfolding csnrstep_def csstep_p_def by auto
  from p_ne obtain i q where p: "p = i # q"
    by (cases p, auto)
  from rstep[unfolded rstep_r_p_s_def'] p have i: "i < length ss"
    and q_pos: "q \<in> poss (ss ! i)"
    and t_def: "t = Fun f (take i ss @
      (ctxt_of_pos_term q (ss ! i))\<langle>snd lr \<cdot> \<sigma>\<rangle> # drop (Suc i) ss)"
    by auto
  let ?ts = "take i ss @ (ctxt_of_pos_term q (ss ! i))\<langle>snd lr \<cdot> \<sigma>\<rangle> # drop (Suc i) ss"
  have t_shape: "\<exists>ts. t = Fun f ts \<and> length ts = length ss \<and>
      (\<forall>j<length ss. j \<noteq> i \<longrightarrow> ts ! j = ss ! j)"
  proof (intro exI[of _ ?ts] conjI allI impI)
    show "t = Fun f ?ts"
      by (rule t_def)
    show "length ?ts = length ss"
      using i by simp
    fix j
    assume j: "j < length ss" and ji: "j \<noteq> i"
    show "?ts ! j = ss ! j"
      using i j ji by (auto simp: nth_append)
  qed
  from cond[unfolded csstep_cond_def, rule_format, of "[]" i q] p i
  have i_mu: "i \<in> \<mu> (f, length ss)"
    using rstep[unfolded rstep_r_p_s_def'] by auto
  from t_shape obtain ts where t: "t = Fun f ts" and len: "length ts = length ss"
    and same: "\<And>j. j < length ss \<Longrightarrow> j \<noteq> i \<Longrightarrow> ts ! j = ss ! j"
    by auto
  have qrstep: "(Fun f ss, t) \<in> qrstep_r_p_s False {} R lr (i # q) \<sigma>"
    using rstep unfolding p qrstep_r_p_s_def rstep_r_p_s_def' by auto
  have qrstep': "(Fun f ss, t) \<in> qrstep_r_p_s False {} R lr ([i] @ q) \<sigma>"
    using qrstep by simp
  have sub_qrstep: "(Fun f ss |_ [i], t |_ [i]) \<in> qrstep_r_p_s False {} R lr q \<sigma>"
    by (rule qrstep_subt_at_gen[OF qrstep'])
  from sub_qrstep p t
  have sub_rstep: "(ss ! i, ts ! i) \<in> rstep_r_p_s R lr q \<sigma>"
    unfolding qrstep_r_p_s_def rstep_r_p_s_def' by auto
  have iq_poss: "i # q \<in> poss (Fun f ss)"
    using rstep p unfolding rstep_r_p_s_def' by auto
  have cond_q: "csstep_cond \<mu> q (ss ! i)"
    by (rule csstep_cond_Cons_FunD(2)[OF cond[unfolded p] iq_poss])
  from sub_rstep cond_q have sub_csstep_p: "(ss ! i, ts ! i) \<in> csstep_p \<mu> R q"
    unfolding csstep_p_def by (cases lr, auto)
  have "(ss ! i, ts ! i) \<in> csstep \<mu> R"
    unfolding csstep_def
    apply (simp add: rel_of)
    using sub_csstep_p by auto
  then show ?thesis
    by (rule that[OF i i_mu t len _ same])
qed

fun mu_fun_poss :: "'f mu \<Rightarrow> ('f, 'v) term \<Rightarrow> pos set"
where
  "mu_fun_poss \<mu> (Var x) = {}"
| "mu_fun_poss \<mu> (Fun f ts) =
    {[]} \<union> (\<Union>i\<in>\<mu> (f, length ts) \<inter> {0..<length ts}. {i # p |p. p \<in> mu_fun_poss \<mu> (ts ! i)})"

fun mu_fun_poss_list :: "'f muL \<Rightarrow> ('f, 'v) term \<Rightarrow> pos list"
where
  "mu_fun_poss_list \<mu> (Var x) = []"
| "mu_fun_poss_list \<mu> (Fun f ts) =
    [] # concat (map (\<lambda>i. map ((#) i) (mu_fun_poss_list \<mu> (ts ! i)))
      [i <- [0..<length ts]. i \<in> mu_of \<mu> (f, length ts)])"

lemma set_mu_fun_poss_list [simp]:
  "set (mu_fun_poss_list \<mu> t) = mu_fun_poss (mu_of \<mu>) t"
proof (induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  have "set (concat (map (\<lambda>i. map ((#) i) (mu_fun_poss_list \<mu> (ts ! i)))
      [i <- [0..<length ts]. i \<in> mu_of \<mu> (f, length ts)])) =
    (\<Union>i\<in>mu_of \<mu> (f, length ts) \<inter> {0..<length ts}. {i # p |p. p \<in> mu_fun_poss (mu_of \<mu>) (ts ! i)})"
    using Fun by auto
  then show ?case by auto
qed

lemma mu_fun_poss_imp_fun_poss:
  assumes "p \<in> mu_fun_poss \<mu> t"
  shows "p \<in> fun_poss t"
  using assms by (induct t arbitrary: p) auto

lemma mu_fun_poss_imp_csstep_cond:
  assumes "p \<in> mu_fun_poss \<mu> t"
  shows "csstep_cond \<mu> p t"
  using assms
proof (induct t arbitrary: p)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  show ?case
  proof (cases p)
    case Nil
    then show ?thesis unfolding csstep_cond_def by simp
  next
    case (Cons i q)
    note p_Cons = Cons
    with Fun.prems obtain p' where
      i: "i \<in> \<mu> (f, length ts)" "i < length ts"
      and q: "q \<in> mu_fun_poss \<mu> (ts ! i)"
      by auto
    have cond_q: "csstep_cond \<mu> q (ts ! i)"
      by (rule Fun.hyps[OF nth_mem[OF i(2)] q])
    show ?thesis unfolding csstep_cond_def
    proof (intro allI impI)
      fix p1 j p2
      assume a: "p = p1 @ j # p2 \<and> p \<in> poss (Fun f ts)"
      show "\<exists>g us. Fun f ts |_ p1 = Fun g us \<and> j \<in> \<mu> (g, length us)"
      proof (cases p1)
        case Nil
        with a p_Cons i show ?thesis by auto
      next
        case (Cons k p1')
        from a p_Cons Cons have eq: "i # q = k # (p1' @ j # p2)"
          by auto
        then have k: "k = i" and decomp: "q = p1' @ j # p2"
          by auto
        from a Cons k i decomp have q_poss: "q \<in> poss (ts ! i)"
          by auto
        from cond_q[unfolded csstep_cond_def, rule_format, of p1' j p2]
        obtain g us where "ts ! i |_ p1' = Fun g us" and "j \<in> \<mu> (g, length us)"
          using decomp q_poss by auto
        with Cons k i show ?thesis by auto
      qed
    qed
  qed
qed

lemma csnrstep_Var_empty:
  "(Var x, t) \<notin> csnrstep \<mu> R"
  unfolding csnrstep_def csstep_p_def rstep_r_p_s_def' by auto

lemma csnrstep_preserves_root:
  assumes "(s, t) \<in> csnrstep \<mu> R"
  shows "root t = root s"
  using assms
proof (cases s)
  case (Var x)
  with assms have False
    using csnrstep_Var_empty[of x t \<mu> R] by simp
  then show ?thesis by blast
next
  case (Fun f ss)
  have step: "(Fun f ss, t) \<in> csnrstep \<mu> R"
    using assms Fun by simp
  from step show ?thesis
  proof (elim csnrstep_FunE)
    fix i ts
    assume "t = Fun f ts" and "length ts = length ss"
    with Fun show ?thesis by simp
  qed
qed

lemma csnrsteps_preserve_root:
  assumes "(s, t) \<in> (csnrstep \<mu> R)\<^sup>*"
  shows "root t = root s"
  using assms by (induct rule: rtrancl.induct, auto dest: csnrstep_preserves_root)

lemma csnrstep_imp_nrrstep:
  assumes "(s, t) \<in> csnrstep \<mu> R"
  shows "(s, t) \<in> nrrstep R"
proof -
  from assms obtain p lr \<sigma> where p: "p \<noteq> []"
    and step: "(s, t) \<in> rstep_r_p_s R lr p \<sigma>"
    unfolding csnrstep_def csstep_p_def by auto
  have step': "(s, t) \<in> qrstep_r_p_s False {} R lr p \<sigma>"
    using step unfolding rstep_r_p_s_def' qrstep_r_p_s_def by auto
  have "(s, t) \<in> nrqrstep False {} R"
    by (rule qrstep_r_p_s_imp_nrqrstep[OF step' p])
  then show ?thesis by simp
qed

lemma csstep_Var_empty_wf:
  assumes wf: "wf_trs R"
  shows "(Var x, t) \<notin> csstep \<mu> R"
proof
  assume "(Var x, t) \<in> csstep \<mu> R"
  then obtain p lr \<sigma> where step: "(Var x, t) \<in> rstep_r_p_s R lr p \<sigma>"
    unfolding csstep_def csstep_p_def by auto
  from step have "p = []"
    unfolding rstep_r_p_s_def' by (cases p, auto)
  with step have "fst lr \<cdot> \<sigma> = Var x" and "lr \<in> R"
    unfolding rstep_r_p_s_def' by auto
  then have "is_Var (fst lr)"
    by (cases "fst lr", auto)
  moreover from wf \<open>lr \<in> R\<close> have "\<exists>f ts. fst lr = Fun f ts"
    unfolding wf_trs_def by (cases lr, auto)
  ultimately show False
    by auto
qed

lemma SN_on_csstep_Var:
  assumes wf: "wf_trs R"
  shows "SN_on (csstep \<mu> R) {Var x}"
  unfolding SN_on_def
proof clarify
  fix f
  assume f0_mem: "f 0 = Var x"
    and chain: "\<forall>i. (f i, f (Suc i)) \<in> csstep \<mu> R"
  then have f0: "f 0 = Var x"
    by simp
  from chain have "(f 0, f (Suc 0)) \<in> csstep \<mu> R"
    by blast
  with f0 have step0: "(Var x, f (Suc 0)) \<in> csstep \<mu> R"
    by simp
  have no_step0: "(Var x, f (Suc 0)) \<notin> csstep \<mu> R"
    by (rule csstep_Var_empty_wf[OF wf])
  from step0 no_step0 show False
    by blast
qed

lemma csrstepE:
  assumes "(s, t) \<in> csrstep \<mu> R"
  obtains l r \<sigma> where "(l, r) \<in> R" "s = l \<cdot> \<sigma>" "t = r \<cdot> \<sigma>"
proof -
  from assms obtain lr \<sigma> where step: "(s, t) \<in> rstep_r_p_s R lr [] \<sigma>"
    unfolding csrstep_iff_rstep_root by auto
  then have "lr \<in> R" "s = fst lr \<cdot> \<sigma>" "t = snd lr \<cdot> \<sigma>"
    unfolding rstep_r_p_s_def' by auto
  then show ?thesis
    by (cases lr, intro that, auto)
qed

lemma csrstep_defined_root:
  assumes wf: "wf_trs R"
    and step: "(Fun f ss, t) \<in> csrstep \<mu> R"
  shows "defined R (f, length ss)"
proof -
  from step obtain l r \<sigma> where lr: "(l, r) \<in> R" and lhs: "Fun f ss = l \<cdot> \<sigma>"
    by (elim csrstepE)
  from wf lr obtain g ts where l: "l = Fun g ts"
    unfolding wf_trs_def by (cases l, auto)
  from lhs l have "g = f" "length ts = length ss"
    by auto
  with lr l show ?thesis
    unfolding defined_def by auto
qed

lemma csstep_Fun_undefined_root_notSN_imp_mu_arg_notSN:
  assumes wf: "wf_trs R"
    and undef: "\<not> defined R (f, length ss)"
    and notSN: "\<not> SN_on (csstep \<mu> R) {Fun f ss}"
  shows "\<exists>i<length ss. i \<in> \<mu> (f, length ss) \<and> \<not> SN_on (csstep \<mu> R) {ss ! i}"
proof (rule ccontr)
  let ?R = "csstep \<mu> R"
  let ?nR = "csnrstep \<mu> R"
  assume no_arg: "\<not> ?thesis"
  then have arg_SN: "\<And>i. i < length ss \<Longrightarrow> i \<in> \<mu> (f, length ss) \<Longrightarrow> SN_on ?R {ss ! i}"
    by auto
  from notSN obtain ts where start: "ts 0 = Fun f ss" and steps: "\<And>i. (ts i, ts (Suc i)) \<in> ?R"
    unfolding SN_on_def by auto
  have shape_nsteps:
    "\<And>i. (\<exists>as. ts i = Fun f as \<and> length as = length ss) \<and>
      (ts i, ts (Suc i)) \<in> ?nR"
  proof -
    fix i
    show "(\<exists>as. ts i = Fun f as \<and> length as = length ss) \<and>
      (ts i, ts (Suc i)) \<in> ?nR"
    proof (induct i)
      case 0
      have shape: "\<exists>as. ts 0 = Fun f as \<and> length as = length ss"
        using start by auto
      from steps[of 0] have step0: "(ts 0, ts (Suc 0)) \<in> csrstep \<mu> R \<union> ?nR"
        unfolding csstep_root_nonroot by simp
      have nstep: "(ts 0, ts (Suc 0)) \<in> ?nR"
      proof (rule ccontr)
        assume "(ts 0, ts (Suc 0)) \<notin> ?nR"
        with step0 have "(ts 0, ts (Suc 0)) \<in> csrstep \<mu> R" by auto
        with start have "defined R (f, length ss)"
          using csrstep_defined_root[OF wf, of f ss "ts (Suc 0)" \<mu>] by simp
        with undef show False by simp
      qed
      from shape nstep show ?case by auto
    next
      case (Suc i)
      from Suc obtain as where tsi: "ts i = Fun f as" and len: "length as = length ss"
        and nstep_i: "(ts i, ts (Suc i)) \<in> ?nR" by auto
      from csnrstep_preserves_root[OF nstep_i] have root_eq:
        "root (ts (Suc i)) = Some (f, length as)"
        unfolding tsi by simp
      then obtain bs where tsSuc: "ts (Suc i) = Fun f bs"
        and len_bs_as: "length bs = length as"
        by (cases "ts (Suc i)", auto)
      from len_bs_as len have len_bs: "length bs = length ss"
        by simp
      from steps[of "Suc i"] have stepSuc: "(ts (Suc i), ts (Suc (Suc i))) \<in> csrstep \<mu> R \<union> ?nR"
        unfolding csstep_root_nonroot by simp
      have nstep: "(ts (Suc i), ts (Suc (Suc i))) \<in> ?nR"
      proof (rule ccontr)
        assume "(ts (Suc i), ts (Suc (Suc i))) \<notin> ?nR"
        with stepSuc have "(ts (Suc i), ts (Suc (Suc i))) \<in> csrstep \<mu> R" by auto
        with tsSuc len_bs have "defined R (f, length ss)"
          using csrstep_defined_root[OF wf, of f bs "ts (Suc (Suc i))" \<mu>] by simp
        with undef show False by simp
      qed
      from tsSuc len_bs nstep show ?case by auto
    qed
  qed
  have roots: "\<exists>as. ts i = Fun f as \<and> length as = length ss" for i
    using shape_nsteps[of i] by auto
  from choice[OF allI[OF roots]] obtain sss where ts: "\<And>i. ts i = Fun f (sss i)"
    and len: "\<And>i. length (sss i) = length ss" by force
  have nsteps: "\<And>i. (Fun f (sss i), Fun f (sss (Suc i))) \<in> ?nR"
    using shape_nsteps[of i for i] by (simp add: ts)
  let ?strict = "\<lambda>i. \<exists>j<length ss. j \<in> \<mu> (f, length ss) \<and>
      (sss i ! j, sss (Suc i) ! j) \<in> ?R"
  have strict_all: "\<And>i. ?strict i"
  proof -
    fix i
    from nsteps[of i] show "?strict i"
    proof (elim csnrstep_FunE)
      fix j us
      assume j: "j < length (sss i)" and jmu: "j \<in> \<mu> (f, length (sss i))"
        and sub: "(sss i ! j, us ! j) \<in> ?R"
        and tgt: "Fun f (sss (Suc i)) = Fun f us"
      from j len[of i] have jss: "j < length ss" by simp
      from jmu len[of i] have jmu': "j \<in> \<mu> (f, length ss)" by simp
      from tgt have us: "sss (Suc i) = us" by simp
      from jss jmu' sub us show ?thesis by auto
    qed
  qed
  let ?idx = "\<lambda>i. SOME j. j < length ss \<and> j \<in> \<mu> (f, length ss) \<and>
      (sss i ! j, sss (Suc i) ! j) \<in> ?R"
  define idx where "idx = ?idx"
  have idx_strict: "idx i < length ss \<and> idx i \<in> \<mu> (f, length ss) \<and>
      (sss i ! idx i, sss (Suc i) ! idx i) \<in> ?R" for i
  proof -
    from strict_all[of i] have ex: "\<exists>j. j < length ss \<and> j \<in> \<mu> (f, length ss) \<and>
      (sss i ! j, sss (Suc i) ! j) \<in> ?R" .
    show ?thesis
      unfolding idx_def by (rule someI_ex[OF ex])
  qed
  have idx_bound: "idx i \<le> length ss" for i
    using idx_strict[of i] by auto
  have fin: "finite (idx ` X)" for X
  proof (rule finite_subset)
    show "idx ` X \<subseteq> {i. i \<le> length ss}" using idx_bound by auto
    have id: "{i. i \<le> length ss} = set [0 ..< Suc (length ss)]" by auto
    show "finite {i. i \<le> length ss}" unfolding id by (rule finite_set)
  qed
  have inf_strict: "infinite {i. ?strict i}"
    using strict_all by simp
  from pigeonhole_infinite[OF inf_strict fin]
  obtain j where infj_set: "infinite {i \<in> {i. ?strict i}. idx i = j}" by auto
  then have infj: "INFM i. idx i = j"
    unfolding INFM_iff_infinite
    using infinite_super[of "{i \<in> {i. ?strict i}. idx i = j}" "{i. idx i = j}"]
    by auto
  from infj[unfolded INFM_nat_le, rule_format, of 0]
  obtain k where kj: "idx k = j" by auto
  from idx_strict[of k] kj have jss: "j < length ss" and jmu: "j \<in> \<mu> (f, length ss)" by auto
  let ?ss = "\<lambda>i. sss i ! j"
  have SN: "SN_on ?R {?ss 0}"
    using arg_SN[OF jss jmu] start ts[of 0] by simp
  have j_steps: "(?ss i, ?ss (Suc i)) \<in> ?R\<^sup>=" for i
  proof -
    from nsteps[of i] show ?thesis
    proof (elim csnrstep_FunE)
      fix k us
      assume k: "k < length (sss i)"
        and step: "(sss i ! k, us ! k) \<in> ?R"
        and tgt: "Fun f (sss (Suc i)) = Fun f us"
        and same: "\<And>l. l < length (sss i) \<Longrightarrow> l \<noteq> k \<Longrightarrow> us ! l = sss i ! l"
      from tgt have us_eq: "sss (Suc i) = us" by simp
      show ?thesis
      proof (cases "j = k")
        case True
        with step us_eq show ?thesis by auto
      next
        case False
        from jss len[of i] have "j < length (sss i)" by simp
        from same[OF this False] us_eq show ?thesis by simp
      qed
    qed
  qed
  have jsteps: "(?ss i, ?ss (Suc i)) \<in> Id \<union> ?R" for i
    using j_steps[of i] by auto
  have compat: "Id O ?R \<subseteq> ?R" by auto
  from non_strict_ending[of ?ss Id ?R, OF allI[OF jsteps] compat SN]
  obtain k where k: "\<And>l. l \<ge> k \<Longrightarrow> (?ss l, ?ss (Suc l)) \<notin> ?R" by auto
  from infj[unfolded INFM_nat_le, rule_format, of k]
  obtain l where lk: "l \<ge> k" and lj: "idx l = j" by auto
  from idx_strict[of l] lj have "(?ss l, ?ss (Suc l)) \<in> ?R" by auto
  with k[OF lk] show False by auto
qed

lemma csstep_notSN_imp_mu_defined_subterm:
  assumes wf: "wf_trs R"
    and notSN: "\<not> SN_on (csstep \<mu> R) {t}"
  shows "\<exists>p f ts. p \<in> mu_fun_poss \<mu> t \<and> t |_ p = Fun f ts \<and>
    defined R (f, length ts) \<and> \<not> SN_on (csstep \<mu> R) {t |_ p}"
  using notSN
proof (induct t)
  case (Var x)
  from SN_on_csstep_Var[OF wf, of \<mu> x] Var.prems show ?case
    by simp
next
  case (Fun f ss)
  show ?case
  proof (cases "defined R (f, length ss)")
    case True
    show ?thesis
      by (intro exI[of _ "[]"] exI[of _ f] exI[of _ ss], insert True Fun.prems, auto)
  next
    case False
    from csstep_Fun_undefined_root_notSN_imp_mu_arg_notSN[OF wf False Fun.prems]
    obtain i where i: "i < length ss" and imu: "i \<in> \<mu> (f, length ss)"
      and notSN_i: "\<not> SN_on (csstep \<mu> R) {ss ! i}"
      by auto
    from Fun.hyps[OF nth_mem[OF i] notSN_i]
    obtain p g ts where p: "p \<in> mu_fun_poss \<mu> (ss ! i)"
      and sub: "ss ! i |_ p = Fun g ts"
      and def: "defined R (g, length ts)"
      and notSN_p: "\<not> SN_on (csstep \<mu> R) {ss ! i |_ p}"
      by auto
    let ?p = "i # p"
    have p_mu: "?p \<in> mu_fun_poss \<mu> (Fun f ss)"
      using i imu p by auto
    have sub_p: "Fun f ss |_ ?p = Fun g ts"
      using i sub by simp
    have notSN_p': "\<not> SN_on (csstep \<mu> R) {Fun f ss |_ ?p}"
      using i notSN_p by simp
    show ?thesis
      by (intro exI[of _ ?p] exI[of _ g] exI[of _ ts],
          insert p_mu sub_p def notSN_p', auto)
  qed
qed

fun mu_poss :: "'f mu \<Rightarrow> ('f, 'v) term \<Rightarrow> pos set"
where
  "mu_poss \<mu> (Var x) = {[]}"
| "mu_poss \<mu> (Fun f ts) =
    {[]} \<union> (\<Union>i\<in>\<mu> (f, length ts) \<inter> {0..<length ts}. {i # p |p. p \<in> mu_poss \<mu> (ts ! i)})"

definition mu_vars_term :: "'f mu \<Rightarrow> ('f, 'v) term \<Rightarrow> 'v set"
where
  "mu_vars_term \<mu> t = {x. \<exists>p. p \<in> mu_poss \<mu> t \<and> t |_ p = Var x}"

definition rhs_mu_vars_condition :: "'f mu \<Rightarrow> ('f, 'v) trs \<Rightarrow> bool"
where
  "rhs_mu_vars_condition \<mu> R \<longleftrightarrow>
    (\<forall>l r x. (l, r) \<in> R \<longrightarrow> x \<in> mu_vars_term \<mu> r \<longrightarrow> x \<in> mu_vars_term \<mu> l)"

lemma mu_fun_poss_imp_mu_poss:
  assumes "p \<in> mu_fun_poss \<mu> t"
  shows "p \<in> mu_poss \<mu> t"
  using assms by (induct t arbitrary: p) auto

lemma mu_poss_imp_poss:
  assumes "p \<in> mu_poss \<mu> t"
  shows "p \<in> poss t"
  using assms by (induct t arbitrary: p) auto

lemma mu_vars_term_imp_vars_term:
  assumes "x \<in> mu_vars_term \<mu> t"
  shows "x \<in> vars_term t"
proof -
  from assms obtain p where p: "p \<in> mu_poss \<mu> t" and sub: "t |_ p = Var x"
    unfolding mu_vars_term_def by auto
  from mu_poss_imp_poss[OF p] sub show ?thesis
    using vars_term_subt_at by force
qed

lemma mu_fun_poss_subst_cases_aux:
  assumes p: "p \<in> mu_fun_poss \<mu> (t \<cdot> \<sigma>)"
  shows "(p \<in> mu_fun_poss \<mu> t \<and> (t \<cdot> \<sigma>) |_ p = (t |_ p) \<cdot> \<sigma>) \<or>
    (\<exists>x q1 q2. q1 \<in> poss t \<and> t |_ q1 = Var x \<and> x \<in> vars_term t \<and>
      p = q1 @ q2 \<and> q2 \<in> mu_fun_poss \<mu> (\<sigma> x) \<and> (t \<cdot> \<sigma>) |_ p = \<sigma> x |_ q2)"
  using p
proof (induct t arbitrary: p)
  case (Var x)
  then show ?case
    by auto
next
  case (Fun f ss)
  show ?case
  proof (cases p)
    case Nil
    then show ?thesis
      by auto
  next
    case (Cons i q)
    from Fun.prems[unfolded Cons]
    have i: "i \<in> \<mu> (f, length ss)" "i < length ss"
      and q: "q \<in> mu_fun_poss \<mu> (ss ! i \<cdot> \<sigma>)"
      by auto
    from Fun.hyps[OF nth_mem[OF i(2)] q]
    show ?thesis
    proof
      assume orig: "q \<in> mu_fun_poss \<mu> (ss ! i) \<and>
        (ss ! i \<cdot> \<sigma>) |_ q = (ss ! i |_ q) \<cdot> \<sigma>"
      then have "p \<in> mu_fun_poss \<mu> (Fun f ss) \<and>
        (Fun f ss \<cdot> \<sigma>) |_ p = (Fun f ss |_ p) \<cdot> \<sigma>"
        using i Cons by auto
      then show ?thesis by auto
    next
      assume subst: "\<exists>x q1 q2. q1 \<in> poss (ss ! i) \<and> ss ! i |_ q1 = Var x \<and>
        x \<in> vars_term (ss ! i) \<and> q = q1 @ q2 \<and>
        q2 \<in> mu_fun_poss \<mu> (\<sigma> x) \<and> (ss ! i \<cdot> \<sigma>) |_ q = \<sigma> x |_ q2"
      then obtain x q1 q2 where q1: "q1 \<in> poss (ss ! i)"
        and sub: "ss ! i |_ q1 = Var x"
        and vars: "x \<in> vars_term (ss ! i)"
        and q_eq: "q = q1 @ q2"
        and q2: "q2 \<in> mu_fun_poss \<mu> (\<sigma> x)"
        and sub_at: "(ss ! i \<cdot> \<sigma>) |_ q = \<sigma> x |_ q2"
        by blast
      have "i # q1 \<in> poss (Fun f ss)"
        using i q1 by auto
      moreover have "Fun f ss |_ (i # q1) = Var x"
        using i sub by simp
      moreover have "x \<in> vars_term (Fun f ss)"
        using i vars by auto
      moreover have "p = (i # q1) @ q2"
        using Cons q_eq by simp
      moreover have "(Fun f ss \<cdot> \<sigma>) |_ p = \<sigma> x |_ q2"
        using i Cons q_eq sub_at by simp
      ultimately show ?thesis
      using q2 by blast
    qed
  qed
qed

lemma mu_fun_poss_subst_cases_aux_mu:
  assumes p: "p \<in> mu_fun_poss \<mu> (t \<cdot> \<sigma>)"
  shows "(p \<in> mu_fun_poss \<mu> t \<and> (t \<cdot> \<sigma>) |_ p = (t |_ p) \<cdot> \<sigma>) \<or>
    (\<exists>x q1 q2. q1 \<in> mu_poss \<mu> t \<and> t |_ q1 = Var x \<and> x \<in> vars_term t \<and>
      p = q1 @ q2 \<and> q2 \<in> mu_fun_poss \<mu> (\<sigma> x) \<and> (t \<cdot> \<sigma>) |_ p = \<sigma> x |_ q2)"
  using p
proof (induct t arbitrary: p)
  case (Var x)
  then show ?case
    by auto
next
  case (Fun f ss)
  then show ?case
  proof (cases p)
    case Nil
    then show ?thesis by auto
  next
    case (Cons i q)
    from Fun.prems[unfolded Cons]
    have i: "i \<in> \<mu> (f, length ss)" "i < length ss"
      and q: "q \<in> mu_fun_poss \<mu> (ss ! i \<cdot> \<sigma>)"
      by auto
    from Fun.hyps[OF nth_mem[OF i(2)] q]
    show ?thesis
    proof
      assume orig: "q \<in> mu_fun_poss \<mu> (ss ! i) \<and>
        (ss ! i \<cdot> \<sigma>) |_ q = (ss ! i |_ q) \<cdot> \<sigma>"
      then have "p \<in> mu_fun_poss \<mu> (Fun f ss) \<and>
        (Fun f ss \<cdot> \<sigma>) |_ p = (Fun f ss |_ p) \<cdot> \<sigma>"
        using i Cons by auto
      then show ?thesis by auto
    next
      assume subst: "\<exists>x q1 q2. q1 \<in> mu_poss \<mu> (ss ! i) \<and> ss ! i |_ q1 = Var x \<and>
        x \<in> vars_term (ss ! i) \<and> q = q1 @ q2 \<and>
        q2 \<in> mu_fun_poss \<mu> (\<sigma> x) \<and> (ss ! i \<cdot> \<sigma>) |_ q = \<sigma> x |_ q2"
      then obtain x q1 q2 where q1: "q1 \<in> mu_poss \<mu> (ss ! i)"
        and sub: "ss ! i |_ q1 = Var x"
        and vars: "x \<in> vars_term (ss ! i)"
        and q_eq: "q = q1 @ q2"
        and q2: "q2 \<in> mu_fun_poss \<mu> (\<sigma> x)"
        and sub_at: "(ss ! i \<cdot> \<sigma>) |_ q = \<sigma> x |_ q2"
        by blast
      have "i # q1 \<in> mu_poss \<mu> (Fun f ss)"
        using i q1 by auto
      moreover have "Fun f ss |_ (i # q1) = Var x"
        using i sub by simp
      moreover have "x \<in> vars_term (Fun f ss)"
        using i vars by auto
      moreover have "p = (i # q1) @ q2"
        using Cons q_eq by simp
      moreover have "(Fun f ss \<cdot> \<sigma>) |_ p = \<sigma> x |_ q2"
        using i Cons q_eq sub_at by simp
      ultimately show ?thesis
        using q2 by blast
    qed
  qed
qed

lemma mu_fun_poss_subst_lift:
  assumes p: "p \<in> mu_fun_poss \<mu> t"
  shows "p \<in> mu_fun_poss \<mu> (t \<cdot> \<sigma>)"
  using assms by (induct t arbitrary: p) auto

lemma mu_poss_subst_lift:
  assumes p: "p \<in> mu_poss \<mu> t"
  shows "p \<in> mu_poss \<mu> (t \<cdot> \<sigma>)"
  using assms
proof (induct t arbitrary: p)
  case (Var x)
  then have "p = []" by simp
  then show ?case by (cases "\<sigma> x", auto)
next
  case (Fun f ts)
  then show ?case by auto
qed

lemma mu_fun_poss_subst_cases [case_names orig subst]:
  assumes p: "p \<in> mu_fun_poss \<mu> (t \<cdot> \<sigma>)"
  obtains
    (orig) "p \<in> mu_fun_poss \<mu> t" "(t \<cdot> \<sigma>) |_ p = (t |_ p) \<cdot> \<sigma>"
  | (subst) x q1 q2 where "q1 \<in> poss t" "t |_ q1 = Var x" "x \<in> vars_term t"
      "p = q1 @ q2" "q2 \<in> mu_fun_poss \<mu> (\<sigma> x)" "(t \<cdot> \<sigma>) |_ p = \<sigma> x |_ q2"
  using mu_fun_poss_subst_cases_aux[OF p] by blast

lemma mu_fun_poss_replace_at_root:
  assumes p: "p \<in> mu_fun_poss \<mu> t"
    and u: "is_Fun u"
  shows "p \<in> mu_fun_poss \<mu> (replace_at t p u)"
  using p
proof (induct t arbitrary: p)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ss)
  show ?case
  proof (cases p)
    case Nil
    then show ?thesis
      using u by (cases u, auto)
  next
    case (Cons i q)
    with Fun.prems have i: "i \<in> \<mu> (f, length ss)" "i < length ss"
      and q: "q \<in> mu_fun_poss \<mu> (ss ! i)"
      by auto
    have rec: "q \<in> mu_fun_poss \<mu> (replace_at (ss ! i) q u)"
      by (rule Fun.hyps[OF nth_mem[OF i(2)] q])
    show ?thesis
      using i rec Cons by (simp add: nth_append)
  qed
qed

lemma mu_fun_poss_replace_at_append:
  assumes p: "p \<in> mu_fun_poss \<mu> t"
    and q: "q \<in> mu_fun_poss \<mu> u"
  shows "p @ q \<in> mu_fun_poss \<mu> (replace_at t p u)"
  using p
proof (induct t arbitrary: p)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ss)
  show ?case
  proof (cases p)
    case Nil
    then show ?thesis
      using q by simp
  next
    case (Cons i p')
    with Fun.prems have i: "i \<in> \<mu> (f, length ss)" "i < length ss"
      and p': "p' \<in> mu_fun_poss \<mu> (ss ! i)"
      by auto
    have rec: "p' @ q \<in> mu_fun_poss \<mu> (replace_at (ss ! i) p' u)"
      by (rule Fun.hyps[OF nth_mem[OF i(2)] p'])
    show ?thesis
      using i rec Cons by (simp add: nth_append)
  qed
qed

lemma csstep_redex_mu_fun_poss:
  assumes wf: "wf_trs R"
    and step: "(s, t) \<in> csstep_p \<mu> R q"
  shows "q \<in> mu_fun_poss \<mu> s"
proof -
  from step obtain lr \<sigma> where rstep: "(s, t) \<in> rstep_r_p_s R lr q \<sigma>"
    and cond: "csstep_cond \<mu> q s"
    unfolding csstep_p_def by auto
  from rstep have lr: "lr \<in> R" and qposs: "q \<in> poss s" and redex: "s |_ q = fst lr \<cdot> \<sigma>"
    unfolding rstep_r_p_s_def' by auto
  obtain l0 r0 where lr0: "lr = (l0, r0)"
    by (cases lr, auto)
  from wf lr have "\<exists>f ts. l0 = Fun f ts"
    unfolding wf_trs_def lr0 by auto
  then obtain f ts where l: "fst lr = Fun f ts"
    unfolding lr0 by auto
  have qfun: "q \<in> fun_poss s"
    by (rule poss_is_Fun_fun_poss[OF qposs], insert redex l, auto)
  from cond qfun show ?thesis
  proof (induct s arbitrary: q)
    case (Var x)
    then show ?case by simp
  next
    case (Fun g ss)
    show ?case
    proof (cases q)
      case Nil
      then show ?thesis by simp
    next
      case (Cons i q')
      from Fun.prems Cons have i: "i < length ss"
        and qfun': "q' \<in> fun_poss (ss ! i)"
        by auto
      have qposs': "q' \<in> poss (ss ! i)"
        by (rule fun_poss_imp_poss[OF qfun'])
      from Fun.prems(1)[unfolded csstep_cond_def, rule_format, of "[]" i q'] Cons i qposs'
      have imu: "i \<in> \<mu> (g, length ss)"
        by auto
      have cond': "csstep_cond \<mu> q' (ss ! i)"
        by (rule csstep_cond_Cons_FunD(2)[OF Fun.prems(1)[unfolded Cons]])
          (use i qposs' in auto)
      have "q' \<in> mu_fun_poss \<mu> (ss ! i)"
        by (rule Fun.hyps[OF nth_mem[OF i(1)] cond' qfun'])
      with i imu Cons show ?thesis by auto
    qed
  qed
qed

lemma replace_at_append:
  assumes p: "p \<in> poss t"
    and q: "q \<in> poss (t |_ p)"
  shows "replace_at t (p @ q) u = replace_at t p (replace_at (t |_ p) q u)"
  unfolding ctxt_of_pos_term_append[OF p]
  by (simp add: replace_at_subt_at[OF p])

lemma replace_at_overwrite:
  assumes p: "p \<in> poss t"
  shows "replace_at (replace_at t p u) p v = replace_at t p v"
  using p
proof (induct p arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons i p)
  then obtain f ts where t: "t = Fun f ts" and i: "i < length ts" and p: "p \<in> poss (ts ! i)"
    by (cases t, auto)
  show ?case
    unfolding t
    using Cons.hyps[OF p] i by (simp add: nth_append)
qed

lemma csstep_mu_subterm_lift:
  assumes wf: "wf_trs R"
    and p: "p \<in> mu_fun_poss \<mu> t"
    and step: "(t |_ p, u) \<in> csstep \<mu> R"
  shows "(t, replace_at t p u) \<in> csstep \<mu> R"
proof -
  from p have pposs: "p \<in> poss t"
    using fun_poss_imp_poss mu_fun_poss_imp_fun_poss by blast
  from step obtain q where stepq: "(t |_ p, u) \<in> csstep_p \<mu> R q"
    unfolding csstep_def by auto
  from stepq obtain lr \<sigma> where rstep: "(t |_ p, u) \<in> rstep_r_p_s R lr q \<sigma>"
    and cond: "csstep_cond \<mu> q (t |_ p)"
    unfolding csstep_p_def by auto
  from rstep have qposs: "q \<in> poss (t |_ p)"
    and u: "u = replace_at (t |_ p) q (snd lr \<cdot> \<sigma>)"
    unfolding rstep_r_p_s_def' by auto
  have q_mu: "q \<in> mu_fun_poss \<mu> (t |_ p)"
    by (rule csstep_redex_mu_fun_poss[OF wf stepq])
  have pq_mu: "p @ q \<in> mu_fun_poss \<mu> t"
  proof -
    have "p @ q \<in> mu_fun_poss \<mu> (replace_at t p (t |_ p))"
      by (rule mu_fun_poss_replace_at_append[OF p q_mu])
    also have "replace_at t p (t |_ p) = t"
      by (rule replace_at_ident[OF pposs refl])
    finally show ?thesis .
  qed
  have cond_pq: "csstep_cond \<mu> (p @ q) t"
    by (rule mu_fun_poss_imp_csstep_cond[OF pq_mu])
  have rstep_pq: "(t, replace_at t p u) \<in> rstep_r_p_s R lr (p @ q) \<sigma>"
    using rstep pposs qposs u
    by (auto simp: rstep_r_p_s_def' replace_at_append)
  from rstep_pq cond_pq have "(t, replace_at t p u) \<in> csstep_p \<mu> R (p @ q)"
    unfolding csstep_p_def by (cases lr, auto)
  then show ?thesis
    unfolding csstep_def by auto
qed

lemma notSN_mu_subterm_imp_notSN:
  assumes wf: "wf_trs R"
    and p: "p \<in> mu_fun_poss \<mu> t"
    and notSN: "\<not> SN_on (csstep \<mu> R) {t |_ p}"
  shows "\<not> SN_on (csstep \<mu> R) {t}"
proof -
  let ?R = "csstep \<mu> R"
  from p have pposs: "p \<in> poss t"
    using fun_poss_imp_poss mu_fun_poss_imp_fun_poss by blast
  from notSN obtain f where f0: "f 0 = t |_ p"
    and chain: "\<And>i. (f i, f (Suc i)) \<in> ?R"
    unfolding SN_on_def by auto
  define g where "g i = replace_at t p (f i)" for i
  have g0: "g 0 = t"
    unfolding g_def f0 by (rule replace_at_ident[OF pposs refl])
  have gstep: "(g i, g (Suc i)) \<in> ?R" for i
  proof -
    have f_fun: "is_Fun (f i)"
    proof (cases "f i")
      case (Var x)
      from chain[of i] have "(Var x, f (Suc i)) \<in> ?R"
        unfolding Var .
      with csstep_Var_empty_wf[OF wf, of x "f (Suc i)" \<mu>] show ?thesis
        by blast
    next
      case (Fun f' ts)
      then show ?thesis by simp
    qed
    have p_g: "p \<in> mu_fun_poss \<mu> (g i)"
      unfolding g_def by (rule mu_fun_poss_replace_at_root[OF p f_fun])
    have sub_g: "g i |_ p = f i"
      unfolding g_def by (rule replace_at_subt_at[OF pposs])
    have "(g i, replace_at (g i) p (f (Suc i))) \<in> ?R"
      by (rule csstep_mu_subterm_lift[OF wf p_g], unfold sub_g, rule chain)
    moreover have "replace_at (g i) p (f (Suc i)) = g (Suc i)"
      unfolding g_def
      by (rule replace_at_overwrite[OF pposs])
    ultimately show ?thesis by simp
  qed
  show ?thesis
    unfolding SN_on_def
    by (intro notI, insert g0 gstep, blast)
qed

lemma SN_on_mu_subterm:
  assumes wf: "wf_trs R"
    and p: "p \<in> mu_fun_poss \<mu> t"
    and SN: "SN_on (csstep \<mu> R) {t}"
  shows "SN_on (csstep \<mu> R) {t |_ p}"
  using assms notSN_mu_subterm_imp_notSN by blast

lemma SN_on_mu_pos:
  assumes wf: "wf_trs R"
    and p: "p \<in> mu_poss \<mu> t"
    and SN: "SN_on (csstep \<mu> R) {t}"
  shows "SN_on (csstep \<mu> R) {t |_ p}"
  using p SN
proof (induct t arbitrary: p)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ss)
  show ?case
  proof (cases p)
    case Nil
    with Fun.prems show ?thesis by simp
  next
    case (Cons i q)
    from Fun.prems(1)[unfolded Cons]
    have i: "i \<in> \<mu> (f, length ss)" "i < length ss"
      and q: "q \<in> mu_poss \<mu> (ss ! i)"
      by auto
    have SN_i: "SN_on (csstep \<mu> R) {ss ! i}"
    proof (cases "ss ! i")
      case (Var x)
      show ?thesis unfolding Var by (rule SN_on_csstep_Var[OF wf])
    next
      case (Fun g ts)
      have "[i] \<in> mu_fun_poss \<mu> (Fun f ss)"
        using i Fun by auto
      from SN_on_mu_subterm[OF wf this Fun.prems(2)]
      show ?thesis by simp
    qed
    from Fun.hyps[OF nth_mem[OF i(2)] q SN_i]
    show ?thesis unfolding Cons by simp
  qed
qed

lemma mu_fun_poss_subst_var_lift:
  assumes p: "p \<in> mu_poss \<mu> t"
    and sub: "t |_ p = Var x"
    and q: "q \<in> mu_fun_poss \<mu> (\<sigma> x)"
  shows "p @ q \<in> mu_fun_poss \<mu> (t \<cdot> \<sigma>)"
  using assms
proof (induct t arbitrary: p)
  case (Var y)
  then have "p = []" and "x = y"
    by auto
  with Var show ?case by simp
next
  case (Fun f ts)
  then show ?case
  proof (cases p)
    case Nil
    with Fun.prems(2) show ?thesis by simp
  next
    case (Cons i p')
    from Fun.prems(1)[unfolded Cons]
    have i: "i \<in> \<mu> (f, length ts)" "i < length ts"
      and p': "p' \<in> mu_poss \<mu> (ts ! i)"
      by auto
    from Fun.prems(2)[unfolded Cons] i
    have sub': "ts ! i |_ p' = Var x"
      by simp
    from Fun.hyps[OF nth_mem[OF i(2)] p' sub' Fun.prems(3)]
    have "p' @ q \<in> mu_fun_poss \<mu> (ts ! i \<cdot> \<sigma>)" .
    with i Cons show ?thesis by auto
  qed
qed

definition mu_supt :: "'f mu \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
where
  "mu_supt \<mu> s t \<longleftrightarrow> (\<exists>i p. i # p \<in> mu_poss \<mu> s \<and> s |_ (i # p) = t)"

definition mu_Tinf :: "'f mu \<Rightarrow> (('f, 'v) term \<times> ('f, 'v) term) set \<Rightarrow> ('f, 'v) term set"
where
  "mu_Tinf \<mu> R = {t. \<not> SN_on R {t} \<and> (\<forall>s. mu_supt \<mu> t s \<longrightarrow> SN_on R {s})}"

lemma mu_supt_imp_supt:
  assumes "mu_supt \<mu> s t"
  shows "s \<rhd> t"
proof -
  from assms obtain i p where ip: "i # p \<in> mu_poss \<mu> s"
    and t: "s |_ (i # p) = t"
    unfolding mu_supt_def by auto
  have "i # p \<in> poss s"
    using ip mu_poss_imp_poss by blast
  then have "s \<rhd> s |_ (i # p)"
    by (rule subt_at_nepos_imp_supt)
  then show ?thesis
    unfolding t .
qed

lemma Tinf_imp_mu_Tinf:
  assumes "t \<in> Tinf R"
  shows "t \<in> mu_Tinf \<mu> R"
  using assms mu_supt_imp_supt unfolding Tinf_def mu_Tinf_def by blast

lemma not_SN_imp_subt_mu_Tinf:
  assumes "\<not> SN_on R {t}"
  shows "\<exists>u. t \<unrhd> u \<and> u \<in> mu_Tinf \<mu> R"
  using not_SN_imp_subt_Tinf[OF assms] Tinf_imp_mu_Tinf by blast

lemma step_SN_on_target:
  assumes SN: "SN_on R {s}"
    and step: "(s, t) \<in> R"
  shows "SN_on R {t}"
proof (rule ccontr)
  assume "\<not> SN_on R {t}"
  then obtain f where f0: "f 0 = t" and steps: "\<And>i. (f i, f (Suc i)) \<in> R"
    unfolding SN_on_def by auto
  define g where "g n = (case n of 0 \<Rightarrow> s | Suc m \<Rightarrow> f m)" for n
  have "g 0 \<in> {s}" unfolding g_def by simp
  moreover have "\<And>i. (g i, g (Suc i)) \<in> R"
  proof -
    fix i
    show "(g i, g (Suc i)) \<in> R"
    proof (cases i)
      case 0
      then show ?thesis using step f0 unfolding g_def by simp
    next
      case (Suc n)
      then show ?thesis using steps[of n] unfolding g_def by simp
    qed
  qed
  ultimately show False
    using SN unfolding SN_on_def by blast
qed

lemma step_notSN_on_source:
  assumes step: "(s, t) \<in> R"
    and notSN: "\<not> SN_on R {t}"
  shows "\<not> SN_on R {s}"
proof
  assume "SN_on R {s}"
  from step_SN_on_target[OF this step] notSN show False by contradiction
qed

lemma steps_notSN_on_source:
  assumes steps: "(s, t) \<in> R\<^sup>*"
    and notSN: "\<not> SN_on R {t}"
  shows "\<not> SN_on R {s}"
  using steps notSN
proof (induct rule: rtrancl_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  from step_notSN_on_source[OF step.hyps(2) step.prems]
  have "\<not> SN_on R {y}" .
  from step.hyps(3)[OF this] show ?case .
qed

lemma csnrstep_mu_Tinf_preserve:
  assumes wf: "wf_trs R"
    and step: "(s, t) \<in> csnrstep \<mu> R"
    and sT: "s \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and notSN_t: "\<not> SN_on (csstep \<mu> R) {t}"
  shows "t \<in> mu_Tinf \<mu> (csstep \<mu> R)"
proof -
  from sT have min: "\<And>u. mu_supt \<mu> s u \<Longrightarrow> SN_on (csstep \<mu> R) {u}"
    unfolding mu_Tinf_def by auto
  show ?thesis
    unfolding mu_Tinf_def
  proof (intro CollectI conjI allI impI)
    show "\<not> SN_on (csstep \<mu> R) {t}"
      by (rule notSN_t)
  next
    fix u
    assume tu: "mu_supt \<mu> t u"
    from step show "SN_on (csstep \<mu> R) {u}"
    proof (cases s)
      case (Var x)
      from step Var have False
        using csnrstep_Var_empty[of x t \<mu> R] by simp
      then show ?thesis by blast
    next
      case (Fun f ss)
      from step[unfolded Fun] show ?thesis
      proof (elim csnrstep_FunE)
        fix i ts
        assume i: "i < length ss" and imu: "i \<in> \<mu> (f, length ss)"
          and t: "t = Fun f ts" and len: "length ts = length ss"
          and substep: "(ss ! i, ts ! i) \<in> csstep \<mu> R"
          and same: "\<And>j. j < length ss \<Longrightarrow> j \<noteq> i \<Longrightarrow> ts ! j = ss ! j"
        from tu[unfolded t mu_supt_def]
        obtain j q where jq: "j # q \<in> mu_poss \<mu> (Fun f ts)"
          and u: "Fun f ts |_ (j # q) = u"
          by auto
        from jq have j: "j < length ts" and jmu: "j \<in> \<mu> (f, length ts)"
          and q: "q \<in> mu_poss \<mu> (ts ! j)"
          by auto
        show ?thesis
        proof (cases "j = i")
          case False
          have same_j: "ts ! j = ss ! j"
            using same[of j] j len False by simp
          have "j # q \<in> mu_poss \<mu> s"
            unfolding Fun using j jmu q len same_j by auto
          moreover have "s |_ (j # q) = u"
            unfolding Fun using j len False same u by simp
          ultimately have "mu_supt \<mu> s u"
            unfolding mu_supt_def by blast
          then show ?thesis by (rule min)
        next
          case True
          have "j # [] \<in> mu_poss \<mu> s"
            unfolding Fun using j jmu len by (cases "ss ! i", auto simp: True)
          moreover have "s |_ (j # []) = ss ! i"
            unfolding Fun using i True by simp
          ultimately have "mu_supt \<mu> s (ss ! i)"
            unfolding mu_supt_def by blast
          then have SN_i: "SN_on (csstep \<mu> R) {ss ! i}"
            by (rule min)
          have SN_ti: "SN_on (csstep \<mu> R) {ts ! i}"
            by (rule step_SN_on_target[OF SN_i substep])
          have q_i: "q \<in> mu_poss \<mu> (ts ! i)"
            using q True by simp
          have u_eq: "u = ts ! i |_ q"
            using u t True j by simp
          show ?thesis
            using SN_on_mu_pos[OF wf q_i SN_ti] u_eq by simp
        qed
      qed
    qed
  qed
qed

lemma csnrsteps_mu_Tinf_preserve:
  assumes wf: "wf_trs R"
    and steps: "(s, t) \<in> (csnrstep \<mu> R)\<^sup>*"
    and sT: "s \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and notSN_t: "\<not> SN_on (csstep \<mu> R) {t}"
  shows "t \<in> mu_Tinf \<mu> (csstep \<mu> R)"
  using steps sT notSN_t
proof (induct rule: rtrancl_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  have yz: "(y, z) \<in> csstep \<mu> R"
    using step.hyps(2) unfolding csstep_root_nonroot by auto
  have notSN_y: "\<not> SN_on (csstep \<mu> R) {y}"
    by (rule step_notSN_on_source[OF yz step.prems(2)])
  from step.hyps(3)[OF step.prems(1) notSN_y]
  have yT: "y \<in> mu_Tinf \<mu> (csstep \<mu> R)" .
  show ?case
    by (rule csnrstep_mu_Tinf_preserve[OF wf step.hyps(2) yT step.prems(2)])
qed

lemma csstep_notSN_imp_mu_Tinf_defined_subterm:
  assumes wf: "wf_trs R"
    and notSN: "\<not> SN_on (csstep \<mu> R) {t}"
  shows "\<exists>p f ts. p \<in> mu_fun_poss \<mu> t \<and> t |_ p = Fun f ts \<and>
    defined R (f, length ts) \<and> t |_ p \<in> mu_Tinf \<mu> (csstep \<mu> R)"
  using notSN
proof (induct t)
  case (Var x)
  from SN_on_csstep_Var[OF wf, of \<mu> x] Var.prems show ?case
    by simp
next
  case (Fun f ss)
  show ?case
  proof (cases "defined R (f, length ss)")
    case root_def: True
    show ?thesis
    proof (cases "\<forall>i<length ss. i \<in> \<mu> (f, length ss) \<longrightarrow> SN_on (csstep \<mu> R) {ss ! i}")
      case args_SN: True
      have min: "\<And>u. mu_supt \<mu> (Fun f ss) u \<Longrightarrow> SN_on (csstep \<mu> R) {u}"
      proof -
        fix u
        assume "mu_supt \<mu> (Fun f ss) u"
        then obtain i q where iq: "i # q \<in> mu_poss \<mu> (Fun f ss)"
          and u: "Fun f ss |_ (i # q) = u"
          unfolding mu_supt_def by auto
        from iq have i: "i < length ss" and imu: "i \<in> \<mu> (f, length ss)"
          and q: "q \<in> mu_poss \<mu> (ss ! i)"
          by auto
        from args_SN i imu have SN_i: "SN_on (csstep \<mu> R) {ss ! i}"
          by auto
        show "SN_on (csstep \<mu> R) {u}"
          using SN_on_mu_pos[OF wf q SN_i] u i by simp
      qed
      have Troot: "Fun f ss \<in> mu_Tinf \<mu> (csstep \<mu> R)"
        unfolding mu_Tinf_def using Fun.prems min by auto
      show ?thesis
        apply (rule exI[where x = "[]"])
        apply (rule exI[where x = f])
        apply (rule exI[where x = ss])
        using root_def Troot apply simp
        done
    next
      case False
      then obtain i where i: "i < length ss" and imu: "i \<in> \<mu> (f, length ss)"
        and notSN_i: "\<not> SN_on (csstep \<mu> R) {ss ! i}"
        by auto
      from Fun.hyps[OF nth_mem[OF i] notSN_i]
      obtain p g ts where p: "p \<in> mu_fun_poss \<mu> (ss ! i)"
        and sub: "ss ! i |_ p = Fun g ts"
        and def: "defined R (g, length ts)"
        and T: "ss ! i |_ p \<in> mu_Tinf \<mu> (csstep \<mu> R)"
        by auto
      let ?p = "i # p"
      have "?p \<in> mu_fun_poss \<mu> (Fun f ss)"
        using i imu p by auto
      moreover have "Fun f ss |_ ?p = Fun g ts"
        using i sub by simp
      moreover have "Fun f ss |_ ?p \<in> mu_Tinf \<mu> (csstep \<mu> R)"
        using i T sub by simp
      ultimately show ?thesis
        by (intro exI[of _ ?p] exI[of _ g] exI[of _ ts], insert def, auto)
    qed
  next
    case False
    from csstep_Fun_undefined_root_notSN_imp_mu_arg_notSN[OF wf False Fun.prems]
    obtain i where i: "i < length ss" and imu: "i \<in> \<mu> (f, length ss)"
      and notSN_i: "\<not> SN_on (csstep \<mu> R) {ss ! i}"
      by auto
    from Fun.hyps[OF nth_mem[OF i] notSN_i]
    obtain p g ts where p: "p \<in> mu_fun_poss \<mu> (ss ! i)"
      and sub: "ss ! i |_ p = Fun g ts"
      and def: "defined R (g, length ts)"
      and T: "ss ! i |_ p \<in> mu_Tinf \<mu> (csstep \<mu> R)"
      by auto
    let ?p = "i # p"
    have "?p \<in> mu_fun_poss \<mu> (Fun f ss)"
      using i imu p by auto
    moreover have "Fun f ss |_ ?p = Fun g ts"
      using i sub by simp
    moreover have "Fun f ss |_ ?p \<in> mu_Tinf \<mu> (csstep \<mu> R)"
      using i T sub by simp
    ultimately show ?thesis
      by (intro exI[of _ ?p] exI[of _ g] exI[of _ ts], insert def, auto)
  qed
qed

lemma mu_Tinf_SN_on_active_subst_mu_subterm:
  assumes lhs: "is_Fun l"
    and T: "l \<cdot> \<sigma> \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and x: "x \<in> mu_vars_term \<mu> l"
    and q: "q \<in> mu_fun_poss \<mu> (\<sigma> x)"
  shows "SN_on (csstep \<mu> R) {\<sigma> x |_ q}"
proof -
  from x obtain p where p: "p \<in> mu_poss \<mu> l" and lp: "l |_ p = Var x"
    unfolding mu_vars_term_def by auto
  have pq: "p @ q \<in> mu_fun_poss \<mu> (l \<cdot> \<sigma>)"
    by (rule mu_fun_poss_subst_var_lift[where t = l and x = x and \<sigma> = \<sigma>, OF p lp q])
  have pq_pos: "p @ q \<in> mu_poss \<mu> (l \<cdot> \<sigma>)"
    by (rule mu_fun_poss_imp_mu_poss[OF pq])
  have pq_ne: "p @ q \<noteq> []"
  proof
    assume "p @ q = []"
    then have "p = []" by simp
    with lp have "l = Var x" by simp
    with lhs show False by (cases l, auto)
  qed
  then obtain i p' where pq_cons: "p @ q = i # p'"
    by (cases "p @ q", auto)
  have sub: "(l \<cdot> \<sigma>) |_ (p @ q) = \<sigma> x |_ q"
    using mu_poss_imp_poss[OF p] lp
    by (simp add: subt_at_append)
  have "mu_supt \<mu> (l \<cdot> \<sigma>) (\<sigma> x |_ q)"
    unfolding mu_supt_def
    by (intro exI[of _ i] exI[of _ p'], insert pq_pos pq_cons sub, auto)
  with T show ?thesis
    unfolding mu_Tinf_def by blast
qed

lemma Tinf_imp_SN_csnr_first_csrstep:
  assumes Tinf: "t \<in> Tinf (csstep \<mu> R)"
  shows "SN_on (csnrstep \<mu> R) {t} \<and>
    (\<exists>s u. (t, s) \<in> (csnrstep \<mu> R)\<^sup>* \<and> (s, u) \<in> csrstep \<mu> R \<and>
      \<not> SN_on (csstep \<mu> R) {u})"
proof -
  let ?R = "csstep \<mu> R"
  let ?nR = "csnrstep \<mu> R"
  let ?rR = "csrstep \<mu> R"
  from Tinf[unfolded Tinf_def] have notSN: "\<not> SN_on ?R {t}"
    and min: "\<And>s. s \<lhd> t \<Longrightarrow> SN_on ?R {s}" by auto
  from notSN obtain ts where start: "ts 0 = t" and steps: "\<And>i. (ts i, ts (Suc i)) \<in> ?R"
    by auto
  show ?thesis
  proof (cases "SN_on ?nR {t}")
    case True
    let ?P = "\<lambda>i. (ts i, ts (Suc i)) \<in> ?rR"
    have root_step: "\<exists>i. ?P i"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have nsteps: "\<And>i. (ts i, ts (Suc i)) \<in> ?nR"
        using steps unfolding csstep_root_nonroot by auto
      with True start show False
        unfolding SN_on_def by blast
    qed
    then obtain k where step_k: "?P k" by auto
    define i where "i = (LEAST i. ?P i)"
    from LeastI[of ?P, OF step_k] have step: "?P i"
      unfolding i_def .
    have nsteps: "\<And>j. j < i \<Longrightarrow> (ts j, ts (Suc j)) \<in> ?nR"
    proof -
      fix j
      assume "j < i"
      from not_less_Least[OF this[unfolded i_def]] have "\<not> ?P j" .
      with steps[of j] show "(ts j, ts (Suc j)) \<in> ?nR"
        unfolding csstep_root_nonroot by auto
    qed
    have pref: "(ts 0, ts i) \<in> ?nR\<^sup>*"
      unfolding rtrancl_fun_conv
      by (intro exI[of _ ts] exI[of _ i], insert nsteps, auto)
    let ?ss = "shift ts (Suc i)"
    have tail_notSN: "\<not> SN_on ?R {ts (Suc i)}"
    proof -
      have "?ss 0 \<in> {ts (Suc i)}"
        by simp
      moreover have "\<And>j. (?ss j, ?ss (Suc j)) \<in> ?R"
        using steps[of "j + Suc i" for j] by auto
      ultimately show ?thesis
        unfolding SN_on_def by blast
    qed
    show ?thesis
      using True pref step tail_notSN start by blast
  next
    case False
    from False obtain ts where start: "ts 0 = t" and nsteps: "\<And>i. (ts i, ts (Suc i)) \<in> ?nR"
      by auto
    obtain f ss where init: "ts 0 = Fun f ss"
      using nsteps[of 0] csnrstep_Var_empty[of _ "ts (Suc 0)" \<mu> R]
      by (cases "ts 0", auto)
    let ?n = "length ss"
    obtain n where n: "n = ?n" by auto
    have roots: "\<exists>ssi. ts i = Fun f ssi \<and> length ssi = n" for i
    proof (induct i)
      case 0
      then show ?case unfolding init n by auto
    next
      case (Suc i)
      from Suc obtain ssi where tsi: "ts i = Fun f ssi" and len: "length ssi = n" by auto
      from csnrstep_preserves_root[OF nsteps[of i]]
      show ?case unfolding tsi root.simps len by (cases "ts (Suc i)", auto)
    qed
    from choice[OF allI[OF roots]] obtain sss where ts: "\<And>i. ts i = Fun f (sss i)"
      and len: "\<And>i. length (sss i) = n" by force
    let ?strict = "\<lambda>i. \<exists>j<n. (sss i ! j, sss (Suc i) ! j) \<in> ?R"
    have strict_all: "\<And>i. ?strict i"
    proof -
      fix i
      have step_i: "(Fun f (sss i), Fun f (sss (Suc i))) \<in> ?nR"
        using nsteps[of i] by (simp add: ts)
      from step_i show "?strict i"
      proof (elim csnrstep_FunE)
        fix j us
        assume j: "j < length (sss i)"
          and sub: "(sss i ! j, us ! j) \<in> ?R"
          and tgt: "Fun f (sss (Suc i)) = Fun f us"
        from tgt have us: "sss (Suc i) = us" by simp
        from j sub us len[of i] show ?thesis by auto
      qed
    qed
    let ?idx = "\<lambda>i. SOME j. j < n \<and> (sss i ! j, sss (Suc i) ! j) \<in> ?R"
    define idx where "idx = ?idx"
    have idx_strict: "idx i < n \<and> (sss i ! idx i, sss (Suc i) ! idx i) \<in> ?R" for i
    proof -
      from strict_all[of i] have ex: "\<exists>j. j < n \<and> (sss i ! j, sss (Suc i) ! j) \<in> ?R" .
      show ?thesis
        unfolding idx_def by (rule someI_ex[OF ex])
    qed
    have idx_n: "idx i \<le> n" for i
      using idx_strict[of i] by auto
    have fin: "finite (idx ` X)" for X
    proof (rule finite_subset)
      show "idx ` X \<subseteq> {i. i \<le> n}" using idx_n by auto
      have id: "{i. i \<le> n} = set [0 ..< Suc n]" by auto
      show "finite {i. i \<le> n}" unfolding id by (rule finite_set)
    qed
    have inf_strict: "infinite {i. ?strict i}"
      using strict_all by simp
    from pigeonhole_infinite[OF inf_strict fin]
    obtain j where infj_set: "infinite {i \<in> {i. ?strict i}. idx i = j}" by auto
    then have infj: "INFM i. idx i = j"
      unfolding INFM_iff_infinite
      using infinite_super[of "{i \<in> {i. ?strict i}. idx i = j}" "{i. idx i = j}"]
      by auto
    from infj[unfolded INFM_nat_le, rule_format, of 0]
    obtain k where kj: "idx k = j" by auto
    from idx_strict[of k] kj have jn: "j < n" by auto
    with n have "ss ! j \<in> set ss" by auto
    with init have "ss ! j \<lhd> ts 0" by auto
    from min[unfolded start[symmetric], OF this] have SN: "SN_on ?R {ss ! j}" by auto
    let ?ss = "\<lambda>i. sss i ! j"
    from SN have SN: "SN_on ?R {?ss 0}" using ts[of 0] init by simp
    have j_steps: "(?ss i, ?ss (Suc i)) \<in> ?R\<^sup>=" for i
    proof -
      have step_i: "(Fun f (sss i), Fun f (sss (Suc i))) \<in> ?nR"
        using nsteps[of i] by (simp add: ts)
      from step_i show ?thesis
      proof (elim csnrstep_FunE)
        fix k us
        assume k: "k < length (sss i)"
          and step: "(sss i ! k, us ! k) \<in> ?R"
          and tgt: "Fun f (sss (Suc i)) = Fun f us"
          and same: "\<And>l. l < length (sss i) \<Longrightarrow> l \<noteq> k \<Longrightarrow> us ! l = sss i ! l"
        from tgt have us_eq: "sss (Suc i) = us" by simp
        show ?thesis
        proof (cases "j = k")
          case True
          with step us_eq show ?thesis by auto
        next
          case False
          from jn len[of i] have "j < length (sss i)" by simp
          from same[OF this False] us_eq show ?thesis by simp
        qed
      qed
    qed
    have jsteps: "(?ss i, ?ss (Suc i)) \<in> Id \<union> ?R" for i
      using j_steps[of i] by auto
    have compat: "Id O ?R \<subseteq> ?R" by auto
    from non_strict_ending[of ?ss Id ?R, OF allI[OF jsteps] compat SN]
    obtain k where k: "\<And>l. l \<ge> k \<Longrightarrow> (?ss l, ?ss (Suc l)) \<notin> ?R" by auto
    from infj[unfolded INFM_nat_le, rule_format, of k]
    obtain l where lk: "l \<ge> k" and lj: "idx l = j" by auto
    from idx_strict[of l] lj have "(?ss l, ?ss (Suc l)) \<in> ?R" by auto
    with k[OF lk] show ?thesis by auto
  qed
qed

lemma mu_Tinf_imp_SN_csnr_first_csrstep:
  assumes wf: "wf_trs R"
    and Tinf: "t \<in> mu_Tinf \<mu> (csstep \<mu> R)"
  shows "SN_on (csnrstep \<mu> R) {t} \<and>
    (\<exists>s u. (t, s) \<in> (csnrstep \<mu> R)\<^sup>* \<and> (s, u) \<in> csrstep \<mu> R \<and>
      \<not> SN_on (csstep \<mu> R) {u})"
proof -
  let ?R = "csstep \<mu> R"
  let ?nR = "csnrstep \<mu> R"
  let ?rR = "csrstep \<mu> R"
  from Tinf[unfolded mu_Tinf_def] have notSN: "\<not> SN_on ?R {t}"
    and min: "\<And>s. mu_supt \<mu> t s \<Longrightarrow> SN_on ?R {s}" by auto
  from notSN obtain ts where start: "ts 0 = t" and steps: "\<And>i. (ts i, ts (Suc i)) \<in> ?R"
    unfolding SN_on_def by auto
  show ?thesis
  proof (cases "SN_on ?nR {t}")
    case True
    let ?P = "\<lambda>i. (ts i, ts (Suc i)) \<in> ?rR"
    have root_step: "\<exists>i. ?P i"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have nsteps: "\<And>i. (ts i, ts (Suc i)) \<in> ?nR"
        using steps unfolding csstep_root_nonroot by auto
      with True start show False
        unfolding SN_on_def by blast
    qed
    then obtain k where step_k: "?P k" by auto
    define i where "i = (LEAST i. ?P i)"
    from LeastI[of ?P, OF step_k] have step: "?P i"
      unfolding i_def .
    have nsteps: "\<And>j. j < i \<Longrightarrow> (ts j, ts (Suc j)) \<in> ?nR"
    proof -
      fix j
      assume "j < i"
      from not_less_Least[OF this[unfolded i_def]] have "\<not> ?P j" .
      with steps[of j] show "(ts j, ts (Suc j)) \<in> ?nR"
        unfolding csstep_root_nonroot by auto
    qed
    have pref: "(ts 0, ts i) \<in> ?nR\<^sup>*"
      unfolding rtrancl_fun_conv
      by (intro exI[of _ ts] exI[of _ i], insert nsteps, auto)
    let ?ss = "shift ts (Suc i)"
    have tail_notSN: "\<not> SN_on ?R {ts (Suc i)}"
    proof -
      have "?ss 0 \<in> {ts (Suc i)}"
        by simp
      moreover have "\<And>j. (?ss j, ?ss (Suc j)) \<in> ?R"
        using steps[of "j + Suc i" for j] by auto
      ultimately show ?thesis
        unfolding SN_on_def by blast
    qed
    show ?thesis
      using True pref step tail_notSN start by blast
  next
    case False
    from False obtain ts where start: "ts 0 = t" and nsteps: "\<And>i. (ts i, ts (Suc i)) \<in> ?nR"
      unfolding SN_on_def by auto
    obtain f ss where init: "ts 0 = Fun f ss"
      using nsteps[of 0] csnrstep_Var_empty[of _ "ts (Suc 0)" \<mu> R]
      by (cases "ts 0", auto)
    let ?n = "length ss"
    obtain n where n: "n = ?n" by auto
    have roots: "\<exists>ssi. ts i = Fun f ssi \<and> length ssi = n" for i
    proof (induct i)
      case 0
      then show ?case unfolding init n by auto
    next
      case (Suc i)
      from Suc obtain ssi where tsi: "ts i = Fun f ssi" and len: "length ssi = n" by auto
      from csnrstep_preserves_root[OF nsteps[of i]]
      show ?case unfolding tsi root.simps len by (cases "ts (Suc i)", auto)
    qed
    from choice[OF allI[OF roots]] obtain sss where ts: "\<And>i. ts i = Fun f (sss i)"
      and len: "\<And>i. length (sss i) = n" by force
    let ?strict = "\<lambda>i. \<exists>j<n. j \<in> \<mu> (f, n) \<and> (sss i ! j, sss (Suc i) ! j) \<in> ?R"
    have strict_all: "\<And>i. ?strict i"
    proof -
      fix i
      have step_i: "(Fun f (sss i), Fun f (sss (Suc i))) \<in> ?nR"
        using nsteps[of i] by (simp add: ts)
      from step_i show "?strict i"
      proof (elim csnrstep_FunE)
        fix j us
        assume j: "j < length (sss i)" and jmu: "j \<in> \<mu> (f, length (sss i))"
          and sub: "(sss i ! j, us ! j) \<in> ?R"
          and tgt: "Fun f (sss (Suc i)) = Fun f us"
        from tgt have us: "sss (Suc i) = us" by simp
        from j jmu sub us len[of i] show ?thesis by auto
      qed
    qed
    let ?idx = "\<lambda>i. SOME j. j < n \<and> j \<in> \<mu> (f, n) \<and> (sss i ! j, sss (Suc i) ! j) \<in> ?R"
    define idx where "idx = ?idx"
    have idx_strict: "idx i < n \<and> idx i \<in> \<mu> (f, n) \<and> (sss i ! idx i, sss (Suc i) ! idx i) \<in> ?R" for i
    proof -
      from strict_all[of i] have ex: "\<exists>j. j < n \<and> j \<in> \<mu> (f, n) \<and> (sss i ! j, sss (Suc i) ! j) \<in> ?R" .
      show ?thesis
        unfolding idx_def by (rule someI_ex[OF ex])
    qed
    have idx_n: "idx i \<le> n" for i
      using idx_strict[of i] by auto
    have fin: "finite (idx ` X)" for X
    proof (rule finite_subset)
      show "idx ` X \<subseteq> {i. i \<le> n}" using idx_n by auto
      have id: "{i. i \<le> n} = set [0 ..< Suc n]" by auto
      show "finite {i. i \<le> n}" unfolding id by (rule finite_set)
    qed
    have inf_strict: "infinite {i. ?strict i}"
      using strict_all by simp
    from pigeonhole_infinite[OF inf_strict fin]
    obtain j where infj_set: "infinite {i \<in> {i. ?strict i}. idx i = j}" by auto
    then have infj: "INFM i. idx i = j"
      unfolding INFM_iff_infinite
      using infinite_super[of "{i \<in> {i. ?strict i}. idx i = j}" "{i. idx i = j}"]
      by auto
    from infj[unfolded INFM_nat_le, rule_format, of 0]
    obtain k where kj: "idx k = j" by auto
    from idx_strict[of k] kj have jn: "j < n" and jmu: "j \<in> \<mu> (f, n)" by auto
    with n have "j # [] \<in> mu_poss \<mu> (Fun f ss)"
      by (cases "ss ! j", auto)
    moreover have "Fun f ss |_ (j # []) = ss ! j"
      using jn n by simp
    ultimately have "mu_supt \<mu> (Fun f ss) (ss ! j)"
      unfolding mu_supt_def by blast
    with min[unfolded start[symmetric] init] have SN: "SN_on ?R {ss ! j}" by auto
    let ?ss = "\<lambda>i. sss i ! j"
    from SN have SN: "SN_on ?R {?ss 0}" using ts[of 0] init by simp
    have j_steps: "(?ss i, ?ss (Suc i)) \<in> ?R\<^sup>=" for i
    proof -
      have step_i: "(Fun f (sss i), Fun f (sss (Suc i))) \<in> ?nR"
        using nsteps[of i] by (simp add: ts)
      from step_i show ?thesis
      proof (elim csnrstep_FunE)
        fix k us
        assume k: "k < length (sss i)"
          and step: "(sss i ! k, us ! k) \<in> ?R"
          and tgt: "Fun f (sss (Suc i)) = Fun f us"
          and same: "\<And>l. l < length (sss i) \<Longrightarrow> l \<noteq> k \<Longrightarrow> us ! l = sss i ! l"
        from tgt have us_eq: "sss (Suc i) = us" by simp
        show ?thesis
        proof (cases "j = k")
          case True
          with step us_eq show ?thesis by auto
        next
          case False
          from jn len[of i] have "j < length (sss i)" by simp
          from same[OF this False] us_eq show ?thesis by simp
        qed
      qed
    qed
    have jsteps: "(?ss i, ?ss (Suc i)) \<in> Id \<union> ?R" for i
      using j_steps[of i] by auto
    have compat: "Id O ?R \<subseteq> ?R" by auto
    from non_strict_ending[of ?ss Id ?R, OF allI[OF jsteps] compat SN]
    obtain k where k: "\<And>l. l \<ge> k \<Longrightarrow> (?ss l, ?ss (Suc l)) \<notin> ?R" by auto
    from infj[unfolded INFM_nat_le, rule_format, of k]
    obtain l where lk: "l \<ge> k" and lj: "idx l = j" by auto
    from idx_strict[of l] lj have "(?ss l, ?ss (Suc l)) \<in> ?R" by auto
    with k[OF lk] show ?thesis by auto
  qed
qed

lemma Tinf_csstep_defined_root:
  assumes wf: "wf_trs R"
    and Tinf: "Fun f ts \<in> Tinf (csstep \<mu> R)"
  shows "defined R (f, length ts)"
proof -
  from Tinf_imp_SN_csnr_first_csrstep[OF Tinf]
  obtain s u where pref: "(Fun f ts, s) \<in> (csnrstep \<mu> R)\<^sup>*"
    and root: "(s, u) \<in> csrstep \<mu> R"
    by auto
  from root obtain l r \<sigma> where lr: "(l, r) \<in> R" and s: "s = l \<cdot> \<sigma>"
    by (elim csrstepE)
  from wf lr obtain g ls where l: "l = Fun g ls"
    unfolding wf_trs_def by (cases l, auto)
  from csnrsteps_preserve_root[OF pref] have "root s = Some (f, length ts)"
    by simp
  with s l have "g = f" "length ls = length ts"
    by auto
  with lr l show ?thesis
    unfolding defined_def by auto
qed

fun mu_poss_list :: "'f muL \<Rightarrow> ('f, 'v) term \<Rightarrow> pos list"
where
  "mu_poss_list \<mu> (Var x) = [[]]"
| "mu_poss_list \<mu> (Fun f ts) =
    [] # concat (map (\<lambda>i. map ((#) i) (mu_poss_list \<mu> (ts ! i)))
      [i <- [0..<length ts]. i \<in> mu_of \<mu> (f, length ts)])"

lemma set_mu_poss_list [simp]:
  "set (mu_poss_list \<mu> t) = mu_poss (mu_of \<mu>) t"
proof (induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  have "set (concat (map (\<lambda>i. map ((#) i) (mu_poss_list \<mu> (ts ! i)))
      [i <- [0..<length ts]. i \<in> mu_of \<mu> (f, length ts)])) =
    (\<Union>i\<in>mu_of \<mu> (f, length ts) \<inter> {0..<length ts}. {i # p |p. p \<in> mu_poss (mu_of \<mu>) (ts ! i)})"
    using Fun by auto
  then show ?case by auto
qed

definition mu_supt_list :: "'f muL \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term list"
where
  "mu_supt_list \<mu> s = map (\<lambda>p. s |_ p) (filter (\<lambda>p. p \<noteq> []) (mu_poss_list \<mu> s))"

lemma set_mu_supt_list [simp]:
  "set (mu_supt_list \<mu> s) = {t. mu_supt (mu_of \<mu>) s t}"
proof
  show "set (mu_supt_list \<mu> s) \<subseteq> {t. mu_supt (mu_of \<mu>) s t}"
    unfolding mu_supt_list_def mu_supt_def
    by (auto, metis list.exhaust)
next
  show "{t. mu_supt (mu_of \<mu>) s t} \<subseteq> set (mu_supt_list \<mu> s)"
    unfolding mu_supt_list_def mu_supt_def
    by auto
qed

fun mu_vars_term_list :: "'f muL \<Rightarrow> ('f, 'v) term \<Rightarrow> 'v list"
where
  "mu_vars_term_list \<mu> (Var x) = [x]"
| "mu_vars_term_list \<mu> (Fun f ts) =
    concat (map (\<lambda>i. mu_vars_term_list \<mu> (ts ! i))
      [i <- [0..<length ts]. i \<in> mu_of \<mu> (f, length ts)])"

lemma set_mu_vars_term_list [simp]:
  "set (mu_vars_term_list \<mu> t) = mu_vars_term (mu_of \<mu>) t"
proof (induct t)
  case (Var x)
  then show ?case
    unfolding mu_vars_term_def by auto
next
  case (Fun f ts)
  show ?case
  proof
    show "set (mu_vars_term_list \<mu> (Fun f ts)) \<subseteq> mu_vars_term (mu_of \<mu>) (Fun f ts)"
    proof
      fix x
      assume x: "x \<in> set (mu_vars_term_list \<mu> (Fun f ts))"
      then obtain i where i: "i < length ts" "i \<in> mu_of \<mu> (f, length ts)"
        and xi: "x \<in> set (mu_vars_term_list \<mu> (ts ! i))"
        by auto
      from Fun.hyps[OF nth_mem[OF i(1)], unfolded mu_vars_term_def] xi
      obtain p where p: "p \<in> mu_poss (mu_of \<mu>) (ts ! i)"
        and sub: "ts ! i |_ p = Var x"
        by auto
      have "i # p \<in> mu_poss (mu_of \<mu>) (Fun f ts)"
        using i p by auto
      moreover have "Fun f ts |_ (i # p) = Var x"
        using i sub by simp
      ultimately show "x \<in> mu_vars_term (mu_of \<mu>) (Fun f ts)"
        unfolding mu_vars_term_def by blast
    qed
  next
    show "mu_vars_term (mu_of \<mu>) (Fun f ts) \<subseteq> set (mu_vars_term_list \<mu> (Fun f ts))"
    proof
      fix x
      assume "x \<in> mu_vars_term (mu_of \<mu>) (Fun f ts)"
      then obtain p where p: "p \<in> mu_poss (mu_of \<mu>) (Fun f ts)"
        and sub: "Fun f ts |_ p = Var x"
        unfolding mu_vars_term_def by auto
      show "x \<in> set (mu_vars_term_list \<mu> (Fun f ts))"
      proof (cases p)
        case Nil
        with sub show ?thesis by simp
      next
        case (Cons i q)
        from p Cons have i: "i < length ts" "i \<in> mu_of \<mu> (f, length ts)"
          and q: "q \<in> mu_poss (mu_of \<mu>) (ts ! i)"
          by auto
        from sub Cons i have sub_i: "ts ! i |_ q = Var x"
          by simp
        have "x \<in> set (mu_vars_term_list \<mu> (ts ! i))"
          using Fun.hyps[OF nth_mem[OF i(1)]] q sub_i
          unfolding mu_vars_term_def by auto
        with i show ?thesis by auto
      qed
    qed
  qed
qed

definition rhs_mu_vars_condition_list :: "'f muL \<Rightarrow> ('f, 'v) rules \<Rightarrow> bool"
where
  "rhs_mu_vars_condition_list \<mu> R \<longleftrightarrow>
     list_all (\<lambda>(l,r). list_all (\<lambda>x. x \<in> set (mu_vars_term_list \<mu> l)) (mu_vars_term_list \<mu> r)) R"

lemma rhs_mu_vars_condition_list_sound:
  assumes "rhs_mu_vars_condition_list \<mu> R"
  shows "rhs_mu_vars_condition (mu_of \<mu>) (set R)"
  using assms
  unfolding rhs_mu_vars_condition_list_def rhs_mu_vars_condition_def list_all_iff
  by auto

definition CSDP_on :: "('f \<Rightarrow> 'f) \<Rightarrow> 'f mu \<Rightarrow> 'f sig \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) trs"
where
  "CSDP_on shp \<mu> D R =
    { (sharp_term shp l, sharp_term shp (r |_ p)) | l r p f ts.
      (l, r) \<in> R \<and> p \<in> mu_fun_poss \<mu> r \<and> r |_ p = Fun f ts \<and>
      (f, length ts) \<in> D \<and> \<not> l \<rhd> r |_ p }"

definition exposed_fun_poss :: "'f mu \<Rightarrow> 'f sig \<Rightarrow> ('f, 'v) term \<Rightarrow> pos set"
where
  "exposed_fun_poss \<mu> D t =
    {p @ q | p q f ts. p \<in> mu_fun_poss \<mu> t \<and> t |_ p = Fun f ts \<and>
      (f, length ts) \<in> D \<and> q \<in> fun_poss (t |_ p)}"

definition exposed_CSDP_on :: "('f \<Rightarrow> 'f) \<Rightarrow> 'f mu \<Rightarrow> 'f sig \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) trs"
where
  "exposed_CSDP_on shp \<mu> D R =
    { (sharp_term shp l, sharp_term shp (r |_ p)) | l r p f ts.
      (l, r) \<in> R \<and> p \<in> exposed_fun_poss \<mu> D r \<and> r |_ p = Fun f ts \<and>
      (f, length ts) \<in> D \<and> \<not> l \<rhd> r |_ p }"

definition safe_CSDP_on :: "('f \<Rightarrow> 'f) \<Rightarrow> 'f sig \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) trs"
where
  "safe_CSDP_on shp D R = DP_on shp D R"

context
  fixes shp :: "'f::{showl, compare_order} \<Rightarrow> 'f"
begin

interpretation sharp_syntax .

definition mu_CSDP_on :: "'f mu \<Rightarrow> 'f sig \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) trs"
where
  "mu_CSDP_on \<mu> D R =
    { (\<sharp> l, \<sharp> (r |_ p)) | l r p f ts.
      (l, r) \<in> R \<and> p \<in> mu_fun_poss \<mu> r \<and> r |_ p = Fun f ts \<and>
      (f, length ts) \<in> D \<and> \<not> mu_supt \<mu> l (r |_ p) }"

lemma rrstep_mu_CSDP_onI:
  assumes lr: "(l, r) \<in> R"
    and lhs: "is_Fun l"
    and p: "p \<in> mu_fun_poss \<mu> r"
    and sub: "r |_ p = Fun f ts"
    and D: "(f, length ts) \<in> D"
    and ns: "\<not> mu_supt \<mu> l (r |_ p)"
  shows "(\<sharp> (l \<cdot> \<sigma>), \<sharp> ((r |_ p) \<cdot> \<sigma>)) \<in> rrstep (mu_CSDP_on \<mu> D R)"
proof -
  have dp: "(\<sharp> l, \<sharp> (r |_ p)) \<in> mu_CSDP_on \<mu> D R"
    unfolding mu_CSDP_on_def
    apply (rule CollectI)
    apply (rule exI[of _ l])
    apply (rule exI[of _ r])
    apply (rule exI[of _ p])
    apply (rule exI[of _ f])
    apply (rule exI[of _ ts])
    using lr p sub D ns by auto
  have l: "\<sharp> (l \<cdot> \<sigma>) = \<sharp> l \<cdot> \<sigma>"
    using lhs by (cases l, auto)
  have r: "\<sharp> ((r |_ p) \<cdot> \<sigma>) = \<sharp> (r |_ p) \<cdot> \<sigma>"
    using sub by simp
  then show ?thesis
    using dp l by auto
qed

lemma csrstep_mu_Tinf_rhs_imp_rrstep_mu_CSDP_on:
  assumes wf: "wf_trs R"
    and step: "(s, t) \<in> csrstep \<mu> R"
    and sT: "s \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and notSN: "\<not> SN_on (csstep \<mu> R) {t}"
    and vc: "rhs_mu_vars_condition \<mu> R"
    and D: "{f. defined R f} \<subseteq> D"
  shows "\<exists>u. u \<in> mu_Tinf \<mu> (csstep \<mu> R) \<and>
    (\<sharp> s, \<sharp> u) \<in> rrstep (mu_CSDP_on \<mu> D R)"
proof -
  from step obtain l r \<sigma> where lr: "(l, r) \<in> R" and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
    by (elim csrstepE)
  from wf lr have lhs: "is_Fun l"
    unfolding wf_trs_def by (cases l, auto)
  from csstep_notSN_imp_mu_Tinf_defined_subterm[OF wf notSN[unfolded t]]
  obtain p f us where p_mu: "p \<in> mu_fun_poss \<mu> (r \<cdot> \<sigma>)"
    and sub_inst: "(r \<cdot> \<sigma>) |_ p = Fun f us"
    and def: "defined R (f, length us)"
    and T_p: "(r \<cdot> \<sigma>) |_ p \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    by blast
  from T_p have notSN_p: "\<not> SN_on (csstep \<mu> R) {(r \<cdot> \<sigma>) |_ p}"
    unfolding mu_Tinf_def by auto
  from mu_fun_poss_subst_cases_aux_mu[OF p_mu]
  show ?thesis
  proof
    assume orig: "p \<in> mu_fun_poss \<mu> r \<and> (r \<cdot> \<sigma>) |_ p = (r |_ p) \<cdot> \<sigma>"
    then have p_r: "p \<in> mu_fun_poss \<mu> r"
      and sub_subst: "(r \<cdot> \<sigma>) |_ p = (r |_ p) \<cdot> \<sigma>"
      by auto
    from mu_fun_poss_imp_fun_poss[OF p_r] obtain g ts where rp0: "r |_ p = Fun g ts"
      using fun_poss_fun_conv by blast
    with sub_subst sub_inst have rp: "r |_ p = Fun f ts" and len: "length us = length ts"
      by auto
    from D def len have fD: "(f, length ts) \<in> D"
      by auto
    have ns: "\<not> mu_supt \<mu> l (r |_ p)"
    proof
      assume supt: "mu_supt \<mu> l (r |_ p)"
      then obtain i q where iq: "i # q \<in> mu_poss \<mu> l"
        and sub_l: "l |_ (i # q) = r |_ p"
        unfolding mu_supt_def by auto
      have iq_poss: "i # q \<in> poss l"
        using iq mu_poss_imp_poss by blast
      have "(l \<cdot> \<sigma>) |_ (i # q) = (r |_ p) \<cdot> \<sigma>"
        using subt_at_subst[OF iq_poss] sub_l by simp
      moreover have "mu_supt \<mu> (l \<cdot> \<sigma>) ((r |_ p) \<cdot> \<sigma>)"
        unfolding mu_supt_def
        by (intro exI[of _ i] exI[of _ q],
            insert mu_poss_subst_lift[OF iq, of \<sigma>]
              \<open>(l \<cdot> \<sigma>) |_ (i # q) = (r |_ p) \<cdot> \<sigma>\<close>, auto)
      ultimately have "SN_on (csstep \<mu> R) {(r |_ p) \<cdot> \<sigma>}"
        using sT unfolding s mu_Tinf_def by blast
      with notSN_p sub_subst show False
        by simp
    qed
    have rr: "(\<sharp> (l \<cdot> \<sigma>), \<sharp> ((r |_ p) \<cdot> \<sigma>)) \<in> rrstep (mu_CSDP_on \<mu> D R)"
      by (rule rrstep_mu_CSDP_onI[OF lr lhs p_r rp fD ns])
    show ?thesis
      using rr T_p sub_subst unfolding s by auto
  next
    assume "\<exists>x q1 q2. q1 \<in> mu_poss \<mu> r \<and> r |_ q1 = Var x \<and> x \<in> vars_term r \<and>
      p = q1 @ q2 \<and> q2 \<in> mu_fun_poss \<mu> (\<sigma> x) \<and> (r \<cdot> \<sigma>) |_ p = \<sigma> x |_ q2"
    then obtain x q1 q2 where q1: "q1 \<in> mu_poss \<mu> r"
      and r_q1: "r |_ q1 = Var x"
      and q2: "q2 \<in> mu_fun_poss \<mu> (\<sigma> x)"
      and sub_q2: "(r \<cdot> \<sigma>) |_ p = \<sigma> x |_ q2"
      by blast
    have "x \<in> mu_vars_term \<mu> r"
      unfolding mu_vars_term_def using q1 r_q1 by blast
    with vc lr have x_l: "x \<in> mu_vars_term \<mu> l"
      unfolding rhs_mu_vars_condition_def by blast
    have lT: "l \<cdot> \<sigma> \<in> mu_Tinf \<mu> (csstep \<mu> R)"
      using sT unfolding s .
    have "SN_on (csstep \<mu> R) {\<sigma> x |_ q2}"
      by (rule mu_Tinf_SN_on_active_subst_mu_subterm[OF lhs lT x_l q2])
    with notSN_p sub_q2 show ?thesis
      by simp
  qed
qed

lemma csnrsteps_imp_sharp_rsteps:
  assumes "(s, t) \<in> (csnrstep \<mu> R)\<^sup>*"
  shows "(\<sharp> s, \<sharp> t) \<in> (rstep R)\<^sup>*"
proof -
  have "(s, t) \<in> (nrrstep R)\<^sup>*"
    using assms
  proof (induct rule: rtrancl_induct)
    case base
    show ?case by simp
  next
    case (step y z)
    from csnrstep_imp_nrrstep[OF step.hyps(2)]
    have "(y, z) \<in> nrrstep R" .
    with step.hyps(3) show ?case by auto
  qed
  then show ?thesis
    by (rule nrrsteps_imp_sharp_rsteps)
qed

lemma csnrstep_imp_csstep:
  assumes "(s, t) \<in> csnrstep \<mu> R"
  shows "(s, t) \<in> csstep \<mu> R"
  using assms unfolding csnrstep_def csstep_def by auto

lemma sharp_csnrstep_imp_csstep:
  assumes sharp_mu: "\<And>f n. \<mu> (f, n) \<subseteq> \<mu> (\<sharp> f, n)"
    and "(s, t) \<in> csnrstep \<mu> R"
  shows "(\<sharp> s, \<sharp> t) \<in> csstep \<mu> R"
proof -
  from assms(2)
  obtain p lr \<sigma> where p_ne: "p \<noteq> []"
    and step: "(s, t) \<in> rstep_r_p_s R lr p \<sigma>"
    and cond: "csstep_cond \<mu> p s"
    unfolding csnrstep_def csstep_p_def by auto
  have "(\<sharp> s, \<sharp> t) \<in> rstep_r_p_s R lr p \<sigma>"
  proof (cases s)
    case (Var x)
    with step p_ne have False
      unfolding rstep_r_p_s_def' by auto
    then show ?thesis ..
  next
    case (Fun f ts)
    from p_ne obtain i q where p: "p = i # q"
      by (cases p, auto)
    from step Fun show ?thesis
      unfolding rstep_r_p_s_def' p by auto
  qed
  moreover have "csstep_cond \<mu> p (\<sharp> s)"
  proof (cases s)
    case (Var x)
    with step p_ne have False
      unfolding rstep_r_p_s_def' by auto
    then show ?thesis ..
  next
    case (Fun f ts)
    from p_ne obtain i q where p: "p = i # q"
      by (cases p, auto)
    show ?thesis
      unfolding csstep_cond_def
    proof (intro allI impI)
      fix p1 j p2
      assume A: "p = p1 @ j # p2 \<and> p \<in> poss (\<sharp> s)"
      show "\<exists>g us. \<sharp> s |_ p1 = Fun g us \<and> j \<in> \<mu> (g, length us)"
      proof (cases p1)
        case Nil
        with A Fun p cond[unfolded csstep_cond_def, rule_format, of "[]" j p2]
        show ?thesis
          using sharp_mu[of f "length ts"] by auto
      next
        case (Cons k qs)
        with A Fun have A': "p = p1 @ j # p2 \<and> p \<in> poss s"
          by auto
        from cond[unfolded csstep_cond_def, rule_format, OF A']
        obtain g us where s_sub: "s |_ p1 = Fun g us" and j: "j \<in> \<mu> (g, length us)"
          by blast
        with Cons Fun show ?thesis
          by auto
      qed
    qed
  qed
  ultimately show ?thesis
    unfolding csstep_def csstep_p_def by blast
qed

lemma csnrsteps_imp_sharp_cssteps:
  assumes sharp_mu: "\<And>f n. \<mu> (f, n) \<subseteq> \<mu> (\<sharp> f, n)"
    and "(s, t) \<in> (csnrstep \<mu> R)\<^sup>*"
  shows "(\<sharp> s, \<sharp> t) \<in> (csstep \<mu> R)\<^sup>*"
  using assms(2)
proof (induct rule: rtrancl_induct)
  case base
  show ?case by simp
next
  case (step y z)
  from sharp_csnrstep_imp_csstep[OF sharp_mu step.hyps(2)]
  have "(\<sharp> y, \<sharp> z) \<in> csstep \<mu> R" .
  with step.hyps(3) show ?case by auto
qed

lemma mu_Tinf_imp_mu_CSDP_relstep:
  assumes wf: "wf_trs R"
    and Tinf: "t \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and vc: "rhs_mu_vars_condition \<mu> R"
    and D: "{f. defined R f} \<subseteq> D"
  shows "\<exists>u. u \<in> mu_Tinf \<mu> (csstep \<mu> R) \<and>
    (\<sharp> t, \<sharp> u) \<in> (rstep R)\<^sup>* O rrstep (mu_CSDP_on \<mu> D R) O (rstep R)\<^sup>*"
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
  from csrstep_mu_Tinf_rhs_imp_rrstep_mu_CSDP_on[OF wf root sT notSN_v vc D]
  obtain u where uT: "u \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and dp: "(\<sharp> s, \<sharp> u) \<in> rrstep (mu_CSDP_on \<mu> D R)"
    by blast
  have left: "(\<sharp> t, \<sharp> s) \<in> (rstep R)\<^sup>*"
    by (rule csnrsteps_imp_sharp_rsteps[OF pref])
  have right: "(\<sharp> u, \<sharp> u) \<in> (rstep R)\<^sup>*"
    by simp
  have "(\<sharp> t, \<sharp> u) \<in> (rstep R)\<^sup>* O rrstep (mu_CSDP_on \<mu> D R) O (rstep R)\<^sup>*"
    using left dp right by auto
  with uT show ?thesis by blast
qed

lemma mu_Tinf_imp_mu_CSDP_csrelstep:
  assumes wf: "wf_trs R"
    and Tinf: "t \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and vc: "rhs_mu_vars_condition \<mu> R"
    and D: "{f. defined R f} \<subseteq> D"
    and sharp_mu: "\<And>f n. \<mu> (f, n) \<subseteq> \<mu> (\<sharp> f, n)"
  shows "\<exists>u. u \<in> mu_Tinf \<mu> (csstep \<mu> R) \<and>
    (\<sharp> t, \<sharp> u) \<in> (csstep \<mu> R)\<^sup>* O rrstep (mu_CSDP_on \<mu> D R) O (csstep \<mu> R)\<^sup>*"
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
  from csrstep_mu_Tinf_rhs_imp_rrstep_mu_CSDP_on[OF wf root sT notSN_v vc D]
  obtain u where uT: "u \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and dp: "(\<sharp> s, \<sharp> u) \<in> rrstep (mu_CSDP_on \<mu> D R)"
    by blast
  have left: "(\<sharp> t, \<sharp> s) \<in> (csstep \<mu> R)\<^sup>*"
    by (rule csnrsteps_imp_sharp_cssteps[OF sharp_mu pref])
  have right: "(\<sharp> u, \<sharp> u) \<in> (csstep \<mu> R)\<^sup>*"
    by simp
  have "(\<sharp> t, \<sharp> u) \<in> (csstep \<mu> R)\<^sup>* O rrstep (mu_CSDP_on \<mu> D R) O (csstep \<mu> R)\<^sup>*"
    using left dp right by auto
  with uT show ?thesis by blast
qed

definition CSDP_list :: "('f, 'v) rules \<Rightarrow> 'f muL \<Rightarrow> ('f \<times> nat) list \<Rightarrow> ('f, 'v) rules"
where
  "CSDP_list R \<mu> d_list =
    concat (map (\<lambda>lr.
      let l = fst lr; r = snd lr; s = \<sharp> l in
      map (\<lambda>p. (s, \<sharp> (r |_ p))) (filter
        (\<lambda>p. \<not> l \<rhd> r |_ p \<and> (case r |_ p of Var x \<Rightarrow> False
          | Fun f ts \<Rightarrow> (f, length ts) \<in> set d_list)) (mu_fun_poss_list \<mu> r))) R)"

definition mu_CSDP_list :: "('f, 'v) rules \<Rightarrow> 'f muL \<Rightarrow> ('f \<times> nat) list \<Rightarrow> ('f, 'v) rules"
where
  "mu_CSDP_list R \<mu> d_list =
    concat (map (\<lambda>lr.
      let l = fst lr; r = snd lr; s = \<sharp> l in
      map (\<lambda>p. (s, \<sharp> (r |_ p))) (filter
        (\<lambda>p. r |_ p \<notin> set (mu_supt_list \<mu> l) \<and> (case r |_ p of Var x \<Rightarrow> False
          | Fun f ts \<Rightarrow> (f, length ts) \<in> set d_list)) (mu_fun_poss_list \<mu> r))) R)"

definition safe_CSDP_list :: "('f, 'v) rules \<Rightarrow> ('f \<times> nat) list \<Rightarrow> ('f, 'v) rules"
where
  "safe_CSDP_list R d_list =
    concat (map (\<lambda>lr.
      let l = fst lr; s = \<sharp> l in
      map (\<lambda>u. (s, \<sharp> u)) (filter
        (\<lambda>u. \<not> l \<rhd> u \<and> is_Fun u \<and> (the (root u)) \<in> set d_list)
        (supteq_list (snd lr)))) R)"

definition exposed_CSDP_list :: "('f, 'v) rules \<Rightarrow> 'f muL \<Rightarrow> ('f \<times> nat) list \<Rightarrow> ('f, 'v) rules"
where
  "exposed_CSDP_list R \<mu> d_list =
    concat (map (\<lambda>lr.
      let l = fst lr; r = snd lr; s = \<sharp> l in
      concat (map (\<lambda>p.
        case r |_ p of Var x \<Rightarrow> []
        | Fun f ts \<Rightarrow>
          if (f, length ts) \<in> set d_list
          then map (\<lambda>u. (s, \<sharp> u)) (filter
            (\<lambda>u. \<not> l \<rhd> u \<and> is_Fun u \<and> the (root u) \<in> set d_list)
            (supteq_list (r |_ p)))
          else []) (mu_fun_poss_list \<mu> r))) R)"

definition
  reduced_csr_dependency_pairs_tt ::
    "('dpp, 'f::{showl, compare_order}, 'v::{showl,compare_order}) dpp_ops \<Rightarrow>
    'f muL \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> 'dpp result"
where
  "reduced_csr_dependency_pairs_tt J \<mu> R P \<equiv>
  let D = defined_list R in
  check_return (do {
     check_wf_trs R;
     check_allm (\<lambda> (f,n). check ((\<sharp> f,n) \<notin> set D)
       (showsl_lit (STR ''sharping '') \<circ> showsl f \<circ> showsl_lit (STR '' yields the defined symbol '') \<circ> showsl (\<sharp> f))) D;
     let P' = set P;
     check_all (\<lambda> dp. dp \<in> P' \<or> (\<exists> dp' \<in> set P. dp =\<^sub>v dp')) (CSDP_list R \<mu> D)
       <+? (\<lambda>dp. showsl_lit (STR ''the CS-DP '') \<circ> showsl_rule dp
         \<circ> showsl_lit (STR '' does not appear in the DP problem\<newline>''))
   } <+? (\<lambda>s. showsl_lit (STR ''the CS-DP transformation is not applied correctly.\<newline>'') \<circ> s))
   (dpp_ops.mk J False False P [] [] [] R)"

definition
  exposed_csr_dependency_pairs_tt ::
    "('dpp, 'f::{showl, compare_order}, 'v::{showl,compare_order}) dpp_ops \<Rightarrow>
    'f muL \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> 'dpp result"
where
  "exposed_csr_dependency_pairs_tt J \<mu> R P \<equiv>
  let D = defined_list R in
  check_return (do {
     check_wf_trs R;
     check_allm (\<lambda> (f,n). check ((\<sharp> f,n) \<notin> set D)
       (showsl_lit (STR ''sharping '') \<circ> showsl f \<circ> showsl_lit (STR '' yields the defined symbol '') \<circ> showsl (\<sharp> f))) D;
     let P' = set P;
     check_all (\<lambda> dp. dp \<in> P' \<or> (\<exists> dp' \<in> set P. dp =\<^sub>v dp')) (exposed_CSDP_list R \<mu> D)
       <+? (\<lambda>dp. showsl_lit (STR ''the exposed CS-DP '') \<circ> showsl_rule dp
         \<circ> showsl_lit (STR '' does not appear in the DP problem\<newline>''))
   } <+? (\<lambda>s. showsl_lit (STR ''the exposed CS-DP transformation is not applied correctly.\<newline>'') \<circ> s))
   (dpp_ops.mk J False False P [] [] [] R)"

definition
  mu_csr_dependency_pairs_tt ::
    "('dpp, 'f::{showl, compare_order}, 'v::{showl,compare_order}) dpp_ops \<Rightarrow>
    'f muL \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> 'dpp result"
where
  "mu_csr_dependency_pairs_tt J \<mu> R P \<equiv>
  let D = defined_list R in
  check_return (do {
     check_wf_trs R;
     check (rhs_mu_vars_condition_list \<mu> R)
       (showsl_lit (STR ''the RHS of a CSR rule contains a variable in an active position that is not active in the LHS\<newline>''));
     check_allm (\<lambda> (f,n). check ((\<sharp> f,n) \<notin> set D)
       (showsl_lit (STR ''sharping '') \<circ> showsl f \<circ> showsl_lit (STR '' yields the defined symbol '') \<circ> showsl (\<sharp> f))) D;
     let P' = set P;
     check_all (\<lambda> dp. dp \<in> P' \<or> (\<exists> dp' \<in> set P. dp =\<^sub>v dp')) (mu_CSDP_list R \<mu> D)
       <+? (\<lambda>dp. showsl_lit (STR ''the replacement-map-specific CS-DP '') \<circ> showsl_rule dp
         \<circ> showsl_lit (STR '' does not appear in the DP problem\<newline>''))
   } <+? (\<lambda>s. showsl_lit (STR ''the replacement-map-specific CS-DP transformation is not applied correctly.\<newline>'') \<circ> s))
   (dpp_ops.mk J False False P [] [] [] R)"

definition
  safe_csr_dependency_pairs_tt ::
    "('dpp, 'f::{showl, compare_order}, 'v::{showl,compare_order}) dpp_ops \<Rightarrow>
    'f muL \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> 'dpp result"
where
  "safe_csr_dependency_pairs_tt J \<mu> R P \<equiv>
  let D = defined_list R in
  check_return (do {
     check_wf_trs R;
     check_allm (\<lambda> (f,n). check ((\<sharp> f,n) \<notin> set D)
       (showsl_lit (STR ''sharping '') \<circ> showsl f \<circ> showsl_lit (STR '' yields the defined symbol '') \<circ> showsl (\<sharp> f))) D;
     let P' = set P;
     check_all (\<lambda> dp. dp \<in> P' \<or> (\<exists> dp' \<in> set P. dp =\<^sub>v dp')) (safe_CSDP_list R D)
       <+? (\<lambda>dp. showsl_lit (STR ''the safe CS-DP '') \<circ> showsl_rule dp
         \<circ> showsl_lit (STR '' does not appear in the DP problem\<newline>''))
   } <+? (\<lambda>s. showsl_lit (STR ''the safe CS-DP transformation is not applied correctly.\<newline>'') \<circ> s))
   (dpp_ops.mk J False True P [] [] [] R)"

definition
  csr_dependency_pairs_tt ::
    "('dpp, 'f::{showl, compare_order}, 'v::{showl,compare_order}) dpp_ops \<Rightarrow>
    'f muL \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> 'dpp result"
where
  "csr_dependency_pairs_tt J \<mu> R P \<equiv>
    (case mu_csr_dependency_pairs_tt J \<mu> R P of
      Inr d \<Rightarrow> Inr d
    | Inl e \<Rightarrow> safe_csr_dependency_pairs_tt J \<mu> R P)"

definition
  csr_mu_usable_rules_proc ::
    "('dpp, 'f::{showl, compare_order}, 'v::{showl, compare_order}) dpp_ops \<Rightarrow>
     'f muL \<Rightarrow> ('f, 'v) rules \<Rightarrow> 'dpp proc"
where
  "csr_mu_usable_rules_proc J \<mu> U dpp \<equiv>
    check_return (do {
      check_allm (\<lambda>(l, r). check (is_Fun l)
        (showsl_lit (STR ''variables as lhss not allowed''))) (dpp_ops.rules J dpp);
      check_ur_P_closed_rm_af (dpp_ops.rules_map J dpp) U (mu_of \<mu>) (dpp_ops.pairs J dpp)
        <+? (\<lambda>s. showsl_lit (STR ''error when checking CSR usable-rule closure\<newline>'') \<circ> s)
    }) (dpp_ops.intersect_rules J dpp U)"

lemma csr_mu_usable_rules_proc_closure:
  assumes J: "dpp_spec J"
    and ok: "csr_mu_usable_rules_proc J \<mu> U dpp = return dpp'"
  shows "ur_closed_af (set (dpp_ops.rules J dpp)) (set U) UNIV (mu_of \<mu>) \<and>
    ur_P_closed_af (set (dpp_ops.rules J dpp)) (set U) UNIV (mu_of \<mu>)
      (set (dpp_ops.pairs J dpp))"
proof -
  interpret dpp_spec J by fact
  from ok[unfolded csr_mu_usable_rules_proc_def, simplified]
  have lhs: "\<And>lr. lr \<in> set (rules dpp) \<Longrightarrow> is_Fun (fst lr)"
    and closed: "isOK (check_ur_P_closed_rm_af (rules_map dpp) U (mu_of \<mu>) (pairs dpp))"
    by (auto simp: isOK_check_allm isOK_check)
  have rm: "\<And>f n. set (rules_map dpp (f, n)) =
    {(l, r). (l, r) \<in> set (rules dpp) \<and> root l = Some (f, n)}"
    using rules_map_sound by auto
  show ?thesis
    by (rule check_ur_P_closed_rm_af_sound[OF lhs rm closed]) auto
qed

lemma mu_CSDP_list:
  "set (mu_CSDP_list R \<mu> D) = mu_CSDP_on (mu_of \<mu>) (set D) (set R)"
proof
  show "set (mu_CSDP_list R \<mu> D) \<subseteq> mu_CSDP_on (mu_of \<mu>) (set D) (set R)"
  proof
    fix dp
    assume "dp \<in> set (mu_CSDP_list R \<mu> D)"
    then obtain lr p where
      lr: "lr \<in> set R" and p: "p \<in> set (mu_fun_poss_list \<mu> (snd lr))"
      and ns: "snd lr |_ p \<notin> set (mu_supt_list \<mu> (fst lr))"
      and def: "(case snd lr |_ p of Var x \<Rightarrow> False
          | Fun f ts \<Rightarrow> (f, length ts) \<in> set D)"
      and dp: "dp = (\<sharp> (fst lr), \<sharp> (snd lr |_ p))"
      unfolding mu_CSDP_list_def Let_def by auto
    obtain l r where lr_pair: "lr = (l, r)"
      by force
    show "dp \<in> mu_CSDP_on (mu_of \<mu>) (set D) (set R)"
    proof (cases "r |_ p")
      case (Var x)
      with def lr_pair show ?thesis by simp
    next
      case (Fun f ts)
      show ?thesis
        unfolding mu_CSDP_on_def
        apply (rule CollectI)
        apply (rule exI[of _ l])
        apply (rule exI[of _ r])
        apply (rule exI[of _ p])
        apply (rule exI[of _ f])
        apply (rule exI[of _ ts])
        using lr p ns def dp lr_pair Fun by auto
    qed
  qed
next
  show "mu_CSDP_on (mu_of \<mu>) (set D) (set R) \<subseteq> set (mu_CSDP_list R \<mu> D)"
  proof
    fix dp
    assume "dp \<in> mu_CSDP_on (mu_of \<mu>) (set D) (set R)"
    then obtain l r p f ts where
      lr: "(l, r) \<in> set R" and p: "p \<in> mu_fun_poss (mu_of \<mu>) r"
      and sub: "r |_ p = Fun f ts" and dmem: "(f, length ts) \<in> set D"
      and ns: "\<not> mu_supt (mu_of \<mu>) l (r |_ p)"
      and dp: "dp = (\<sharp> l, \<sharp> (r |_ p))"
      unfolding mu_CSDP_on_def by auto
    from lr obtain bef aft where R: "R = bef @ (l, r) # aft"
      by (metis split_list)
    from p have p_list: "p \<in> set (mu_fun_poss_list \<mu> r)"
      by simp
    have filt: "p \<in> set (filter
        (\<lambda>p. r |_ p \<notin> set (mu_supt_list \<mu> l) \<and> (case r |_ p of Var x \<Rightarrow> False
          | Fun f ts \<Rightarrow> (f, length ts) \<in> set D)) (mu_fun_poss_list \<mu> r))"
      using p_list sub dmem ns by simp
    have mapped: "dp \<in> set (map (\<lambda>p. (\<sharp> l, \<sharp> (r |_ p))) (filter
        (\<lambda>p. r |_ p \<notin> set (mu_supt_list \<mu> l) \<and> (case r |_ p of Var x \<Rightarrow> False
          | Fun f ts \<Rightarrow> (f, length ts) \<in> set D)) (mu_fun_poss_list \<mu> r)))"
      unfolding set_map
    proof (rule image_eqI[of _ _ p])
      show "dp = (\<lambda>p. (\<sharp> l, \<sharp> (r |_ p))) p"
        using dp by simp
      show "p \<in> set (filter
        (\<lambda>p. r |_ p \<notin> set (mu_supt_list \<mu> l) \<and> (case r |_ p of Var x \<Rightarrow> False
          | Fun f ts \<Rightarrow> (f, length ts) \<in> set D)) (mu_fun_poss_list \<mu> r))"
        by (rule filt)
    qed
    then show "dp \<in> set (mu_CSDP_list R \<mu> D)"
      unfolding mu_CSDP_list_def R Let_def by auto
  qed
qed

lemma safe_CSDP_list:
  "set (safe_CSDP_list R D) = safe_CSDP_on shp (set D) (set R)"
proof
  show "set (safe_CSDP_list R D) \<subseteq> safe_CSDP_on shp (set D) (set R)"
  proof
    fix dp
    assume "dp \<in> set (safe_CSDP_list R D)"
    then obtain l r u where lr: "(l, r) \<in> set R"
      and sub: "r \<unrhd> u"
      and ns: "\<not> l \<rhd> u"
      and fun_u: "is_Fun u"
      and dmem: "the (root u) \<in> set D"
      and dp: "dp = (\<sharp> l, \<sharp> u)"
      unfolding safe_CSDP_list_def Let_def by auto
    from fun_u obtain f ts where u: "u = Fun f ts"
      by (cases u, auto)
    with dmem have "(f, length ts) \<in> set D"
      by simp
    with lr sub ns dp u show "dp \<in> safe_CSDP_on shp (set D) (set R)"
      unfolding safe_CSDP_on_def DP_on_def by auto
  qed
next
  show "safe_CSDP_on shp (set D) (set R) \<subseteq> set (safe_CSDP_list R D)"
  proof
    fix dp
    assume "dp \<in> safe_CSDP_on shp (set D) (set R)"
    then obtain l r f ts where lr: "(l, r) \<in> set R"
      and sub: "r \<unrhd> Fun f ts" and dmem: "(f, length ts) \<in> set D"
      and ns: "\<not> l \<rhd> Fun f ts" and dp: "dp = (\<sharp> l, \<sharp> (Fun f ts))"
      unfolding safe_CSDP_on_def DP_on_def by auto
    from lr obtain bef aft where R: "R = bef @ (l, r) # aft"
      by (metis split_list)
    have mem_filter: "Fun f ts \<in> set (filter
        (\<lambda>u. \<not> l \<rhd> u \<and> is_Fun u \<and> the (root u) \<in> set D) (supteq_list r))"
      using sub dmem ns by simp
    have "dp \<in> set (map (\<lambda>u. (\<sharp> l, \<sharp> u)) (filter
        (\<lambda>u. \<not> l \<rhd> u \<and> is_Fun u \<and> the (root u) \<in> set D) (supteq_list r)))"
    proof -
      have eq: "dp = (\<lambda>u. (\<sharp> l, \<sharp> u)) (Fun f ts)"
        using dp by simp
      show ?thesis
        unfolding set_map
      proof (rule image_eqI[of _ _ "Fun f ts"])
        show "dp = (\<lambda>u. (\<sharp> l, \<sharp> u)) (Fun f ts)"
          by (rule eq)
        show "Fun f ts \<in> set (filter
          (\<lambda>u. \<not> l \<rhd> u \<and> is_Fun u \<and> the (root u) \<in> set D) (supteq_list r))"
          by (rule mem_filter)
      qed
    qed
    then show "dp \<in> set (safe_CSDP_list R D)"
      unfolding safe_CSDP_list_def R Let_def by auto
  qed
qed

lemma exposed_CSDP_list:
  "set (exposed_CSDP_list R \<mu> D) = exposed_CSDP_on shp (mu_of \<mu>) (set D) (set R)"
proof
  show "set (exposed_CSDP_list R \<mu> D) \<subseteq> exposed_CSDP_on shp (mu_of \<mu>) (set D) (set R)"
  proof
    fix dp
    assume "dp \<in> set (exposed_CSDP_list R \<mu> D)"
    then obtain l r p u f ts where lr: "(l, r) \<in> set R"
      and p: "p \<in> set (mu_fun_poss_list \<mu> r)"
      and rp: "r |_ p = Fun f ts"
      and fD: "(f, length ts) \<in> set D"
      and sub: "Fun f ts \<unrhd> u"
      and ns: "\<not> l \<rhd> u"
      and u_fun: "is_Fun u"
      and uD: "the (root u) \<in> set D"
      and dp: "dp = (\<sharp> l, \<sharp> u)"
      unfolding exposed_CSDP_list_def Let_def
      by (auto split: term.splits if_splits)
    from u_fun obtain g us where u: "u = Fun g us"
      by (cases u, auto)
    with uD have gD: "(g, length us) \<in> set D"
      by simp
    from supteq_imp_subt_at[OF sub[unfolded rp[symmetric]]]
    obtain q where q: "q \<in> poss (r |_ p)" and u_sub: "u = r |_ p |_ q"
      by auto
    from q u_fun u_sub have q_fun: "q \<in> fun_poss (r |_ p)"
      using poss_is_Fun_fun_poss by blast
    from p have p_mu: "p \<in> mu_fun_poss (mu_of \<mu>) r"
      by simp
    have p_poss: "p \<in> poss r"
      using fun_poss_imp_poss mu_fun_poss_imp_fun_poss p_mu by blast
    have pq: "p @ q \<in> exposed_fun_poss (mu_of \<mu>) (set D) r"
      unfolding exposed_fun_poss_def
      using p_mu rp fD q_fun by blast
    have sub_pq: "r |_ (p @ q) = u"
      using p_poss q u_sub by (simp add: subt_at_append)
    show "dp \<in> exposed_CSDP_on shp (mu_of \<mu>) (set D) (set R)"
      unfolding exposed_CSDP_on_def
      apply (rule CollectI)
      apply (rule exI[of _ l])
      apply (rule exI[of _ r])
      apply (rule exI[of _ "p @ q"])
      apply (rule exI[of _ g])
      apply (rule exI[of _ us])
      using lr pq sub_pq u gD ns dp by auto
  qed
next
  show "exposed_CSDP_on shp (mu_of \<mu>) (set D) (set R) \<subseteq> set (exposed_CSDP_list R \<mu> D)"
  proof
    fix dp
    assume "dp \<in> exposed_CSDP_on shp (mu_of \<mu>) (set D) (set R)"
    then obtain l r pq g us where lr: "(l, r) \<in> set R"
      and pq_exp: "pq \<in> exposed_fun_poss (mu_of \<mu>) (set D) r"
      and pq_sub: "r |_ pq = Fun g us"
      and gD: "(g, length us) \<in> set D"
      and ns: "\<not> l \<rhd> r |_ pq"
      and dp: "dp = (\<sharp> l, \<sharp> (r |_ pq))"
      unfolding exposed_CSDP_on_def by auto
    from pq_exp obtain p q f ts where pq: "pq = p @ q"
      and p_mu: "p \<in> mu_fun_poss (mu_of \<mu>) r"
      and rp: "r |_ p = Fun f ts"
      and fD: "(f, length ts) \<in> set D"
      and q_fun: "q \<in> fun_poss (r |_ p)"
      unfolding exposed_fun_poss_def by blast
    from p_mu have p_list: "p \<in> set (mu_fun_poss_list \<mu> r)"
      by simp
    from p_mu have p_poss: "p \<in> poss r"
      using fun_poss_imp_poss mu_fun_poss_imp_fun_poss by blast
    from q_fun have q_poss: "q \<in> poss (r |_ p)"
      by (rule fun_poss_imp_poss)
    have at_pq: "r |_ (p @ q) = r |_ p |_ q"
      by (rule subt_at_append[OF p_poss])
    have q_sub: "r |_ p |_ q = Fun g us"
      using pq_sub pq at_pq by simp
    have sub_u: "Fun g us \<in> set (supteq_list (r |_ p))"
      using subt_at_imp_supteq[OF q_poss, unfolded q_sub]
      by simp
    have filt: "Fun g us \<in> set (filter
        (\<lambda>u. \<not> l \<rhd> u \<and> is_Fun u \<and> the (root u) \<in> set D)
        (supteq_list (r |_ p)))"
      using sub_u ns gD pq pq_sub by simp
    from lr obtain bef aft where R: "R = bef @ (l, r) # aft"
      by (metis split_list)
    have p_mem: "p \<in> set (mu_fun_poss_list \<mu> r)"
      using p_list .
    have dp_g: "dp = (\<sharp> l, \<sharp> (Fun g us))"
      using dp pq_sub by simp
    have mapped_mem: "dp \<in> set (map (\<lambda>u. (\<sharp> l, \<sharp> u)) (filter
        (\<lambda>u. \<not> l \<rhd> u \<and> is_Fun u \<and> the (root u) \<in> set D)
        (supteq_list (r |_ p))))"
      unfolding set_map
    proof (rule image_eqI[of _ _ "Fun g us"])
      show "dp = (\<lambda>u. (\<sharp> l, \<sharp> u)) (Fun g us)"
        using dp_g by simp
      show "Fun g us \<in> set (filter
        (\<lambda>u. \<not> l \<rhd> u \<and> is_Fun u \<and> the (root u) \<in> set D)
        (supteq_list (r |_ p)))"
        by (rule filt)
    qed
    have pair_mem: "dp \<in> set (case r |_ p of Var x \<Rightarrow> []
        | Fun f ts \<Rightarrow>
          if (f, length ts) \<in> set D
          then map (\<lambda>u. (\<sharp> l, \<sharp> u)) (filter
            (\<lambda>u. \<not> l \<rhd> u \<and> is_Fun u \<and> the (root u) \<in> set D)
            (supteq_list (r |_ p)))
          else [])"
      using rp fD mapped_mem by auto
    show "dp \<in> set (exposed_CSDP_list R \<mu> D)"
      unfolding exposed_CSDP_list_def R Let_def
      using p_mem pair_mem by auto
  qed
qed

lemma mu_csr_dependency_pairs_tt_finite_mu_CSDP_on:
  assumes J: "dpp_spec J"
    and tt: "mu_csr_dependency_pairs_tt J \<mu> R P = return d"
    and fin: "finite_dpp (dpp_ops.dpp J d)"
  shows "finite_dpp
    (False, False, mu_CSDP_on (mu_of \<mu>) (set (defined_list R)) (set R), {}, {}, {}, set R)"
proof -
  interpret dpp_spec J by fact
  let ?D = "defined_list R"
  let ?P = "mu_CSDP_on (mu_of \<mu>) (set ?D) (set R)"
  note tt' = tt[unfolded mu_csr_dependency_pairs_tt_def Let_def, simplified]
  from tt' have d: "d = dpp_ops.mk J False False P [] [] [] R"
    by auto
  from tt' have cover: "\<And>dp. dp \<in> set (mu_CSDP_list R \<mu> ?D) \<Longrightarrow>
      dp \<in> set P \<or> (\<exists>dp'\<in>set P. dp =\<^sub>v dp')"
    by auto
  have cover': "\<And>dp. dp \<in> ?P \<Longrightarrow>
      dp \<in> set P \<or> (\<exists>dp'\<in>set P. dp =\<^sub>v dp')"
    using cover unfolding mu_CSDP_list by auto
  have finP: "finite_dpp (False, False, set P, {}, {}, {}, set R)"
    using fin unfolding d mk_sound by simp
  show ?thesis
  proof (rule finite_dpp_rename_vars[OF finP])
    fix dp
    assume "dp \<in> ?P"
    from cover'[OF this] show "\<exists>dp'. dp' \<in> set P \<and> dp =\<^sub>v dp'"
      using eq_rule_mod_vars_refl[of dp] by blast
  qed auto
qed

lemma safe_csr_dependency_pairs_tt_finite_safe_CSDP_on:
  assumes J: "dpp_spec J"
    and tt: "safe_csr_dependency_pairs_tt J \<mu> R P = return d"
    and fin: "finite_dpp (dpp_ops.dpp J d)"
  shows "finite_dpp
    (False, True, safe_CSDP_on shp (set (defined_list R)) (set R), {}, {}, {}, set R)"
proof -
  interpret dpp_spec J by fact
  let ?D = "defined_list R"
  let ?P = "safe_CSDP_on shp (set ?D) (set R)"
  note tt' = tt[unfolded safe_csr_dependency_pairs_tt_def Let_def, simplified]
  from tt' have d: "d = dpp_ops.mk J False True P [] [] [] R"
    by auto
  from tt' have cover: "\<And>dp. dp \<in> set (safe_CSDP_list R ?D) \<Longrightarrow>
      dp \<in> set P \<or> (\<exists>dp'\<in>set P. dp =\<^sub>v dp')"
    by auto
  have cover': "\<And>dp. dp \<in> ?P \<Longrightarrow>
      dp \<in> set P \<or> (\<exists>dp'\<in>set P. dp =\<^sub>v dp')"
    using cover unfolding safe_CSDP_list by auto
  have finP: "finite_dpp (False, True, set P, {}, {}, {}, set R)"
    using fin unfolding d mk_sound by simp
  show ?thesis
  proof (rule finite_dpp_rename_vars[OF finP])
    fix dp
    assume "dp \<in> ?P"
    from cover'[OF this] show "\<exists>dp'. dp' \<in> set P \<and> dp =\<^sub>v dp'"
      using eq_rule_mod_vars_refl[of dp] by blast
  qed auto
qed

lemma exposed_csr_dependency_pairs_tt_finite_exposed_CSDP_on:
  assumes J: "dpp_spec J"
    and tt: "exposed_csr_dependency_pairs_tt J \<mu> R P = return d"
    and fin: "finite_dpp (dpp_ops.dpp J d)"
  shows "finite_dpp
    (False, False, exposed_CSDP_on shp (mu_of \<mu>) (set (defined_list R)) (set R), {}, {}, {}, set R)"
proof -
  interpret dpp_spec J by fact
  let ?D = "defined_list R"
  let ?P = "exposed_CSDP_on shp (mu_of \<mu>) (set ?D) (set R)"
  note tt' = tt[unfolded exposed_csr_dependency_pairs_tt_def Let_def, simplified]
  from tt' have d: "d = dpp_ops.mk J False False P [] [] [] R"
    by auto
  from tt' have cover: "\<And>dp. dp \<in> set (exposed_CSDP_list R \<mu> ?D) \<Longrightarrow>
      dp \<in> set P \<or> (\<exists>dp'\<in>set P. dp =\<^sub>v dp')"
    by auto
  have cover': "\<And>dp. dp \<in> ?P \<Longrightarrow>
      dp \<in> set P \<or> (\<exists>dp'\<in>set P. dp =\<^sub>v dp')"
    using cover unfolding exposed_CSDP_list by auto
  have finP: "finite_dpp (False, False, set P, {}, {}, {}, set R)"
    using fin unfolding d mk_sound by simp
  show ?thesis
  proof (rule finite_dpp_rename_vars[OF finP])
    fix dp
    assume "dp \<in> ?P"
    from cover'[OF this] show "\<exists>dp'. dp' \<in> set P \<and> dp =\<^sub>v dp'"
      using eq_rule_mod_vars_refl[of dp] by blast
  qed auto
qed

lemma finite_mu_CSDP_on_imp_SN_rel:
  assumes fin: "finite_dpp (False, False, mu_CSDP_on \<mu> D R, {}, {}, {}, R)"
  shows "SN_rel (rrstep (mu_CSDP_on \<mu> D R)) (rstep R)"
  using fin
  unfolding finite_dpp_iff_SN_rel CS_rrstep_conv by simp

definition finite_csr_dpp ::
  "'f mu \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> bool"
where
  "finite_csr_dpp \<mu> P R \<longleftrightarrow> SN_rel (rrstep P) (csstep \<mu> R)"

lemma finite_dpp_imp_finite_csr_dpp:
  assumes fin: "finite_dpp (False, False, P, {}, {}, {}, R)"
  shows "finite_csr_dpp \<mu> P R"
proof -
  have rel: "SN_rel (rrstep P) (rstep R)"
    using fin unfolding finite_dpp_iff_SN_rel CS_rrstep_conv by simp
  have cs_sub: "csstep \<mu> R \<subseteq> rstep R"
    unfolding csstep_def csstep_p_def
    by (auto dest: rstep_r_p_s_imp_rstep)
  show ?thesis
    unfolding finite_csr_dpp_def
    by (rule SN_rel_mono[OF subset_refl cs_sub rel])
qed

lemma csstep_mono:
  assumes "R \<subseteq> S"
  shows "csstep \<mu> R \<subseteq> csstep \<mu> S"
  using assms unfolding csstep_def csstep_p_def rstep_r_p_s_def' by auto

lemma rrstep_mono:
  assumes "P \<subseteq> Q"
  shows "rrstep P \<subseteq> rrstep Q"
  using assms unfolding rrstep_def' by auto

lemma finite_csr_dpp_mono:
  assumes fin: "finite_csr_dpp \<mu> P' R'"
    and P: "P \<subseteq> P'"
    and R: "R \<subseteq> R'"
  shows "finite_csr_dpp \<mu> P R"
  using fin unfolding finite_csr_dpp_def
  by (rule SN_rel_mono[OF rrstep_mono[OF P] csstep_mono[OF R]])

lemma finite_csr_dpp_imp_SN_csstep_if_mu_Tinf_progress:
  assumes progress: "\<And>t. t \<in> mu_Tinf \<mu> (csstep \<mu> R) \<Longrightarrow>
      \<exists>u. u \<in> mu_Tinf \<mu> (csstep \<mu> R) \<and>
        (\<sharp> t, \<sharp> u) \<in> (csstep \<mu> R)\<^sup>* O rrstep P O (csstep \<mu> R)\<^sup>*"
    and fin: "finite_csr_dpp \<mu> P R"
  shows "SN (csstep \<mu> R)"
proof (rule ccontr)
  assume "\<not> SN (csstep \<mu> R)"
  from not_SN_imp_Tinf[OF this]
  obtain t0 where t0_T: "t0 \<in> Tinf (csstep \<mu> R)"
    by blast
  from Tinf_imp_mu_Tinf[OF t0_T]
  have t0: "t0 \<in> mu_Tinf \<mu> (csstep \<mu> R)" .
  let ?S = "csstep \<mu> R"
  let ?rel = "?S\<^sup>* O rrstep P O ?S\<^sup>*"
  have all_ex: "\<forall>t. \<exists>u. t \<in> mu_Tinf \<mu> ?S \<longrightarrow>
    u \<in> mu_Tinf \<mu> ?S \<and> (\<sharp> t, \<sharp> u) \<in> ?rel"
    using progress by blast
  from choice[OF all_ex]
  obtain nxt where nxt: "\<And>t. t \<in> mu_Tinf \<mu> ?S \<Longrightarrow>
    nxt t \<in> mu_Tinf \<mu> ?S \<and> (\<sharp> t, \<sharp> (nxt t)) \<in> ?rel"
    by blast
  define ts where "ts = rec_nat t0 (\<lambda>n t. nxt t)"
  have ts_T: "ts n \<in> mu_Tinf \<mu> ?S" for n
  proof (induct n)
    case 0
    then show ?case unfolding ts_def using t0 by simp
  next
    case (Suc n)
    from nxt[OF Suc.hyps] have "nxt (ts n) \<in> mu_Tinf \<mu> ?S"
      by simp
    show ?case
      using \<open>nxt (ts n) \<in> mu_Tinf \<mu> ?S\<close>
      unfolding ts_def by simp
  qed
  have ts_step: "(\<sharp> (ts n), \<sharp> (ts (Suc n))) \<in> ?rel" for n
  proof -
    from nxt[OF ts_T[of n]]
    have step: "(\<sharp> (ts n), \<sharp> (nxt (ts n))) \<in> ?rel"
      by simp
    show ?thesis
      using step unfolding ts_def by simp
  qed
  define f where "f n = \<sharp> (ts n)" for n
  have chain: "\<And>n. (f n, f (Suc n)) \<in> ?rel"
    unfolding f_def using ts_step by simp
  have "\<not> SN_rel (rrstep P) ?S"
    unfolding SN_rel_on_def SN_defs
    using chain by blast
  moreover from fin have "SN_rel (rrstep P) ?S"
    unfolding finite_csr_dpp_def .
  ultimately show False by contradiction
qed

lemma finite_mu_CSDP_on_imp_SN_csstep_if_mu_Tinf_progress:
  assumes progress: "\<And>t. t \<in> mu_Tinf \<mu> (csstep \<mu> R) \<Longrightarrow>
      \<exists>u. u \<in> mu_Tinf \<mu> (csstep \<mu> R) \<and>
        (\<sharp> t, \<sharp> u) \<in> (rstep R)\<^sup>* O rrstep (mu_CSDP_on \<mu> D R) O (rstep R)\<^sup>*"
    and fin: "finite_dpp (False, False, mu_CSDP_on \<mu> D R, {}, {}, {}, R)"
  shows "SN (csstep \<mu> R)"
proof (rule ccontr)
  assume "\<not> SN (csstep \<mu> R)"
  from not_SN_imp_Tinf[OF this]
  obtain t0 where t0_T: "t0 \<in> Tinf (csstep \<mu> R)"
    by blast
  from Tinf_imp_mu_Tinf[OF t0_T]
  have t0: "t0 \<in> mu_Tinf \<mu> (csstep \<mu> R)" .
  let ?P = "rrstep (mu_CSDP_on \<mu> D R)"
  let ?S = "rstep R"
  let ?rel = "?S\<^sup>* O ?P O ?S\<^sup>*"
  have step_ex: "\<And>t. t \<in> mu_Tinf \<mu> (csstep \<mu> R) \<Longrightarrow>
    \<exists>u. u \<in> mu_Tinf \<mu> (csstep \<mu> R) \<and> (\<sharp> t, \<sharp> u) \<in> ?rel"
    using progress by blast
  have all_ex: "\<forall>t. \<exists>u. t \<in> mu_Tinf \<mu> (csstep \<mu> R) \<longrightarrow>
    u \<in> mu_Tinf \<mu> (csstep \<mu> R) \<and> (\<sharp> t, \<sharp> u) \<in> ?rel"
    using step_ex by blast
  from choice[OF all_ex]
  obtain nxt where nxt: "\<And>t. t \<in> mu_Tinf \<mu> (csstep \<mu> R) \<Longrightarrow>
    nxt t \<in> mu_Tinf \<mu> (csstep \<mu> R) \<and> (\<sharp> t, \<sharp> (nxt t)) \<in> ?rel"
    by blast
  define ts where "ts = rec_nat t0 (\<lambda>n t. nxt t)"
  have ts_T: "ts n \<in> mu_Tinf \<mu> (csstep \<mu> R)" for n
  proof (induct n)
    case 0
    then show ?case unfolding ts_def using t0 by simp
  next
    case (Suc n)
    from nxt[OF Suc.hyps] have "nxt (ts n) \<in> mu_Tinf \<mu> (csstep \<mu> R)"
      by simp
    show ?case
      using \<open>nxt (ts n) \<in> mu_Tinf \<mu> (csstep \<mu> R)\<close>
      unfolding ts_def by simp
  qed
  have ts_step: "(\<sharp> (ts n), \<sharp> (ts (Suc n))) \<in> ?rel" for n
  proof -
    from nxt[OF ts_T[of n]]
    have step: "(\<sharp> (ts n), \<sharp> (nxt (ts n))) \<in> ?rel"
      by simp
    show ?thesis
      using step unfolding ts_def by simp
  qed
  define f where "f n = \<sharp> (ts n)" for n
  have chain: "\<And>n. (f n, f (Suc n)) \<in> ?rel"
    unfolding f_def using ts_step by simp
  have "\<not> SN_rel ?P ?S"
    unfolding SN_rel_on_def SN_defs
    using chain by blast
  moreover from finite_mu_CSDP_on_imp_SN_rel[OF fin]
  have "SN_rel ?P ?S" .
  ultimately show False by contradiction
qed

lemma finite_mu_CSDP_on_imp_SN_csstep:
  assumes wf: "wf_trs R"
    and vc: "rhs_mu_vars_condition \<mu> R"
    and D: "{f. defined R f} \<subseteq> D"
    and fin: "finite_dpp (False, False, mu_CSDP_on \<mu> D R, {}, {}, {}, R)"
  shows "SN (csstep \<mu> R)"
  by (rule finite_mu_CSDP_on_imp_SN_csstep_if_mu_Tinf_progress[OF _ fin],
      rule mu_Tinf_imp_mu_CSDP_relstep[OF wf _ vc D])

lemma finite_csr_mu_CSDP_on_imp_SN_csstep:
  assumes wf: "wf_trs R"
    and vc: "rhs_mu_vars_condition \<mu> R"
    and D: "{f. defined R f} \<subseteq> D"
    and sharp_mu: "\<And>f n. \<mu> (f, n) \<subseteq> \<mu> (\<sharp> f, n)"
    and fin: "finite_csr_dpp \<mu> (mu_CSDP_on \<mu> D R) R"
  shows "SN (csstep \<mu> R)"
  by (rule finite_csr_dpp_imp_SN_csstep_if_mu_Tinf_progress[OF _ fin],
      rule mu_Tinf_imp_mu_CSDP_csrelstep[OF wf _ vc D sharp_mu])


end

datatype (dead 'f, dead 'l, dead 'v) csr_dp_termination_proof =
  CSR_DP_P_is_Empty
| CSR_DP_Ordinary_Proof "('f, 'l, 'v) dp_termination_proof"
| CSR_DP_Subterm_Criterion_Proc "('f, 'l) lab projL" "('f, 'l, 'v) rseqL"
    "('f, 'l, 'v) trsLL" "('f, 'l, 'v) csr_dp_termination_proof"
| CSR_DP_Gen_Subterm_Criterion_Proc "('f, 'l) lab status_impl"
    "('f, 'l, 'v) trsLL" "('f, 'l, 'v) csr_dp_termination_proof"
| CSR_DP_Usable_Rules_Proc "('f, 'l, 'v) trsLL" "('f, 'l, 'v) csr_dp_termination_proof"
| CSR_DP_Dep_Graph_Proc "(('f, 'l, 'v) csr_dp_termination_proof option \<times> ('f, 'l, 'v) trsLL) list"
| CSR_DP_Size_Change_Subterm_Proc
    "((('f, 'l) lab, 'v) rule \<times> ((nat \<times> nat) list \<times> (nat \<times> nat) list)) list"

datatype (dead 'f, dead 'l, dead 'v) csr_termination_proof =
  CSR_R_is_Empty
| CSR_Rule_Removal
    "('f, 'l) lab redtriple_impl" "('f, 'l, 'v) trsLL"
    "('f, 'l, 'v) csr_termination_proof"
| CSR_Dependency_Pairs
    "('f, 'l, 'v) trsLL" "('f, 'l, 'v) csr_dp_termination_proof"

fun dp_proof_of_csr_dp_termination_proof ::
  "('f, 'l, 'v) csr_dp_termination_proof \<Rightarrow> ('f, 'l, 'v) dp_termination_proof"
where
  "dp_proof_of_csr_dp_termination_proof CSR_DP_P_is_Empty = P_is_Empty"
| "dp_proof_of_csr_dp_termination_proof (CSR_DP_Ordinary_Proof prf) = prf"
| "dp_proof_of_csr_dp_termination_proof
    (CSR_DP_Subterm_Criterion_Proc p rseq Pr prf) =
    Subterm_Criterion_Proc p rseq Pr (dp_proof_of_csr_dp_termination_proof prf)"
| "dp_proof_of_csr_dp_termination_proof
    (CSR_DP_Gen_Subterm_Criterion_Proc p Pr prf) =
    Gen_Subterm_Criterion_Proc p Pr (dp_proof_of_csr_dp_termination_proof prf)"
| "dp_proof_of_csr_dp_termination_proof (CSR_DP_Usable_Rules_Proc U prf) =
    Usable_Rules_Proc U (dp_proof_of_csr_dp_termination_proof prf)"
| "dp_proof_of_csr_dp_termination_proof (CSR_DP_Dep_Graph_Proc edpts) =
    Dep_Graph_Proc
      (map (\<lambda>(prf, P). (map_option dp_proof_of_csr_dp_termination_proof prf, P)) edpts)"
| "dp_proof_of_csr_dp_termination_proof (CSR_DP_Size_Change_Subterm_Proc graphs) =
    Size_Change_Subterm_Proc graphs"

definition check_csr_dp_termination_proof ::
  "('tp, ('f::{showl, compare_order,countable}, label_type) lab, string) tp_ops \<Rightarrow>
   ('dpp, ('f, label_type) lab, string) dpp_ops \<Rightarrow> bool \<Rightarrow>
   showsl \<Rightarrow> 'dpp \<Rightarrow>
   ('f, label_type, string) csr_dp_termination_proof \<Rightarrow> showsl check"
where
  "check_csr_dp_termination_proof I J a i dpp prf =
    check_dp_termination_proof I J a i dpp (dp_proof_of_csr_dp_termination_proof prf)"

primrec check_csr_termination_proof ::
  "('tp, ('f::{showl, compare_order,countable}, label_type) lab, string) tp_ops \<Rightarrow>
   ('dpp, ('f, label_type) lab, string) dpp_ops \<Rightarrow> bool \<Rightarrow>
   showsl \<Rightarrow> (('f, label_type) lab) muL \<Rightarrow>
   ('f, label_type, string) trsLL \<Rightarrow> ('f, label_type, string) csr_termination_proof \<Rightarrow> showsl check"
where
  "check_csr_termination_proof I J a i \<mu> R CSR_R_is_Empty = debug i (STR ''CSR R is empty'')
     (if R = []
      then succeed
      else error (i \<circ> showsl_lit (STR '': CSR R is not empty'')))"
| "check_csr_termination_proof I J a i \<mu> R (CSR_Rule_Removal redp Rr prf) =
    debug i (STR ''CSR rule removal'')
      (case csr_rule_removal_impl redp \<mu> Rr R of
        Inl e \<Rightarrow> Inl e
      | Inr R2 \<Rightarrow> check_csr_termination_proof I J a i \<mu> R2 prf)"
| "check_csr_termination_proof I J a i \<mu> R (CSR_Dependency_Pairs P prf) =
    debug i (STR ''CSR dependency pairs'') (do {
      csr_sharp_mu_check \<mu>
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': invalid replacement map for CSR dependency pairs\<newline>'') \<circ> s);
      dpp \<leftarrow> csr_dependency_pairs_tt Sharp J \<mu> R P
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when switching from CSR to a CS-DP problem\<newline>'')
          \<circ> showsl_rules R \<circ> showsl_lit (STR ''\<newline>with pairs\<newline>'') \<circ> showsl_rules P
          \<circ> showsl_nl \<circ> s);
      check_csr_dp_termination_proof I J False (add_index i 1) dpp prf
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below CSR dependency pairs\<newline>'') \<circ> s)
    })"

lemma check_csr_dp_termination_proof_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_csr_dp_termination_proof I J False i dpp prf)"
  shows "finite_dpp (dpp_ops.dpp J dpp)"
  using ok unfolding check_csr_dp_termination_proof_def
  by (rule check_dp_termination_proof[OF I J])

lemma csstep_subset_rstep: "csstep \<mu> R \<subseteq> rstep R"
proof
  fix st
  assume "st \<in> csstep \<mu> R"
  then obtain p lr \<sigma> where "st \<in> rstep_r_p_s R lr p \<sigma>"
    unfolding csstep_def csstep_p_def by auto
  then obtain s t where st: "st = (s, t)" and step: "(s, t) \<in> rstep_r_p_s R lr p \<sigma>"
    by (cases st, auto)
  from step have "(s, t) \<in> rstep R"
    by (rule rstep_r_p_s_imp_rstep)
  then show "st \<in> rstep R"
    using st by simp
qed

context
  fixes shp :: "'f::{showl, compare_order} \<Rightarrow> 'f"
begin

interpretation sharp_syntax .

lemma finite_safe_CSDP_on_imp_SN_csstep:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. (f, n) \<in> D \<Longrightarrow> \<not> defined R (shp f, n)"
    and D: "\<And>fn. defined R fn \<Longrightarrow> fn \<in> D"
    and fin: "finite_dpp (False, True, safe_CSDP_on shp D R, {}, {}, {}, R)"
  shows "SN (csstep \<mu> R)"
proof -
  have SN_r: "SN (rstep R)"
  proof (rule ccontr)
    assume nSN: "\<not> SN (rstep R)"
    have nSNq: "\<not> SN (qrstep False {} R)"
      using nSN by simp
    have wfq: "wf_qtrs False {} R"
      using wf unfolding wf_qtrs_def wwf_qtrs_wf_trs by simp
    have ndefQ: "\<And>f n ss. defined (applicable_rules {} R) (f, n) \<Longrightarrow>
      length ss = n \<Longrightarrow> Fun (shp f) ss \<notin> {}"
      by simp
    have m: "True = (\<forall>f n. defined (applicable_rules {} R) (f, n) \<longrightarrow>
      \<not> defined (applicable_rules {} R) (shp f, n))"
      using fresh D by auto
    have ex_chain: "\<exists>s t \<sigma>. min_ichain (initial_dpp shp False True {} R) s t \<sigma>"
      using not_SN_imp_min_ichain[OF wfq nSNq ndefQ m] .
    from ex_chain
    obtain s t \<sigma> where chain: "min_ichain (initial_dpp shp False True {} R) s t \<sigma>"
      by blast
    have P_sub: "DP_on shp {fn. defined R fn} R \<subseteq> safe_CSDP_on shp D R"
    proof
      fix dp
      assume "dp \<in> DP_on shp {fn. defined R fn} R"
      then obtain l r h us where dp: "dp = (\<sharp> l, \<sharp> (Fun h us))"
        and lr: "(l, r) \<in> R" and sub: "r \<unrhd> Fun h us"
        and hdef: "defined R (h, length us)" and ns: "\<not> l \<rhd> Fun h us"
        unfolding DP_on_def by auto
      from D[OF hdef] have "(h, length us) \<in> D" .
      with dp lr sub ns show "dp \<in> safe_CSDP_on shp D R"
        unfolding safe_CSDP_on_def DP_on_def by blast
    qed
    have fin_init: "finite_dpp (False, True, DP_on shp {fn. defined R fn} R, {}, {}, {}, R)"
      by (rule finite_dpp_mono[OF fin P_sub]) (insert P_sub, auto)
    have init: "initial_dpp shp False True {} R =
      (False, True, DP_on shp {fn. defined R fn} R, {}, {}, {}, R)"
      by (simp add: applicable_rules_empty)
    from fin_init chain show False
      unfolding finite_dpp_def init[symmetric] by blast
  qed
  show ?thesis
    by (rule SN_subset[OF SN_r csstep_subset_rstep])
qed

end

lemma check_csr_termination_proof_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_csr_termination_proof I J a i \<mu> R prf)"
  shows "SN (csstep (mu_of \<mu>) (set R))"
  using ok
  apply (induct "prf" arbitrary: R)
  subgoal by auto
  subgoal
    apply (simp split: sum.splits)
    apply (rule csr_rule_removal_impl)
     apply assumption
    apply auto
    done
  subgoal for P dp_prf R0
  proof -
    assume ok_case:
      "isOK (check_csr_termination_proof I J a i \<mu> R0 (CSR_Dependency_Pairs P dp_prf))"
    let ?i = "add_index i 1"
    have sharp_ok: "isOK (csr_sharp_mu_check \<mu>)"
      using ok_case by auto
    obtain dpp where
      dp: "csr_dependency_pairs_tt Sharp J \<mu> R0 P = return dpp"
      and rec: "isOK (check_csr_dp_termination_proof I J False ?i dpp dp_prf)"
      using ok_case by auto
    have fin: "finite_dpp (dpp_ops.dpp J dpp)"
      by (rule check_csr_dp_termination_proof_sound[OF I J rec])
    show ?thesis
    proof (cases "mu_csr_dependency_pairs_tt Sharp J \<mu> R0 P")
      case (Inl e)
      from dp Inl have safe_dp: "safe_csr_dependency_pairs_tt Sharp J \<mu> R0 P = return dpp"
        unfolding csr_dependency_pairs_tt_def by simp
      have fin_safe: "finite_dpp
        (False, True, safe_CSDP_on Sharp (set (defined_list R0)) (set R0), {}, {}, {}, set R0)"
        by (rule safe_csr_dependency_pairs_tt_finite_safe_CSDP_on[OF J safe_dp fin])
      note safe_dp' = safe_dp[unfolded safe_csr_dependency_pairs_tt_def Let_def, simplified]
      have wf: "wf_trs (set R0)"
        using safe_dp' by auto
      have fresh: "\<And>f n. (f, n) \<in> set (defined_list R0) \<Longrightarrow>
        \<not> defined (set R0) (Sharp f, n)"
        using safe_dp' by auto
      have D: "\<And>fn. defined (set R0) fn \<Longrightarrow> fn \<in> set (defined_list R0)"
        using safe_dp' by auto
      show ?thesis
        by (rule finite_safe_CSDP_on_imp_SN_csstep[OF wf fresh D fin_safe])
    next
      case (Inr d)
      from dp Inr have d: "d = dpp"
        unfolding csr_dependency_pairs_tt_def by simp
      have mu_dp: "mu_csr_dependency_pairs_tt Sharp J \<mu> R0 P = return dpp"
        using Inr d by simp
      have fin_mu: "finite_dpp
        (False, False, mu_CSDP_on Sharp (mu_of \<mu>) (set (defined_list R0)) (set R0), {}, {}, {}, set R0)"
        by (rule mu_csr_dependency_pairs_tt_finite_mu_CSDP_on[OF J mu_dp fin])
      have fin_mu_csr: "finite_csr_dpp (mu_of \<mu>)
        (mu_CSDP_on Sharp (mu_of \<mu>) (set (defined_list R0)) (set R0)) (set R0)"
        by (rule finite_dpp_imp_finite_csr_dpp[OF fin_mu])
      note mu_dp' = mu_dp[unfolded mu_csr_dependency_pairs_tt_def Let_def, simplified]
      have wf: "wf_trs (set R0)"
        using mu_dp' by auto
      have vc: "rhs_mu_vars_condition (mu_of \<mu>) (set R0)"
        by (rule rhs_mu_vars_condition_list_sound, insert mu_dp', auto)
      have D: "{f. defined (set R0) f} \<subseteq> set (defined_list R0)"
        using mu_dp' by auto
      have sharp_mu: "\<And>f n. mu_of \<mu> (f, n) \<subseteq> mu_of \<mu> (Sharp f, n)"
        by (rule csr_sharp_mu_check_sound[OF sharp_ok])
      show ?thesis
        by (rule finite_csr_mu_CSDP_on_imp_SN_csstep[OF wf vc D sharp_mu fin_mu_csr])
    qed
  qed
  done

lemma (in mono_redpair) csr_rule_removal:
  assumes strict: "Rs \<subseteq> S"
    and weak: "Rr \<subseteq> NS"
    and rec: "SN (csstep \<mu> Rr)"
  shows "SN (csstep \<mu> (Rs \<union> Rr))"
proof -
  have mono_S: "af_monotone \<mu> S"
    by (rule ctxt_closed_imp_af_monotone[OF ctxt_S])
  have mono_NS: "af_monotone \<mu> NS"
    by (rule ctxt_closed_imp_af_monotone[OF ctxt_NS])
  have s_sub: "csstep \<mu> Rs \<subseteq> S"
    by (rule csstep_subset_order[OF strict mono_S subst_S])
  have ns_sub: "csstep \<mu> Rr \<subseteq> NS"
    by (rule csstep_subset_order[OF weak mono_NS subst_NS])
  have rel: "SN_rel (csstep \<mu> Rs) (csstep \<mu> Rr)"
    by (rule SN_rel_mono[OF s_sub ns_sub],
        unfold SN_rel_defs,
        rule SN_subset[OF compatible_SN'[OF compat_NS_S SN]],
        regexp)
  have relto: "SN (relto (csstep \<mu> Rs) (csstep \<mu> Rr))"
    by (rule SN_rel_imp_SN_relto[OF rel])
  have "SN (csstep \<mu> Rs \<union> csstep \<mu> Rr)"
    using relto rec SN_on_Un[of "csstep \<mu> Rs" "csstep \<mu> Rr" UNIV]
    by simp
  moreover have "csstep \<mu> (Rs \<union> Rr) \<subseteq> csstep \<mu> Rs \<union> csstep \<mu> Rr"
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
  ultimately show ?thesis
    by (rule SN_subset)
qed

end
