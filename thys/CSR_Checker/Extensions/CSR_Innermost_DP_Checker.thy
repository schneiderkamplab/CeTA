(*
Author: Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Innermost_DP_Checker
  imports CSR_Checker_Extensions.CSR_Innermost_Switch
begin

datatype csr_rewrite_mode = CSR_Full | CSR_Innermost

definition innermost_pair_source ::
  "('f \<Rightarrow> 'f) \<Rightarrow> 'f mu \<Rightarrow> ('f, 'v) trs \<Rightarrow>
    ('f, 'v) term \<Rightarrow> bool"
where
  "innermost_pair_source shp \<mu> R s \<longleftrightarrow> (\<exists>l r \<sigma>.
    (l,r) \<in> R \<and> is_Fun l \<and>
    s = sharp_term shp (l \<cdot> \<sigma>) \<and>
    (\<forall>u. mu_supt \<mu> (l \<cdot> \<sigma>) u \<longrightarrow> u \<in> NF (csstep \<mu> R)))"

definition innermost_rrstep ::
  "('f \<Rightarrow> 'f) \<Rightarrow> 'f mu \<Rightarrow> ('f, 'v) trs \<Rightarrow>
    ('f, 'v) trs \<Rightarrow> ('f, 'v) term rel"
where
  "innermost_rrstep shp \<mu> R P =
    {(s,t). (s,t) \<in> rrstep P \<and> innermost_pair_source shp \<mu> R s}"

context
  fixes shp :: "'f::{showl,compare_order} \<Rightarrow> 'f"
begin

interpretation sharp_syntax .

fun csr_mode_step where
  "csr_mode_step CSR_Full \<mu> R = csstep \<mu> R"
| "csr_mode_step CSR_Innermost \<mu> R = innermost_csstep \<mu> R"

definition innermost_csstep_p ::
  "'f mu \<Rightarrow> ('f, 'v) trs \<Rightarrow> pos \<Rightarrow> ('f, 'v) term rel"
where
  "innermost_csstep_p \<mu> R p = {(s,t). \<exists>lr \<sigma>.
    (s,t) \<in> rstep_r_p_s R lr p \<sigma> \<and>
    csstep_cond \<mu> p s \<and>
    (\<forall>u. mu_supt \<mu> (fst lr \<cdot> \<sigma>) u \<longrightarrow>
      u \<in> NF (csstep \<mu> R))}"

definition innermost_csrstep ::
  "'f mu \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) term rel"
where
  "innermost_csrstep \<mu> R = innermost_csstep_p \<mu> R []"

definition innermost_csnrstep ::
  "'f mu \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) term rel"
where
  "innermost_csnrstep \<mu> R = {(s,t). \<exists>p.
    p \<noteq> [] \<and> (s,t) \<in> innermost_csstep_p \<mu> R p}"

lemma innermost_csstep_position_union:
  "innermost_csstep \<mu> R = (\<Union>p. innermost_csstep_p \<mu> R p)"
  unfolding innermost_csstep_def innermost_csstep_p_def by blast

lemma innermost_csstep_root_nonroot:
  "innermost_csstep \<mu> R =
    innermost_csrstep \<mu> R \<union> innermost_csnrstep \<mu> R"
  unfolding innermost_csstep_position_union innermost_csrstep_def
    innermost_csnrstep_def
  by (auto, metis list.exhaust)

lemma innermost_csstep_p_subset_csstep_p:
  "innermost_csstep_p \<mu> R p \<subseteq> csstep_p \<mu> R p"
  unfolding innermost_csstep_p_def csstep_p_def by blast

lemma innermost_csrstep_subset_csrstep:
  "innermost_csrstep \<mu> R \<subseteq> csrstep \<mu> R"
  unfolding innermost_csrstep_def csrstep_def
  using innermost_csstep_p_subset_csstep_p .

lemma innermost_csnrstep_subset_csnrstep:
  "innermost_csnrstep \<mu> R \<subseteq> csnrstep \<mu> R"
  unfolding innermost_csnrstep_def csnrstep_def
  using innermost_csstep_p_subset_csstep_p by blast

lemma innermost_csnrstep_FunE:
  assumes step: "(Fun f ss,t) \<in> innermost_csnrstep \<mu> R"
  obtains i ts where "i < length ss" "i \<in> \<mu> (f,length ss)"
    "t = Fun f ts" "length ts = length ss"
    "(ss ! i,ts ! i) \<in> innermost_csstep \<mu> R"
    "\<And>j. j < length ss \<Longrightarrow> j \<noteq> i \<Longrightarrow> ts ! j = ss ! j"
proof -
  from step obtain p lr \<sigma> where p_ne: "p \<noteq> []"
    and rstep: "(Fun f ss,t) \<in> rstep_r_p_s R lr p \<sigma>"
    and cond: "csstep_cond \<mu> p (Fun f ss)"
    and inner: "\<And>u. mu_supt \<mu> (fst lr \<cdot> \<sigma>) u \<Longrightarrow>
      u \<in> NF (csstep \<mu> R)"
    unfolding innermost_csnrstep_def innermost_csstep_p_def by blast
  from p_ne obtain i q where p: "p = i # q"
    by (cases p, auto)
  from rstep[unfolded rstep_r_p_s_def'] p have i: "i < length ss"
    and t_def: "t = Fun f (take i ss @
      (ctxt_of_pos_term q (ss ! i))\<langle>snd lr \<cdot> \<sigma>\<rangle> #
      drop (Suc i) ss)"
    by auto
  let ?ts = "take i ss @
    (ctxt_of_pos_term q (ss ! i))\<langle>snd lr \<cdot> \<sigma>\<rangle> #
    drop (Suc i) ss"
  have t_shape: "\<exists>ts. t = Fun f ts \<and> length ts = length ss \<and>
      (\<forall>j<length ss. j \<noteq> i \<longrightarrow> ts ! j = ss ! j)"
  proof (intro exI[of _ ?ts] conjI allI impI)
    show "t = Fun f ?ts" by (rule t_def)
    show "length ?ts = length ss" using i by simp
    fix j
    assume j: "j < length ss" and ji: "j \<noteq> i"
    show "?ts ! j = ss ! j"
      using i j ji by (auto simp: nth_append)
  qed
  from cond[unfolded csstep_cond_def, rule_format, of "[]" i q] p i
  have i_mu: "i \<in> \<mu> (f,length ss)"
    using rstep[unfolded rstep_r_p_s_def'] by auto
  from t_shape obtain ts where t: "t = Fun f ts"
    and len: "length ts = length ss"
    and same: "\<And>j. j < length ss \<Longrightarrow> j \<noteq> i \<Longrightarrow>
      ts ! j = ss ! j"
    by auto
  have qrstep: "(Fun f ss,t) \<in>
      qrstep_r_p_s False {} R lr ([i] @ q) \<sigma>"
    using rstep unfolding p qrstep_r_p_s_def rstep_r_p_s_def' by auto
  have sub_qrstep: "(Fun f ss |_ [i],t |_ [i]) \<in>
      qrstep_r_p_s False {} R lr q \<sigma>"
    by (rule qrstep_subt_at_gen[OF qrstep])
  from sub_qrstep p t
  have sub_rstep: "(ss ! i,ts ! i) \<in> rstep_r_p_s R lr q \<sigma>"
    unfolding qrstep_r_p_s_def rstep_r_p_s_def' by auto
  have iq_poss: "i # q \<in> poss (Fun f ss)"
    using rstep p unfolding rstep_r_p_s_def' by auto
  have cond_q: "csstep_cond \<mu> q (ss ! i)"
    by (rule csstep_cond_Cons_FunD(2)[OF cond[unfolded p] iq_poss])
  have local: "(ss ! i,ts ! i) \<in> innermost_csstep \<mu> R"
    unfolding innermost_csstep_def
    using sub_rstep cond_q inner by blast
  show ?thesis
    by (rule that[OF i i_mu t len local same])
qed

definition innermost_csdp_step ::
  "'f mu \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) term rel"
where
  "innermost_csdp_step \<mu> R = {(s,t). \<exists>p lr \<sigma>.
    (s,t) \<in> rstep_r_p_s R lr p \<sigma> \<and>
    csdp_step_cond shp \<mu> p s \<and>
    (\<forall>u. mu_supt \<mu> (fst lr \<cdot> \<sigma>) u \<longrightarrow>
      u \<in> NF (csstep \<mu> R))}"

fun csr_mode_csdp_step where
  "csr_mode_csdp_step CSR_Full \<mu> R = csdp_step shp \<mu> R"
| "csr_mode_csdp_step CSR_Innermost \<mu> R = innermost_csdp_step \<mu> R"

fun csr_mode_rrstep where
  "csr_mode_rrstep CSR_Full \<mu> R P = rrstep P"
| "csr_mode_rrstep CSR_Innermost \<mu> R P = innermost_rrstep shp \<mu> R P"

definition finite_mode_csr_dpp ::
  "csr_rewrite_mode \<Rightarrow> 'f mu \<Rightarrow> ('f, 'v) trs \<Rightarrow>
    ('f, 'v) trs \<Rightarrow> bool"
where
  "finite_mode_csr_dpp mode \<mu> P R \<longleftrightarrow>
    SN_rel (csr_mode_rrstep mode \<mu> R P)
      (csr_mode_csdp_step mode \<mu> R)"

lemma finite_mode_csr_dpp_full [simp]:
  "finite_mode_csr_dpp CSR_Full \<mu> P R = finite_csr_dpp shp \<mu> P R"
  unfolding finite_mode_csr_dpp_def finite_csr_dpp_def by simp

lemma innermost_csdp_step_subset_csdp_step:
  "innermost_csdp_step \<mu> R \<subseteq> csdp_step shp \<mu> R"
  unfolding innermost_csdp_step_def csdp_step_def csdp_step_p_def by blast

lemma innermost_rrstep_subset_rrstep:
  "innermost_rrstep shp \<mu> R P \<subseteq> rrstep P"
  unfolding innermost_rrstep_def by blast

fun csr_dp_unsharp_root ::
  "((('f, 'l) lab), 'v) term \<Rightarrow> ((('f, 'l) lab), 'v) term"
where
  "csr_dp_unsharp_root (Var x) = Var x"
| "csr_dp_unsharp_root (Fun (Sharp f) ts) = Fun f ts"
| "csr_dp_unsharp_root (Fun f ts) = Fun f ts"

definition csr_dp_root_supt ::
  "(('f, 'l) lab) mu \<Rightarrow> ((('f, 'l) lab), 'v) term \<Rightarrow>
    ((('f, 'l) lab), 'v) term \<Rightarrow> bool"
where
  "csr_dp_root_supt \<mu> s t \<longleftrightarrow>
    mu_supt \<mu> (csr_dp_unsharp_root s) t"

lemma csr_dp_unsharp_root_subst:
  assumes "is_Fun s"
  shows "csr_dp_unsharp_root (s \<cdot> \<sigma>) =
    csr_dp_unsharp_root s \<cdot> \<sigma>"
  using assms by (cases s rule: csr_dp_unsharp_root.cases) auto

lemma csr_dp_root_supt_sharp:
  assumes "is_Fun s"
  shows "csr_dp_root_supt \<mu> (sharp_term Sharp s) t = mu_supt \<mu> s t"
  using assms unfolding csr_dp_root_supt_def by (cases s) auto

lemma csr_dp_root_supt_subst:
  assumes fun_s: "is_Fun s" and supt: "csr_dp_root_supt \<mu> s t"
  shows "csr_dp_root_supt \<mu> (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)"
  using mu_supt_subst[OF supt[unfolded csr_dp_root_supt_def], of \<sigma>]
  unfolding csr_dp_root_supt_def csr_dp_unsharp_root_subst[OF fun_s] .

definition innermost_csr_lhs_blocked ::
  "(('f, 'l) lab) mu \<Rightarrow> ((('f, 'l) lab), 'v) trs \<Rightarrow>
    ((('f, 'l) lab), 'v) term \<Rightarrow> bool"
where
  "innermost_csr_lhs_blocked \<mu> R u \<longleftrightarrow> (\<exists>w l r \<rho>.
    csr_dp_root_supt \<mu> u w \<and> (l,r) \<in> R \<and>
    w = l \<cdot> \<rho>)"

lemma innermost_csr_lhs_blocked_no_pair_source:
  assumes blocked: "innermost_csr_lhs_blocked \<mu> R u"
    and source: "innermost_pair_source Sharp \<mu> R (u \<cdot> \<tau>)"
  shows False
proof -
  from blocked obtain w l r \<rho> where uw:
      "csr_dp_root_supt \<mu> u w"
    and lr: "(l,r) \<in> R" and w: "w = l \<cdot> \<rho>"
    unfolding innermost_csr_lhs_blocked_def by blast
  have fun_u: "is_Fun u"
    using uw unfolding csr_dp_root_supt_def mu_supt_def
    by (cases u rule: csr_dp_unsharp_root.cases) auto
  from source obtain l0 r0 \<sigma> where lr0: "(l0,r0) \<in> R"
    and fun_l0: "is_Fun l0"
    and source_eq: "u \<cdot> \<tau> = sharp_term Sharp (l0 \<cdot> \<sigma>)"
    and normal: "\<And>x. mu_supt \<mu> (l0 \<cdot> \<sigma>) x \<Longrightarrow>
      x \<in> NF (csstep \<mu> R)"
    unfolding innermost_pair_source_def by blast
  have fun_inst: "is_Fun (l0 \<cdot> \<sigma>)"
    using fun_l0 by (cases l0) auto
  from csr_dp_root_supt_subst[OF fun_u uw, of \<tau>]
  have active0:
    "csr_dp_root_supt \<mu> (sharp_term Sharp (l0 \<cdot> \<sigma>)) (w \<cdot> \<tau>)"
    unfolding source_eq .
  from active0 have active: "mu_supt \<mu> (l0 \<cdot> \<sigma>) (w \<cdot> \<tau>)"
    unfolding csr_dp_root_supt_sharp[OF fun_inst] .
  have nf: "w \<cdot> \<tau> \<in> NF (csstep \<mu> R)"
    by (rule normal[OF active])
  let ?\<delta> = "\<rho> \<circ>\<^sub>s \<tau>"
  have root: "(l \<cdot> ?\<delta>, r \<cdot> ?\<delta>) \<in> csrstep \<mu> R"
    unfolding csrstep_iff_rstep_root
  proof (intro exI[of _ "(l,r)"] exI[of _ ?\<delta>])
    show "(l \<cdot> ?\<delta>, r \<cdot> ?\<delta>) \<in>
      rstep_r_p_s R (l,r) [] ?\<delta>"
      unfolding rstep_r_p_s_def' using lr by simp
  qed
  have rewrite: "(l \<cdot> ?\<delta>, r \<cdot> ?\<delta>) \<in> csstep \<mu> R"
    using root unfolding csstep_root_nonroot by blast
  have "(w \<cdot> \<tau>, r \<cdot> ?\<delta>) \<in> csstep \<mu> R"
    using rewrite unfolding w by simp
  with nf show False
    unfolding NF_def by blast
qed

definition csr_dp_root_supt_list ::
  "(('f, 'l) lab) muL \<Rightarrow> ((('f, 'l) lab), 'v) term \<Rightarrow>
    ((('f, 'l) lab), 'v) term list"
where
  "csr_dp_root_supt_list \<mu> s =
    mu_supt_list \<mu> (csr_dp_unsharp_root s)"

lemma set_csr_dp_root_supt_list [simp]:
  "set (csr_dp_root_supt_list \<mu> s) =
    {t. csr_dp_root_supt (mu_of \<mu>) s t}"
  unfolding csr_dp_root_supt_list_def csr_dp_root_supt_def by simp

definition innermost_csr_lhs_blocked_check ::
  "(('f::{showl,compare_order}, 'l::{showl,compare_order}) lab) muL \<Rightarrow>
    (((('f, 'l) lab), 'v::compare_order) rule) list \<Rightarrow>
    ((('f, 'l) lab), 'v) term \<Rightarrow> bool"
where
  "innermost_csr_lhs_blocked_check \<mu> R u =
    list_ex (\<lambda>w. list_ex (\<lambda>(l,r). matches w l) R)
      (csr_dp_root_supt_list \<mu> u)"

lemma innermost_csr_lhs_blocked_check_iff [simp]:
  "innermost_csr_lhs_blocked_check \<mu> R u \<longleftrightarrow>
    innermost_csr_lhs_blocked (mu_of \<mu>) (set R) u"
  unfolding innermost_csr_lhs_blocked_check_def
    innermost_csr_lhs_blocked_def list_ex_iff matches_iff
  by auto

fun innermost_csr_dep_graph_edge_check ::
  "(('f::{showl,compare_order}, 'l::{showl,compare_order}) lab) muL \<Rightarrow>
   (((('f, 'l) lab), 'v::compare_order) rules) \<Rightarrow>
   (((((('f, 'l) lab), 'v) rule) \<times> unit) \<times>
    ((((('f, 'l) lab), 'v) rule) \<times> unit)) \<Rightarrow> bool"
where
  "innermost_csr_dep_graph_edge_check \<mu> R
      (((s,t),_),((u,v),_)) =
    (csr_dep_graph_edge_check (csr_dp_root_mu (mu_of \<mu>)) R
      (((s,t),()),((u,v),())) \<and>
     \<not> innermost_csr_lhs_blocked_check \<mu> R u)"

lemma innermost_csr_dep_graph_edge_check_stronger:
  assumes "innermost_csr_dep_graph_edge_check \<mu> R (x,y)"
  shows "csr_dep_graph_edge_check (csr_dp_root_mu (mu_of \<mu>)) R (x,y)"
  using assms by (cases x; cases y; auto split: prod.splits)

lemma innermost_csr_dep_graph_target_not_blocked:
  assumes edge: "innermost_csr_dep_graph_edge_check \<mu> R
      (((s,t),()),((u,v),()))"
  shows "\<not> innermost_csr_lhs_blocked (mu_of \<mu>) (set R) u"
  using edge by simp

lemma innermost_rrstep_target_lhs_not_blocked:
  assumes step: "(u \<cdot> \<tau>,v \<cdot> \<tau>) \<in>
      innermost_rrstep Sharp (mu_of \<mu>) (set R) P"
    and pair: "(u,v) \<in> P"
  shows "\<not> innermost_csr_lhs_blocked (mu_of \<mu>) (set R) u"
proof
  assume blocked: "innermost_csr_lhs_blocked (mu_of \<mu>) (set R) u"
  from step have source:
    "innermost_pair_source Sharp (mu_of \<mu>) (set R) (u \<cdot> \<tau>)"
    unfolding innermost_rrstep_def by blast
  from innermost_csr_lhs_blocked_no_pair_source[OF blocked source]
  show False .
qed

lemma sharp_innermost_csnrstep_imp_innermost_csdp_step:
  assumes step: "(s,t) \<in> innermost_csnrstep \<mu> R"
  shows "(\<sharp> s,\<sharp> t) \<in> innermost_csdp_step \<mu> R"
proof -
  from step obtain p lr \<sigma> where p_ne: "p \<noteq> []"
    and rewrite: "(s,t) \<in> rstep_r_p_s R lr p \<sigma>"
    and cond: "csstep_cond \<mu> p s"
    and inner: "\<And>u. mu_supt \<mu> (fst lr \<cdot> \<sigma>) u \<Longrightarrow>
      u \<in> NF (csstep \<mu> R)"
    unfolding innermost_csnrstep_def innermost_csstep_p_def by blast
  have rewrite': "(\<sharp> s,\<sharp> t) \<in> rstep_r_p_s R lr p \<sigma>"
  proof (cases s)
    case (Var x)
    with rewrite p_ne have False
      unfolding rstep_r_p_s_def' by auto
    then show ?thesis ..
  next
    case (Fun f ts)
    from p_ne obtain i q where p: "p = i # q"
      by (cases p, auto)
    from rewrite Fun show ?thesis
      unfolding rstep_r_p_s_def' p by auto
  qed
  have cond': "csdp_step_cond shp \<mu> p (\<sharp> s)"
  proof (cases s)
    case (Var x)
    with rewrite p_ne have False
      unfolding rstep_r_p_s_def' by auto
    then show ?thesis ..
  next
    case (Fun f ts)
    from p_ne obtain i q where p: "p = i # q"
      by (cases p, auto)
    show ?thesis
      unfolding csdp_step_cond_def
    proof (intro allI impI)
      fix p1 j p2
      assume A: "p = p1 @ j # p2 \<and> p \<in> poss (\<sharp> s)"
      show "\<exists>g us. \<sharp> s |_ p1 = Fun g us \<and>
        (case p1 of [] \<Rightarrow> \<exists>h. g = shp h \<and> j \<in> \<mu> (h,length us)
          | _ \<Rightarrow> j \<in> \<mu> (g,length us))"
      proof (cases p1)
        case Nil
        with A Fun p cond[unfolded csstep_cond_def, rule_format,
          of "[]" j p2]
        show ?thesis by auto
      next
        case (Cons k qs)
        with A Fun have A': "p = p1 @ j # p2 \<and> p \<in> poss s"
          by auto
        from cond[unfolded csstep_cond_def, rule_format, OF A']
        obtain g us where sub: "s |_ p1 = Fun g us"
          and j: "j \<in> \<mu> (g,length us)"
          by blast
        with Cons Fun show ?thesis by auto
      qed
    qed
  qed
  show ?thesis
    unfolding innermost_csdp_step_def
    using rewrite' cond' inner by blast
qed

lemma innermost_csnrsteps_imp_sharp_innermost_csdp_steps:
  assumes "(s,t) \<in> (innermost_csnrstep \<mu> R)\<^sup>*"
  shows "(\<sharp> s,\<sharp> t) \<in> (innermost_csdp_step \<mu> R)\<^sup>*"
  using assms
proof (induct rule: rtrancl_induct)
  case base
  show ?case by simp
next
  case (step y z)
  from sharp_innermost_csnrstep_imp_innermost_csdp_step[OF step.hyps(2)]
  have "(\<sharp> y,\<sharp> z) \<in> innermost_csdp_step \<mu> R" .
  with step.hyps(3) show ?case by auto
qed

lemma Tinf_innermost_imp_first_root_step:
  assumes Tinf: "t \<in> Tinf (innermost_csstep \<mu> R)"
  shows "SN_on (innermost_csnrstep \<mu> R) {t} \<and>
    (\<exists>s u. (t,s) \<in> (innermost_csnrstep \<mu> R)\<^sup>* \<and>
      (s,u) \<in> innermost_csrstep \<mu> R \<and>
      \<not> SN_on (innermost_csstep \<mu> R) {u})"
proof -
  let ?R = "innermost_csstep \<mu> R"
  let ?nR = "innermost_csnrstep \<mu> R"
  let ?rR = "innermost_csrstep \<mu> R"
  from Tinf[unfolded Tinf_def]
  have notSN: "\<not> SN_on ?R {t}"
    and min: "\<And>s. s \<lhd> t \<Longrightarrow> SN_on ?R {s}"
    by auto
  from notSN obtain ts where start: "ts 0 = t"
    and steps: "\<And>i. (ts i,ts (Suc i)) \<in> ?R"
    unfolding SN_on_def by auto
  show ?thesis
  proof (cases "SN_on ?nR {t}")
    case True
    let ?P = "\<lambda>i. (ts i,ts (Suc i)) \<in> ?rR"
    have root_step: "\<exists>i. ?P i"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have nsteps: "\<And>i. (ts i,ts (Suc i)) \<in> ?nR"
        using steps unfolding innermost_csstep_root_nonroot by auto
      with True start show False
        unfolding SN_on_def by blast
    qed
    then obtain k where step_k: "?P k" by auto
    define i where "i = (LEAST i. ?P i)"
    from LeastI[of ?P, OF step_k] have step: "?P i"
      unfolding i_def .
    have nsteps: "\<And>j. j < i \<Longrightarrow> (ts j,ts (Suc j)) \<in> ?nR"
    proof -
      fix j
      assume "j < i"
      from not_less_Least[OF this[unfolded i_def]] have "\<not> ?P j" .
      with steps[of j] show "(ts j,ts (Suc j)) \<in> ?nR"
        unfolding innermost_csstep_root_nonroot by auto
    qed
    have pref: "(ts 0,ts i) \<in> ?nR\<^sup>*"
      unfolding rtrancl_fun_conv
      by (intro exI[of _ ts] exI[of _ i], insert nsteps, auto)
    let ?ss = "shift ts (Suc i)"
    have tail_notSN: "\<not> SN_on ?R {ts (Suc i)}"
    proof -
      have "?ss 0 \<in> {ts (Suc i)}" by simp
      moreover have "\<And>j. (?ss j,?ss (Suc j)) \<in> ?R"
        using steps[of "j + Suc i" for j] by auto
      ultimately show ?thesis unfolding SN_on_def by blast
    qed
    show ?thesis
      using True pref step tail_notSN start by blast
  next
    case False
    from False obtain ts where start': "ts 0 = t"
      and nsteps: "\<And>i. (ts i,ts (Suc i)) \<in> ?nR"
      unfolding SN_on_def by auto
    have n0: "(ts 0,ts (Suc 0)) \<in> csnrstep \<mu> R"
      using innermost_csnrstep_subset_csnrstep nsteps[of 0] by blast
    obtain f ss where init: "ts 0 = Fun f ss"
      using n0 csnrstep_Var_empty[of _ "ts (Suc 0)" \<mu> R]
      by (cases "ts 0", auto)
    let ?n = "length ss"
    obtain n where n: "n = ?n" by auto
    have roots: "\<exists>ssi. ts i = Fun f ssi \<and> length ssi = n" for i
    proof (induct i)
      case 0
      then show ?case unfolding init n by auto
    next
      case (Suc i)
      from Suc obtain ssi where tsi: "ts i = Fun f ssi"
        and len: "length ssi = n" by auto
      from csnrstep_preserves_root[
        OF innermost_csnrstep_subset_csnrstep[THEN subsetD,
          OF nsteps[of i]]]
      show ?case unfolding tsi root.simps len
        by (cases "ts (Suc i)", auto)
    qed
    from choice[OF allI[OF roots]] obtain sss where
      ts: "\<And>i. ts i = Fun f (sss i)"
      and len: "\<And>i. length (sss i) = n"
      by force
    let ?strict = "\<lambda>i. \<exists>j<n.
      (sss i ! j,sss (Suc i) ! j) \<in> ?R"
    have strict_all: "\<And>i. ?strict i"
    proof -
      fix i
      have step_i: "(Fun f (sss i),Fun f (sss (Suc i))) \<in> ?nR"
        using nsteps[of i] by (simp add: ts)
      from step_i show "?strict i"
      proof (elim innermost_csnrstep_FunE)
        fix j us
        assume j: "j < length (sss i)"
          and sub: "(sss i ! j,us ! j) \<in> ?R"
          and tgt: "Fun f (sss (Suc i)) = Fun f us"
        from tgt have us: "sss (Suc i) = us" by simp
        from j sub us len[of i] show ?thesis by auto
      qed
    qed
    let ?idx = "\<lambda>i. SOME j. j < n \<and>
      (sss i ! j,sss (Suc i) ! j) \<in> ?R"
    define idx where "idx = ?idx"
    have idx_strict: "idx i < n \<and>
      (sss i ! idx i,sss (Suc i) ! idx i) \<in> ?R" for i
    proof -
      from strict_all[of i] have ex: "\<exists>j. j < n \<and>
        (sss i ! j,sss (Suc i) ! j) \<in> ?R" .
      show ?thesis unfolding idx_def by (rule someI_ex[OF ex])
    qed
    have idx_n: "idx i \<le> n" for i
      using idx_strict[of i] by auto
    have fin: "finite (idx ` X)" for X
    proof (rule finite_subset)
      show "idx ` X \<subseteq> {i. i \<le> n}" using idx_n by auto
      have id: "{i. i \<le> n} = set [0..<Suc n]" by auto
      show "finite {i. i \<le> n}" unfolding id by (rule finite_set)
    qed
    have inf_strict: "infinite {i. ?strict i}"
      using strict_all by simp
    from pigeonhole_infinite[OF inf_strict fin]
    obtain j where infj_set:
      "infinite {i \<in> {i. ?strict i}. idx i = j}" by auto
    then have infj: "INFM i. idx i = j"
      unfolding INFM_iff_infinite
      using infinite_super[of
        "{i \<in> {i. ?strict i}. idx i = j}" "{i. idx i = j}"]
      by auto
    from infj[unfolded INFM_nat_le, rule_format, of 0]
    obtain k where kj: "idx k = j" by auto
    from idx_strict[of k] kj have jn: "j < n" by auto
    with n have "ss ! j \<in> set ss" by auto
    with init have "ss ! j \<lhd> ts 0" by auto
    from min[unfolded start'[symmetric], OF this]
    have SN: "SN_on ?R {ss ! j}" by auto
    let ?ss = "\<lambda>i. sss i ! j"
    from SN have SN: "SN_on ?R {?ss 0}"
      using ts[of 0] init by simp
    have j_steps: "(?ss i,?ss (Suc i)) \<in> ?R\<^sup>=" for i
    proof -
      have step_i: "(Fun f (sss i),Fun f (sss (Suc i))) \<in> ?nR"
        using nsteps[of i] by (simp add: ts)
      from step_i show ?thesis
      proof (elim innermost_csnrstep_FunE)
        fix k us
        assume k: "k < length (sss i)"
          and step: "(sss i ! k,us ! k) \<in> ?R"
          and tgt: "Fun f (sss (Suc i)) = Fun f us"
          and same: "\<And>l. l < length (sss i) \<Longrightarrow> l \<noteq> k \<Longrightarrow>
            us ! l = sss i ! l"
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
    have jsteps: "(?ss i,?ss (Suc i)) \<in> Id \<union> ?R" for i
      using j_steps[of i] by auto
    have compat: "Id O ?R \<subseteq> ?R" by auto
    from non_strict_ending[of ?ss Id ?R, OF allI[OF jsteps] compat SN]
    obtain k where k: "\<And>l. l \<ge> k \<Longrightarrow>
      (?ss l,?ss (Suc l)) \<notin> ?R" by auto
    from infj[unfolded INFM_nat_le, rule_format, of k]
    obtain l where lk: "l \<ge> k" and lj: "idx l = j" by auto
    from idx_strict[of l] lj have "(?ss l,?ss (Suc l)) \<in> ?R"
      by auto
    with k[OF lk] show ?thesis by auto
  qed
qed

lemma mu_Tinf_innermost_imp_first_root_step:
  assumes Tinf: "t \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
  shows "SN_on (innermost_csnrstep \<mu> R) {t} \<and>
    (\<exists>s u. (t,s) \<in> (innermost_csnrstep \<mu> R)\<^sup>* \<and>
      (s,u) \<in> innermost_csrstep \<mu> R \<and>
      \<not> SN_on (innermost_csstep \<mu> R) {u})"
proof -
  let ?R = "innermost_csstep \<mu> R"
  let ?nR = "innermost_csnrstep \<mu> R"
  let ?rR = "innermost_csrstep \<mu> R"
  from Tinf[unfolded mu_Tinf_def]
  have notSN: "\<not> SN_on ?R {t}"
    and min: "\<And>s. mu_supt \<mu> t s \<Longrightarrow> SN_on ?R {s}"
    by auto
  from notSN obtain ts where start: "ts 0 = t"
    and steps: "\<And>i. (ts i,ts (Suc i)) \<in> ?R"
    unfolding SN_on_def by auto
  show ?thesis
  proof (cases "SN_on ?nR {t}")
    case True
    let ?P = "\<lambda>i. (ts i,ts (Suc i)) \<in> ?rR"
    have root_step: "\<exists>i. ?P i"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have nsteps: "\<And>i. (ts i,ts (Suc i)) \<in> ?nR"
        using steps unfolding innermost_csstep_root_nonroot by auto
      with True start show False unfolding SN_on_def by blast
    qed
    then obtain k where step_k: "?P k" by auto
    define i where "i = (LEAST i. ?P i)"
    from LeastI[of ?P, OF step_k] have step: "?P i"
      unfolding i_def .
    have nsteps: "\<And>j. j < i \<Longrightarrow> (ts j,ts (Suc j)) \<in> ?nR"
    proof -
      fix j
      assume "j < i"
      from not_less_Least[OF this[unfolded i_def]] have "\<not> ?P j" .
      with steps[of j] show "(ts j,ts (Suc j)) \<in> ?nR"
        unfolding innermost_csstep_root_nonroot by auto
    qed
    have pref: "(ts 0,ts i) \<in> ?nR\<^sup>*"
      unfolding rtrancl_fun_conv
      by (intro exI[of _ ts] exI[of _ i], insert nsteps, auto)
    let ?ss = "shift ts (Suc i)"
    have tail_notSN: "\<not> SN_on ?R {ts (Suc i)}"
    proof -
      have "?ss 0 \<in> {ts (Suc i)}" by simp
      moreover have "\<And>j. (?ss j,?ss (Suc j)) \<in> ?R"
        using steps[of "j + Suc i" for j] by auto
      ultimately show ?thesis unfolding SN_on_def by blast
    qed
    show ?thesis using True pref step tail_notSN start by blast
  next
    case False
    from False obtain ts where start': "ts 0 = t"
      and nsteps: "\<And>i. (ts i,ts (Suc i)) \<in> ?nR"
      unfolding SN_on_def by auto
    have n0: "(ts 0,ts (Suc 0)) \<in> csnrstep \<mu> R"
      using innermost_csnrstep_subset_csnrstep nsteps[of 0] by blast
    obtain f ss where init: "ts 0 = Fun f ss"
      using n0 csnrstep_Var_empty[of _ "ts (Suc 0)" \<mu> R]
      by (cases "ts 0", auto)
    obtain n where n: "n = length ss" by auto
    have roots: "\<exists>ssi. ts i = Fun f ssi \<and> length ssi = n" for i
    proof (induct i)
      case 0
      then show ?case unfolding init n by auto
    next
      case (Suc i)
      from Suc obtain ssi where tsi: "ts i = Fun f ssi"
        and len: "length ssi = n" by auto
      from csnrstep_preserves_root[
        OF innermost_csnrstep_subset_csnrstep[THEN subsetD,
          OF nsteps[of i]]]
      show ?case unfolding tsi root.simps len
        by (cases "ts (Suc i)", auto)
    qed
    from choice[OF allI[OF roots]] obtain sss where
      ts: "\<And>i. ts i = Fun f (sss i)"
      and len: "\<And>i. length (sss i) = n"
      by force
    let ?strict = "\<lambda>i. \<exists>j<n. j \<in> \<mu> (f,n) \<and>
      (sss i ! j,sss (Suc i) ! j) \<in> ?R"
    have strict_all: "\<And>i. ?strict i"
    proof -
      fix i
      have step_i: "(Fun f (sss i),Fun f (sss (Suc i))) \<in> ?nR"
        using nsteps[of i] by (simp add: ts)
      from step_i show "?strict i"
      proof (elim innermost_csnrstep_FunE)
        fix j us
        assume j: "j < length (sss i)"
          and jmu: "j \<in> \<mu> (f,length (sss i))"
          and sub: "(sss i ! j,us ! j) \<in> ?R"
          and tgt: "Fun f (sss (Suc i)) = Fun f us"
        from tgt have us: "sss (Suc i) = us" by simp
        from j jmu sub us len[of i] show ?thesis by auto
      qed
    qed
    let ?idx = "\<lambda>i. SOME j. j < n \<and> j \<in> \<mu> (f,n) \<and>
      (sss i ! j,sss (Suc i) ! j) \<in> ?R"
    define idx where "idx = ?idx"
    have idx_strict: "idx i < n \<and> idx i \<in> \<mu> (f,n) \<and>
      (sss i ! idx i,sss (Suc i) ! idx i) \<in> ?R" for i
    proof -
      from strict_all[of i] have ex: "\<exists>j. j < n \<and>
        j \<in> \<mu> (f,n) \<and>
        (sss i ! j,sss (Suc i) ! j) \<in> ?R" .
      show ?thesis unfolding idx_def by (rule someI_ex[OF ex])
    qed
    have idx_n: "idx i \<le> n" for i
      using idx_strict[of i] by auto
    have fin: "finite (idx ` X)" for X
    proof (rule finite_subset)
      show "idx ` X \<subseteq> {i. i \<le> n}" using idx_n by auto
      have id: "{i. i \<le> n} = set [0..<Suc n]" by auto
      show "finite {i. i \<le> n}" unfolding id by (rule finite_set)
    qed
    have inf_strict: "infinite {i. ?strict i}"
      using strict_all by simp
    from pigeonhole_infinite[OF inf_strict fin]
    obtain j where infj_set:
      "infinite {i \<in> {i. ?strict i}. idx i = j}" by auto
    then have infj: "INFM i. idx i = j"
      unfolding INFM_iff_infinite
      using infinite_super[of
        "{i \<in> {i. ?strict i}. idx i = j}" "{i. idx i = j}"]
      by auto
    from infj[unfolded INFM_nat_le, rule_format, of 0]
    obtain k where kj: "idx k = j" by auto
    from idx_strict[of k] kj
    have jn: "j < n" and jmu: "j \<in> \<mu> (f,n)" by auto
    with n have "j # [] \<in> mu_poss \<mu> (Fun f ss)"
      by (cases "ss ! j", auto)
    moreover have "Fun f ss |_ (j # []) = ss ! j"
      using jn n by simp
    ultimately have "mu_supt \<mu> (Fun f ss) (ss ! j)"
      unfolding mu_supt_def by blast
    with min[unfolded start'[symmetric] init]
    have SN: "SN_on ?R {ss ! j}" by auto
    let ?ss = "\<lambda>i. sss i ! j"
    from SN have SN: "SN_on ?R {?ss 0}"
      using ts[of 0] init by simp
    have j_steps: "(?ss i,?ss (Suc i)) \<in> ?R\<^sup>=" for i
    proof -
      have step_i: "(Fun f (sss i),Fun f (sss (Suc i))) \<in> ?nR"
        using nsteps[of i] by (simp add: ts)
      from step_i show ?thesis
      proof (elim innermost_csnrstep_FunE)
        fix k us
        assume k: "k < length (sss i)"
          and step: "(sss i ! k,us ! k) \<in> ?R"
          and tgt: "Fun f (sss (Suc i)) = Fun f us"
          and same: "\<And>l. l < length (sss i) \<Longrightarrow> l \<noteq> k \<Longrightarrow>
            us ! l = sss i ! l"
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
    have jsteps: "(?ss i,?ss (Suc i)) \<in> Id \<union> ?R" for i
      using j_steps[of i] by auto
    have compat: "Id O ?R \<subseteq> ?R" by auto
    from non_strict_ending[of ?ss Id ?R, OF allI[OF jsteps] compat SN]
    obtain k where k: "\<And>l. l \<ge> k \<Longrightarrow>
      (?ss l,?ss (Suc l)) \<notin> ?R" by auto
    from infj[unfolded INFM_nat_le, rule_format, of k]
    obtain l where lk: "l \<ge> k" and lj: "idx l = j" by auto
    from idx_strict[of l] lj have "(?ss l,?ss (Suc l)) \<in> ?R"
      by auto
    with k[OF lk] show ?thesis by auto
  qed
qed

lemma innermost_csnrstep_mu_Tinf_preserve:
  assumes wf: "wf_trs R"
    and step: "(s,t) \<in> innermost_csnrstep \<mu> R"
    and sT: "s \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
    and notSN_t: "\<not> SN_on (innermost_csstep \<mu> R) {t}"
  shows "t \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
proof -
  from sT have min: "\<And>u. mu_supt \<mu> s u \<Longrightarrow>
    SN_on (innermost_csstep \<mu> R) {u}"
    unfolding mu_Tinf_def by auto
  show ?thesis
    unfolding mu_Tinf_def
  proof (intro CollectI conjI allI impI)
    show "\<not> SN_on (innermost_csstep \<mu> R) {t}"
      by (rule notSN_t)
  next
    fix u
    assume tu: "mu_supt \<mu> t u"
    from step show "SN_on (innermost_csstep \<mu> R) {u}"
    proof (cases s)
      case (Var x)
      from innermost_csnrstep_subset_csnrstep[THEN subsetD, OF step]
        Var csnrstep_Var_empty[of x t \<mu> R]
      show ?thesis by simp
    next
      case (Fun f ss)
      from step[unfolded Fun] show ?thesis
      proof (elim innermost_csnrstep_FunE)
        fix i ts
        assume i: "i < length ss"
          and imu: "i \<in> \<mu> (f,length ss)"
          and t: "t = Fun f ts"
          and len: "length ts = length ss"
          and substep: "(ss ! i,ts ! i) \<in> innermost_csstep \<mu> R"
          and same: "\<And>j. j < length ss \<Longrightarrow> j \<noteq> i \<Longrightarrow>
            ts ! j = ss ! j"
        from tu[unfolded t mu_supt_def]
        obtain j q where jq: "j # q \<in> mu_poss \<mu> (Fun f ts)"
          and u: "Fun f ts |_ (j # q) = u"
          by auto
        from jq have j: "j < length ts"
          and jmu: "j \<in> \<mu> (f,length ts)"
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
            unfolding Fun using j jmu len
            by (cases "ss ! i", auto simp: True)
          moreover have "s |_ (j # []) = ss ! i"
            unfolding Fun using i True by simp
          ultimately have "mu_supt \<mu> s (ss ! i)"
            unfolding mu_supt_def by blast
          then have SN_i: "SN_on (innermost_csstep \<mu> R) {ss ! i}"
            by (rule min)
          have SN_ti: "SN_on (innermost_csstep \<mu> R) {ts ! i}"
            by (rule step_SN_on_target[OF SN_i substep])
          have q_i: "q \<in> mu_poss \<mu> (ts ! i)"
            using q True by simp
          have u_eq: "u = ts ! i |_ q"
            using u t True j by simp
          show ?thesis
            using SN_on_innermost_csstep_mu_pos[OF wf q_i SN_ti]
              u_eq by simp
        qed
      qed
    qed
  qed
qed

lemma innermost_csnrsteps_mu_Tinf_preserve:
  assumes wf: "wf_trs R"
    and steps: "(s,t) \<in> (innermost_csnrstep \<mu> R)\<^sup>*"
    and sT: "s \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
    and notSN_t: "\<not> SN_on (innermost_csstep \<mu> R) {t}"
  shows "t \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
  using steps sT notSN_t
proof (induct rule: rtrancl_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  have yz: "(y,z) \<in> innermost_csstep \<mu> R"
    using step.hyps(2) unfolding innermost_csstep_root_nonroot by auto
  have notSN_y: "\<not> SN_on (innermost_csstep \<mu> R) {y}"
    by (rule step_notSN_on_source[OF yz step.prems(2)])
  from step.hyps(3)[OF step.prems(1) notSN_y]
  have yT: "y \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)" .
  show ?case
    by (rule innermost_csnrstep_mu_Tinf_preserve[
      OF wf step.hyps(2) yT step.prems(2)])
qed

lemma innermost_notSN_imp_active_mu_Tinf:
  fixes R :: "('f,'v) trs"
  assumes wf: "wf_trs R"
    and notSN: "\<not> SN_on (innermost_csstep \<mu> R) {t}"
  shows "\<exists>p f ts. p \<in> mu_fun_poss \<mu> t \<and>
    t |_ p = Fun f ts \<and>
    t |_ p \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
  using notSN
proof (induct t)
  case (Var x)
  have subset: "innermost_csstep \<mu> R \<subseteq> csstep \<mu> R"
    by (rule innermost_csstep_subset_csstep)
  from SN_on_csstep_Var[OF wf, of \<mu> x]
  have full: "SN_on (csstep \<mu> R) {Var x}" .
  have "SN_on (innermost_csstep \<mu> R) {Var x}"
    by (rule SN_on_subset1[OF full subset])
  with Var.prems show ?case by contradiction
next
  case (Fun f ss)
  show ?case
  proof (cases "Fun f ss \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)")
    case True
    show ?thesis
      by (intro exI[of _ "[]"] exI[of _ f] exI[of _ ss],
          insert True, auto)
  next
    case False
    from False Fun.prems obtain u where su: "mu_supt \<mu> (Fun f ss) u"
      and u_notSN: "\<not> SN_on (innermost_csstep \<mu> R) {u}"
      unfolding mu_Tinf_def by blast
    from su obtain i q where iq: "i # q \<in> mu_poss \<mu> (Fun f ss)"
      and u: "Fun f ss |_ (i # q) = u"
      unfolding mu_supt_def by blast
    from iq have i: "i < length ss"
      and imu: "i \<in> \<mu> (f,length ss)"
      and q: "q \<in> mu_poss \<mu> (ss ! i)"
      by auto
    have arg_notSN:
      "\<not> SN_on (innermost_csstep \<mu> R) {ss ! i}"
    proof
      assume arg_SN: "SN_on (innermost_csstep \<mu> R) {ss ! i}"
      from SN_on_innermost_csstep_mu_pos[OF wf q arg_SN]
      have "SN_on (innermost_csstep \<mu> R) {ss ! i |_ q}" .
      with u_notSN u i show False by simp
    qed
    from Fun.hyps[OF nth_mem[OF i] arg_notSN]
    obtain p g ts where p: "p \<in> mu_fun_poss \<mu> (ss ! i)"
      and sub: "ss ! i |_ p = Fun g ts"
      and T: "ss ! i |_ p \<in>
        mu_Tinf \<mu> (innermost_csstep \<mu> R)"
      by blast
    have "i # p \<in> mu_fun_poss \<mu> (Fun f ss)"
      using i imu p by auto
    moreover have "Fun f ss |_ (i # p) = Fun g ts"
      using i sub by simp
    moreover have "Fun f ss |_ (i # p) \<in>
      mu_Tinf \<mu> (innermost_csstep \<mu> R)"
      using i T sub by simp
    ultimately show ?thesis
      by (intro exI[of _ "i # p"] exI[of _ g] exI[of _ ts], auto)
  qed
qed

lemma innermost_notSN_imp_mu_Tinf_defined_subterm:
  fixes R :: "('f,'v) trs"
  assumes wf: "wf_trs R"
    and notSN: "\<not> SN_on (innermost_csstep \<mu> R) {t}"
  shows "\<exists>p f ts. p \<in> mu_fun_poss \<mu> t \<and>
    t |_ p = Fun f ts \<and> defined R (f,length ts) \<and>
    t |_ p \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
proof -
  from innermost_notSN_imp_active_mu_Tinf[OF wf notSN]
  obtain p f ts where p: "p \<in> mu_fun_poss \<mu> t"
    and sub: "t |_ p = Fun f ts"
    and T: "t |_ p \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
    by blast
  have first:
    "SN_on (innermost_csnrstep \<mu> R) {t |_ p} \<and>
      (\<exists>s u. (t |_ p,s) \<in> (innermost_csnrstep \<mu> R)\<^sup>* \<and>
        (s,u) \<in> innermost_csrstep \<mu> R \<and>
        \<not> SN_on (innermost_csstep \<mu> R) {u})"
    by (rule mu_Tinf_innermost_imp_first_root_step[
      where t = "t |_ p" and \<mu> = \<mu> and R = R], rule T)
  from first
  obtain s u where pref:
      "(t |_ p,s) \<in> (innermost_csnrstep \<mu> R)\<^sup>*"
    and root: "(s,u) \<in> innermost_csrstep \<mu> R"
    by blast
  have pref_full: "(t |_ p,s) \<in> (csnrstep \<mu> R)\<^sup>*"
    by (rule rtrancl_mono[OF innermost_csnrstep_subset_csnrstep,
      THEN subsetD, OF pref])
  from csnrsteps_preserve_root[OF pref_full]
  have root_s: "root s = Some (f,length ts)"
    unfolding sub by simp
  from innermost_csrstep_subset_csrstep[THEN subsetD, OF root]
  obtain l r \<sigma> where lr: "(l,r) \<in> R" and s: "s = l \<cdot> \<sigma>"
    by (elim csrstepE)
  from wf lr obtain g ls where l: "l = Fun g ls"
    unfolding wf_trs_def by (cases l, auto)
  have root_l: "root l = Some (f,length ts)"
    using root_s unfolding s l by simp
  have "defined R (f,length ts)"
    unfolding defined_def
    by (intro exI[of _ l] conjI exI[of _ r], rule lr, rule root_l)
  with p sub T show ?thesis by blast
qed

lemma innermost_mu_Tinf_SN_on_active_subst_mu_subterm:
  fixes R :: "('f,'v) trs"
  assumes lhs: "is_Fun l"
    and T: "l \<cdot> \<sigma> \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
    and x: "x \<in> mu_vars_term \<mu> l"
    and q: "q \<in> mu_fun_poss \<mu> (\<sigma> x)"
  shows "SN_on (innermost_csstep \<mu> R) {\<sigma> x |_ q}"
proof -
  from x obtain p where p: "p \<in> mu_poss \<mu> l"
    and lp: "l |_ p = Var x"
    unfolding mu_vars_term_def by auto
  have pq: "p @ q \<in> mu_fun_poss \<mu> (l \<cdot> \<sigma>)"
    by (rule mu_fun_poss_subst_var_lift[
      where t = l and x = x and \<sigma> = \<sigma>, OF p lp q])
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
    using mu_poss_imp_poss[OF p] lp by (simp add: subt_at_append)
  have "mu_supt \<mu> (l \<cdot> \<sigma>) (\<sigma> x |_ q)"
    unfolding mu_supt_def
    by (intro exI[of _ i] exI[of _ p'],
      insert pq_pos pq_cons sub, auto)
  with T show ?thesis unfolding mu_Tinf_def by blast
qed

lemma innermost_csrstep_mu_Tinf_rhs_imp_rrstep_mu_CSDP_on:
  fixes R :: "('f,'v) trs"
  assumes wf: "wf_trs R"
    and step: "(s,t) \<in> innermost_csrstep \<mu> R"
    and sT: "s \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
    and notSN: "\<not> SN_on (innermost_csstep \<mu> R) {t}"
    and vc: "rhs_mu_vars_condition \<mu> R"
    and D: "{f. defined R f} \<subseteq> D"
  shows "\<exists>u. u \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R) \<and>
    (\<sharp> s,\<sharp> u) \<in>
      innermost_rrstep shp \<mu> R (mu_CSDP_on shp \<mu> D R)"
proof -
  from step obtain lr \<sigma> where rewrite:
      "(s,t) \<in> rstep_r_p_s R lr [] \<sigma>"
    and inner0: "\<And>u. mu_supt \<mu> (fst lr \<cdot> \<sigma>) u \<Longrightarrow>
      u \<in> NF (csstep \<mu> R)"
    unfolding innermost_csrstep_def innermost_csstep_p_def by blast
  obtain l r where lr_def: "lr = (l,r)"
    by (cases lr)
  from rewrite have lr: "(l,r) \<in> R"
    and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
    unfolding lr_def rstep_r_p_s_def' by auto
  have inner: "\<And>u. mu_supt \<mu> (l \<cdot> \<sigma>) u \<Longrightarrow>
      u \<in> NF (csstep \<mu> R)"
    using inner0 unfolding lr_def by simp
  from wf lr have lhs: "is_Fun l"
    unfolding wf_trs_def by (cases l, auto)
  have inner_source: "innermost_pair_source shp \<mu> R (\<sharp> s)"
    unfolding innermost_pair_source_def s
    using lr lhs inner by blast
  from innermost_notSN_imp_mu_Tinf_defined_subterm[
    OF wf notSN[unfolded t]]
  obtain p f us where p_mu: "p \<in> mu_fun_poss \<mu> (r \<cdot> \<sigma>)"
    and sub_inst: "(r \<cdot> \<sigma>) |_ p = Fun f us"
    and def: "defined R (f,length us)"
    and T_p: "(r \<cdot> \<sigma>) |_ p \<in>
      mu_Tinf \<mu> (innermost_csstep \<mu> R)"
    by blast
  from T_p have notSN_p:
    "\<not> SN_on (innermost_csstep \<mu> R) {(r \<cdot> \<sigma>) |_ p}"
    unfolding mu_Tinf_def by auto
  from mu_fun_poss_subst_cases_aux_mu[OF p_mu]
  show ?thesis
  proof
    assume orig: "p \<in> mu_fun_poss \<mu> r \<and>
      (r \<cdot> \<sigma>) |_ p = (r |_ p) \<cdot> \<sigma>"
    then have p_r: "p \<in> mu_fun_poss \<mu> r"
      and sub_subst: "(r \<cdot> \<sigma>) |_ p = (r |_ p) \<cdot> \<sigma>"
      by auto
    from mu_fun_poss_imp_fun_poss[OF p_r]
    obtain g ts where rp0: "r |_ p = Fun g ts"
      using fun_poss_fun_conv by blast
    with sub_subst sub_inst
    have rp: "r |_ p = Fun f ts" and len: "length us = length ts"
      by auto
    from D def len have fD: "(f,length ts) \<in> D" by auto
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
            \<open>(l \<cdot> \<sigma>) |_ (i # q) = (r |_ p) \<cdot> \<sigma>\<close>,
          auto)
      ultimately have
        "SN_on (innermost_csstep \<mu> R) {(r |_ p) \<cdot> \<sigma>}"
        using sT unfolding s mu_Tinf_def by blast
      with notSN_p sub_subst show False by simp
    qed
    have rr:
      "(\<sharp> (l \<cdot> \<sigma>),\<sharp> ((r |_ p) \<cdot> \<sigma>)) \<in>
        innermost_rrstep shp \<mu> R (mu_CSDP_on shp \<mu> D R)"
      unfolding innermost_rrstep_def
      using rrstep_mu_CSDP_onI[
        where shp = shp, OF lr lhs p_r rp fD ns]
        inner_source unfolding s by blast
    show ?thesis
      using rr T_p sub_subst unfolding s by auto
  next
    assume subst: "\<exists>x q1 q2. q1 \<in> mu_poss \<mu> r \<and>
      r |_ q1 = Var x \<and> x \<in> vars_term r \<and>
      p = q1 @ q2 \<and> q2 \<in> mu_fun_poss \<mu> (\<sigma> x) \<and>
      (r \<cdot> \<sigma>) |_ p = \<sigma> x |_ q2"
    then obtain x q1 q2 where q1: "q1 \<in> mu_poss \<mu> r"
      and r_q1: "r |_ q1 = Var x"
      and q2: "q2 \<in> mu_fun_poss \<mu> (\<sigma> x)"
      and sub_q2: "(r \<cdot> \<sigma>) |_ p = \<sigma> x |_ q2"
      by blast
    have "x \<in> mu_vars_term \<mu> r"
      unfolding mu_vars_term_def using q1 r_q1 by blast
    with vc lr have x_l: "x \<in> mu_vars_term \<mu> l"
      unfolding rhs_mu_vars_condition_def by blast
    have lT: "l \<cdot> \<sigma> \<in>
      mu_Tinf \<mu> (innermost_csstep \<mu> R)"
      using sT unfolding s .
    have "SN_on (innermost_csstep \<mu> R) {\<sigma> x |_ q2}"
      by (rule innermost_mu_Tinf_SN_on_active_subst_mu_subterm[
        OF lhs lT x_l q2])
    with notSN_p sub_q2 show ?thesis by simp
  qed
qed

lemma mu_Tinf_imp_innermost_mu_CSDP_relstep:
  fixes R :: "('f,'v) trs"
  assumes wf: "wf_trs R"
    and Tinf: "t \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
    and vc: "rhs_mu_vars_condition \<mu> R"
    and D: "{f. defined R f} \<subseteq> D"
  shows "\<exists>u. u \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R) \<and>
    (\<sharp> t,\<sharp> u) \<in>
      (innermost_csdp_step \<mu> R)\<^sup>* O
      innermost_rrstep shp \<mu> R (mu_CSDP_on shp \<mu> D R) O
      (innermost_csdp_step \<mu> R)\<^sup>*"
proof -
  from mu_Tinf_innermost_imp_first_root_step[OF Tinf]
  obtain s v where pref:
      "(t,s) \<in> (innermost_csnrstep \<mu> R)\<^sup>*"
    and root: "(s,v) \<in> innermost_csrstep \<mu> R"
    and notSN_v: "\<not> SN_on (innermost_csstep \<mu> R) {v}"
    by blast
  have sv: "(s,v) \<in> innermost_csstep \<mu> R"
    using root unfolding innermost_csstep_root_nonroot by auto
  have notSN_s: "\<not> SN_on (innermost_csstep \<mu> R) {s}"
    by (rule step_notSN_on_source[OF sv notSN_v])
  have sT: "s \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
    by (rule innermost_csnrsteps_mu_Tinf_preserve[
      OF wf pref Tinf notSN_s])
  from innermost_csrstep_mu_Tinf_rhs_imp_rrstep_mu_CSDP_on[
    OF wf root sT notSN_v vc D]
  obtain u where uT: "u \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)"
    and dp: "(\<sharp> s,\<sharp> u) \<in>
      innermost_rrstep shp \<mu> R (mu_CSDP_on shp \<mu> D R)"
    by blast
  have left: "(\<sharp> t,\<sharp> s) \<in>
      (innermost_csdp_step \<mu> R)\<^sup>*"
    by (rule innermost_csnrsteps_imp_sharp_innermost_csdp_steps[OF pref])
  have right: "(\<sharp> u,\<sharp> u) \<in>
      (innermost_csdp_step \<mu> R)\<^sup>*"
    by simp
  have "(\<sharp> t,\<sharp> u) \<in>
      (innermost_csdp_step \<mu> R)\<^sup>* O
      innermost_rrstep shp \<mu> R (mu_CSDP_on shp \<mu> D R) O
      (innermost_csdp_step \<mu> R)\<^sup>*"
    using left dp right by auto
  with uT show ?thesis by blast
qed

lemma finite_full_imp_finite_innermost_csr_dpp:
  assumes "finite_mode_csr_dpp CSR_Full \<mu> P R"
  shows "finite_mode_csr_dpp CSR_Innermost \<mu> P R"
proof -
  from assms have full:
    "SN_rel (rrstep P) (csdp_step shp \<mu> R)"
    unfolding finite_mode_csr_dpp_def by simp
  have inner: "SN_rel (innermost_rrstep shp \<mu> R P)
      (innermost_csdp_step \<mu> R)"
    by (rule SN_rel_mono[OF innermost_rrstep_subset_rrstep
      innermost_csdp_step_subset_csdp_step full])
  show ?thesis
    unfolding finite_mode_csr_dpp_def using inner by simp
qed

lemma finite_innermost_csr_dpp_imp_SN_if_progress:
  assumes progress:
    "\<And>t. t \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R) \<Longrightarrow>
      \<exists>u. u \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R) \<and>
        (\<sharp> t, \<sharp> u) \<in>
          (innermost_csdp_step \<mu> R)\<^sup>* O
          innermost_rrstep shp \<mu> R P O
          (innermost_csdp_step \<mu> R)\<^sup>*"
    and fin: "finite_mode_csr_dpp CSR_Innermost \<mu> P R"
  shows "SN (innermost_csstep \<mu> R)"
proof (rule ccontr)
  assume not_sn: "\<not> SN (innermost_csstep \<mu> R)"
  from not_SN_imp_Tinf[OF not_sn]
  obtain t0 where t0_T: "t0 \<in> Tinf (innermost_csstep \<mu> R)"
    by blast
  from Tinf_imp_mu_Tinf[OF t0_T]
  have t0: "t0 \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)" .
  let ?T = "innermost_csstep \<mu> R"
  let ?S = "innermost_csdp_step \<mu> R"
  let ?rel = "?S\<^sup>* O innermost_rrstep shp \<mu> R P O ?S\<^sup>*"
  have all_ex: "\<forall>t. \<exists>u. t \<in> mu_Tinf \<mu> ?T \<longrightarrow>
      u \<in> mu_Tinf \<mu> ?T \<and> (\<sharp> t, \<sharp> u) \<in> ?rel"
    using progress by blast
  from choice[OF all_ex]
  obtain nxt where nxt: "\<And>t. t \<in> mu_Tinf \<mu> ?T \<Longrightarrow>
      nxt t \<in> mu_Tinf \<mu> ?T \<and> (\<sharp> t, \<sharp> (nxt t)) \<in> ?rel"
    by blast
  define ts where "ts = rec_nat t0 (\<lambda>n t. nxt t)"
  have ts_T: "ts n \<in> mu_Tinf \<mu> ?T" for n
  proof (induct n)
    case 0
    then show ?case unfolding ts_def using t0 by simp
  next
    case (Suc n)
    from nxt[OF Suc.hyps]
    have "nxt (ts n) \<in> mu_Tinf \<mu> ?T" by simp
    then show ?case unfolding ts_def by simp
  qed
  have ts_step: "(\<sharp> (ts n), \<sharp> (ts (Suc n))) \<in> ?rel" for n
    using nxt[OF ts_T[of n]] unfolding ts_def by simp
  define f where "f n = \<sharp> (ts n)" for n
  have chain: "\<And>n. (f n, f (Suc n)) \<in> ?rel"
    unfolding f_def using ts_step by simp
  have "\<not> SN_rel (innermost_rrstep shp \<mu> R P) ?S"
    unfolding SN_rel_on_def SN_defs using chain by blast
  moreover from fin have "SN_rel (innermost_rrstep shp \<mu> R P) ?S"
    unfolding finite_mode_csr_dpp_def by simp
  ultimately show False by contradiction
qed

theorem finite_innermost_mu_CSDP_on_imp_SN:
  fixes R :: "('f,'v) trs"
  assumes wf: "wf_trs R"
    and vc: "rhs_mu_vars_condition \<mu> R"
    and D: "{f. defined R f} \<subseteq> D"
    and fin: "finite_mode_csr_dpp CSR_Innermost \<mu>
      (mu_CSDP_on shp \<mu> D R) R"
  shows "SN (innermost_csstep \<mu> R)"
  by (rule finite_innermost_csr_dpp_imp_SN_if_progress[OF _ fin],
      rule mu_Tinf_imp_innermost_mu_CSDP_relstep[OF wf _ vc D])

theorem csr_switch_via_innermost_mu_CSDP_on:
  fixes R :: "('f,string) trs"
  assumes overlay: "csr_switch_overlay R"
    and wf: "wf_trs R"
    and vc: "rhs_mu_vars_condition \<mu> R"
    and D: "{f. defined R f} \<subseteq> D"
    and fin: "finite_mode_csr_dpp CSR_Innermost \<mu>
      (mu_CSDP_on shp \<mu> D R) R"
  shows "SN (csstep \<mu> R)"
  by (rule csr_switch_overlay_innermost_termination[OF overlay wf],
      rule finite_innermost_mu_CSDP_on_imp_SN[OF wf vc D fin])

lemma csr_switch_via_finite_innermost_csr_dpp:
  fixes R :: "('f,string) trs"
  assumes overlay: "csr_switch_overlay R"
    and wf: "wf_trs R"
    and progress:
      "\<And>t. t \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R) \<Longrightarrow>
        \<exists>u. u \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R) \<and>
          (\<sharp> t, \<sharp> u) \<in>
            (innermost_csdp_step \<mu> R)\<^sup>* O
            innermost_rrstep shp \<mu> R P O
            (innermost_csdp_step \<mu> R)\<^sup>*"
    and fin: "finite_mode_csr_dpp CSR_Innermost \<mu> P R"
  shows "SN (csstep \<mu> R)"
  by (rule csr_switch_overlay_innermost_termination[OF overlay wf],
      rule finite_innermost_csr_dpp_imp_SN_if_progress[OF progress fin])

end

lemma innermost_csr_dep_graph_edge_check_steps:
  fixes R :: "((('f::{showl,compare_order}, 'l::{showl,compare_order}) lab),
    'v::compare_order) rules"
  assumes wf: "wf_trs (set R)"
    and connect: "(t \<cdot> \<sigma>,u \<cdot> \<tau>) \<in>
      (innermost_csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
    and target: "(u \<cdot> \<tau>,v \<cdot> \<tau>) \<in>
      innermost_rrstep Sharp (mu_of \<mu>) (set R) P"
    and pair: "(u,v) \<in> P"
  shows "innermost_csr_dep_graph_edge_check \<mu> R
    (((s,t),()),((u,v),()))"
proof -
  have connect_full: "(t \<cdot> \<sigma>,u \<cdot> \<tau>) \<in>
      (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
    using connect innermost_csdp_step_subset_csdp_step
    by (meson rtrancl_mono subset_eq)
  have old: "csr_dep_graph_edge_check
      (csr_dp_root_mu (mu_of \<mu>)) R (((s,t),()),((u,v),()))"
    by (rule csr_dep_graph_edge_check_steps[OF wf connect_full])
  have not_blocked:
    "\<not> innermost_csr_lhs_blocked_check \<mu> R u"
    using innermost_rrstep_target_lhs_not_blocked[OF target pair]
    by simp
  show ?thesis using old not_blocked by simp
qed

definition check_innermost_csr_dep_graph_proc ::
  "('dpp, ('f::{showl,compare_order}, 'l::{showl,compare_order}) lab,
      string) dpp_ops \<Rightarrow>
   (('f, 'l) lab) muL \<Rightarrow> 'dpp \<Rightarrow>
   ('a option \<times> ((('f, 'l) lab), string) rules) list \<Rightarrow> showsl check"
where
  "check_innermost_csr_dep_graph_proc J \<mu> dpp dps = do {
    let P = dpp_ops.pairs J dpp;
    let R = dpp_ops.rules J dpp;
    check_wf_trs R;
    check_subseteq P (concat (map snd dps))
      <+? (\<lambda>dp. showsl_lit (STR ''innermost CSR dependency pair '') \<circ>
        showsl_rule dp \<circ> showsl_lit (STR '' is missing in decomposition\<newline>''));
    check_graph_decomp
      (showsl \<circ> fst)
      (Multi_Map.empty (root o fst o fst))
      graph_approx_csr_rt
      Multi_Map.insert
      (innermost_csr_dep_graph_edge_check \<mu> R)
      (map (\<lambda>(real,Cs).
        (real \<noteq> None,map (\<lambda>(s,t). ((s,t),())) Cs)) dps)
      <+? (\<lambda>s. showsl_lit
        (STR ''invalid innermost CSR dependency-graph decomposition:\<newline>'') \<circ> s)
  }"

fun check_innermost_csr_dp_termination_proof ::
  "('tp, ('f::{showl,compare_order,countable}, label_type) lab,
      string) tp_ops \<Rightarrow>
   ('dpp, ('f,label_type) lab,string) dpp_ops \<Rightarrow>
   (('f,label_type) lab) muL \<Rightarrow> showsl \<Rightarrow> 'dpp \<Rightarrow>
   ('f,label_type,string) csr_dp_termination_proof \<Rightarrow> showsl check"
and check_innermost_csr_dp_graph_components ::
  "('tp, ('f::{showl,compare_order,countable}, label_type) lab,
      string) tp_ops \<Rightarrow>
   ('dpp, ('f,label_type) lab,string) dpp_ops \<Rightarrow>
   (('f,label_type) lab) muL \<Rightarrow> showsl \<Rightarrow> 'dpp \<Rightarrow>
   (('f,label_type,string) csr_dp_termination_proof option \<times>
    ('f,label_type,string) trsLL) list \<Rightarrow> showsl check"
where
  "check_innermost_csr_dp_termination_proof I J \<mu> i dpp
      (CSR_DP_Dep_Graph_Proc edps) =
    debug i (STR ''innermost CSR-DP dependency graph'') (do {
      _ \<leftarrow> check_innermost_csr_dep_graph_proc J \<mu> dpp edps;
      check_innermost_csr_dp_graph_components I J \<mu> i dpp edps
    })"
| "check_innermost_csr_dp_termination_proof I J \<mu> i dpp prf =
    check_csr_dp_termination_proof_core I J \<mu> False i dpp prf"
| "check_innermost_csr_dp_graph_components I J \<mu> i dpp [] = succeed"
| "check_innermost_csr_dp_graph_components I J \<mu> i dpp
      ((None,P)#rest) =
    check_innermost_csr_dp_graph_components I J \<mu>
      (add_index i 1) dpp rest"
| "check_innermost_csr_dp_graph_components I J \<mu> i dpp
      ((Some prf,P)#rest) = do {
    check_innermost_csr_dp_termination_proof I J \<mu> (add_index i 1)
      (dpp_ops.intersect_pairs J dpp P) prf;
    check_innermost_csr_dp_graph_components I J \<mu>
      (add_index i 1) dpp rest
  }"

lemma check_innermost_csr_dp_graph_components_member:
  assumes ok: "isOK (check_innermost_csr_dp_graph_components
      I J \<mu> i dpp edps)"
    and mem: "(Some prf,P) \<in> set edps"
  shows "\<exists>j. isOK (check_innermost_csr_dp_termination_proof
    I J \<mu> j (dpp_ops.intersect_pairs J dpp P) prf)"
  using ok mem
proof (induct edps arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons head rest)
  obtain po C where head: "head = (po,C)" by (cases head)
  show ?case
  proof (cases po)
    case None
    from Cons.prems(1) head None have tail:
      "isOK (check_innermost_csr_dp_graph_components
        I J \<mu> (add_index i 1) dpp rest)" by simp
    from Cons.prems(2) head None have mem': "(Some prf,P) \<in> set rest"
      by auto
    show ?thesis by (rule Cons.hyps[OF tail mem'])
  next
    case (Some p)
    show ?thesis
    proof (cases "(Some prf,P) = head")
      case True
      from Cons.prems(1) head Some True show ?thesis by auto
    next
      case False
      from Cons.prems(1) head Some have tail:
        "isOK (check_innermost_csr_dp_graph_components
          I J \<mu> (add_index i 1) dpp rest)" by simp
      from Cons.prems(2) False have mem': "(Some prf,P) \<in> set rest"
        by auto
      show ?thesis by (rule Cons.hyps[OF tail mem'])
    qed
  qed
qed

lemma check_innermost_csr_dep_graph_proc_sound:
  assumes J: "dpp_spec J"
    and plain: "plain_csr_dpp J dpp"
    and check: "isOK (check_innermost_csr_dep_graph_proc J \<mu> dpp edps)"
    and fin: "\<And>prf C. (Some prf,C) \<in> set edps \<Longrightarrow>
      finite_mode_csr_dpp Sharp CSR_Innermost (mu_of \<mu>)
        (set (dpp_ops.pairs J dpp) \<inter> set C)
        (set (dpp_ops.rules J dpp))"
  shows "finite_mode_csr_dpp Sharp CSR_Innermost (mu_of \<mu>)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
proof -
  interpret dpp_spec J by fact
  let ?P = "set (pairs dpp)"
  let ?RL = "rules dpp"
  let ?R = "set ?RL"
  let ?S = "innermost_csdp_step Sharp (mu_of \<mu>) ?R"
  let ?T = "innermost_rrstep Sharp (mu_of \<mu>) ?R ?P"
  let ?echeck = "innermost_csr_dep_graph_edge_check \<mu> ?RL"
  let ?conv = "\<lambda>(real,Cs).
    (real \<noteq> None,map (\<lambda>(s,t). ((s,t),())) Cs)"
  from check have wf: "wf_trs ?R"
    and subset: "?P \<subseteq> set (concat (map snd edps))"
    and scc: "isOK (check_graph_decomp (showsl \<circ> fst)
      (Multi_Map.empty (root o fst o fst))
      graph_approx_csr_rt Multi_Map.insert ?echeck (map ?conv edps))"
    unfolding check_innermost_csr_dep_graph_proc_def
    by (auto simp: Let_def)
  show ?thesis
    unfolding finite_mode_csr_dpp_def csr_mode_rrstep.simps
      csr_mode_csdp_step.simps SN_rel_defs SN_defs
  proof (rule notI)
    assume infinite: "\<exists>f. f 0 \<in> UNIV \<and>
      (\<forall>i. (f i,f (Suc i)) \<in> relto ?T ?S)"
    then obtain ch where chain: "\<And>i.
      (ch i,ch (Suc i)) \<in> relto ?T ?S" by auto
    from chain have chain': "\<And>i. (ch i,ch (Suc i)) \<in>
      ?S\<^sup>* O ?T O ?S\<^sup>*" by auto
    have ex_step: "\<forall>i. \<exists>l r \<sigma>.
      (l,r) \<in> ?P \<and>
      (ch i,l \<cdot> \<sigma>) \<in> ?S\<^sup>* \<and>
      (l \<cdot> \<sigma>,r \<cdot> \<sigma>) \<in> ?T \<and>
      (r \<cdot> \<sigma>,ch (Suc i)) \<in> ?S\<^sup>*"
    proof
      fix i
      from chain'[of i] obtain x y where pre: "(ch i,x) \<in> ?S\<^sup>*"
        and strict: "(x,y) \<in> ?T"
        and post: "(y,ch (Suc i)) \<in> ?S\<^sup>*" by auto
      from strict have root: "(x,y) \<in> rrstep ?P"
        unfolding innermost_rrstep_def by blast
      from rrstepE[OF root] obtain l r \<sigma> where pair: "(l,r) \<in> ?P"
        and x: "x = l \<cdot> \<sigma>" and y: "y = r \<cdot> \<sigma>" .
      show "\<exists>l r \<sigma>. (l,r) \<in> ?P \<and>
        (ch i,l \<cdot> \<sigma>) \<in> ?S\<^sup>* \<and>
        (l \<cdot> \<sigma>,r \<cdot> \<sigma>) \<in> ?T \<and>
        (r \<cdot> \<sigma>,ch (Suc i)) \<in> ?S\<^sup>*"
        using pair pre strict post unfolding x y by blast
    qed
    then obtain s t \<sigma> where pair: "\<And>i. (s i,t i) \<in> ?P"
      and pre: "\<And>i. (ch i,s i \<cdot> \<sigma> i) \<in> ?S\<^sup>*"
      and strict: "\<And>i. (s i \<cdot> \<sigma> i,t i \<cdot> \<sigma> i) \<in> ?T"
      and post: "\<And>i. (t i \<cdot> \<sigma> i,ch (Suc i)) \<in> ?S\<^sup>*"
      by metis
    have steps: "\<And>i. (t i \<cdot> \<sigma> i,
        s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?S\<^sup>*"
      using post pre by (meson rtrancl_trans)
    let ?p = "\<lambda>i. ((s i,t i),())"
    have path: "\<And>i. ?echeck (?p i,?p (Suc i))"
      by (rule innermost_csr_dep_graph_edge_check_steps[
        OF wf steps strict pair])
    have lift_node: "\<And>l r. (l,r) \<in> set (concat (map snd edps)) \<Longrightarrow>
      ((l,r),()) \<in> set (concat (map snd (map ?conv edps)))"
    proof -
      fix l r
      assume lr: "(l,r) \<in> set (concat (map snd edps))"
      then obtain x where x: "x \<in> set edps" and lrx: "(l,r) \<in> set (snd x)"
        by auto
      obtain real Cs where xeq: "x = (real,Cs)" by (cases x) auto
      from x xeq have mem: "(real,Cs) \<in> set edps" by simp
      from lrx xeq have lrCs: "(l,r) \<in> set Cs" by simp
      have node: "((l,r),()) \<in> set (map (\<lambda>(s,t). ((s,t),())) Cs)"
        using lrCs by force
      have conv_mem: "?conv (real,Cs) \<in> set (map ?conv edps)"
        using mem by (auto split: prod.splits)
      have comp_mem: "snd (?conv (real,Cs)) \<in>
          set (map snd (map ?conv edps))"
        using conv_mem unfolding set_map by blast
      have node': "((l,r),()) \<in> set (snd (?conv (real,Cs)))"
        using node by simp
      show "((l,r),()) \<in> set (concat (map snd (map ?conv edps)))"
        using comp_mem node' unfolding set_concat by blast
    qed
    have nodes: "path_nodes ?p \<subseteq>
        set (concat (map snd (map ?conv edps)))"
    proof
      fix x
      assume "x \<in> path_nodes ?p"
      then obtain i where x: "x = ?p i"
        unfolding path_nodes_def by auto
      from pair[of i] subset have
        "(s i,t i) \<in> set (concat (map snd edps))" by auto
      then show "x \<in> set (concat (map snd (map ?conv edps)))"
        unfolding x by (rule lift_node)
    qed
    have key_insert: "\<And>x m.
      Multi_Map.key_fun m = root \<circ> fst \<circ> fst \<Longrightarrow>
      Multi_Map.key_fun (Multi_Map.insert x m) = root \<circ> fst \<circ> fst"
      by simp
    have approx: "\<And>m a b.
      Multi_Map.key_fun m = root \<circ> fst \<circ> fst \<Longrightarrow>
      ?echeck (a,b) \<Longrightarrow> b \<in> set (Multi_Map.values m) \<Longrightarrow>
      b \<in> set (graph_approx_csr_rt m a)"
      unfolding graph_approx_csr_rt.simps by simp
    have component: "\<exists>q C. ?p =\<dots> q \<and>
      C \<in> set (map snd (filter fst (map ?conv edps))) \<and>
      path_nodes q \<subseteq> set C"
      by (rule check_graph_decomp_sound[of
        "\<lambda>m. set (Multi_Map.values m)", OF values_empty values_insert,
        of "\<lambda>m. Multi_Map.key_fun m = (root o fst o fst)",
        OF key_fun_empty key_insert approx scc path nodes])
    then obtain q C where suffix: "?p =\<dots> q"
      and ending: "path_nodes q \<subseteq> set C"
      and component_mem:
        "C \<in> set (map snd (filter fst (map ?conv edps)))" by blast
    from component_mem obtain proof_id Cs where mem:
      "(Some proof_id,Cs) \<in> set edps"
      and C: "C = map (\<lambda>(s,t). ((s,t),())) Cs" by force
    from suffix obtain n where pq: "\<And>m. ?p (m+n) = q m"
      unfolding Graph.suffix_def by blast
    have CP: "\<And>m. (s (m+n),t (m+n)) \<in> ?P \<inter> set Cs"
    proof -
      fix m
      have "?p (m+n) \<in> path_nodes q"
        using pq[of m] unfolding path_nodes_def by blast
      with ending C pair[of "m+n"] show
        "(s (m+n),t (m+n)) \<in> ?P \<inter> set Cs" by force
    qed
    let ?tail = "\<lambda>m. ch (m+n)"
    let ?PT = "?P \<inter> set Cs"
    have strict_tail: "\<And>m.
      (s (m+n) \<cdot> \<sigma> (m+n),t (m+n) \<cdot> \<sigma> (m+n)) \<in>
      innermost_rrstep Sharp (mu_of \<mu>) ?R ?PT"
    proof -
      fix m
      from strict[of "m+n"] have source:
        "innermost_pair_source Sharp (mu_of \<mu>) ?R
          (s (m+n) \<cdot> \<sigma> (m+n))"
        unfolding innermost_rrstep_def by blast
      have rr: "(s (m+n) \<cdot> \<sigma> (m+n),
          t (m+n) \<cdot> \<sigma> (m+n)) \<in> rrstep ?PT"
        unfolding rrstep_def' using CP[of m] by blast
      show "(s (m+n) \<cdot> \<sigma> (m+n),
          t (m+n) \<cdot> \<sigma> (m+n)) \<in>
          innermost_rrstep Sharp (mu_of \<mu>) ?R ?PT"
        unfolding innermost_rrstep_def using rr source by blast
    qed
    have tail_chain: "\<And>m. (?tail m,?tail (Suc m)) \<in>
      relto (innermost_rrstep Sharp (mu_of \<mu>) ?R ?PT) ?S"
    proof -
      fix m
      have suc_add: "Suc m+n = Suc (m+n)" by simp
      from pre[of "m+n"] post[of "m+n"] strict_tail[of m]
      show "(?tail m,?tail (Suc m)) \<in>
        relto (innermost_rrstep Sharp (mu_of \<mu>) ?R ?PT) ?S"
        unfolding suc_add by auto
    qed
    have tail_is_chain: "chain
      (relto (innermost_rrstep Sharp (mu_of \<mu>) ?R ?PT) ?S) ?tail"
      using tail_chain by simp
    have tail_sn: "SN
      (relto (innermost_rrstep Sharp (mu_of \<mu>) ?R ?PT) ?S)"
      using fin[OF mem]
      unfolding finite_mode_csr_dpp_def SN_rel_on_def by simp
    have not_tail_sn: "\<not> SN
      (relto (innermost_rrstep Sharp (mu_of \<mu>) ?R ?PT) ?S)"
      by (rule not_SN_onI[of ?tail], simp, rule tail_is_chain)
    from tail_sn not_tail_sn show False by contradiction
  qed
qed

lemma check_csr_dp_core_imp_finite_innermost:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and plain: "plain_csr_dpp J dpp"
    and ok: "isOK (check_csr_dp_termination_proof_core
      I J \<mu> False i dpp prf)"
  shows "finite_mode_csr_dpp Sharp CSR_Innermost (mu_of \<mu>)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
proof -
  have full: "finite_mode_csr_dpp Sharp CSR_Full (mu_of \<mu>)
      (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
    using check_csr_dp_termination_proof_core_sound[OF I J plain ok] by simp
  show ?thesis
    by (rule finite_full_imp_finite_innermost_csr_dpp[OF full])
qed

lemma check_innermost_csr_dp_termination_proof_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and plain: "plain_csr_dpp J dpp"
    and ok: "isOK (check_innermost_csr_dp_termination_proof
      I J \<mu> i dpp prf)"
  shows "finite_mode_csr_dpp Sharp CSR_Innermost (mu_of \<mu>)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
  using ok plain
proof (induct "prf" arbitrary: dpp i)
  case CSR_DP_P_is_Empty
  from CSR_DP_P_is_Empty.prems(1) have core:
    "isOK (check_csr_dp_termination_proof_core I J \<mu> False i dpp
      CSR_DP_P_is_Empty)"
    using CSR_DP_P_is_Empty.prems(1)
    by (simp only: check_innermost_csr_dp_termination_proof.simps)
  show ?case by (rule check_csr_dp_core_imp_finite_innermost[
    OF I J CSR_DP_P_is_Empty.prems(2) core])
next
  case (CSR_DP_Ordinary_Proof x)
  from CSR_DP_Ordinary_Proof.prems(1) have core:
    "isOK (check_csr_dp_termination_proof_core I J \<mu> False i dpp
      (CSR_DP_Ordinary_Proof x))"
    using CSR_DP_Ordinary_Proof.prems(1)
    by (simp only: check_innermost_csr_dp_termination_proof.simps)
  show ?case by (rule check_csr_dp_core_imp_finite_innermost[
    OF I J CSR_DP_Ordinary_Proof.prems(2) core])
next
  case (CSR_DP_Subterm_Criterion_Proc x1 x2 x3 subproof)
  from CSR_DP_Subterm_Criterion_Proc.prems(1) have core:
    "isOK (check_csr_dp_termination_proof_core I J \<mu> False i dpp
      (CSR_DP_Subterm_Criterion_Proc x1 x2 x3 subproof))"
    using CSR_DP_Subterm_Criterion_Proc.prems(1)
    by (simp only: check_innermost_csr_dp_termination_proof.simps)
  show ?case by (rule check_csr_dp_core_imp_finite_innermost[
    OF I J CSR_DP_Subterm_Criterion_Proc.prems(2) core])
next
  case (CSR_DP_Gen_Subterm_Criterion_Proc x1 x2 subproof)
  from CSR_DP_Gen_Subterm_Criterion_Proc.prems(1) have core:
    "isOK (check_csr_dp_termination_proof_core I J \<mu> False i dpp
      (CSR_DP_Gen_Subterm_Criterion_Proc x1 x2 subproof))"
    using CSR_DP_Gen_Subterm_Criterion_Proc.prems(1)
    by (simp only: check_innermost_csr_dp_termination_proof.simps)
  show ?case by (rule check_csr_dp_core_imp_finite_innermost[
    OF I J CSR_DP_Gen_Subterm_Criterion_Proc.prems(2) core])
next
  case (CSR_DP_Usable_Rules_Proc x1 subproof)
  from CSR_DP_Usable_Rules_Proc.prems(1) have core:
    "isOK (check_csr_dp_termination_proof_core I J \<mu> False i dpp
      (CSR_DP_Usable_Rules_Proc x1 subproof))"
    using CSR_DP_Usable_Rules_Proc.prems(1)
    by (simp only: check_innermost_csr_dp_termination_proof.simps)
  show ?case by (rule check_csr_dp_core_imp_finite_innermost[
    OF I J CSR_DP_Usable_Rules_Proc.prems(2) core])
next
  case (CSR_DP_Dep_Graph_Proc edps)
  from CSR_DP_Dep_Graph_Proc.prems(1) have graph_ok:
      "isOK (check_innermost_csr_dep_graph_proc J \<mu> dpp edps)"
    and components_ok:
      "isOK (check_innermost_csr_dp_graph_components
        I J \<mu> i dpp edps)" by auto
  show ?case
  proof (rule check_innermost_csr_dep_graph_proc_sound[
      OF J CSR_DP_Dep_Graph_Proc.prems(2) graph_ok])
    fix proof_id C
    assume mem: "(Some proof_id,C) \<in> set edps"
    let ?d = "dpp_ops.intersect_pairs J dpp C"
    from check_innermost_csr_dp_graph_components_member[
      OF components_ok mem]
    obtain j where rec: "isOK (check_innermost_csr_dp_termination_proof
      I J \<mu> j ?d proof_id)" by blast
    have plain': "plain_csr_dpp J ?d"
      by (rule plain_csr_dpp_intersect_pairs[
        OF J CSR_DP_Dep_Graph_Proc.prems(2)])
    have ih: "finite_mode_csr_dpp Sharp CSR_Innermost (mu_of \<mu>)
      (set (dpp_ops.pairs J ?d)) (set (dpp_ops.rules J ?d))"
      apply (rule CSR_DP_Dep_Graph_Proc.hyps)
          apply (rule mem)
         apply simp
        apply simp
       apply (rule rec)
      apply (rule plain')
      done
    interpret dpp_spec J by fact
    have sem: "dpp_ops.dpp J ?d =
      (NFS dpp,M dpp,set (P dpp) \<inter> set C,
        set (Pw dpp) \<inter> set C,set (Q dpp),set (R dpp),set (Rw dpp))"
      by (rule intersect_pairs_sound)
    have sem': "dpp_ops.dpp J ?d =
      (NFS ?d,M ?d,set (P ?d),set (Pw ?d),set (Q ?d),set (R ?d),set (Rw ?d))"
      by (rule dpp_sound)
    have pairs: "set (pairs ?d) = set (pairs dpp) \<inter> set C"
      using sem sem' pairs_sound[of dpp] pairs_sound[of ?d] by auto
    have rules: "set (rules ?d) = set (rules dpp)"
      using sem sem' rules_sound[of dpp] rules_sound[of ?d] by auto
    show "finite_mode_csr_dpp Sharp CSR_Innermost (mu_of \<mu>)
      (set (dpp_ops.pairs J dpp) \<inter> set C)
      (set (dpp_ops.rules J dpp))"
      using ih unfolding pairs rules .
  qed
next
  case (CSR_DP_Instantiation_Proc x1 x2 subproof)
  from CSR_DP_Instantiation_Proc.prems(1) have core:
    "isOK (check_csr_dp_termination_proof_core I J \<mu> False i dpp
      (CSR_DP_Instantiation_Proc x1 x2 subproof))"
    using CSR_DP_Instantiation_Proc.prems(1)
    by (simp only: check_innermost_csr_dp_termination_proof.simps)
  show ?case by (rule check_csr_dp_core_imp_finite_innermost[
    OF I J CSR_DP_Instantiation_Proc.prems(2) core])
next
  case (CSR_DP_Forward_Instantiation_Proc x1 x2 subproof)
  from CSR_DP_Forward_Instantiation_Proc.prems(1) have core:
    "isOK (check_csr_dp_termination_proof_core I J \<mu> False i dpp
      (CSR_DP_Forward_Instantiation_Proc x1 x2 subproof))"
    using CSR_DP_Forward_Instantiation_Proc.prems(1)
    by (simp only: check_innermost_csr_dp_termination_proof.simps)
  show ?case by (rule check_csr_dp_core_imp_finite_innermost[
    OF I J CSR_DP_Forward_Instantiation_Proc.prems(2) core])
next
  case (CSR_DP_Redpair_UR_Proc x1 x2 x3 subproof)
  from CSR_DP_Redpair_UR_Proc.prems(1) have core:
    "isOK (check_csr_dp_termination_proof_core I J \<mu> False i dpp
      (CSR_DP_Redpair_UR_Proc x1 x2 x3 subproof))"
    using CSR_DP_Redpair_UR_Proc.prems(1)
    by (simp only: check_innermost_csr_dp_termination_proof.simps)
  show ?case by (rule check_csr_dp_core_imp_finite_innermost[
    OF I J CSR_DP_Redpair_UR_Proc.prems(2) core])
next
  case (CSR_DP_Size_Change_Subterm_Proc x)
  from CSR_DP_Size_Change_Subterm_Proc.prems(1) have core:
    "isOK (check_csr_dp_termination_proof_core I J \<mu> False i dpp
      (CSR_DP_Size_Change_Subterm_Proc x))"
    using CSR_DP_Size_Change_Subterm_Proc.prems(1)
    by (simp only: check_innermost_csr_dp_termination_proof.simps)
  show ?case by (rule check_csr_dp_core_imp_finite_innermost[
    OF I J CSR_DP_Size_Change_Subterm_Proc.prems(2) core])
qed

lemma mu_csr_dependency_pairs_tt_finite_innermost_mu_CSDP_on:
  assumes J: "dpp_spec J"
    and tt: "mu_csr_dependency_pairs_tt Sharp J \<mu> R P = return d"
    and fin: "finite_mode_csr_dpp Sharp CSR_Innermost (mu_of \<mu>)
      (set (dpp_ops.pairs J d)) (set (dpp_ops.rules J d))"
  shows "finite_mode_csr_dpp Sharp CSR_Innermost (mu_of \<mu>)
    (mu_CSDP_on Sharp (mu_of \<mu>) (set (defined_list R)) (set R))
    (set R)"
proof -
  interpret dpp_spec J by fact
  let ?D = "defined_list R"
  let ?MP = "mu_CSDP_on Sharp (mu_of \<mu>) (set ?D) (set R)"
  note tt' = tt[unfolded mu_csr_dependency_pairs_tt_def Let_def,
    simplified]
  from tt' have d: "d = dpp_ops.mk J False False P [] [] [] R" by auto
  from tt' have cover: "\<And>dp.
    dp \<in> set (mu_CSDP_list Sharp R \<mu> ?D) \<Longrightarrow>
    dp \<in> set P \<or> (\<exists>dp'\<in>set P. dp =\<^sub>v dp')" by auto
  have cover': "\<And>dp. dp \<in> ?MP \<Longrightarrow>
    dp \<in> set P \<or> (\<exists>dp'\<in>set P. dp =\<^sub>v dp')"
    using cover unfolding mu_CSDP_list by auto
  have finP: "finite_mode_csr_dpp Sharp CSR_Innermost (mu_of \<mu>)
      (set P) (set R)"
    using fin unfolding d mk_sound by simp
  have root_steps: "rrstep ?MP \<subseteq> rrstep (set P)"
  proof
    fix s t
    assume "(s,t) \<in> rrstep ?MP"
    then obtain l r \<sigma> where st: "s = l \<cdot> \<sigma>" "t = r \<cdot> \<sigma>"
      and lr: "(l,r) \<in> ?MP" unfolding rrstep_def' by auto
    from cover'[OF lr] show "(s,t) \<in> rrstep (set P)"
    proof
      assume "(l,r) \<in> set P"
      with st show ?thesis unfolding rrstep_def' by blast
    next
      assume "\<exists>dp'\<in>set P. (l,r) =\<^sub>v dp'"
      then obtain l' r' where lr': "(l',r') \<in> set P"
        and eq: "(l,r) =\<^sub>v (l',r')" by auto
      from eq_rule_mod_varsE[OF eq] obtain \<tau> where
        l: "l = l' \<cdot> \<tau>" and r: "r = r' \<cdot> \<tau>" by blast
      have step: "\<exists>la ra \<rho>. (la,ra) \<in> set P \<and>
        s = la \<cdot> \<rho> \<and> t = ra \<cdot> \<rho>"
        using lr' st unfolding l r
        by (intro exI[of _ l'] exI[of _ r']
          exI[of _ "\<tau> \<circ>\<^sub>s \<sigma>"], simp)
      show ?thesis unfolding rrstep_def' using step by auto
    qed
  qed
  have inner_steps:
    "innermost_rrstep Sharp (mu_of \<mu>) (set R) ?MP \<subseteq>
     innermost_rrstep Sharp (mu_of \<mu>) (set R) (set P)"
    using root_steps unfolding innermost_rrstep_def by blast
  show ?thesis
    using finP unfolding finite_mode_csr_dpp_def
      csr_mode_rrstep.simps csr_mode_csdp_step.simps
    by (rule SN_rel_mono[OF inner_steps subset_refl])
qed

definition check_innermost_csr_termination_proof ::
  "('tp, ('f::{showl,compare_order,countable}, label_type) lab,
      string) tp_ops \<Rightarrow>
   ('dpp, ('f,label_type) lab,string) dpp_ops \<Rightarrow>
   showsl \<Rightarrow> (('f,label_type) lab) muL \<Rightarrow>
   ('f,label_type,string) trsLL \<Rightarrow>
   ('f,label_type,string) trsLL \<Rightarrow>
   ('f,label_type,string) csr_dp_termination_proof \<Rightarrow> showsl check"
where
  "check_innermost_csr_termination_proof I J i \<mu> R P prf =
    debug i (STR ''innermost CSR dependency pairs'') (do {
      check_csr_orthogonal R;
      csr_sharp_mu_check \<mu>;
      dpp \<leftarrow> mu_csr_dependency_pairs_tt Sharp J \<mu> R P;
      check_innermost_csr_dp_termination_proof I J \<mu>
        (add_index i 1) dpp prf
    })"

lemma check_innermost_csr_termination_proof_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_innermost_csr_termination_proof
      I J i \<mu> R P prf)"
  shows "SN (csstep (mu_of \<mu>) (set R))"
proof -
  from ok obtain d where ortho_ok: "isOK (check_csr_orthogonal R)"
    and mu_dp: "mu_csr_dependency_pairs_tt Sharp J \<mu> R P = return d"
    and rec: "isOK (check_innermost_csr_dp_termination_proof
      I J \<mu> (add_index i 1) d prf)"
    unfolding check_innermost_csr_termination_proof_def by auto
  have plain: "plain_csr_dpp J d"
  proof -
    interpret dpp_spec J by fact
    from mu_dp[unfolded mu_csr_dependency_pairs_tt_def Let_def,
      simplified]
    have d: "d = dpp_ops.mk J False False P [] [] [] R" by auto
    have sem: "dpp_ops.dpp J d = (False,False,set P,{},{},{},set R)"
      using d unfolding dpp_spec.mk_sound[OF J] by simp
    have sem': "dpp_ops.dpp J d =
      (NFS d,M d,set (local.P d),set (Pw d),set (Q d),
        set (local.R d),set (Rw d))" by (rule dpp_sound)
    from sem sem' have "\<not> NFS d" "\<not> M d" "set (Pw d) = {}"
      "set (Q d) = {}" "set (local.R d) = {}" by auto
    then show ?thesis unfolding plain_csr_dpp_def by auto
  qed
  have fin: "finite_mode_csr_dpp Sharp CSR_Innermost (mu_of \<mu>)
      (set (dpp_ops.pairs J d)) (set (dpp_ops.rules J d))"
    by (rule check_innermost_csr_dp_termination_proof_sound[
      OF I J plain rec])
  have fin_exact: "finite_mode_csr_dpp Sharp CSR_Innermost (mu_of \<mu>)
      (mu_CSDP_on Sharp (mu_of \<mu>) (set (defined_list R)) (set R))
      (set R)"
    by (rule mu_csr_dependency_pairs_tt_finite_innermost_mu_CSDP_on[
      OF J mu_dp fin])
  note mu_dp' = mu_dp[unfolded mu_csr_dependency_pairs_tt_def Let_def,
    simplified]
  have overlay: "csr_switch_overlay (set R)"
    by (rule check_csr_orthogonal_sound[OF ortho_ok])
  have wf: "wf_trs (set R)" using mu_dp' by auto
  have vc: "rhs_mu_vars_condition (mu_of \<mu>) (set R)"
    by (rule rhs_mu_vars_condition_list_sound, insert mu_dp', auto)
  have D: "{f. defined (set R) f} \<subseteq> set (defined_list R)"
    using mu_dp' by auto
  show ?thesis
    by (rule csr_switch_via_innermost_mu_CSDP_on[
      OF overlay wf vc D fin_exact])
qed

end
