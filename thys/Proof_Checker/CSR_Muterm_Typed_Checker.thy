(*
Author: Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Muterm_Typed_Checker
  imports CSR_Muterm_Typed_Recursive_Redpair.CSR_Muterm_Typed_Recursive_Redpair
begin

lemma finite_muterm_min_typed_imp_finite_innermost_min_typed_overlay:
  assumes overlay: "csr_switch_overlay R"
    and wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and fin: "finite_muterm_min_typed_dpp Sharp \<mu> R P B"
  shows "finite_muterm_innermost_min_typed_dpp Sharp \<mu> R P B"
proof -
  have pair_sub: "muterm_innermost_min_typed_pair_step Sharp \<mu> R P B
      \<subseteq> muterm_min_typed_pair_step Sharp \<mu> R P B"
  proof
    fix st
    assume st: "st \<in> muterm_innermost_min_typed_pair_step Sharp \<mu> R P B"
    obtain s t where pair: "st = (s,t)" by (cases st)
    from st[unfolded pair muterm_innermost_min_typed_pair_step_def
        muterm_innermost_typed_pair_step_def]
    have typed: "(s,t) \<in> muterm_typed_pair_step P B"
      and target: "\<exists>u. t = sharp_term Sharp u \<and>
        u \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)" by auto
    from target obtain u where t: "t = sharp_term Sharp u"
      and uT: "u \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)" by blast
    have full_uT: "u \<in> mu_Tinf \<mu> (csstep \<mu> R)"
      by (rule mu_Tinf_innermost_imp_mu_Tinf[OF overlay wf uT])
    have target_SN: "SN_on (csdp_step Sharp \<mu> R) {t}"
      unfolding t by (rule mu_Tinf_imp_SN_sharp_csdp[OF wf fresh full_uT])
    show "st \<in> muterm_min_typed_pair_step Sharp \<mu> R P B"
      unfolding pair muterm_min_typed_pair_step_def using typed target_SN by auto
  qed
  show ?thesis
    unfolding finite_muterm_innermost_min_typed_dpp_def
      finite_muterm_min_typed_dpp_def
    by (rule SN_rel_mono[
      OF pair_sub innermost_csdp_step_subset_csdp_step
        fin[unfolded finite_muterm_min_typed_dpp_def]])
qed

lemma finite_muterm_typed_imp_finite_innermost_min_typed:
  assumes fin: "finite_muterm_typed_dpp shp \<mu> R P B"
  shows "finite_muterm_innermost_min_typed_dpp shp \<mu> R P B"
proof -
  have pair_sub: "muterm_innermost_min_typed_pair_step shp \<mu> R P B
      \<subseteq> muterm_typed_pair_step P B"
    unfolding muterm_innermost_min_typed_pair_step_def
      muterm_innermost_typed_pair_step_def by auto
  show ?thesis
    unfolding finite_muterm_innermost_min_typed_dpp_def
      finite_muterm_typed_dpp_def
    by (rule SN_rel_mono[
      OF pair_sub innermost_csdp_step_subset_csdp_step
        fin[unfolded finite_muterm_typed_dpp_def]])
qed

lemma muterm_typed_pair_step_subset_ordinary:
  "muterm_typed_pair_step P S \<subseteq>
    (rstep (R \<union> S))\<^sup>* O rrstep P O (rstep (R \<union> S))\<^sup>*"
proof
  fix st
  assume step: "st \<in> muterm_typed_pair_step P S"
  obtain s t where st: "st = (s,t)" by (cases st)
  from step have cases:
      "muterm_noncollapsing_rrstep P s t \<or>
       (\<exists>x. muterm_collapsing_rrstep P s x \<and> (x,t) \<in> rrstep S)"
    unfolding st muterm_typed_pair_step_def by auto
  from cases show "st \<in> (rstep (R \<union> S))\<^sup>* O rrstep P O
    (rstep (R \<union> S))\<^sup>*"
  proof
    assume noncoll: "muterm_noncollapsing_rrstep P s t"
    then have pair: "(s,t) \<in> rrstep P"
      unfolding muterm_noncollapsing_rrstep_def rrstep_def' by blast
    show "st \<in> (rstep (R \<union> S))\<^sup>* O rrstep P O
      (rstep (R \<union> S))\<^sup>*"
      unfolding st using pair by auto
  next
    assume collapsing:
      "\<exists>x. muterm_collapsing_rrstep P s x \<and> (x,t) \<in> rrstep S"
    then obtain x where pair: "(s,x) \<in> rrstep P"
      and bridge: "(x,t) \<in> rrstep S"
      using muterm_collapsing_rrstep_imp_rrstep by blast
    from bridge obtain l r \<sigma> where lr: "(l,r) \<in> S"
      and x: "x = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
      unfolding rrstep_def' by blast
    have weak: "(x,t) \<in> rstep (R \<union> S)"
      unfolding x t
      by (rule rstepI[OF UnI2[OF lr], of _ Hole \<sigma>], simp_all)
    show "st \<in> (rstep (R \<union> S))\<^sup>* O rrstep P O
      (rstep (R \<union> S))\<^sup>*"
      unfolding st using pair weak by auto
  qed
qed

theorem finite_ordinary_imp_finite_muterm_typed:
  assumes fin: "finite_dpp (False,False,P,{},{},{},R \<union> S)"
  shows "finite_muterm_typed_dpp Sharp \<mu> R P S"
proof -
  let ?A = "(rstep (R \<union> S))\<^sup>* O rrstep P O
    (rstep (R \<union> S))\<^sup>*"
  let ?B = "(csdp_step Sharp \<mu> R)\<^sup>* O
    muterm_typed_pair_step P S O (csdp_step Sharp \<mu> R)\<^sup>*"
  from fin have sn: "SN ?A"
    unfolding finite_dpp_iff_SN_rel CS_rrstep_conv SN_rel_on_def by simp
  have cs_sub: "csdp_step Sharp \<mu> R \<subseteq> rstep (R \<union> S)"
  proof -
    have "csdp_step Sharp \<mu> R \<subseteq> rstep R"
      unfolding csdp_step_def csdp_step_p_def
      by (auto dest: rstep_r_p_s_imp_rstep)
    also have "rstep R \<subseteq> rstep (R \<union> S)"
      by (rule rstep_mono, auto)
    finally show ?thesis .
  qed
  have strict_sub: "muterm_typed_pair_step P S \<subseteq> ?A"
    by (rule muterm_typed_pair_step_subset_ordinary)
  have pre_sub: "(csdp_step Sharp \<mu> R)\<^sup>* \<subseteq>
      (rstep (R \<union> S))\<^sup>*"
    by (rule rtrancl_mono[OF cs_sub])
  have sub: "?B \<subseteq> ?A"
  proof
    fix st
    assume mem: "st \<in> ?B"
    obtain s t where st: "st = (s,t)" by (cases st)
    from mem obtain x y where pre: "(s,x) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
      and strict: "(x,y) \<in> muterm_typed_pair_step P S"
      and post: "(y,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
      unfolding st by auto
    from strict_sub strict obtain a b where xa: "(x,a) \<in> (rstep (R \<union> S))\<^sup>*"
      and pair: "(a,b) \<in> rrstep P"
      and by_step: "(b,y) \<in> (rstep (R \<union> S))\<^sup>*"
      by auto
    have sa: "(s,a) \<in> (rstep (R \<union> S))\<^sup>*"
      by (rule rtrancl_trans[OF set_mp[OF pre_sub pre] xa])
    have bt: "(b,t) \<in> (rstep (R \<union> S))\<^sup>*"
      by (rule rtrancl_trans[OF by_step set_mp[OF pre_sub post]])
    show "st \<in> ?A" unfolding st using sa pair bt by auto
  qed
  then have "SN ?B" by (rule SN_subset[OF sn])
  then show ?thesis unfolding finite_muterm_typed_dpp_def SN_rel_on_def .
qed

text \<open>
  The expanded pairs over-approximate every typed pair step, including a
  collapsing step followed by its recorded unhiding bridge.  Therefore a
  minimal CSR proof for the expanded problem is a sound, self-contained
  continuation for the native typed problem.
\<close>
fun check_muterm_expanded_extended_basic_proof ::
  "('tp, ('f::{showl,compare_order,countable},label_type) lab,string) tp_ops \<Rightarrow>
   ('dpp, ('f,label_type) lab,string) dpp_ops \<Rightarrow>
   (('f,label_type) lab) muL \<Rightarrow> showsl \<Rightarrow> 'dpp \<Rightarrow>
   ('f,label_type,string) csr_dp_termination_proof \<Rightarrow> showsl check"
and check_muterm_expanded_extended_basic_components ::
  "('tp, ('f::{showl,compare_order,countable},label_type) lab,string) tp_ops \<Rightarrow>
   ('dpp, ('f,label_type) lab,string) dpp_ops \<Rightarrow>
   (('f,label_type) lab) muL \<Rightarrow> showsl \<Rightarrow> 'dpp \<Rightarrow>
   (('f,label_type,string) csr_dp_termination_proof option \<times>
    ('f,label_type,string) trsLL) list \<Rightarrow> showsl check"
where
  "check_muterm_expanded_extended_basic_proof I J \<mu> i dpp
      (CSR_DP_Dep_Graph_Proc edpts) =
    debug i (STR ''expanded extended-basic MU-TERM dependency graph'') (do {
      _ \<leftarrow> check_csr_dep_graph_proc J \<mu> dpp edpts;
      check_muterm_expanded_extended_basic_components I J \<mu> i dpp edpts
    })"
| "check_muterm_expanded_extended_basic_proof I J \<mu> i dpp
      (CSR_DP_Ordinary_Proof (Redpair_UR_Proc redp Pr U subprf)) =
    debug i (STR ''expanded extended-basic MU-TERM reduction pair'') (do {
      dpp' \<leftarrow> muterm_extended_basic_redpair_proc J \<mu>
        (get_rel_impl redp) Pr U dpp;
      check_csr_dp_termination_proof_min I J \<mu> False
        (add_index i 1) dpp' (CSR_DP_Ordinary_Proof subprf)
    })"
| "check_muterm_expanded_extended_basic_proof I J \<mu> i dpp
      (CSR_DP_Instantiation_Proc st sts prf) =
    debug i (STR ''expanded extended-basic MU-TERM instantiation'') (do {
      dpp' \<leftarrow> csr_instantiation_proc J \<mu> st sts dpp;
      check_muterm_expanded_extended_basic_proof I J \<mu>
        (add_index i 1) dpp' prf
    })"
| "check_muterm_expanded_extended_basic_proof I J \<mu> i dpp prf =
    check_muterm_expanded_csr_proof I J \<mu> i dpp prf"
| "check_muterm_expanded_extended_basic_components I J \<mu> i dpp [] = succeed"
| "check_muterm_expanded_extended_basic_components I J \<mu> i dpp
      ((None,C)#rest) =
    check_muterm_expanded_extended_basic_components I J \<mu>
      (add_index i 1) dpp rest"
| "check_muterm_expanded_extended_basic_components I J \<mu> i dpp
      ((Some prf,C)#rest) = do {
    check_muterm_expanded_extended_basic_proof I J \<mu> (add_index i 1)
      (dpp_ops.intersect_pairs J dpp C) prf;
    check_muterm_expanded_extended_basic_components I J \<mu>
      (add_index i 1) dpp rest
  }"

lemma check_muterm_expanded_extended_basic_components_member:
  assumes ok: "isOK (check_muterm_expanded_extended_basic_components
      I J \<mu> i dpp edps)"
    and mem: "(Some prf,C) \<in> set edps"
  shows "\<exists>j. isOK (check_muterm_expanded_extended_basic_proof I J \<mu> j
    (dpp_ops.intersect_pairs J dpp C) prf)"
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
    from Cons.prems head None show ?thesis by (auto intro: Cons.hyps)
  next
    case (Some p)
    show ?thesis
    proof (cases "(Some prf,C) = head")
      case True
      with Cons.prems head Some show ?thesis by auto
    next
      case False
      from Cons.prems head Some False show ?thesis by (auto intro: Cons.hyps)
    qed
  qed
qed

lemma check_muterm_expanded_extended_basic_proof_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and plain: "plain_csr_dpp J dpp"
    and wf: "wf_trs (set (dpp_ops.rules J dpp))"
    and fresh: "\<And>f n. \<not> defined
      (set (dpp_ops.rules J dpp)) (Sharp f,n)"
    and ok: "isOK (check_muterm_expanded_extended_basic_proof
      I J \<mu> i dpp prf)"
  shows "finite_min_csr_dpp Sharp (mu_of \<mu>)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
  using ok plain wf fresh
proof (induct "prf" arbitrary: dpp i)
  case (CSR_DP_Ordinary_Proof dpprf)
  show ?case
  proof (cases "\<exists>redp Pr U subprf.
      dpprf = Redpair_UR_Proc redp Pr U subprf")
    case False
    from CSR_DP_Ordinary_Proof.prems False have old:
      "isOK (check_muterm_expanded_csr_proof I J \<mu> i dpp
        (CSR_DP_Ordinary_Proof dpprf))" by (cases dpprf, auto)
    show ?thesis by (rule check_muterm_expanded_csr_proof_sound[
      OF I J CSR_DP_Ordinary_Proof.prems(2-4) old])
  next
    case True
    then obtain redp Pr U subprf where shape:
      "dpprf = Redpair_UR_Proc redp Pr U subprf" by blast
    from CSR_DP_Ordinary_Proof.prems(1) shape obtain dpp' where proc:
      "muterm_extended_basic_redpair_proc J \<mu>
        (get_rel_impl redp) Pr U dpp = return dpp'"
      and rec: "isOK (check_csr_dp_termination_proof_min I J \<mu> False
        (add_index i 1) dpp' (CSR_DP_Ordinary_Proof subprf))"
      by auto
    have dpp_eq: "dpp' = dpp_spec.delete_pairs J dpp Pr"
      using proc unfolding muterm_extended_basic_redpair_proc_def by auto
    have plain': "plain_csr_dpp J dpp'"
      unfolding dpp_eq by (rule plain_csr_dpp_delete_pairs[
        OF J CSR_DP_Ordinary_Proof.prems(2)])
    interpret dpp_spec J by fact
    have rules': "set (rules dpp') = set (rules dpp)"
      using dpp_eq delete_P_Pw_sound[of dpp Pr Pr]
        rules_sound[of dpp'] by auto
    have wf': "wf_trs (set (rules dpp'))"
      using CSR_DP_Ordinary_Proof.prems(3) unfolding rules' .
    have fresh': "\<And>f n. \<not> defined (set (rules dpp')) (Sharp f,n)"
      using CSR_DP_Ordinary_Proof.prems(4) unfolding rules' .
    have fin: "finite_min_csr_dpp Sharp (mu_of \<mu>)
        (set (pairs dpp')) (set (rules dpp'))"
      by (rule check_csr_dp_termination_proof_min_sound[
        OF I J plain' wf' fresh' rec])
    show ?thesis by (rule muterm_extended_basic_redpair_proc_sound[
      OF J get_rel_impl proc CSR_DP_Ordinary_Proof.prems(3-4) fin])
  qed
next
  case (CSR_DP_Dep_Graph_Proc edps)
  from CSR_DP_Dep_Graph_Proc.prems(1) have graph:
      "isOK (check_csr_dep_graph_proc J \<mu> dpp edps)"
    and components: "isOK (check_muterm_expanded_extended_basic_components
      I J \<mu> i dpp edps)" by auto
  show ?case
  proof (rule check_csr_dep_graph_proc_min_sound[
      OF J CSR_DP_Dep_Graph_Proc.prems(2) graph])
    fix p C
    assume mem: "(Some p,C) \<in> set edps"
    let ?d = "dpp_ops.intersect_pairs J dpp C"
    from check_muterm_expanded_extended_basic_components_member[
      OF components mem]
    obtain j where rec: "isOK (check_muterm_expanded_extended_basic_proof
      I J \<mu> j ?d p)" by blast
    have plain': "plain_csr_dpp J ?d"
      by (rule plain_csr_dpp_intersect_pairs[
        OF J CSR_DP_Dep_Graph_Proc.prems(2)])
    interpret dpp_spec J by fact
    have sem: "dpp_ops.dpp J ?d =
      (NFS dpp,M dpp,set (P dpp) \<inter> set C,
        set (Pw dpp) \<inter> set C,set (Q dpp),set (R dpp),set (Rw dpp))"
      by (rule intersect_pairs_sound)
    have rules': "set (rules ?d) = set (rules dpp)"
      using sem dpp_sound[of dpp] dpp_sound[of ?d]
        rules_sound[of dpp] rules_sound[of ?d] by auto
    have fin: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (pairs ?d)) (set (rules ?d))"
      apply (rule CSR_DP_Dep_Graph_Proc.hyps[OF mem])
          apply simp
         apply simp
        apply (rule rec)
       apply (rule plain')
      using CSR_DP_Dep_Graph_Proc.prems(3-4) unfolding rules' by auto
    have pairs': "set (pairs ?d) = set (pairs dpp) \<inter> set C"
      using sem dpp_sound[of dpp] dpp_sound[of ?d]
        pairs_sound[of dpp] pairs_sound[of ?d] by auto
    show "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (pairs dpp) \<inter> set C) (set (rules dpp))"
      using fin unfolding pairs' rules' .
  qed
next
  case CSR_DP_P_is_Empty
  from CSR_DP_P_is_Empty.prems(1) have old:
    "isOK (check_muterm_expanded_csr_proof I J \<mu> i dpp
      CSR_DP_P_is_Empty)" by simp
  show ?case by (rule check_muterm_expanded_csr_proof_sound[
    OF I J CSR_DP_P_is_Empty.prems(2-4) old])
next
  case (CSR_DP_Subterm_Criterion_Proc x1 x2 x3 child)
  from CSR_DP_Subterm_Criterion_Proc.prems(1) have old:
    "isOK (check_muterm_expanded_csr_proof I J \<mu> i dpp
      (CSR_DP_Subterm_Criterion_Proc x1 x2 x3 child))" by simp
  show ?case by (rule check_muterm_expanded_csr_proof_sound[
    OF I J CSR_DP_Subterm_Criterion_Proc.prems(2-4) old])
next
  case (CSR_DP_Gen_Subterm_Criterion_Proc x1 x2 child)
  from CSR_DP_Gen_Subterm_Criterion_Proc.prems(1) have old:
    "isOK (check_muterm_expanded_csr_proof I J \<mu> i dpp
      (CSR_DP_Gen_Subterm_Criterion_Proc x1 x2 child))" by simp
  show ?case by (rule check_muterm_expanded_csr_proof_sound[
    OF I J CSR_DP_Gen_Subterm_Criterion_Proc.prems(2-4) old])
next
  case (CSR_DP_Usable_Rules_Proc x1 child)
  from CSR_DP_Usable_Rules_Proc.prems(1) have old:
    "isOK (check_muterm_expanded_csr_proof I J \<mu> i dpp
      (CSR_DP_Usable_Rules_Proc x1 child))"
    by (simp only: check_muterm_expanded_extended_basic_proof.simps
      check_muterm_expanded_csr_proof.simps)
  show ?case by (rule check_muterm_expanded_csr_proof_sound[
    OF I J CSR_DP_Usable_Rules_Proc.prems(2-4) old])
next
  case (CSR_DP_Instantiation_Proc st sts child)
  from CSR_DP_Instantiation_Proc.prems(1)
  obtain dpp' where proc:
      "csr_instantiation_proc J \<mu> st sts dpp = return dpp'"
    and rec: "isOK (check_muterm_expanded_extended_basic_proof
      I J \<mu> (add_index i 1) dpp' child)"
    by auto
  note proc_sound = csr_instantiation_proc_sound[OF proc]
  obtain s t where st: "st = (s,t)" by (cases st)
  interpret dpp_spec J by fact
  have dpp'_def: "dpp' = replace_pair dpp (s,t) sts"
    using proc_sound(1) st by simp
  have sem: "dpp_ops.dpp J dpp' =
      (NFS dpp, M dpp, replace (s,t) (set sts) (set (P dpp)),
       replace (s,t) (set sts) (set (Pw dpp)), set (Q dpp),
       set (R dpp), set (Rw dpp))"
    unfolding dpp'_def by (rule replace_pair_sound)
  have sem': "dpp_ops.dpp J dpp' =
      (NFS dpp', M dpp', set (P dpp'), set (Pw dpp'), set (Q dpp'),
       set (R dpp'), set (Rw dpp'))"
    by (rule dpp_sound)
  from CSR_DP_Instantiation_Proc.prems(2)
  have plain_fields:
      "\<not> NFS dpp" "\<not> M dpp" "Pw dpp = []" "Q dpp = []" "R dpp = []"
    unfolding plain_csr_dpp_def by auto
  have rules': "set (rules dpp') = set (rules dpp)"
    using sem sem' rules_sound[of dpp] rules_sound[of dpp'] by auto
  have plain': "plain_csr_dpp J dpp'"
    using sem sem' plain_fields
    unfolding plain_csr_dpp_def Util.replace_def by auto
  have wf': "wf_trs (set (rules dpp'))"
    using CSR_DP_Instantiation_Proc.prems(3) unfolding rules' .
  have fresh': "\<And>f n. \<not> defined (set (rules dpp')) (Sharp f,n)"
    using CSR_DP_Instantiation_Proc.prems(4) unfolding rules' .
  have fin': "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (pairs dpp')) (set (rules dpp'))"
    by (rule CSR_DP_Instantiation_Proc.hyps[OF rec plain' wf' fresh'])
  show ?case by (rule csr_instantiation_proc_finite_sound[
    OF J proc CSR_DP_Instantiation_Proc.prems(3) fin'])
next
  case (CSR_DP_Forward_Instantiation_Proc x1 x2 child)
  from CSR_DP_Forward_Instantiation_Proc.prems(1) have old:
    "isOK (check_muterm_expanded_csr_proof I J \<mu> i dpp
      (CSR_DP_Forward_Instantiation_Proc x1 x2 child))" by simp
  show ?case by (rule check_muterm_expanded_csr_proof_sound[
    OF I J CSR_DP_Forward_Instantiation_Proc.prems(2-4) old])
next
  case (CSR_DP_Redpair_UR_Proc x1 x2 x3 child)
  from CSR_DP_Redpair_UR_Proc.prems(1) have old:
    "isOK (check_muterm_expanded_csr_proof I J \<mu> i dpp
      (CSR_DP_Redpair_UR_Proc x1 x2 x3 child))" by simp
  show ?case by (rule check_muterm_expanded_csr_proof_sound[
    OF I J CSR_DP_Redpair_UR_Proc.prems(2-4) old])
next
  case (CSR_DP_Size_Change_Subterm_Proc x)
  from CSR_DP_Size_Change_Subterm_Proc.prems(1) have old:
    "isOK (check_muterm_expanded_csr_proof I J \<mu> i dpp
      (CSR_DP_Size_Change_Subterm_Proc x))" by simp
  show ?case by (rule check_muterm_expanded_csr_proof_sound[
    OF I J CSR_DP_Size_Change_Subterm_Proc.prems(2-4) old])
qed

theorem check_muterm_typed_dp_proof_sound:
  fixes I :: "('tp,('f::{showl,compare_order,countable},label_type) lab,string) tp_ops"
    and J :: "('dpp,('f,label_type) lab,string) dpp_ops"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and wf: "wf_trs (set R)"
    and fresh: "\<And>f n. \<not> defined (set R) (Sharp f,n)"
    and ok: "isOK (check_muterm_typed_dp_proof I J \<mu> i R S P p)"
  shows "finite_muterm_min_typed_dpp Sharp (mu_of \<mu>)
    (set R) (set P) (set S)"
  using ok
proof (induct p arbitrary: i P)
  case Muterm_Typed_P_Is_Empty
  then have "P = []" by simp
  then have empty: "muterm_min_typed_pair_step Sharp (mu_of \<mu>)
      (set R) (set P) (set S) = {}"
    unfolding muterm_min_typed_pair_step_def by simp
  show ?case unfolding finite_muterm_min_typed_dpp_def empty
    by (rule SN_rel_empty1)
next
  case (Muterm_Typed_Local_Usable U child)
  from Muterm_Typed_Local_Usable.prems have closure_ok:
      "muterm_qcs_ur_closed_check R S U \<mu> P"
    and child_ok:
      "isOK (check_dp_termination_proof I J False
        (add_index i 1) (dpp_ops.mk J False False P [] [] [] U) child)"
    unfolding muterm_qcs_ur_closed_check_def Let_def by auto
  have child_fin: "finite_dpp (False,False,set P,{},{},{},set U)"
  proof -
    have raw: "finite_dpp (dpp_ops.dpp J
      (dpp_ops.mk J False False P [] [] [] U))"
      by (rule check_dp_termination_proof[OF I J child_ok])
    show ?thesis using raw dpp_spec.mk_sound[
      OF J, of False False P "[]" "[]" "[]" U] by simp
  qed
  have closed: "muterm_qcs_ur_closed (set R) (set S) (set U)
      (mu_of \<mu>) (set P)"
    by (rule muterm_qcs_ur_closed_check_sound[OF closure_ok])
  have full: "finite_muterm_typed_dpp Sharp (mu_of \<mu>)
      (set R) (set P) (set S)"
    by (rule finite_muterm_typed_dpp_usable[OF wf fresh closed child_fin])
  show ?case by (rule finite_muterm_typed_imp_finite_min_typed[OF full])
next
  case (Muterm_Typed_General_Usable redp Pr U child)
  let ?d = "dpp_ops.mk J False False P [] [] [] R"
  from Muterm_Typed_General_Usable.prems obtain d' where proc:
      "muterm_general_ur_redpair_proc J \<mu> (get_rel_impl redp)
        Pr U S ?d = return d'"
    and rec: "isOK (check_muterm_typed_dp_proof I J \<mu>
      (add_index i 1) R S (dpp_ops.pairs J d') child)"
    by (auto simp: Let_def)
  have child_fin: "finite_muterm_min_typed_dpp Sharp (mu_of \<mu>)
      (set R) (set (dpp_ops.pairs J d')) (set S)"
    by (rule Muterm_Typed_General_Usable.hyps[OF rec])
  interpret dpp_spec J by fact
  have sem: "dpp ?d = (False,False,set P,{},{},{},set R)"
    using mk_sound[of False False P "[]" "[]" "[]" R] by simp
  have rules_d: "set (rules ?d) = set R"
    using sem dpp_sound[of ?d] rules_sound[of ?d] by auto
  have pairs_d: "set (pairs ?d) = set P"
    using sem dpp_sound[of ?d] pairs_sound[of ?d] by auto
  have d'_def: "d' = delete_pairs ?d Pr"
    using proc unfolding muterm_general_ur_redpair_proc_def
    by (cases "rel_impl.not_wst (get_rel_impl redp)"; auto)
  have rules': "set (rules d') = set (rules ?d)"
    using d'_def delete_P_Pw_sound[of ?d Pr Pr] rules_sound[of d'] by auto
  have child_fin': "finite_muterm_min_typed_dpp Sharp (mu_of \<mu>)
      (set (rules d')) (set (pairs d')) (set S)"
    using child_fin unfolding rules' rules_d .
  have raw: "finite_muterm_min_typed_dpp Sharp (mu_of \<mu>)
      (set (rules ?d)) (set (pairs ?d)) (set S)"
    by (rule muterm_general_ur_redpair_proc_sound[
      OF J get_rel_impl proc _ _ child_fin'])
       (use wf fresh in \<open>simp_all add: rules_d\<close>)
  show ?case using raw unfolding rules_d pairs_d .
next
  case (Muterm_Typed_Pair_Augmentation st sts child)
  let ?d = "dpp_ops.mk J False False P [] [] [] R"
  from Muterm_Typed_Pair_Augmentation.prems obtain d' where proc:
      "csr_instantiation_proc J \<mu> st sts ?d = return d'"
    and sub: "isOK (check_subseteq P (dpp_ops.pairs J d'))"
    and rec: "isOK (check_muterm_typed_dp_proof I J \<mu>
      (add_index i 1) R S (dpp_ops.pairs J d') child)"
    by (auto simp: Let_def)
  have fin': "finite_muterm_min_typed_dpp Sharp (mu_of \<mu>)
      (set R) (set (dpp_ops.pairs J d')) (set S)"
    by (rule Muterm_Typed_Pair_Augmentation.hyps[OF rec])
  from sub have subset: "set P \<subseteq> set (dpp_ops.pairs J d')"
    by (induct P; auto)
  show ?case by (rule finite_muterm_min_typed_dpp_mono_pairs[OF subset fin'])
next
  case (Muterm_Typed_CSR_Proof child)
  let ?d = "dpp_ops.mk J False False P [] [] [] R"
  from Muterm_Typed_CSR_Proof.prems have nc_list:
      "list_all (is_Fun \<circ> snd) P"
    and child_ok: "isOK (check_csr_dp_termination_proof_min
      I J \<mu> False (add_index i 1) ?d child)"
    by (auto simp: Let_def)
  have plain: "plain_csr_dpp J ?d"
    unfolding plain_csr_dpp_def
    using dpp_spec.mk_sound[OF J, of False False P "[]" "[]" "[]" R]
      dpp_spec.dpp_sound[OF J, of ?d]
    by auto
  have rules_d: "set (dpp_ops.rules J ?d) = set R"
    using dpp_spec.mk_sound[OF J, of False False P "[]" "[]" "[]" R]
      dpp_spec.rules_sound[OF J, of ?d]
      dpp_spec.dpp_sound[OF J, of ?d]
    by auto
  have wf_d: "wf_trs (set (dpp_ops.rules J ?d))"
    unfolding rules_d by (rule wf)
  have fresh_d: "\<And>f n.
      \<not> defined (set (dpp_ops.rules J ?d)) (Sharp f,n)"
    unfolding rules_d by (rule fresh)
  have raw: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (dpp_ops.pairs J ?d)) (set (dpp_ops.rules J ?d))"
    by (rule check_csr_dp_termination_proof_min_sound[
      OF I J plain wf_d fresh_d child_ok])
  have sem: "dpp_ops.dpp J ?d =
      (False,False,set P,{},{},{},set R)"
    using dpp_spec.mk_sound[OF J, of False False P "[]" "[]" "[]" R]
    by simp
  have fin: "finite_min_csr_dpp Sharp (mu_of \<mu>) (set P) (set R)"
    using raw sem dpp_spec.pairs_sound[OF J,of ?d]
      dpp_spec.rules_sound[OF J,of ?d]
      dpp_spec.dpp_sound[OF J,of ?d] by auto
  have nc: "\<forall>dp\<in>set P. is_Fun (snd dp)"
    using nc_list by (simp add: list_all_iff)
  show ?case
    by (rule finite_min_csr_dpp_imp_finite_muterm_min_typed_noncollapsing[
      OF nc fin])
next
  case (Muterm_Typed_Expanded_CSR_Proof child)
  let ?E = "muterm_expanded_pairs_list string_renameN P S"
  let ?d = "dpp_ops.mk J False False ?E [] [] [] R"
  from Muterm_Typed_Expanded_CSR_Proof.prems have child_ok:
      "isOK (check_muterm_expanded_csr_proof
        I J \<mu> (add_index i 1) ?d child)"
    by (simp add: Let_def)
  have plain: "plain_csr_dpp J ?d"
    unfolding plain_csr_dpp_def
    using dpp_spec.mk_sound[OF J, of False False ?E "[]" "[]" "[]" R]
      dpp_spec.dpp_sound[OF J, of ?d]
    by auto
  have rules_d: "set (dpp_ops.rules J ?d) = set R"
    using dpp_spec.mk_sound[OF J, of False False ?E "[]" "[]" "[]" R]
      dpp_spec.rules_sound[OF J, of ?d]
      dpp_spec.dpp_sound[OF J, of ?d]
    by auto
  have wf_d: "wf_trs (set (dpp_ops.rules J ?d))"
    unfolding rules_d by (rule wf)
  have fresh_d: "\<And>f n.
      \<not> defined (set (dpp_ops.rules J ?d)) (Sharp f,n)"
    unfolding rules_d by (rule fresh)
  have raw: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (dpp_ops.pairs J ?d)) (set (dpp_ops.rules J ?d))"
    by (rule check_muterm_expanded_csr_proof_sound[
      OF I J plain wf_d fresh_d child_ok])
  have sem: "dpp_ops.dpp J ?d =
      (False,False,set ?E,{},{},{},set R)"
    using dpp_spec.mk_sound[OF J, of False False ?E "[]" "[]" "[]" R]
    by simp
  have fin: "finite_min_csr_dpp Sharp (mu_of \<mu>) (set ?E) (set R)"
    using raw sem dpp_spec.pairs_sound[OF J,of ?d]
      dpp_spec.rules_sound[OF J,of ?d]
      dpp_spec.dpp_sound[OF J,of ?d] by auto
  have fin': "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (muterm_expanded_pairs string_renameN (set P) (set S)) (set R)"
    using fin set_muterm_expanded_pairs_list[of string_renameN P S] by simp
  show ?case
    by (rule finite_min_csr_dpp_expanded_imp_finite_muterm_min_typed[OF fin'])
next
  case (Muterm_Typed_Expanded_Extended_Basic_CSR_Proof child)
  then show ?case by simp
next
  case (Muterm_Typed_Expanded_Local_Usable U child)
  let ?E = "muterm_expanded_pairs_list string_renameN P S"
  from Muterm_Typed_Expanded_Local_Usable.prems have closure_ok:
      "muterm_qcs_expanded_ur_closed_check R S U \<mu> P"
    and child_ok:
      "isOK (check_dp_termination_proof I J False (add_index i 1)
        (dpp_ops.mk J False False ?E [] [] [] U) child)"
    unfolding muterm_qcs_expanded_ur_closed_check_def Let_def by auto
  have raw: "finite_dpp (False,False,set ?E,{},{},{},set U)"
  proof -
    have "finite_dpp (dpp_ops.dpp J
      (dpp_ops.mk J False False ?E [] [] [] U))"
      by (rule check_dp_termination_proof[OF I J child_ok])
    then show ?thesis using dpp_spec.mk_sound[
      OF J, of False False ?E "[]" "[]" "[]" U] by simp
  qed
  have fin: "finite_dpp (False,False,
      muterm_expanded_pairs string_renameN (set P) (set S),{},{},{},set U)"
    using raw by (simp only:
      set_muterm_expanded_pairs_list[of string_renameN P S])
  have closed: "muterm_qcs_expanded_ur_closed (set R) (set S) (set U)
      (mu_of \<mu>) (set P)"
    by (rule muterm_qcs_expanded_ur_closed_check_sound[OF closure_ok])
  have full: "finite_muterm_typed_dpp Sharp (mu_of \<mu>)
      (set R) (set P) (set S)"
    by (rule finite_muterm_typed_dpp_expanded_usable[
      OF wf fresh closed fin])
  show ?case by (rule finite_muterm_typed_imp_finite_min_typed[OF full])
next
  case (Muterm_Typed_Expanded_Strong_Usable U redp Pr child)
  let ?E = "muterm_expanded_pairs_list string_renameN P S"
  let ?d = "dpp_ops.mk J False False ?E [] [] [] R"
  from Muterm_Typed_Expanded_Strong_Usable.prems
  obtain d' where proc:
      "muterm_strong_ur_redpair_proc J \<mu> (get_rel_impl redp) Pr U ?d = return d'"
    and child_ok: "isOK (check_csr_dp_termination_proof_min I J \<mu> False
      (add_index i 1) d' child)" by (auto simp: Let_def)
  have d': "d' = dpp_spec.delete_pairs J ?d Pr"
    using proc unfolding muterm_strong_ur_redpair_proc_def by auto
  have plain: "plain_csr_dpp J ?d"
    unfolding plain_csr_dpp_def
    using dpp_spec.mk_sound[OF J,of False False ?E "[]" "[]" "[]" R]
      dpp_spec.dpp_sound[OF J,of ?d] by auto
  have plain': "plain_csr_dpp J d'"
    unfolding d' by (rule plain_csr_dpp_delete_pairs[OF J plain])
  interpret dpp_spec J by fact
  have rules_d: "set (rules ?d) = set R"
    using mk_sound[of False False ?E "[]" "[]" "[]" R]
      rules_sound[of ?d] dpp_sound[of ?d] by auto
  have rules': "set (rules d') = set (rules ?d)"
    using d' delete_P_Pw_sound[of ?d Pr Pr] rules_sound[of d'] by auto
  have wf_d: "wf_trs (set (rules ?d))" using wf unfolding rules_d .
  have fresh_d: "\<And>f n. \<not> defined (set (rules ?d)) (Sharp f,n)"
    using fresh unfolding rules_d .
  have wf': "wf_trs (set (rules d'))" using wf_d unfolding rules' .
  have fresh': "\<And>f n. \<not> defined (set (rules d')) (Sharp f,n)"
    using fresh_d unfolding rules' .
  have child_fin: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (pairs d')) (set (rules d'))"
    by (rule check_csr_dp_termination_proof_min_sound[
      OF I J plain' wf' fresh' child_ok])
  have fin: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (pairs ?d)) (set (rules ?d))"
    by (rule muterm_strong_ur_redpair_proc_sound[
      OF J get_rel_impl proc wf_d fresh_d child_fin])
  have sem: "dpp_ops.dpp J ?d =
      (False,False,set ?E,{},{},{},set R)"
    using mk_sound[of False False ?E "[]" "[]" "[]" R] by simp
  have expanded_fin: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (muterm_expanded_pairs string_renameN (set P) (set S)) (set R)"
    using fin sem pairs_sound[of ?d] rules_sound[of ?d] dpp_sound[of ?d]
      set_muterm_expanded_pairs_list[of string_renameN P S] by auto
  show ?case
    by (rule finite_min_csr_dpp_expanded_imp_finite_muterm_min_typed[
      OF expanded_fin])
next
  case (Muterm_Typed_Expanded_Ordinary child)
  let ?E = "muterm_expanded_pairs_list string_renameN P S"
  from Muterm_Typed_Expanded_Ordinary.prems have child_ok:
      "isOK (check_dp_termination_proof I J False (add_index i 1)
        (dpp_ops.mk J False False ?E [] [] [] R) child)"
    by (simp add: Let_def)
  have raw: "finite_dpp (False,False,set ?E,{},{},{},set R)"
  proof -
    have "finite_dpp (dpp_ops.dpp J
      (dpp_ops.mk J False False ?E [] [] [] R))"
      by (rule check_dp_termination_proof[OF I J child_ok])
    then show ?thesis using dpp_spec.mk_sound[
      OF J, of False False ?E "[]" "[]" "[]" R] by simp
  qed
  have fin: "finite_dpp (False,False,
      muterm_expanded_pairs string_renameN (set P) (set S),{},{},{},
      set R)"
    using raw set_muterm_expanded_pairs_list[of string_renameN P S]
    by simp
  have full: "finite_muterm_typed_dpp Sharp (mu_of \<mu>)
      (set R) (set P) (set S)"
    by (rule finite_muterm_typed_dpp_expanded_ordinary[OF fin])
  show ?case by (rule finite_muterm_typed_imp_finite_min_typed[OF full])
next
  case (Muterm_Typed_Dep_Graph edps)
  from Muterm_Typed_Dep_Graph.prems have graph_ok:
      "isOK (check_muterm_typed_dep_graph \<mu> R S P edps)"
    and components_ok: "isOK (check_muterm_typed_graph_components
      I J \<mu> i R S P edps)"
    by (auto simp: Let_def)
  show ?case
  proof (rule check_muterm_min_typed_dep_graph_sound[OF graph_ok])
    fix p C
    assume mem: "(Some p,C) \<in> set edps"
    from check_muterm_typed_graph_components_member[OF components_ok mem]
    obtain j where rec: "isOK (check_muterm_typed_dp_proof I J \<mu> j R S
      (filter (\<lambda>dp. dp \<in> set C) P) p)" by blast
    have set_filter: "set (filter (\<lambda>dp. dp \<in> set C) P) =
      set P \<inter> set C" by auto
    show "finite_muterm_min_typed_dpp Sharp (mu_of \<mu>) (set R)
      (set P \<inter> set C) (set S)"
      unfolding set_filter[symmetric]
      apply (rule Muterm_Typed_Dep_Graph.hyps)
       apply (rule mem)
      apply simp
      apply simp
      apply (rule rec)
      done
  qed
qed

(* Obsolete expanded extended-basic compatibility path.  Keeping this source
   commented documents the rejected representation without making production
   checker builds depend on the expensive experimental theory. *)
(*
fun check_muterm_typed_dp_proof_production where
  "check_muterm_typed_dp_proof_production I J \<mu> i R S P
      (Muterm_Typed_Expanded_Extended_Basic_CSR_Proof prf) =
    debug i (STR ''expanded typed extended-basic MU-TERM CSR component'') (do {
      let E = muterm_expanded_pairs_list string_renameN P S;
      let dpp = dpp_ops.mk J False False E [] [] [] R;
      check_muterm_expanded_extended_basic_proof I J \<mu>
        (add_index i 1) dpp prf
    })"
| "check_muterm_typed_dp_proof_production I J \<mu> i R S P prf =
    check_muterm_typed_dp_proof I J \<mu> i R S P prf"

(* Superseded by the depth-induction formulation below. *)
(*
theorem check_muterm_typed_dp_proof_production_sound:
  fixes I :: "('tp,('f::{showl,compare_order,countable},label_type) lab,string) tp_ops"
    and J :: "('dpp,('f,label_type) lab,string) dpp_ops"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and wf: "wf_trs (set R)"
    and fresh: "\<And>f n. \<not> defined (set R) (Sharp f,n)"
    and ok: "isOK (check_muterm_typed_dp_proof_production
      I J \<mu> i R S P p)"
  shows "finite_muterm_min_typed_dpp Sharp (mu_of \<mu>)
    (set R) (set P) (set S)"
proof (cases "\<exists>prf. p =
    Muterm_Typed_Expanded_Extended_Basic_CSR_Proof prf")
  case True
  then show ?thesis
  proof (elim exE)
    fix q
    assume p_eq:
      "p = Muterm_Typed_Expanded_Extended_Basic_CSR_Proof q"
    let ?E = "muterm_expanded_pairs_list string_renameN P S"
    let ?d = "dpp_ops.mk J False False ?E [] [] [] R"
    from ok p_eq have child_ok:
      "isOK (check_muterm_expanded_extended_basic_proof I J \<mu>
        (add_index i 1) ?d q)" by (simp add: Let_def)
    have plain: "plain_csr_dpp J ?d"
      unfolding plain_csr_dpp_def
      using dpp_spec.mk_sound[OF J,of False False ?E "[]" "[]" "[]" R]
        dpp_spec.dpp_sound[OF J,of ?d] by auto
    interpret dpp_spec J by fact
    have sem: "dpp ?d = (False,False,set ?E,{},{},{},set R)"
      using mk_sound[of False False ?E "[]" "[]" "[]" R] by simp
    have rules: "set (rules ?d) = set R"
      using sem rules_sound[of ?d] dpp_sound[of ?d] by auto
    have wf_d: "wf_trs (set (rules ?d))"
      using wf unfolding rules .
    have fresh_d: "\<And>f n. \<not> defined (set (rules ?d)) (Sharp f,n)"
      using fresh unfolding rules .
    have raw: "finite_min_csr_dpp Sharp (mu_of \<mu>)
        (set (pairs ?d)) (set (rules ?d))"
      by (rule check_muterm_expanded_extended_basic_proof_sound[
        OF I J plain wf_d fresh_d child_ok])
    have expanded: "finite_min_csr_dpp Sharp (mu_of \<mu>)
        (muterm_expanded_pairs string_renameN (set P) (set S)) (set R)"
      using raw sem pairs_sound[of ?d] rules_sound[of ?d] dpp_sound[of ?d]
        set_muterm_expanded_pairs_list[of string_renameN P S] by auto
    show ?thesis
      by (rule finite_min_csr_dpp_expanded_imp_finite_muterm_min_typed[
        OF expanded])
  qed
next
  case False
  from ok False have old:
    "isOK (check_muterm_typed_dp_proof I J \<mu> i R S P p)"
    by (cases p; simp)
  show ?thesis by (rule check_muterm_typed_dp_proof_sound[
    OF I J wf fresh old])
qed
*)
*)

text \<open>
  The semantic MU-TERM development lives in locale @{locale muterm_i4}, whose
  sole assumption is well-formedness of the source TRS.  Definitions made in
  that locale consequently acquire conditional code equations.  The checker
  has already established well-formedness, but Isabelle's code generator does
  not discharge locale premises while extracting a caller.  Keep an explicit,
  unconditional executable presentation here and relate it definitionally to
  the locale operations below.  This is an extraction bridge only: the
  soundness proof continues to use the locale processor.
\<close>

fun muterm_unmarked_term_check_exec where
  "muterm_unmarked_term_check_exec (Var x) = True"
| "muterm_unmarked_term_check_exec (Fun f ts) =
    (\<not> is_sharp_lab f \<and> list_all muterm_unmarked_term_check_exec ts)"

definition muterm_i4_mu_exec where
  "muterm_i4_mu_exec \<mu> fn =
    (if is_sharp_lab (fst fn) then {0..<snd fn} else \<mu> fn)"

fun muterm_i4_symbolically_covered_exec where
  "muterm_i4_symbolically_covered_exec \<mu> \<Delta> E (Var x) = True"
| "muterm_i4_symbolically_covered_exec \<mu> \<Delta> E (Fun f ts) =
    ((is_sharp_lab f \<or>
      (muterm_unmarked_term_check_exec (Fun f ts) \<and>
       ((f,length ts) \<in> \<Delta> \<or> Fun f ts \<in> E))) \<and>
     (\<forall>i<length ts. i \<in> muterm_i4_mu_exec \<mu> (f,length ts) \<longrightarrow>
       muterm_i4_symbolically_covered_exec \<mu> \<Delta> E (ts ! i)))"

definition muterm_no_bridge_matches_exec where
  "muterm_no_bridge_matches_exec B q \<longleftrightarrow>
    (\<forall>(a,b)\<in>set B. \<not> matches q a)"

definition muterm_root_pair_selects_or_ground_blocked_exec where
  "muterm_root_pair_selects_or_ground_blocked_exec Rs \<mu> \<Delta> B f i ts lr \<longleftrightarrow>
    (case lr of (l,r) \<Rightarrow> case l of
      Var x \<Rightarrow> False
    | Fun h ls \<Rightarrow> (case h of
        Sharp g \<Rightarrow> if g \<noteq> f then True else
          (case r of
            Fun k rs \<Rightarrow> False
          | Var y \<Rightarrow>
              (i < length ls \<and> ls ! i = Var y) \<or>
              (\<exists>j<length ls. j < length ts \<and>
                j \<notin> csr_dp_root_mu \<mu> (Sharp f,length ts) \<and>
                ls ! j = Var y \<and> ground (ts ! j) \<and>
                muterm_no_bridge_matches_exec B (ts ! j)))
      | _ \<Rightarrow> False))"

definition muterm_root_successors_select_or_block_check_exec where
  "muterm_root_successors_select_or_block_check_exec Rs \<mu> \<Delta> P B f i ts =
    list_all
      (muterm_root_pair_selects_or_ground_blocked_exec Rs \<mu> \<Delta> B f i ts) P"

definition muterm_recursive_pair_safe_check_exec where
  "muterm_recursive_pair_safe_check_exec Rs \<mu> \<Delta> P B lr \<longleftrightarrow>
    (case lr of (l,r) \<Rightarrow> case l of
      Var x \<Rightarrow> False
    | Fun h ls \<Rightarrow> (case h of
        Sharp k \<Rightarrow>
          muterm_i4_symbolically_covered_exec \<mu> \<Delta> {} l \<and>
          vars_term r \<subseteq> vars_term l \<and>
          (case r of
            Var y \<Rightarrow> True
          | Fun q ts \<Rightarrow> (case q of
              Sharp f \<Rightarrow>
                muterm_i4_symbolically_covered_exec \<mu> \<Delta> {} r \<or>
                list_ex (\<lambda>(i,v). case v of
                    Var z \<Rightarrow> False
                  | Fun g us \<Rightarrow> (case us of
                      [u] \<Rightarrow>
                        i \<notin> csr_dp_root_mu \<mu> (Sharp f,length ts) \<and>
                        (g,1) \<notin> set (defined_list Rs) \<and>
                        muterm_i4_symbolically_covered_exec \<mu> \<Delta> {u} r \<and>
                        muterm_root_successors_select_or_block_check_exec
                          Rs \<mu> \<Delta> P B f i ts
                    | _ \<Rightarrow> False))
                  (zip [0..<length ts] ts)
            | _ \<Rightarrow> False))
      | _ \<Rightarrow> False))"

definition muterm_recursive_pairs_safe_check_exec where
  "muterm_recursive_pairs_safe_check_exec Rs \<mu> \<Delta> P B =
    list_all (muterm_recursive_pair_safe_check_exec Rs \<mu> \<Delta> P B) P"

definition muterm_recursive_bridges_safe_check_exec where
  "muterm_recursive_bridges_safe_check_exec Ds \<mu> \<Delta> B = list_all (\<lambda>lr.
    vars_term (snd lr) \<subseteq> vars_term (fst lr) \<and>
    (muterm_i4_symbolically_covered_exec \<mu> \<Delta> {fst lr} (fst lr) \<or>
      (case fst lr of
        Var x \<Rightarrow> False
      | Fun f ts \<Rightarrow> (case ts of
          [u] \<Rightarrow> (f,1) \<notin> set Ds \<and>
            muterm_i4_symbolically_covered_exec \<mu> \<Delta> {u} (fst lr)
        | _ \<Rightarrow> False))) \<and>
    muterm_i4_symbolically_covered_exec \<mu> \<Delta> {} (snd lr)) B"

definition muterm_recursive_target_shape_check_exec where
  "muterm_recursive_target_shape_check_exec P B =
    (list_all (\<lambda>lr. case snd lr of
        Var x \<Rightarrow> True
      | Fun h ts \<Rightarrow> (case h of
          Sharp f \<Rightarrow> \<not> is_sharp_lab f \<and>
            list_all muterm_unmarked_term_check_exec ts
        | _ \<Rightarrow> False)) P \<and>
     list_all (\<lambda>lr. case snd lr of
        Var x \<Rightarrow> False
      | Fun h ts \<Rightarrow> (case h of
          Sharp f \<Rightarrow> \<not> is_sharp_lab f \<and>
            list_all muterm_unmarked_term_check_exec ts
        | _ \<Rightarrow> False)) B)"

fun muterm_i4_mu_vars_term_list_exec where
  "muterm_i4_mu_vars_term_list_exec \<mu> (Var x) = [x]"
| "muterm_i4_mu_vars_term_list_exec \<mu> (Fun f ts) = concat (map
    (\<lambda>i. muterm_i4_mu_vars_term_list_exec \<mu> (ts ! i))
    [i <- [0..<length ts]. is_sharp_lab f \<or> i \<in> \<mu> (f,length ts)])"

fun muterm_i4_non_mu_vars_term_list_exec where
  "muterm_i4_non_mu_vars_term_list_exec \<mu> (Var x) = []"
| "muterm_i4_non_mu_vars_term_list_exec \<mu> (Fun f ts) = concat (map
    (\<lambda>i. if is_sharp_lab f \<or> i \<in> \<mu> (f,length ts)
      then muterm_i4_non_mu_vars_term_list_exec \<mu> (ts ! i)
      else vars_term_list (ts ! i)) [0..<length ts])"

definition muterm_i4_partition_check_exec where
  "muterm_i4_partition_check_exec \<mu> t =
    (set (muterm_i4_mu_vars_term_list_exec \<mu> t) \<inter>
      set (muterm_i4_non_mu_vars_term_list_exec \<mu> t) = {})"

definition muterm_i4_full_check_exec where
  "muterm_i4_full_check_exec \<mu> t = list_all
    (\<lambda>x. x \<in> set (muterm_i4_mu_vars_term_list_exec \<mu> t))
    (vars_term_list t)"

definition muterm_recursive_i4_shape_check_exec where
  "muterm_recursive_i4_shape_check_exec \<mu> P B =
    (list_all (\<lambda>lr.
       muterm_i4_partition_check_exec \<mu> (fst lr) \<and>
       muterm_i4_full_check_exec \<mu> (fst lr) \<and>
       (is_Var (snd lr) \<or>
        (muterm_i4_partition_check_exec \<mu> (snd lr) \<and>
         muterm_i4_full_check_exec \<mu> (snd lr)))) P \<and>
     list_all (\<lambda>lr.
       muterm_i4_partition_check_exec \<mu> (fst lr) \<and>
       muterm_i4_partition_check_exec \<mu> (snd lr) \<and>
       muterm_i4_full_check_exec \<mu> (snd lr) \<and>
       list_all (\<lambda>x. x \<in>
          set (muterm_i4_mu_vars_term_list_exec \<mu> (fst lr)))
         (muterm_i4_mu_vars_term_list_exec \<mu> (snd lr))) B)"

definition muterm_recursive_rta08_ur_redpair_proc_exec where
  "muterm_recursive_rta08_ur_redpair_proc_exec Rs \<mu> \<Delta> J m rp Premove U B dpp =
    check_return (do {
      rel_impl_redpair rp;
      let (ps,pns) = dpp_ops.split_pairs J dpp Premove;
      let T = dpp_ops.pairs J dpp @ B @ U;
      check (muterm_innermost_ur_closed_check
          (dpp_ops.rules J dpp) U m T)
        (showsl_lit (STR ''recursive MU-TERM usable-rule closure failed''));
      check (muterm_strongly_conservative_check m U)
        (showsl_lit (STR ''recursive MU-TERM strong-conservativity check failed''));
      check (list_all (is_Fun \<circ> fst) T)
        (showsl_lit (STR ''recursive MU-TERM rule has a variable left-hand side''));
      check (muterm_recursive_pairs_safe_check_exec Rs \<mu> \<Delta>
          (dpp_ops.pairs J dpp) B)
        (showsl_lit (STR ''recursive MU-TERM pair safety check failed''));
      check (muterm_recursive_bridges_safe_check_exec
          (defined_list Rs) \<mu> \<Delta> B)
        (showsl_lit (STR ''recursive MU-TERM unhiding safety check failed''));
      check (muterm_recursive_target_shape_check_exec (dpp_ops.pairs J dpp) B)
        (showsl_lit (STR ''recursive MU-TERM target-shape check failed''));
      check (muterm_recursive_i4_shape_check_exec \<mu> (dpp_ops.pairs J dpp) B)
        (showsl_lit (STR ''recursive MU-TERM interpretation-shape check failed''));
      check (muterm_marked_mu_equal_check m)
        (showsl_lit (STR ''marked replacement-map entries differ from source symbols''));
      rel_impl.ce_compat rp;
      rel_impl_ns rp (U @ B @ pns)
        <+? (\<lambda>s. showsl_lit
          (STR ''problem weakly orienting recursive MU-TERM rules, unhiding rules, or pairs\<newline>'' ) \<circ> s);
      rel_impl_s rp ps
        <+? (\<lambda>s. showsl_lit
          (STR ''problem strictly orienting recursive MU-TERM pairs\<newline>'' ) \<circ> s)
    }) (dpp_spec.delete_pairs J dpp Premove)"

context muterm_i4
begin

lemma muterm_unmarked_term_check_exec_eq:
  "muterm_unmarked_term_check_exec t = muterm_unmarked_term_check t"
  by (induct t; simp add: list_all_iff)

lemma muterm_i4_mu_exec_eq:
  "muterm_i4_mu_exec \<mu> fn = i4_mu fn"
  unfolding muterm_i4_mu_exec_def i4_mu_def by simp

lemma muterm_i4_symbolically_covered_exec_eq:
  "muterm_i4_symbolically_covered_exec \<mu> \<Delta> E t =
    i4_symbolically_covered E t"
  by (induct t arbitrary: E; simp add: muterm_i4_mu_exec_eq
      muterm_unmarked_term_check_exec_eq muterm_unmarked_term_check_sound)

lemma muterm_no_bridge_matches_exec_eq:
  "muterm_no_bridge_matches_exec B q = muterm_no_bridge_matches B q"
  unfolding muterm_no_bridge_matches_exec_def muterm_no_bridge_matches_def by simp

lemma muterm_root_pair_selects_or_ground_blocked_exec_eq:
  "muterm_root_pair_selects_or_ground_blocked_exec Rs \<mu> \<Delta> B f i ts lr =
    muterm_root_pair_selects_or_ground_blocked B f i ts lr"
  unfolding muterm_root_pair_selects_or_ground_blocked_exec_def
    muterm_root_pair_selects_or_ground_blocked_def
  by (simp add: muterm_no_bridge_matches_exec_eq split: prod.splits term.splits lab.splits)

lemma muterm_root_successors_select_or_block_check_exec_eq:
  "muterm_root_successors_select_or_block_check_exec Rs \<mu> \<Delta> P B f i ts =
    muterm_root_successors_select_or_block_check P B f i ts"
  unfolding muterm_root_successors_select_or_block_check_exec_def
    muterm_root_successors_select_or_block_check_def
  by (simp add: list_all_iff
      muterm_root_pair_selects_or_ground_blocked_exec_eq)

lemma muterm_recursive_pair_safe_check_exec_eq:
  "muterm_recursive_pair_safe_check_exec Rs \<mu> \<Delta> P B lr =
    muterm_recursive_pair_safe_check P B lr"
  unfolding muterm_recursive_pair_safe_check_exec_def
    muterm_recursive_pair_safe_check_def
  by (simp add: list_ex_iff set_defined_list muterm_i4_mu_exec_eq
      muterm_i4_symbolically_covered_exec_eq
      muterm_root_successors_select_or_block_check_exec_eq
      split: prod.splits term.splits lab.splits list.splits)

lemma muterm_recursive_pairs_safe_check_exec_eq:
  "muterm_recursive_pairs_safe_check_exec Rs \<mu> \<Delta> P B =
    muterm_recursive_pairs_safe_check P B"
  unfolding muterm_recursive_pairs_safe_check_exec_def
    muterm_recursive_pairs_safe_check_def
  by (simp add: list_all_iff muterm_recursive_pair_safe_check_exec_eq)

lemma muterm_recursive_bridges_safe_check_exec_eq:
  "muterm_recursive_bridges_safe_check_exec (defined_list Rs) \<mu> \<Delta> B =
    muterm_recursive_bridges_safe_check B"
  unfolding muterm_recursive_bridges_safe_check_exec_def
    muterm_recursive_bridges_safe_check_def
  by (simp add: muterm_i4_symbolically_covered_exec_eq
      muterm_i4_mu_exec_eq muterm_unmarked_term_check_exec_eq
      muterm_unmarked_term_check_sound set_defined_list
      split: term.splits list.splits)

lemma muterm_recursive_target_shape_check_exec_eq:
  "muterm_recursive_target_shape_check_exec P B =
    muterm_recursive_target_shape_check P B"
  unfolding muterm_recursive_target_shape_check_exec_def
    muterm_recursive_target_shape_check_def
  by (simp add: list_all_iff muterm_unmarked_term_check_exec_eq
      split: term.splits lab.splits)

lemma muterm_i4_mu_vars_term_list_exec_eq:
  "muterm_i4_mu_vars_term_list_exec \<mu> t = muterm_i4_mu_vars_term_list t"
proof (induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  let ?is = "[i <- [0..<length ts].
    is_sharp_lab f \<or> i \<in> \<mu> (f,length ts)]"
  have mapped: "map
      (\<lambda>i. muterm_i4_mu_vars_term_list_exec \<mu> (ts ! i)) ?is =
      map (\<lambda>i. muterm_i4_mu_vars_term_list (ts ! i)) ?is"
  proof (rule map_cong)
    show "?is = ?is" by simp
    fix i
    assume i: "i \<in> set ?is"
    then have ilt: "i < length ts" by simp
    show "muterm_i4_mu_vars_term_list_exec \<mu> (ts ! i) =
        muterm_i4_mu_vars_term_list (ts ! i)"
      by (rule Fun.hyps[OF nth_mem[OF ilt]])
  qed
  show ?case
    by (simp only: muterm_i4_mu_vars_term_list_exec.simps
        muterm_i4_mu_vars_term_list.simps, rule arg_cong[OF mapped])
qed

lemma muterm_i4_non_mu_vars_term_list_exec_eq:
  "muterm_i4_non_mu_vars_term_list_exec \<mu> t =
    muterm_i4_non_mu_vars_term_list t"
proof (induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  have mapped: "map
      (\<lambda>i. if is_sharp_lab f \<or> i \<in> \<mu> (f,length ts)
        then muterm_i4_non_mu_vars_term_list_exec \<mu> (ts ! i)
        else vars_term_list (ts ! i)) [0..<length ts] =
      map
      (\<lambda>i. if is_sharp_lab f \<or> i \<in> \<mu> (f,length ts)
        then muterm_i4_non_mu_vars_term_list (ts ! i)
        else vars_term_list (ts ! i)) [0..<length ts]"
  proof (rule map_cong)
    show "[0..<length ts] = [0..<length ts]" by simp
    fix i
    assume i: "i \<in> set [0..<length ts]"
    then have ilt: "i < length ts" by simp
    have ih: "muterm_i4_non_mu_vars_term_list_exec \<mu> (ts ! i) =
        muterm_i4_non_mu_vars_term_list (ts ! i)"
      by (rule Fun.hyps[OF nth_mem[OF ilt]])
    show "(if is_sharp_lab f \<or> i \<in> \<mu> (f,length ts)
          then muterm_i4_non_mu_vars_term_list_exec \<mu> (ts ! i)
          else vars_term_list (ts ! i)) =
        (if is_sharp_lab f \<or> i \<in> \<mu> (f,length ts)
          then muterm_i4_non_mu_vars_term_list (ts ! i)
          else vars_term_list (ts ! i))"
      using ih by simp
  qed
  show ?case
    by (simp only: muterm_i4_non_mu_vars_term_list_exec.simps
        muterm_i4_non_mu_vars_term_list.simps, rule arg_cong[OF mapped])
qed

lemma muterm_recursive_i4_shape_check_exec_eq:
  "muterm_recursive_i4_shape_check_exec \<mu> P B =
    muterm_recursive_i4_shape_check P B"
  unfolding muterm_recursive_i4_shape_check_exec_def
    muterm_recursive_i4_shape_check_def muterm_i4_partition_check_exec_def
    muterm_i4_partition_check_def muterm_i4_full_check_exec_def
    muterm_i4_full_check_def
  by (simp add: muterm_i4_mu_vars_term_list_exec_eq
      muterm_i4_non_mu_vars_term_list_exec_eq)

lemma muterm_recursive_rta08_ur_redpair_proc_exec_eq:
  "muterm_recursive_rta08_ur_redpair_proc_exec Rs \<mu> \<Delta>
      J m rp Premove U B dpp =
    muterm_recursive_rta08_ur_redpair_proc J m rp Premove U B dpp"
  unfolding muterm_recursive_rta08_ur_redpair_proc_exec_def
    muterm_recursive_rta08_ur_redpair_proc_def
  by (simp add: muterm_recursive_pairs_safe_check_exec_eq
      muterm_recursive_bridges_safe_check_exec_eq
      muterm_recursive_target_shape_check_exec_eq
      muterm_recursive_i4_shape_check_exec_eq)

end

fun check_muterm_recursive_dp_proof where
  "check_muterm_recursive_dp_proof J m i R B U P P_is_Empty =
    check (P = [])
      (i \<circ> showsl_lit (STR '': recursive MU-TERM pairs are not empty''))"
| "check_muterm_recursive_dp_proof J m i R B U P
      (Redpair_Proc redp Pr child) =
    debug i (STR ''recursive MU-TERM reduction pair'') (do {
      let dpp = dpp_ops.mk J False False P [] [] [] R;
      dpp' \<leftarrow> muterm_recursive_rta08_ur_redpair_proc_exec
        (dpp_ops.rules J dpp) (mu_of m)
        (csr_u3_delta (set (dpp_ops.rules J dpp)) (set U)) J m
        (get_rel_impl redp) Pr U B dpp;
      check_muterm_recursive_dp_proof J m (add_index i 1) R B U
        (dpp_ops.pairs J dpp') child
    })"
| "check_muterm_recursive_dp_proof J m i R B U P
      (Dep_Graph_Proc edps) =
    debug i (STR ''terminal recursive MU-TERM dependency graph'') (do {
      check_muterm_typed_dep_graph m R B P edps;
      check (list_all (\<lambda>(po,C). po = None) edps)
        (i \<circ> showsl_lit
          (STR '': recursive MU-TERM graph has a nonterminal component''))
    })"
| "check_muterm_recursive_dp_proof J m i R B U P child =
    error (i \<circ> showsl_lit
      (STR '': unsupported processor in recursive MU-TERM continuation''))"

fun muterm_recursive_proof_depth where
  "muterm_recursive_proof_depth (Redpair_Proc _ _ child) =
    Suc (muterm_recursive_proof_depth child)"
| "muterm_recursive_proof_depth _ = 0"

lemma check_muterm_recursive_redpair_step_sound:
  fixes J :: "('dpp,('f::{showl,compare_order},label_type) lab,string) dpp_ops"
  assumes J: "dpp_spec J"
    and wf: "wf_trs (set R)"
    and overlay: "csr_switch_overlay (set R)"
    and exact: "set B = set (muterm_exact_unhiding_rules_list Sharp m D R)"
    and fresh: "\<And>h n. \<not> defined (set R) (Sharp h,n)"
    and rules_unmarked: "\<And>fn. fn \<in> funas_trs (set R) \<Longrightarrow>
      \<not> is_sharp_lab (fst fn)"
    and marked: "\<And>f n. \<not> is_sharp_lab f \<Longrightarrow>
      mu_of m (Sharp f,n) = mu_of m (f,n)"
    and proc: "muterm_recursive_rta08_ur_redpair_proc_exec
      (dpp_ops.rules J (dpp_ops.mk J False False P [] [] [] R)) (mu_of m)
      (csr_u3_delta
        (set (dpp_ops.rules J (dpp_ops.mk J False False P [] [] [] R)))
        (set U)) J m (get_rel_impl redp) Pr U B
      (dpp_ops.mk J False False P [] [] [] R) = return d'"
    and child_fin: "muterm_i4.finite_muterm_i4_good_typed_dpp
      R (mu_of m) (set (dpp_ops.pairs J d')) (set B)"
  shows "muterm_i4.finite_muterm_i4_good_typed_dpp
    R (mu_of m) (set P) (set B)"
proof -
  let ?d = "dpp_ops.mk J False False P [] [] [] R"
  interpret ds: dpp_spec J by (rule J)
  have sem: "dpp_ops.dpp J ?d =
      (False,False,set P,{},{},{},set R)"
    using dpp_spec.mk_sound[OF J, of False False P "[]" "[]" "[]" R]
    by simp
  have rules_d: "set (dpp_ops.rules J ?d) = set R"
    using sem dpp_spec.dpp_sound[OF J, of ?d]
      dpp_spec.rules_sound[OF J, of ?d] by auto
  have pairs_d: "set (dpp_ops.pairs J ?d) = set P"
    using sem dpp_spec.dpp_sound[OF J, of ?d]
      dpp_spec.pairs_sound[OF J, of ?d] by auto
  interpret M0: muterm_i4 R "mu_of m"
      "csr_u3_delta (set R) (set U)" "undefined"
    by (unfold_locales, rule wf)
  have wf_d: "wf_trs (set (dpp_ops.rules J ?d))"
    using wf rules_d by simp
  interpret M1: muterm_i4 "dpp_ops.rules J ?d" "mu_of m"
      "csr_u3_delta (set (dpp_ops.rules J ?d)) (set U)" "undefined"
    by (unfold_locales, rule wf_d)
  have proc_locale: "M1.muterm_recursive_rta08_ur_redpair_proc
      J m (get_rel_impl redp) Pr U B ?d = return d'"
  proof -
    have eq: "M1.muterm_recursive_rta08_ur_redpair_proc
        J m (get_rel_impl redp) Pr U B ?d =
      muterm_recursive_rta08_ur_redpair_proc_exec
        (dpp_ops.rules J ?d) (mu_of m)
        (csr_u3_delta (set (dpp_ops.rules J ?d)) (set U))
        J m (get_rel_impl redp) Pr U B ?d"
      by (rule sym, rule M1.muterm_recursive_rta08_ur_redpair_proc_exec_eq)
    show ?thesis by (subst eq, rule proc)
  qed
  obtain ps pns where split:
      "dpp_ops.split_pairs J ?d Pr = (ps,pns)" by force
  have deleted: "d' = dpp_ops.delete_P_Pw J ?d Pr Pr"
    using proc_locale[unfolded M1.muterm_recursive_rta08_ur_redpair_proc_def
      Let_def split,simplified]
    by (auto simp: isOK_check rel_impl_list)
  have rules': "set (dpp_ops.rules J d') =
      set (dpp_ops.rules J ?d)"
    using deleted dpp_spec.delete_P_Pw_sound[OF J, of ?d Pr Pr]
      dpp_spec.rules_sound[OF J, of d']
      dpp_spec.rules_sound[OF J, of ?d] by auto
  have wf': "wf_trs (set (dpp_ops.rules J d'))"
    using wf_d rules' by simp
  interpret M': muterm_i4 "dpp_ops.rules J d'" "mu_of m"
      "csr_u3_delta (set (dpp_ops.rules J d')) (set U)" "undefined"
    by (unfold_locales, rule wf')
  have child_fin': "M'.finite_muterm_i4_good_typed_dpp
      (set (dpp_ops.pairs J d')) (set B)"
    using child_fin unfolding M0.finite_muterm_i4_good_typed_dpp_def
      M'.finite_muterm_i4_good_typed_dpp_def
      M0.muterm_i4_good_pair_step_def M'.muterm_i4_good_pair_step_def
      rules' rules_d by simp
  have child_fin'': "muterm_i4.finite_muterm_i4_good_typed_dpp
      (dpp_ops.rules J d') (mu_of m) (set (dpp_ops.pairs J d')) (set B)"
    using child_fin' unfolding M'.finite_muterm_i4_good_typed_dpp_def
      muterm_i4.finite_muterm_i4_good_typed_dpp_def
      M'.muterm_i4_good_pair_step_def
      muterm_i4.muterm_i4_good_pair_step_def by simp
  have exact': "set B = set (muterm_exact_unhiding_rules_list
      Sharp m D (dpp_ops.rules J ?d))"
    using exact unfolding muterm_exact_unhiding_rules_list_set rules_d .
  have full: "muterm_i4.finite_muterm_i4_good_typed_dpp
      (dpp_ops.rules J ?d) (mu_of m)
      (set (dpp_ops.pairs J ?d)) (set B)"
    by (rule muterm_recursive_rta08_ur_redpair_proc_sound[
      OF J get_rel_impl proc_locale _ _ _ _ _ _ child_fin''])
       (use wf overlay exact' fresh rules_unmarked marked in
          \<open>simp_all add: rules_d\<close>)
  show ?thesis using full
    unfolding M1.finite_muterm_i4_good_typed_dpp_def
      M0.finite_muterm_i4_good_typed_dpp_def
      M1.muterm_i4_good_pair_step_def M0.muterm_i4_good_pair_step_def
      rules_d pairs_d by simp
qed

theorem check_muterm_recursive_dp_proof_sound:
  fixes J :: "('dpp,('f::{showl,compare_order},label_type) lab,string) dpp_ops"
  assumes J: "dpp_spec J"
    and wf: "wf_trs (set R)"
    and overlay: "csr_switch_overlay (set R)"
    and exact: "set B = set (muterm_exact_unhiding_rules_list Sharp m D R)"
    and fresh: "\<And>h n. \<not> defined (set R) (Sharp h,n)"
    and rules_unmarked: "\<And>fn. fn \<in> funas_trs (set R) \<Longrightarrow>
      \<not> is_sharp_lab (fst fn)"
    and marked: "\<And>f n. \<not> is_sharp_lab f \<Longrightarrow>
      mu_of m (Sharp f,n) = mu_of m (f,n)"
    and ok: "isOK (check_muterm_recursive_dp_proof J m i R B U P p)"
  shows "muterm_i4.finite_muterm_i4_good_typed_dpp
    R (mu_of m) (set P) (set B)"
  using ok
proof (induct "muterm_recursive_proof_depth p" arbitrary: p i P
    rule: less_induct)
  case less
  show ?case
  proof (cases p)
    case P_is_Empty
    from less.prems have P: "P = []" unfolding P_is_Empty by simp
    interpret M: muterm_i4 R "mu_of m" "{}" "undefined"
      by (unfold_locales, rule wf)
    have empty: "muterm_innermost_min_typed_pair_step Sharp (mu_of m)
        (set R) {} (set B) = {}"
      unfolding muterm_innermost_min_typed_pair_step_def
        muterm_innermost_typed_pair_step_def muterm_typed_pair_step_def
        muterm_noncollapsing_rrstep_def muterm_collapsing_rrstep_def
      by auto
    have raw: "finite_muterm_innermost_min_typed_dpp Sharp (mu_of m)
        (set R) {} (set B)"
      unfolding finite_muterm_innermost_min_typed_dpp_def empty
      by (rule SN_rel_empty1)
    have "M.finite_muterm_i4_good_typed_dpp {} (set B)"
      by (rule M.finite_muterm_innermost_min_typed_dpp_imp_i4_good[OF raw])
    then show ?thesis using P by simp
  next
    case (Redpair_Proc redp Pr child)
    let ?d = "dpp_ops.mk J False False P [] [] [] R"
    from less.prems Redpair_Proc obtain d' where proc:
        "muterm_recursive_rta08_ur_redpair_proc_exec
          (dpp_ops.rules J ?d) (mu_of m)
          (csr_u3_delta (set (dpp_ops.rules J ?d)) (set U)) J m
          (get_rel_impl redp) Pr U B ?d = return d'"
      and rec: "isOK (check_muterm_recursive_dp_proof J m
          (add_index i 1) R B U (dpp_ops.pairs J d') child)"
      by (auto simp: Let_def)
    have depth: "muterm_recursive_proof_depth child <
        muterm_recursive_proof_depth p"
      using Redpair_Proc by simp
    have child_fin: "muterm_i4.finite_muterm_i4_good_typed_dpp
        R (mu_of m) (set (dpp_ops.pairs J d')) (set B)"
      by (rule less.hyps[OF depth rec])
    show ?thesis
      by (rule check_muterm_recursive_redpair_step_sound[
        OF J wf overlay exact fresh rules_unmarked marked proc child_fin])
  next
    case (Dep_Graph_Proc edps)
    from less.prems Dep_Graph_Proc have graph:
        "isOK (check_muterm_typed_dep_graph m R B P edps)"
      and terminal: "list_all (\<lambda>(po,C). po = None) edps"
      by auto
    have raw: "finite_muterm_innermost_min_typed_dpp Sharp (mu_of m)
        (set R) (set P) (set B)"
    proof (rule check_muterm_innermost_min_typed_dep_graph_sound[OF graph])
      fix child0 C
      assume mem: "(Some child0,C) \<in> set edps"
      from terminal mem show "finite_muterm_innermost_min_typed_dpp
        Sharp (mu_of m) (set R) (set P \<inter> set C) (set B)"
        by (auto simp: list_all_iff)
    qed
    interpret M: muterm_i4 R "mu_of m" "{}" "undefined"
      by (unfold_locales, rule wf)
    show ?thesis
      by (rule M.finite_muterm_innermost_min_typed_dpp_imp_i4_good[OF raw])
  next
    case (Subterm_Criterion_Proc x1 x2 x3 x4)
    with less.prems show ?thesis by simp
  next
    case (Gen_Subterm_Criterion_Proc x1 x2 x3)
    with less.prems show ?thesis by simp
  next
    case (Redpair_UR_Proc x1 x2 x3 x4)
    with less.prems show ?thesis by simp
  next
    case (Usable_Rules_Proc x1 x2)
    with less.prems show ?thesis by simp
  next
    case (Mono_Redpair_Proc x1 x2 x3 x4)
    with less.prems show ?thesis by simp
  next
    case (Mono_URM_Redpair_Proc x1 x2 x3 x4)
    with less.prems show ?thesis by simp
  next
    case (Mono_Redpair_UR_Proc x1 x2 x3 x4 x5)
    with less.prems show ?thesis by simp
  next
    case (Size_Change_Subterm_Proc x1)
    with less.prems show ?thesis by simp
  next
    case (Size_Change_Redpair_Proc x1 x2 x3)
    with less.prems show ?thesis by simp
  next
    case (Uncurry_Proc x1 x2 x3 x4 x5)
    with less.prems show ?thesis by simp
  next
    case (Fcc_Proc x1 x2 x3 x4 x5)
    with less.prems show ?thesis by simp
  next
    case (Split_Proc x1 x2 x3 x4)
    with less.prems show ?thesis by simp
  next
    case (Semlab_Proc x1 x2 x3 x4 x5)
    with less.prems show ?thesis by simp
  next
    case (Switch_Innermost_Proc x1 x2)
    with less.prems show ?thesis by simp
  next
    case (Rewriting_Proc x1 x2 x3 x4 x5 x6 x7)
    with less.prems show ?thesis by simp
  next
    case (Instantiation_Proc x1 x2 x3)
    with less.prems show ?thesis by simp
  next
    case (Forward_Instantiation_Proc x1 x2 x3 x4)
    with less.prems show ?thesis by simp
  next
    case (Narrowing_Proc x1 x2 x3 x4)
    with less.prems show ?thesis by simp
  next
    case (Assume_Finite x1 x2)
    with less.prems show ?thesis by simp
  next
    case (Q_Reduction_Proc x1 x2)
    with less.prems show ?thesis by simp
  next
    case (Complex_Constant_Removal_Proc x1 x2)
    with less.prems show ?thesis by simp
  next
    case (General_Redpair_Proc x1 x2 x3 x4 x5)
    with less.prems show ?thesis by simp
  next
    case (To_Trs_Proc x1)
    with less.prems show ?thesis by simp
  qed
qed

fun check_muterm_typed_dp_proof_production
and check_muterm_innermost_typed_graph_components where
  "check_muterm_typed_dp_proof_production I J \<mu> i R S P
      Muterm_Typed_P_Is_Empty =
    check (P = [])
      (i \<circ> showsl_lit (STR '': innermost typed MU-TERM pairs are not empty''))"
| "check_muterm_typed_dp_proof_production I J \<mu> i R S P
      (Muterm_Typed_Expanded_Extended_Basic_CSR_Proof child) =
    debug i (STR ''expanded typed extended-basic MU-TERM CSR component'') (do {
      let E = muterm_expanded_pairs_list string_renameN P S;
      let dpp = dpp_ops.mk J False False E [] [] [] R;
      check_muterm_expanded_extended_basic_proof I J \<mu>
        (add_index i 1) dpp child
    })"
| "check_muterm_typed_dp_proof_production I J \<mu> i R S P
      (Muterm_Typed_General_Usable redp Pr U child) =
    debug i (STR ''innermost typed RTA'08 MU-TERM usable-rule reduction pair'') (do {
      let dpp = dpp_ops.mk J False False P [] [] [] R;
      dpp' \<leftarrow> muterm_general_rta08_ur_redpair_proc J \<mu>
        (get_rel_impl redp) Pr U S dpp;
      check_muterm_typed_dp_proof_production I J \<mu> (add_index i 1)
        R S (dpp_ops.pairs J dpp') child
    })"
| "check_muterm_typed_dp_proof_production I J \<mu> i R S P
      (Muterm_Typed_Pair_Augmentation st sts child) =
    debug i (STR ''innermost typed MU-TERM pair augmentation'') (do {
      let dpp = dpp_ops.mk J False False P [] [] [] R;
      dpp' \<leftarrow> csr_instantiation_proc J \<mu> st sts dpp;
      check_subseteq P (dpp_ops.pairs J dpp')
        <+? (\<lambda>_. showsl_lit
          (STR ''typed MU-TERM augmentation removed an original pair''));
      check_muterm_typed_dp_proof_production I J \<mu> (add_index i 1)
        R S (dpp_ops.pairs J dpp') child
    })"
| "check_muterm_typed_dp_proof_production I J \<mu> i R S P
      (Muterm_Typed_CSR_Proof child) =
    debug i (STR ''innermost typed MU-TERM noncollapsing CSR component'') (do {
      check (list_all (is_Fun \<circ> snd) P)
        (i \<circ> showsl_lit
          (STR '': collapsing pair requires the typed MU-TERM processor''));
      let dpp = dpp_ops.mk J False False P [] [] [] R;
      check_csr_dp_termination_proof_min I J \<mu> False
        (add_index i 1) dpp child
    })"
| "check_muterm_typed_dp_proof_production I J \<mu> i R S P
      (Muterm_Typed_Local_Usable U child) =
    error (i \<circ> showsl_lit
      (STR '': recursive local usable rules require the invariant graph checker''))"
| "check_muterm_typed_dp_proof_production I J \<mu> i R S P
      (Muterm_Typed_Expanded_CSR_Proof child) =
    debug i (STR ''expanded typed MU-TERM CSR component'') (do {
      let E = muterm_expanded_pairs_list string_renameN P S;
      let dpp = dpp_ops.mk J False False E [] [] [] R;
      check_muterm_expanded_csr_proof I J \<mu> (add_index i 1) dpp child
    })"
| "check_muterm_typed_dp_proof_production I J \<mu> i R S P
      (Muterm_Typed_Expanded_Local_Usable U child) =
    debug i (STR ''expanded innermost typed MU-TERM local usable rules'') (do {
      check (list_all (\<lambda>lr. lr \<in> set R) U)
        (i \<circ> showsl_lit (STR '': extraneous MU-TERM usable rule''));
      check (list_all (\<lambda>lr.
          qcs_ur_closed_term_check R U \<mu> (snd lr)) U)
        (i \<circ> showsl_lit (STR '': ordinary MU-TERM rule closure failed''));
      check (list_all (\<lambda>lr.
          qcs_ur_closed_dp_rhs_check R U \<mu> (snd lr)) S)
        (i \<circ> showsl_lit (STR '': MU-TERM unhiding closure failed''));
      check (list_all (\<lambda>dp. is_Var (snd dp) \<or>
          qcs_ur_closed_dp_rhs_check R U \<mu> (snd dp)) P)
        (i \<circ> showsl_lit (STR '': MU-TERM pair closure failed''));
      let E = muterm_expanded_pairs_list string_renameN P S;
      check_dp_termination_proof I J False (add_index i 1)
        (dpp_ops.mk J False False E [] [] [] U) child
    })"
| "check_muterm_typed_dp_proof_production I J \<mu> i R S P
      (Muterm_Typed_Expanded_Ordinary child) =
    debug i (STR ''expanded typed MU-TERM ordinary DP continuation'') (do {
      let E = muterm_expanded_pairs_list string_renameN P S;
      check_dp_termination_proof I J False (add_index i 1)
        (dpp_ops.mk J False False E [] [] [] R) child
    })"
| "check_muterm_typed_dp_proof_production I J \<mu> i R S P
      (Muterm_Typed_Dep_Graph edps) =
    debug i (STR ''innermost typed MU-TERM dependency graph'') (do {
      check_muterm_typed_dep_graph \<mu> R S P edps;
      check_muterm_innermost_typed_graph_components I J \<mu> i R S P edps
    })"
| "check_muterm_typed_dp_proof_production I J \<mu> i R S P child =
    error (i \<circ> showsl_lit
      (STR '': processor is not supported inside an innermost typed MU-TERM chain''))"
| "check_muterm_innermost_typed_graph_components I J \<mu> i R S P [] = succeed"
| "check_muterm_innermost_typed_graph_components I J \<mu> i R S P
      ((None,C)#rest) =
    check_muterm_innermost_typed_graph_components I J \<mu>
      (add_index i 1) R S P rest"
| "check_muterm_innermost_typed_graph_components I J \<mu> i R S P
      ((Some child,C)#rest) = do {
    check_muterm_typed_dp_proof_production I J \<mu> (add_index i 1)
      R S (filter (\<lambda>dp. dp \<in> set C) P) child;
    check_muterm_innermost_typed_graph_components I J \<mu>
      (add_index i 1) R S P rest
  }"

lemma check_muterm_innermost_typed_graph_components_member:
  assumes ok: "isOK (check_muterm_innermost_typed_graph_components
      I J \<mu> i R S P edps)"
    and mem: "(Some child,C) \<in> set edps"
  shows "\<exists>j. isOK (check_muterm_typed_dp_proof_production
    I J \<mu> j R S (filter (\<lambda>dp. dp \<in> set C) P) child)"
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
    from Cons.prems head None show ?thesis by (auto intro: Cons.hyps)
  next
    case (Some p)
    show ?thesis
    proof (cases "(Some child,C) = head")
      case True
      with Cons.prems head Some show ?thesis by auto
    next
      case False
      from Cons.prems head Some False show ?thesis
        by (auto intro: Cons.hyps)
    qed
  qed
qed

fun check_muterm_i4_graph_component where
  "check_muterm_i4_graph_component I J m i R B P (None,C) = succeed"
| "check_muterm_i4_graph_component I J m i R B P
      (Some (Muterm_Typed_Local_Usable U child),C) = do {
    check (list_all (\<lambda>lr. lr \<in> set R \<or> lr \<in> set B) U)
      (i \<circ> showsl_lit
        (STR '': extraneous recursive MU-TERM usable rule''));
    let U0 = filter (\<lambda>lr. lr \<in> set R) U;
    check_muterm_recursive_dp_proof J m (add_index i 1) R B U0
      (filter (\<lambda>dp. dp \<in> set C) P) child
  }"
| "check_muterm_i4_graph_component I J m i R B P (Some child,C) =
    check_muterm_typed_dp_proof_production I J m (add_index i 1)
      R B (filter (\<lambda>dp. dp \<in> set C) P) child"

fun check_muterm_i4_graph_components where
  "check_muterm_i4_graph_components I J m i R B P [] = succeed"
| "check_muterm_i4_graph_components I J m i R B P (head#rest) = do {
    check_muterm_i4_graph_component I J m i R B P head;
    check_muterm_i4_graph_components I J m (add_index i 1) R B P rest
  }"

fun check_muterm_i4_root_proof where
  "check_muterm_i4_root_proof I J m i R B P
      (Muterm_Typed_Dep_Graph edps) = do {
    check_muterm_typed_dep_graph m R B P edps;
    check_muterm_i4_graph_components I J m i R B P edps
  }"
| "check_muterm_i4_root_proof I J m i R B P child =
    check_muterm_typed_dp_proof_production I J m i R B P child"

lemma check_muterm_i4_root_proof_non_graph:
  assumes "\<nexists>edps. p = Muterm_Typed_Dep_Graph edps"
  shows "check_muterm_i4_root_proof I J m i R B P p =
    check_muterm_typed_dp_proof_production I J m i R B P p"
  using assms by (cases p; simp)

lemma check_muterm_i4_graph_components_local_member:
  assumes ok: "isOK (check_muterm_i4_graph_components
      I J m i R B P edps)"
    and mem: "(Some (Muterm_Typed_Local_Usable U child),C) \<in> set edps"
  shows "\<exists>j. isOK (check_muterm_recursive_dp_proof J m j R B
    (filter (\<lambda>lr. lr \<in> set R) U)
    (filter (\<lambda>x. x \<in> set C) P) child)"
  using ok mem
proof (induct edps arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons head rest)
  obtain po D where head: "head = (po,D)" by (cases head)
  have head_ok: "isOK (check_muterm_i4_graph_component
      I J m i R B P head)" and rest_ok:
      "isOK (check_muterm_i4_graph_components
        I J m (add_index i 1) R B P rest)"
    using Cons.prems(1) by auto
  show ?case
  proof (cases "(Some (Muterm_Typed_Local_Usable U child),C) = head")
    case True
    from True head_ok show ?thesis
      by (cases po; auto simp: head)
  next
    case False
    have rest_mem: "(Some (Muterm_Typed_Local_Usable U child),C)
        \<in> set rest"
      using Cons.prems(2) False by auto
    show ?thesis by (rule Cons.hyps[OF rest_ok rest_mem])
  qed
qed

lemma check_muterm_i4_graph_components_nonlocal_member:
  assumes ok: "isOK (check_muterm_i4_graph_components
      I J m i R B P edps)"
    and mem: "(Some child,C) \<in> set edps"
    and nonlocal: "\<And>U dp. child \<noteq> Muterm_Typed_Local_Usable U dp"
  shows "\<exists>j. isOK (check_muterm_typed_dp_proof_production
    I J m j R B (filter (\<lambda>x. x \<in> set C) P) child)"
  using ok mem
proof (induct edps arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons head rest)
  obtain po D where head: "head = (po,D)" by (cases head)
  have head_ok: "isOK (check_muterm_i4_graph_component
      I J m i R B P head)" and rest_ok:
      "isOK (check_muterm_i4_graph_components
        I J m (add_index i 1) R B P rest)"
    using Cons.prems(1) by auto
  show ?case
  proof (cases "(Some child,C) = head")
    case True
    from True head_ok nonlocal show ?thesis
      by (cases po; cases child; auto simp: head)
  next
    case False
    have rest_mem: "(Some child,C) \<in> set rest"
      using Cons.prems(2) False by auto
    show ?thesis by (rule Cons.hyps[OF rest_ok rest_mem])
  qed
qed

lemma finite_min_csr_dpp_imp_finite_muterm_innermost_min_typed_noncollapsing:
  assumes overlay: "csr_switch_overlay R"
    and wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and nc: "\<forall>dp\<in>P. is_Fun (snd dp)"
    and fin: "finite_min_csr_dpp Sharp \<mu> P R"
  shows "finite_muterm_innermost_min_typed_dpp Sharp \<mu> R P B"
proof -
  have pair_sub: "muterm_innermost_min_typed_pair_step Sharp \<mu> R P B
      \<subseteq> csr_min_pair_step Sharp \<mu> P R"
  proof
    fix st
    assume member: "st \<in>
      muterm_innermost_min_typed_pair_step Sharp \<mu> R P B"
    obtain s t where st: "st = (s,t)" by (cases st)
    from member[unfolded st muterm_innermost_min_typed_pair_step_def
        muterm_innermost_typed_pair_step_def]
    have typed: "(s,t) \<in> muterm_typed_pair_step P B"
      and target: "\<exists>u. t = sharp_term Sharp u \<and>
        u \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)" by auto
    have pair: "(s,t) \<in> rrstep P"
      using typed muterm_typed_pair_step_noncollapsing[OF nc] by simp
    from target obtain u where t: "t = sharp_term Sharp u"
      and inner: "u \<in> mu_Tinf \<mu> (innermost_csstep \<mu> R)" by blast
    have full: "u \<in> mu_Tinf \<mu> (csstep \<mu> R)"
      by (rule mu_Tinf_innermost_imp_mu_Tinf[OF overlay wf inner])
    have target_SN: "SN_on (csdp_step Sharp \<mu> R) {t}"
      unfolding t by (rule mu_Tinf_imp_SN_sharp_csdp[OF wf fresh full])
    show "st \<in> csr_min_pair_step Sharp \<mu> P R"
      unfolding st csr_min_pair_step_def using pair target_SN by simp
  qed
  show ?thesis
    unfolding finite_muterm_innermost_min_typed_dpp_def
      finite_min_csr_dpp_def
    by (rule SN_rel_mono[
      OF pair_sub innermost_csdp_step_subset_csdp_step
        fin[unfolded finite_min_csr_dpp_def]])
qed

lemma check_muterm_typed_expanded_ordinary_innermost_sound:
  fixes I :: "('tp,('f::{showl,compare_order,countable},label_type) lab,string) tp_ops"
    and J :: "('dpp,('f,label_type) lab,string) dpp_ops"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_dp_termination_proof I J False i
      (dpp_ops.mk J False False
        (muterm_expanded_pairs_list string_renameN P S) [] [] [] R) child)"
  shows "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
    (set R) (set P) (set S)"
proof -
  let ?E = "muterm_expanded_pairs_list string_renameN P S"
  have raw: "finite_dpp (False,False,set ?E,{},{},{},set R)"
  proof -
    have "finite_dpp (dpp_ops.dpp J
      (dpp_ops.mk J False False ?E [] [] [] R))"
      by (rule check_dp_termination_proof[OF I J ok])
    then show ?thesis using dpp_spec.mk_sound[
      OF J, of False False ?E "[]" "[]" "[]" R] by simp
  qed
  have fin: "finite_dpp (False,False,
      muterm_expanded_pairs string_renameN (set P) (set S),{},{},{},set R)"
    using raw by (simp only:
      set_muterm_expanded_pairs_list[of string_renameN P S])
  have full: "finite_muterm_typed_dpp Sharp (mu_of \<mu>)
      (set R) (set P) (set S)"
    by (rule finite_muterm_typed_dpp_expanded_ordinary[OF fin])
  show ?thesis
    by (rule finite_muterm_typed_imp_finite_innermost_min_typed[OF full])
qed

lemma muterm_typed_empty_production_sound:
  assumes empty: "P = []"
  shows "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
    (set R) (set P) (set S)"
proof -
  have step_empty: "muterm_innermost_min_typed_pair_step Sharp (mu_of \<mu>)
      (set R) (set P) (set S) = {}"
    using empty
    unfolding muterm_innermost_min_typed_pair_step_def
      muterm_innermost_typed_pair_step_def muterm_typed_pair_step_def
      muterm_noncollapsing_rrstep_def muterm_collapsing_rrstep_def
    by auto
  show ?thesis unfolding finite_muterm_innermost_min_typed_dpp_def step_empty
    by (rule SN_rel_empty1)
qed

lemma muterm_typed_general_usable_production_sound:
  fixes J :: "('dpp,('f::{showl,compare_order,countable},label_type) lab,string) dpp_ops"
  assumes J: "dpp_spec J"
    and wf: "wf_trs (set R)"
    and overlay: "csr_switch_overlay (set R)"
    and fresh: "\<And>f n. \<not> defined (set R) (Sharp f,n)"
    and proc: "muterm_general_rta08_ur_redpair_proc J \<mu>
      (get_rel_impl redp) Pr U S
      (dpp_ops.mk J False False P [] [] [] R) = return d'"
    and child_fin: "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
      (set R) (set (dpp_ops.pairs J d')) (set S)"
  shows "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
    (set R) (set P) (set S)"
by (rule muterm_innermost_general_ur_redpair_proc_mk_sound[
  where J=J and \<mu>=\<mu> and rp="get_rel_impl redp" and Premove=Pr
    and U=U and B=S and P=P and R=R and dpp'=d',
  OF J wf overlay fresh proc get_rel_impl child_fin])

lemma muterm_typed_pair_augmentation_production_sound:
  fixes J :: "('dpp,('f::{showl,compare_order,countable},label_type) lab,string) dpp_ops"
  assumes sub: "isOK (check_subseteq P (dpp_ops.pairs J d'))"
    and child_fin: "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
      (set R) (set (dpp_ops.pairs J d')) (set S)"
  shows "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
    (set R) (set P) (set S)"
proof -
  from sub have subset: "set P \<subseteq> set (dpp_ops.pairs J d')"
    by (induct P; auto)
  show ?thesis unfolding finite_muterm_innermost_min_typed_dpp_def
    by (rule SN_rel_mono[
      OF muterm_innermost_min_typed_pair_step_mono_pairs[OF subset]
        subset_refl
        child_fin[unfolded finite_muterm_innermost_min_typed_dpp_def]])
qed

lemma muterm_typed_csr_component_production_sound:
  fixes I :: "('tp,('f::{showl,compare_order,countable},label_type) lab,string) tp_ops"
    and J :: "('dpp,('f,label_type) lab,string) dpp_ops"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and wf: "wf_trs (set R)"
    and overlay: "csr_switch_overlay (set R)"
    and fresh: "\<And>f n. \<not> defined (set R) (Sharp f,n)"
    and noncoll_list: "list_all (is_Fun \<circ> snd) P"
    and child_ok: "isOK (check_csr_dp_termination_proof_min I J \<mu> False i
      (dpp_ops.mk J False False P [] [] [] R) child)"
  shows "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
    (set R) (set P) (set S)"
proof -
  let ?d = "dpp_ops.mk J False False P [] [] [] R"
  have plain: "plain_csr_dpp J ?d"
    unfolding plain_csr_dpp_def
    using dpp_spec.mk_sound[OF J, of False False P "[]" "[]" "[]" R]
      dpp_spec.dpp_sound[OF J, of ?d] by auto
  have sem: "dpp_ops.dpp J ?d = (False,False,set P,{},{},{},set R)"
    using dpp_spec.mk_sound[OF J, of False False P "[]" "[]" "[]" R]
    by simp
  have rules_d: "set (dpp_ops.rules J ?d) = set R"
    using sem dpp_spec.dpp_sound[OF J,of ?d]
      dpp_spec.rules_sound[OF J,of ?d] by auto
  have wf_d: "wf_trs (set (dpp_ops.rules J ?d))"
    using wf unfolding rules_d .
  have fresh_d: "\<And>f n.
      \<not> defined (set (dpp_ops.rules J ?d)) (Sharp f,n)"
    using fresh unfolding rules_d .
  have raw: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (dpp_ops.pairs J ?d)) (set (dpp_ops.rules J ?d))"
    by (rule check_csr_dp_termination_proof_min_sound[
      OF I J plain wf_d fresh_d child_ok])
  have pairs_d: "set (dpp_ops.pairs J ?d) = set P"
    using sem dpp_spec.dpp_sound[OF J,of ?d]
      dpp_spec.pairs_sound[OF J,of ?d] by auto
  have fin: "finite_min_csr_dpp Sharp (mu_of \<mu>) (set P) (set R)"
    using raw unfolding pairs_d rules_d .
  have noncoll: "\<forall>dp\<in>set P. is_Fun (snd dp)"
    using noncoll_list by (simp add: list_all_iff)
  show ?thesis
    by (rule finite_min_csr_dpp_imp_finite_muterm_innermost_min_typed_noncollapsing[
      OF overlay wf fresh noncoll fin])
qed

lemma muterm_typed_expanded_csr_component_production_sound:
  fixes I :: "('tp,('f::{showl,compare_order,countable},label_type) lab,string) tp_ops"
    and J :: "('dpp,('f,label_type) lab,string) dpp_ops"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and wf: "wf_trs (set R)"
    and overlay: "csr_switch_overlay (set R)"
    and fresh: "\<And>f n. \<not> defined (set R) (Sharp f,n)"
    and child_ok: "isOK (check_muterm_expanded_csr_proof I J \<mu> i
      (dpp_ops.mk J False False
        (muterm_expanded_pairs_list string_renameN P S) [] [] [] R) child)"
  shows "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
    (set R) (set P) (set S)"
proof -
  let ?E = "muterm_expanded_pairs_list string_renameN P S"
  let ?d = "dpp_ops.mk J False False ?E [] [] [] R"
  have plain: "plain_csr_dpp J ?d"
    unfolding plain_csr_dpp_def
    using dpp_spec.mk_sound[OF J,of False False ?E "[]" "[]" "[]" R]
      dpp_spec.dpp_sound[OF J,of ?d] by auto
  interpret dpp_spec J by fact
  have sem: "dpp ?d = (False,False,set ?E,{},{},{},set R)"
    using mk_sound[of False False ?E "[]" "[]" "[]" R] by simp
  have rules: "set (rules ?d) = set R"
    using sem rules_sound[of ?d] dpp_sound[of ?d] by auto
  have wf_d: "wf_trs (set (rules ?d))" using wf unfolding rules .
  have fresh_d: "\<And>f n. \<not> defined (set (rules ?d)) (Sharp f,n)"
    using fresh unfolding rules .
  have raw: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (pairs ?d)) (set (rules ?d))"
    by (rule check_muterm_expanded_csr_proof_sound[
      OF I J plain wf_d fresh_d child_ok])
  have expanded: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (muterm_expanded_pairs string_renameN (set P) (set S)) (set R)"
    using raw sem pairs_sound[of ?d] rules_sound[of ?d] dpp_sound[of ?d]
      set_muterm_expanded_pairs_list[of string_renameN P S] by auto
  have full: "finite_muterm_min_typed_dpp Sharp (mu_of \<mu>)
      (set R) (set P) (set S)"
    by (rule finite_min_csr_dpp_expanded_imp_finite_muterm_min_typed[
      OF expanded])
  show ?thesis by (rule finite_muterm_min_typed_imp_finite_innermost_min_typed_overlay[
    OF overlay wf fresh full])
qed

lemma muterm_typed_dep_graph_production_sound:
  fixes \<mu> :: "(('f::{showl,compare_order},label_type) lab) muL"
  assumes graph: "isOK (check_muterm_typed_dep_graph \<mu> R S P edps)"
    and components: "\<And>child C. (Some child,C) \<in> set edps \<Longrightarrow>
      finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
        (set R) (set (filter (\<lambda>dp. dp \<in> set C) P)) (set S)"
  shows "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
    (set R) (set P) (set S)"
proof (rule check_muterm_innermost_min_typed_dep_graph_sound[
    where \<mu>=\<mu> and R=R and B=S and P=P and edps=edps])
  show "isOK (check_muterm_typed_dep_graph \<mu> R S P edps)" by (rule graph)
next
  fix child C
  assume mem: "(Some child,C) \<in> set edps"
  have set_filter: "set (filter (\<lambda>dp. dp \<in> set C) P) =
    set P \<inter> set C" by auto
  show "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
    (set R) (set P \<inter> set C) (set S)"
    unfolding set_filter[symmetric] by (rule components[OF mem])
qed

lemma muterm_typed_expanded_basic_component_production_sound:
  fixes I :: "('tp,('f::{showl,compare_order,countable},label_type) lab,string) tp_ops"
    and J :: "('dpp,('f,label_type) lab,string) dpp_ops"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and wf: "wf_trs (set R)"
    and overlay: "csr_switch_overlay (set R)"
    and fresh: "\<And>f n. \<not> defined (set R) (Sharp f,n)"
    and child_ok: "isOK (check_muterm_expanded_extended_basic_proof
      I J \<mu> i (dpp_ops.mk J False False
        (muterm_expanded_pairs_list string_renameN P S) [] [] [] R) child)"
  shows "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
    (set R) (set P) (set S)"
proof -
  let ?E = "muterm_expanded_pairs_list string_renameN P S"
  let ?d = "dpp_ops.mk J False False ?E [] [] [] R"
  have plain: "plain_csr_dpp J ?d"
    unfolding plain_csr_dpp_def
    using dpp_spec.mk_sound[OF J,of False False ?E "[]" "[]" "[]" R]
      dpp_spec.dpp_sound[OF J,of ?d] by auto
  interpret dpp_spec J by fact
  have sem: "dpp ?d = (False,False,set ?E,{},{},{},set R)"
    using mk_sound[of False False ?E "[]" "[]" "[]" R] by simp
  have rules: "set (rules ?d) = set R"
    using sem rules_sound[of ?d] dpp_sound[of ?d] by auto
  have raw: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (pairs ?d)) (set (rules ?d))"
    by (rule check_muterm_expanded_extended_basic_proof_sound[
      OF I J plain _ _ child_ok])
       (use wf fresh in \<open>simp_all add: rules\<close>)
  have expanded: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (muterm_expanded_pairs string_renameN (set P) (set S)) (set R)"
    using raw sem pairs_sound[of ?d] rules_sound[of ?d] dpp_sound[of ?d]
      set_muterm_expanded_pairs_list[of string_renameN P S] by auto
  have full: "finite_muterm_min_typed_dpp Sharp (mu_of \<mu>)
      (set R) (set P) (set S)"
    by (rule finite_min_csr_dpp_expanded_imp_finite_muterm_min_typed[
      OF expanded])
  show ?thesis by (rule finite_muterm_min_typed_imp_finite_innermost_min_typed_overlay[
    OF overlay wf fresh full])
qed

lemma muterm_typed_expanded_local_component_production_sound:
  fixes I :: "('tp,('f::{showl,compare_order,countable},label_type) lab,string) tp_ops"
    and J :: "('dpp,('f,label_type) lab,string) dpp_ops"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and wf: "wf_trs (set R)"
    and overlay: "csr_switch_overlay (set R)"
    and fresh: "\<And>f n. \<not> defined (set R) (Sharp f,n)"
    and closure_ok: "muterm_qcs_expanded_ur_closed_check R S U \<mu> P"
    and child_ok: "isOK (check_dp_termination_proof I J False i
      (dpp_ops.mk J False False
        (muterm_expanded_pairs_list string_renameN P S) [] [] [] U) child)"
  shows "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
    (set R) (set P) (set S)"
proof -
  let ?E = "muterm_expanded_pairs_list string_renameN P S"
  have raw: "finite_dpp (False,False,set ?E,{},{},{},set U)"
  proof -
    have "finite_dpp (dpp_ops.dpp J
      (dpp_ops.mk J False False ?E [] [] [] U))"
      by (rule check_dp_termination_proof[OF I J child_ok])
    then show ?thesis using dpp_spec.mk_sound[
      OF J, of False False ?E "[]" "[]" "[]" U] by simp
  qed
  have fin: "finite_dpp (False,False,
      muterm_expanded_pairs string_renameN (set P) (set S),{},{},{},set U)"
    using raw set_muterm_expanded_pairs_list[of string_renameN P S] by simp
  have closed: "muterm_qcs_expanded_ur_closed (set R) (set S) (set U)
      (mu_of \<mu>) (set P)"
    by (rule muterm_qcs_expanded_ur_closed_check_sound[OF closure_ok])
  have typed: "finite_muterm_typed_dpp Sharp (mu_of \<mu>)
      (set R) (set P) (set S)"
    by (rule finite_muterm_typed_dpp_expanded_usable[
      OF wf fresh closed fin])
  have full: "finite_muterm_min_typed_dpp Sharp (mu_of \<mu>)
      (set R) (set P) (set S)"
    by (rule finite_muterm_typed_imp_finite_min_typed[OF typed])
  show ?thesis by (rule finite_muterm_min_typed_imp_finite_innermost_min_typed_overlay[
    OF overlay wf fresh full])
qed

(* Superseded by the mutual functional-induction proof below. *)
(*
theorem check_muterm_typed_dp_proof_production_sound:
  fixes I :: "('tp,('f::{showl,compare_order,countable},label_type) lab,string) tp_ops"
    and J :: "('dpp,('f,label_type) lab,string) dpp_ops"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and wf: "wf_trs (set R)"
    and overlay: "csr_switch_overlay (set R)"
    and fresh: "\<And>f n. \<not> defined (set R) (Sharp f,n)"
    and ok: "isOK (check_muterm_typed_dp_proof_production
      I J \<mu> i R S P p)"
  shows "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
    (set R) (set P) (set S)"
proof (cases "\<exists>child. p = Muterm_Typed_Expanded_Ordinary child")
  case True
  then obtain child where p:
      "p = Muterm_Typed_Expanded_Ordinary child" by blast
  let ?E = "muterm_expanded_pairs_list string_renameN P S"
  from ok p have child_ok:
      "isOK (check_dp_termination_proof I J False (add_index i 1)
        (dpp_ops.mk J False False ?E [] [] [] R) child)"
    by (simp add: Let_def)
  from check_muterm_typed_expanded_ordinary_innermost_sound[
    where I=I and J=J and i="add_index i 1" and P=P and S=S and R=R
      and child=child and \<mu>=\<mu>, OF I J child_ok]
  show ?thesis .
next
  case False
  from ok show ?thesis
proof (induct p arbitrary: i P
    rule: muterm_typed_dp_proof_induct_nonordinary[OF False])
  case Muterm_Typed_P_Is_Empty
  then have "P = []" by simp
  then show ?case by (rule muterm_typed_empty_production_sound)
next
  case (Muterm_Typed_General_Usable redp Pr U child)
  let ?d = "dpp_ops.mk J False False P [] [] [] R"
  from Muterm_Typed_General_Usable.prems obtain d' where proc:
      "muterm_general_rta08_ur_redpair_proc J \<mu>
        (get_rel_impl redp) Pr U S ?d = return d'"
    and rec: "isOK (check_muterm_typed_dp_proof_production I J \<mu>
      (add_index i 1) R S (dpp_ops.pairs J d') child)"
    by (auto simp: Let_def)
  have child_fin: "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
      (set R) (set (dpp_ops.pairs J d')) (set S)"
    by (rule Muterm_Typed_General_Usable.hyps[OF rec])
  show ?case by (rule muterm_typed_general_usable_production_sound[
    OF J wf overlay fresh proc child_fin])
next
  case (Muterm_Typed_Pair_Augmentation st sts child)
  let ?d = "dpp_ops.mk J False False P [] [] [] R"
  from Muterm_Typed_Pair_Augmentation.prems obtain d' where proc:
      "csr_instantiation_proc J \<mu> st sts ?d = return d'"
    and sub: "isOK (check_subseteq P (dpp_ops.pairs J d'))"
    and rec: "isOK (check_muterm_typed_dp_proof_production I J \<mu>
      (add_index i 1) R S (dpp_ops.pairs J d') child)"
    by (auto simp: Let_def)
  have fin': "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
      (set R) (set (dpp_ops.pairs J d')) (set S)"
    by (rule Muterm_Typed_Pair_Augmentation.hyps[OF rec])
  show ?case by (rule muterm_typed_pair_augmentation_production_sound[
    OF sub fin'])
next
  case (Muterm_Typed_CSR_Proof child)
  let ?d = "dpp_ops.mk J False False P [] [] [] R"
  from Muterm_Typed_CSR_Proof.prems have noncoll_list:
      "list_all (is_Fun \<circ> snd) P"
    and child_ok: "isOK (check_csr_dp_termination_proof_min
      I J \<mu> False (add_index i 1) ?d child)" by (auto simp: Let_def)
  show ?case by (rule muterm_typed_csr_component_production_sound[
    OF I J wf overlay fresh noncoll_list child_ok])
next
  case (Muterm_Typed_Expanded_CSR_Proof child)
  let ?E = "muterm_expanded_pairs_list string_renameN P S"
  let ?d = "dpp_ops.mk J False False ?E [] [] [] R"
  from Muterm_Typed_Expanded_CSR_Proof.prems have child_ok:
      "isOK (check_muterm_expanded_csr_proof I J \<mu>
        (add_index i 1) ?d child)" by (simp add: Let_def)
  show ?case by (rule muterm_typed_expanded_csr_component_production_sound[
    OF I J wf overlay fresh child_ok])
next
  case (Muterm_Typed_Dep_Graph edps)
  from Muterm_Typed_Dep_Graph.prems have graph:
      "isOK (check_muterm_typed_dep_graph \<mu> R S P edps)"
    and components: "isOK (check_muterm_innermost_typed_graph_components
      I J \<mu> i R S P edps)" by (auto simp: Let_def)
  show ?case
  proof (rule muterm_typed_dep_graph_production_sound[OF graph])
    fix child C
    assume mem: "(Some child,C) \<in> set edps"
    from check_muterm_innermost_typed_graph_components_member[
      OF components mem]
    obtain j where rec: "isOK (check_muterm_typed_dp_proof_production
      I J \<mu> j R S (filter (\<lambda>dp. dp \<in> set C) P) child)" by blast
    show "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
      (set R) (set (filter (\<lambda>dp. dp \<in> set C) P)) (set S)"
      apply (rule Muterm_Typed_Dep_Graph.hyps)
         apply (rule mem)
        apply simp
       apply simp
      apply (rule rec)
      done
  qed
next
  case (Muterm_Typed_Local_Usable x1 x2)
  then show ?case by simp
next
  case (Muterm_Typed_Expanded_Extended_Basic_CSR_Proof child)
  let ?E = "muterm_expanded_pairs_list string_renameN P S"
  let ?d = "dpp_ops.mk J False False ?E [] [] [] R"
  from Muterm_Typed_Expanded_Extended_Basic_CSR_Proof.prems have child_ok:
      "isOK (check_muterm_expanded_extended_basic_proof I J \<mu>
        (add_index i 1) ?d child)" by (simp add: Let_def)
  show ?case
    apply (rule muterm_typed_expanded_basic_component_production_sound[
      where I=I and J=J and R=R and P=P and S=S and \<mu>=\<mu>
        and i="add_index i 1" and child=child])
         apply (rule I_spec)
        apply (rule J_spec)
       apply (rule wf_R)
      apply (rule overlay_R)
     apply (rule fresh_R)
    apply (rule child_ok)
    done
next
  case (Muterm_Typed_Expanded_Local_Usable U child)
  let ?E = "muterm_expanded_pairs_list string_renameN P S"
  from Muterm_Typed_Expanded_Local_Usable.prems have closure_ok:
      "muterm_qcs_expanded_ur_closed_check R S U \<mu> P"
    and child_ok:
      "isOK (check_dp_termination_proof I J False (add_index i 1)
        (dpp_ops.mk J False False ?E [] [] [] U) child)"
    unfolding muterm_qcs_expanded_ur_closed_check_def Let_def by auto
  show ?case by (rule muterm_typed_expanded_local_component_production_sound[
    OF I J wf overlay fresh closure_ok child_ok])
next
  case (Muterm_Typed_Expanded_Strong_Usable x1 x2 x3 x4)
  then show ?case by simp
qed
qed
*)

lemma check_muterm_typed_production_mutual_sound:
  fixes I :: "('tp,('f::{showl,compare_order,countable},label_type) lab,string) tp_ops"
    and J :: "('dpp,('f,label_type) lab,string) dpp_ops"
  shows "tp_spec I \<Longrightarrow> dpp_spec J \<Longrightarrow>
    wf_trs (set R) \<Longrightarrow> csr_switch_overlay (set R) \<Longrightarrow>
    (\<And>f n. \<not> defined (set R) (Sharp f,n)) \<Longrightarrow>
    isOK (check_muterm_typed_dp_proof_production I J \<mu> i R S P p)
    \<Longrightarrow> finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
      (set R) (set P) (set S)"
    and "tp_spec I \<Longrightarrow> dpp_spec J \<Longrightarrow>
      wf_trs (set R) \<Longrightarrow> csr_switch_overlay (set R) \<Longrightarrow>
      (\<And>f n. \<not> defined (set R) (Sharp f,n)) \<Longrightarrow>
      isOK (check_muterm_innermost_typed_graph_components
      I J \<mu> i R S P edps) \<Longrightarrow>
      (\<forall>child C. (Some child,C) \<in> set edps \<longrightarrow>
        finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
          (set R) (set (filter (\<lambda>dp. dp \<in> set C) P)) (set S))"
proof (induct I J \<mu> i R S P p
    and I J \<mu> i R S P edps rule:
    check_muterm_typed_dp_proof_production_check_muterm_innermost_typed_graph_components.induct)
  case (1 I J \<mu> i R S P)
  from 1 have "P = []" by simp
  then show ?case by (rule muterm_typed_empty_production_sound)
next
  case (2 I J \<mu> i R S P child)
  let ?E = "muterm_expanded_pairs_list string_renameN P S"
  have I_spec: "tp_spec I" by (rule 2(1))
  have J_spec: "dpp_spec J" by (rule 2(2))
  have wf_R: "wf_trs (set R)" by (rule 2(3))
  have overlay_R: "csr_switch_overlay (set R)" by (rule 2(4))
  have fresh_R: "\<And>f n. \<not> defined (set R) (Sharp f,n)"
    by (rule 2(5))
  from 2(6) have child_ok:
      "isOK (check_muterm_expanded_extended_basic_proof I J \<mu>
        (add_index i 1) (dpp_ops.mk J False False ?E [] [] [] R) child)"
    by (simp add: Let_def)
  show ?case
    apply (rule muterm_typed_expanded_basic_component_production_sound[
      where I=I and J=J and R=R and P=P and S=S and \<mu>=\<mu>
        and i="add_index i 1" and child=child])
         apply (rule I_spec)
        apply (rule J_spec)
       apply (rule wf_R)
      apply (rule overlay_R)
     apply (rule fresh_R)
    apply (rule child_ok)
    done
next
  case (3 I J \<mu> i R S P redp Pr U child)
  let ?d = "dpp_ops.mk J False False P [] [] [] R"
  have I_spec: "tp_spec I" by (rule 3(2))
  have J_spec: "dpp_spec J" by (rule 3(3))
  have wf_R: "wf_trs (set R)" by (rule 3(4))
  have overlay_R: "csr_switch_overlay (set R)" by (rule 3(5))
  have fresh_R: "\<And>f n. \<not> defined (set R) (Sharp f,n)"
    by (rule 3(6))
  from 3(7) obtain d' where proc:
      "muterm_general_rta08_ur_redpair_proc J \<mu>
        (get_rel_impl redp) Pr U S ?d = return d'"
    and rec: "isOK (check_muterm_typed_dp_proof_production I J \<mu>
      (add_index i 1) R S (dpp_ops.pairs J d') child)"
    by (auto simp: Let_def)
  have child_fin: "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
      (set R) (set (dpp_ops.pairs J d')) (set S)"
    by (rule 3(1)[OF refl proc I_spec J_spec wf_R overlay_R fresh_R rec])
  show ?case
    apply (rule muterm_typed_general_usable_production_sound[
      where J=J and R=R and P=P and S=S and \<mu>=\<mu>
        and redp=redp and Pr=Pr and U=U and d'=d'])
       apply (rule J_spec)
      apply (rule wf_R)
     apply (rule overlay_R)
      apply (rule fresh_R)
     apply (rule proc)
    apply (rule child_fin)
    done
next
  case (4 I J \<mu> i R S P st sts child)
  let ?d = "dpp_ops.mk J False False P [] [] [] R"
  have I_spec: "tp_spec I" by (rule 4(2))
  have J_spec: "dpp_spec J" by (rule 4(3))
  have wf_R: "wf_trs (set R)" by (rule 4(4))
  have overlay_R: "csr_switch_overlay (set R)" by (rule 4(5))
  have fresh_R: "\<And>f n. \<not> defined (set R) (Sharp f,n)"
    by (rule 4(6))
  from 4(7) obtain d' where proc:
      "csr_instantiation_proc J \<mu> st sts ?d = return d'"
    and sub: "isOK (check_subseteq P (dpp_ops.pairs J d'))"
    and rec: "isOK (check_muterm_typed_dp_proof_production I J \<mu>
      (add_index i 1) R S (dpp_ops.pairs J d') child)"
    by (cases "csr_instantiation_proc J \<mu> st sts ?d"; auto simp: Let_def)
  have sub_ctx: "(check_subseteq P (dpp_ops.pairs J d') <+?
      (\<lambda>_. showsl_lit
        (STR ''typed MU-TERM augmentation removed an original pair''))) = return ()"
    using sub by (cases "check_subseteq P (dpp_ops.pairs J d')"; simp)
  have child_fin: "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
      (set R) (set (dpp_ops.pairs J d')) (set S)"
    apply (rule 4(1)[where ya="()"])
             apply (rule refl)
            apply (rule proc)
           apply (rule sub_ctx)
          apply (rule I_spec)
         apply (rule J_spec)
        apply (rule wf_R)
       apply (rule overlay_R)
      apply (rule fresh_R)
     apply (rule rec)
    done
  show ?case by (rule muterm_typed_pair_augmentation_production_sound[
    OF sub child_fin])
next
  case (5 I J \<mu> i R S P child)
  then show ?case by (solves \<open>auto simp: Let_def
    intro: muterm_typed_csr_component_production_sound\<close>)
next
  case (6 I J \<mu> i R S P U child)
  then show ?case by (solves \<open>simp\<close>)
next
  case (7 I J \<mu> i R S P child)
  then show ?case by (solves \<open>auto simp: Let_def
    intro: muterm_typed_expanded_csr_component_production_sound\<close>)
next
  case (8 I J \<mu> i R S P U child)
  let ?E = "muterm_expanded_pairs_list string_renameN P S"
  have I_spec: "tp_spec I" by (rule 8(1))
  have J_spec: "dpp_spec J" by (rule 8(2))
  have wf_R: "wf_trs (set R)" by (rule 8(3))
  have overlay_R: "csr_switch_overlay (set R)" by (rule 8(4))
  have fresh_R: "\<And>f n. \<not> defined (set R) (Sharp f,n)"
    by (rule 8(5))
  from 8(6) have closure_ok:
      "muterm_qcs_expanded_ur_closed_check R S U \<mu> P"
    and child_ok:
      "isOK (check_dp_termination_proof I J False (add_index i 1)
        (dpp_ops.mk J False False ?E [] [] [] U) child)"
    unfolding muterm_qcs_expanded_ur_closed_check_def Let_def by auto
  show ?case
    apply (rule muterm_typed_expanded_local_component_production_sound[
      where I=I and J=J and R=R and P=P and S=S and U=U and \<mu>=\<mu>
        and i="add_index i 1" and child=child])
          apply (rule I_spec)
         apply (rule J_spec)
        apply (rule wf_R)
       apply (rule overlay_R)
      apply (rule fresh_R)
     apply (rule closure_ok)
    apply (rule child_ok)
    done
next
  case (9 I J \<mu> i R S P child)
  then show ?case by (solves \<open>auto simp: Let_def
    intro: check_muterm_typed_expanded_ordinary_innermost_sound\<close>)
next
  case (10 I J \<mu> i R S P edps)
  have I_spec: "tp_spec I" by (rule 10(2))
  have J_spec: "dpp_spec J" by (rule 10(3))
  have wf_R: "wf_trs (set R)" by (rule 10(4))
  have overlay_R: "csr_switch_overlay (set R)" by (rule 10(5))
  have fresh_R: "\<And>f n. \<not> defined (set R) (Sharp f,n)"
    by (rule 10(6))
  from 10(7) obtain z where graph_eq:
      "check_muterm_typed_dep_graph \<mu> R S P edps = return z"
    and components: "isOK (check_muterm_innermost_typed_graph_components
      I J \<mu> i R S P edps)" by (auto simp: Let_def)
  have graph: "isOK (check_muterm_typed_dep_graph \<mu> R S P edps)"
    using graph_eq by simp
  have all_components: "\<forall>child C. (Some child,C) \<in> set edps \<longrightarrow>
      finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
        (set R) (set (filter (\<lambda>dp. dp \<in> set C) P)) (set S)"
    by (rule 10(1)[OF graph_eq I_spec J_spec wf_R overlay_R fresh_R components])
  show ?case by (solves \<open>
    rule muterm_typed_dep_graph_production_sound[OF graph];
    use all_components in auto\<close>)
next
  case (11 I J \<mu> i R S P child)
  then show ?case by (solves \<open>simp\<close>)
next
  case (12 I J \<mu> i R S P)
  then show ?case by (solves \<open>simp\<close>)
next
  case (13 I J \<mu> i R S P C rest)
  then show ?case by (solves \<open>auto\<close>)
next
  case (14 I J \<mu> i R S P child C rest)
  show ?case
  proof (intro allI impI)
    fix requested D
    assume mem: "(Some requested,D) \<in> set ((Some child,C)#rest)"
    have I_spec: "tp_spec I" by (rule 14(3))
    have J_spec: "dpp_spec J" by (rule 14(4))
    have wf_R: "wf_trs (set R)" by (rule 14(5))
    have overlay_R: "csr_switch_overlay (set R)" by (rule 14(6))
    have fresh_R: "\<And>f n. \<not> defined (set R) (Sharp f,n)"
      by (rule 14(7))
    from 14(8) obtain z where child_eq:
        "check_muterm_typed_dp_proof_production
          I J \<mu> (add_index i 1) R S
            (filter (\<lambda>dp. dp \<in> set C) P) child = return z"
      and rest_ok: "isOK (check_muterm_innermost_typed_graph_components
        I J \<mu> (add_index i 1) R S P rest)" by auto
    have child_ok: "isOK (check_muterm_typed_dp_proof_production
        I J \<mu> (add_index i 1) R S
          (filter (\<lambda>dp. dp \<in> set C) P) child)"
      using child_eq by simp
    show "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
        (set R) (set (filter (\<lambda>dp. dp \<in> set D) P)) (set S)"
    proof (cases "requested = child \<and> D = C")
      case True
      have child_fin: "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
          (set R) (set (filter (\<lambda>dp. dp \<in> set C) P)) (set S)"
        apply (rule 14(1))
             apply (rule I_spec)
            apply (rule J_spec)
           apply (rule wf_R)
          apply (rule overlay_R)
         apply (rule fresh_R)
        apply (rule child_ok)
        done
      then show ?thesis using True by simp
    next
      case False
      from mem False have rest_mem: "(Some requested,D) \<in> set rest" by auto
      have rest_sound: "\<forall>q E. (Some q,E) \<in> set rest \<longrightarrow>
          finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
            (set R) (set (filter (\<lambda>dp. dp \<in> set E) P)) (set S)"
        apply (rule 14(2))
             apply (rule child_eq)
            apply (rule I_spec)
           apply (rule J_spec)
          apply (rule wf_R)
         apply (rule overlay_R)
        apply (rule fresh_R)
       apply (rule rest_ok)
        done
      show ?thesis using rest_sound rest_mem by blast
    qed
  qed
qed

lemmas check_muterm_typed_dp_proof_production_sound_aux =
  check_muterm_typed_production_mutual_sound(1)
lemmas check_muterm_innermost_typed_graph_components_sound_aux =
  check_muterm_typed_production_mutual_sound(2)

theorem check_muterm_typed_dp_proof_production_sound:
  fixes I :: "('tp,('f::{showl,compare_order,countable},label_type) lab,string) tp_ops"
    and J :: "('dpp,('f,label_type) lab,string) dpp_ops"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and wf: "wf_trs (set R)"
    and overlay: "csr_switch_overlay (set R)"
    and fresh: "\<And>f n. \<not> defined (set R) (Sharp f,n)"
    and ok: "isOK (check_muterm_typed_dp_proof_production
      I J \<mu> i R S P p)"
  shows "finite_muterm_innermost_min_typed_dpp Sharp (mu_of \<mu>)
    (set R) (set P) (set S)"
  by (rule check_muterm_typed_dp_proof_production_sound_aux[
    OF I J wf overlay fresh ok])

lemma check_muterm_typed_production_imp_i4_good:
  fixes I :: "('tp,('f::{showl,compare_order,countable},label_type) lab,string) tp_ops"
    and J :: "('dpp,('f,label_type) lab,string) dpp_ops"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and wf: "wf_trs (set R)"
    and overlay: "csr_switch_overlay (set R)"
    and fresh: "\<And>h n. \<not> defined (set R) (Sharp h,n)"
    and ok: "isOK (check_muterm_typed_dp_proof_production
      I J m i R B Q q)"
  shows "muterm_i4.finite_muterm_i4_good_typed_dpp
    R (mu_of m) (set Q) (set B)"
proof -
  interpret M: muterm_i4_label R "mu_of m" "{}" "undefined"
    by (unfold_locales, rule wf)
  have raw: "finite_muterm_innermost_min_typed_dpp Sharp (mu_of m)
      (set R) (set Q) (set B)"
    by (rule check_muterm_typed_dp_proof_production_sound[
      OF I J wf overlay fresh ok])
  show ?thesis
    by (rule M.finite_muterm_innermost_min_typed_dpp_imp_i4_good[OF raw])
qed

lemma check_muterm_i4_graph_local_component_sound:
  fixes J :: "('dpp,('f::{showl,compare_order,countable},label_type) lab,string) dpp_ops"
  assumes J: "dpp_spec J" and wf: "wf_trs (set R)"
    and overlay: "csr_switch_overlay (set R)"
    and exact: "set B = set (muterm_exact_unhiding_rules_list Sharp m D R)"
    and fresh: "\<And>h n. \<not> defined (set R) (Sharp h,n)"
    and rules_unmarked: "\<And>fn. fn \<in> funas_trs (set R) \<Longrightarrow>
      \<not> is_sharp_lab (fst fn)"
    and marked: "\<And>f n. \<not> is_sharp_lab f \<Longrightarrow>
      mu_of m (Sharp f,n) = mu_of m (f,n)"
    and components: "isOK (check_muterm_i4_graph_components
      I J m i R B P edps)"
    and mem: "(Some (Muterm_Typed_Local_Usable U dp),C) \<in> set edps"
  shows "muterm_i4.finite_muterm_i4_good_typed_dpp
    R (mu_of m) (set P \<inter> set C) (set B)"
proof -
  interpret M: muterm_i4_label R "mu_of m" "{}" "undefined"
    by (unfold_locales, rule wf)
  from check_muterm_i4_graph_components_local_member[
    OF components mem]
  obtain j where rec: "isOK (check_muterm_recursive_dp_proof
    J m j R B (filter (\<lambda>lr. lr \<in> set R) U)
      (filter (\<lambda>x. x \<in> set C) P) dp)" by blast
  have good: "M.finite_muterm_i4_good_typed_dpp
    (set (filter (\<lambda>x. x \<in> set C) P)) (set B)"
    by (rule check_muterm_recursive_dp_proof_sound[
      OF J wf overlay exact fresh rules_unmarked marked rec])
  have set_filter: "set (filter (\<lambda>x. x \<in> set C) P) =
      set P \<inter> set C" by auto
  show "M.finite_muterm_i4_good_typed_dpp
      (set P \<inter> set C) (set B)"
    using good unfolding set_filter .
qed

lemma check_muterm_i4_graph_nonlocal_component_sound:
  fixes I :: "('tp,('f::{showl,compare_order,countable},label_type) lab,string) tp_ops"
    and J :: "('dpp,('f,label_type) lab,string) dpp_ops"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and wf: "wf_trs (set R)" and overlay: "csr_switch_overlay (set R)"
    and fresh: "\<And>h n. \<not> defined (set R) (Sharp h,n)"
    and components: "isOK (check_muterm_i4_graph_components
      I J m i R B P edps)"
    and mem: "(Some child,C) \<in> set edps"
    and nonlocal: "\<And>U dp.
      child \<noteq> Muterm_Typed_Local_Usable U dp"
  shows "muterm_i4.finite_muterm_i4_good_typed_dpp
    R (mu_of m) (set P \<inter> set C) (set B)"
proof -
  interpret M: muterm_i4_label R "mu_of m" "{}" "undefined"
    by (unfold_locales, rule wf)
  from check_muterm_i4_graph_components_nonlocal_member[
    OF components mem nonlocal]
  obtain j where prod: "isOK
    (check_muterm_typed_dp_proof_production I J m j R B
      (filter (\<lambda>x. x \<in> set C) P) child)" by blast
  from check_muterm_typed_production_imp_i4_good[
    where I=I and J=J and m=m and i=j and R=R and B=B
      and Q="filter (\<lambda>x. x \<in> set C) P" and q=child,
      OF I J wf overlay fresh prod]
  have good: "M.finite_muterm_i4_good_typed_dpp
    (set (filter (\<lambda>x. x \<in> set C) P)) (set B)" .
  have set_filter: "set (filter (\<lambda>x. x \<in> set C) P) =
      set P \<inter> set C" by auto
  show "M.finite_muterm_i4_good_typed_dpp
      (set P \<inter> set C) (set B)"
    using good unfolding set_filter .
qed

lemma check_muterm_i4_graph_component_sound:
  fixes I :: "('tp,('f::{showl,compare_order,countable},label_type) lab,string) tp_ops"
    and J :: "('dpp,('f,label_type) lab,string) dpp_ops"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and wf: "wf_trs (set R)"
    and overlay: "csr_switch_overlay (set R)"
    and exact: "set B = set (muterm_exact_unhiding_rules_list Sharp m D R)"
    and fresh: "\<And>h n. \<not> defined (set R) (Sharp h,n)"
    and rules_unmarked: "\<And>fn. fn \<in> funas_trs (set R) \<Longrightarrow>
      \<not> is_sharp_lab (fst fn)"
    and marked: "\<And>f n. \<not> is_sharp_lab f \<Longrightarrow>
      mu_of m (Sharp f,n) = mu_of m (f,n)"
    and components: "isOK (check_muterm_i4_graph_components
      I J m i R B P edps)"
    and mem: "(Some child,C) \<in> set edps"
  shows "muterm_i4.finite_muterm_i4_good_typed_dpp
    R (mu_of m) (set P \<inter> set C) (set B)"
proof -
  show ?thesis
  proof (cases "\<exists>U dp. child = Muterm_Typed_Local_Usable U dp")
    case True
    then obtain U dp where child:
        "child = Muterm_Typed_Local_Usable U dp" by blast
    have local_mem:
        "(Some (Muterm_Typed_Local_Usable U dp),C) \<in> set edps"
      using mem child by simp
    show ?thesis by (rule check_muterm_i4_graph_local_component_sound[
      OF J wf overlay exact fresh rules_unmarked marked components local_mem])
  next
    case False
    have nonlocal: "\<And>U dp.
        child \<noteq> Muterm_Typed_Local_Usable U dp"
      using False by blast
    show ?thesis by (rule check_muterm_i4_graph_nonlocal_component_sound[
      OF I J wf overlay fresh components mem nonlocal])
  qed
qed

lemma check_muterm_i4_graph_root_sound:
  fixes I :: "('tp,('f::{showl,compare_order,countable},label_type) lab,string) tp_ops"
    and J :: "('dpp,('f,label_type) lab,string) dpp_ops"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and wf: "wf_trs (set R)"
    and overlay: "csr_switch_overlay (set R)"
    and exact: "set B = set (muterm_exact_unhiding_rules_list Sharp m D R)"
    and fresh: "\<And>h n. \<not> defined (set R) (Sharp h,n)"
    and rules_unmarked: "\<And>fn. fn \<in> funas_trs (set R) \<Longrightarrow>
      \<not> is_sharp_lab (fst fn)"
    and marked: "\<And>f n. \<not> is_sharp_lab f \<Longrightarrow>
      mu_of m (Sharp f,n) = mu_of m (f,n)"
    and graph: "isOK (check_muterm_typed_dep_graph m R B P edps)"
    and components: "isOK (check_muterm_i4_graph_components
      I J m i R B P edps)"
  shows "muterm_i4.finite_muterm_i4_good_typed_dpp
    R (mu_of m) (set P) (set B)"
proof -
  interpret M: muterm_i4_label R "mu_of m" "{}" "undefined"
    by (unfold_locales, rule wf)
  show ?thesis
  proof (rule M.check_muterm_i4_good_dep_graph_sound[OF refl graph])
    fix child C
    assume mem: "(Some child,C) \<in> set edps"
    show "M.finite_muterm_i4_good_typed_dpp
      (set P \<inter> set C) (set B)"
      by (rule check_muterm_i4_graph_component_sound[
        OF I J wf overlay exact fresh rules_unmarked marked components mem])
  qed
qed

theorem check_muterm_i4_root_proof_sound:
  fixes I :: "('tp,('f::{showl,compare_order,countable},label_type) lab,string) tp_ops"
    and J :: "('dpp,('f,label_type) lab,string) dpp_ops"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and wf: "wf_trs (set R)"
    and overlay: "csr_switch_overlay (set R)"
    and exact: "set B = set (muterm_exact_unhiding_rules_list Sharp m D R)"
    and fresh: "\<And>h n. \<not> defined (set R) (Sharp h,n)"
    and rules_unmarked: "\<And>fn. fn \<in> funas_trs (set R) \<Longrightarrow>
      \<not> is_sharp_lab (fst fn)"
    and marked: "\<And>f n. \<not> is_sharp_lab f \<Longrightarrow>
      mu_of m (Sharp f,n) = mu_of m (f,n)"
    and ok: "isOK (check_muterm_i4_root_proof I J m i R B P p)"
  shows "muterm_i4.finite_muterm_i4_good_typed_dpp
    R (mu_of m) (set P) (set B)"
proof (cases "\<exists>edps. p = Muterm_Typed_Dep_Graph edps")
  case True
  then obtain edps where p: "p = Muterm_Typed_Dep_Graph edps" by blast
  from ok p have graph:
      "isOK (check_muterm_typed_dep_graph m R B P edps)"
    and components: "isOK (check_muterm_i4_graph_components
      I J m i R B P edps)" by auto
  show ?thesis by (rule check_muterm_i4_graph_root_sound[
    OF I J wf overlay exact fresh rules_unmarked marked graph components])
next
  case False
  have eq: "check_muterm_i4_root_proof I J m i R B P p =
      check_muterm_typed_dp_proof_production I J m i R B P p"
    by (rule check_muterm_i4_root_proof_non_graph[OF False])
  from ok have prod:
      "isOK (check_muterm_typed_dp_proof_production I J m i R B P p)"
    unfolding eq .
  from check_muterm_typed_production_imp_i4_good[
    where I=I and J=J and m=m and i=i and R=R and B=B and Q=P and q=p,
      OF I J wf overlay fresh prod]
  show ?thesis .
qed

end
