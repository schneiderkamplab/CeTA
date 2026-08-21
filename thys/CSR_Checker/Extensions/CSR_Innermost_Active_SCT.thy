(*
Author: Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Innermost_Active_SCT
  imports CSR_Checker_Extensions.CSR_Innermost_DP_Checker
begin

lemma csdp_Fun_undefined_active_args_NF:
  assumes wf: "wf_trs R"
    and undef: "\<not> defined R (shp f, length ss)"
    and marked_inj: "inj shp"
    and args_NF: "\<And>i. i < length ss \<Longrightarrow>
      i \<in> \<mu> (f, length ss) \<Longrightarrow>
      ss ! i \<in> NF (csstep \<mu> R)"
  shows "Fun (shp f) ss \<in> NF (csdp_step shp \<mu> R)"
proof (unfold NF_iff_no_step, intro allI notI)
  fix t
  assume step: "(Fun (shp f) ss, t) \<in> csdp_step shp \<mu> R"
  from step obtain p where
    step_p: "(Fun (shp f) ss,t) \<in> csdp_step_p shp \<mu> p R"
    unfolding csdp_step_def by blast
  from step_p obtain lr \<sigma> where
    rw: "(Fun (shp f) ss,t) \<in> rstep_r_p_s R lr p \<sigma>"
    and cond: "csdp_step_cond shp \<mu> p (Fun (shp f) ss)"
    unfolding csdp_step_p_def by auto
  show False
  proof (cases p)
    case Nil
    from rw Nil have lr: "lr \<in> R"
      and lhs: "fst lr \<cdot> \<sigma> = Fun (shp f) ss"
      unfolding rstep_r_p_s_def' by auto
    from wf lr have lhs_fun: "is_Fun (fst lr)"
      unfolding wf_trs_def by (cases lr, force)
    then obtain g ts where lhs0: "fst lr = Fun g ts"
      by (cases "fst lr", auto)
    from lhs lhs0 have g: "g = shp f" and len: "length ts = length ss"
      by auto
    from lr lhs0 g len have "defined R (shp f, length ss)"
      unfolding defined_def by (cases lr, auto)
    with undef show False by contradiction
  next
    case (Cons i q)
    from rw[unfolded rstep_r_p_s_def'] Cons have i: "i < length ss"
      and q_pos: "q \<in> poss (ss ! i)"
      and t_def: "t = Fun (shp f) (take i ss @
        (ctxt_of_pos_term q (ss ! i))\<langle>snd lr \<cdot> \<sigma>\<rangle> #
        drop (Suc i) ss)"
      by auto
    let ?ts = "take i ss @
      (ctxt_of_pos_term q (ss ! i))\<langle>snd lr \<cdot> \<sigma>\<rangle> #
      drop (Suc i) ss"
    have qrstep: "(Fun (shp f) ss,t) \<in>
        qrstep_r_p_s False {} R lr ([i] @ q) \<sigma>"
      using rw unfolding Cons qrstep_r_p_s_def rstep_r_p_s_def' by auto
    have sub_qrstep: "(Fun (shp f) ss |_ [i],t |_ [i]) \<in>
        qrstep_r_p_s False {} R lr q \<sigma>"
      by (rule qrstep_subt_at_gen[OF qrstep])
    have sub: "(ss ! i, ?ts ! i) \<in> rstep_r_p_s R lr q \<sigma>"
      using sub_qrstep t_def i
      unfolding qrstep_r_p_s_def rstep_r_p_s_def'
      by auto
    from cond[unfolded csdp_step_cond_def, rule_format,
        of "[]" i q] i q_pos Cons obtain g where
      marked: "shp f = shp g" and active_g: "i \<in> \<mu> (g, length ss)"
      by auto
    from injD[OF marked_inj marked] active_g
    have active: "i \<in> \<mu> (f, length ss)" by simp
    have cond_q: "csstep_cond \<mu> q (ss ! i)"
    proof (unfold csstep_cond_def, intro allI impI)
      fix p1 j p2
      assume A: "q = p1 @ j # p2 \<and> q \<in> poss (ss ! i)"
      from cond[unfolded csdp_step_cond_def, rule_format,
          of "i # p1" j p2] A Cons i
      show "\<exists>g us. ss ! i |_ p1 = Fun g us \<and>
        j \<in> \<mu> (g, length us)"
        by auto
    qed
    have sub_p: "(ss ! i, ?ts ! i) \<in> csstep_p \<mu> R q"
      unfolding csstep_p_def using sub cond_q by (cases lr, auto)
    have "(ss ! i, ?ts ! i) \<in> csstep \<mu> R"
      unfolding csstep_def using sub_p by blast
    with args_NF[OF i active] show False
      unfolding NF_iff_no_step by blast
  qed
qed

lemma innermost_pair_source_Sharp_active_arg_NF:
  assumes source: "innermost_pair_source Sharp \<mu> R
      (Fun (Sharp f) ss \<cdot> \<tau>)"
    and i: "i < length ss"
    and active: "i \<in> \<mu> (f, length ss)"
  shows "ss ! i \<cdot> \<tau> \<in> NF (csstep \<mu> R)"
proof -
  from source obtain l r \<sigma> where rule: "(l,r) \<in> R"
    and fun_l: "is_Fun l"
    and sharp: "Fun (Sharp f) ss \<cdot> \<tau> = sharp_term Sharp (l \<cdot> \<sigma>)"
    and normal: "\<And>u. mu_supt \<mu> (l \<cdot> \<sigma>) u \<Longrightarrow>
      u \<in> NF (csstep \<mu> R)"
    unfolding innermost_pair_source_def by blast
  from fun_l obtain g ls where l: "l = Fun g ls"
    by (cases l, auto)
  from sharp[unfolded l] have g: "g = f"
    and args: "map (\<lambda>s. s \<cdot> \<sigma>) ls = map (\<lambda>s. s \<cdot> \<tau>) ss"
    by auto
  have root_active: "mu_supt \<mu>
      (Fun f (map (\<lambda>s. s \<cdot> \<tau>) ss)) (ss ! i \<cdot> \<tau>)"
  proof (unfold mu_supt_def, intro exI[of _ i] exI[of _ "[]"], intro conjI)
    show "i # [] \<in> mu_poss \<mu> (Fun f (map (\<lambda>s. s \<cdot> \<tau>) ss))"
      using i active by (cases "ss ! i \<cdot> \<tau>", auto simp: nth_map)
    show "Fun f (map (\<lambda>s. s \<cdot> \<tau>) ss) |_ (i # []) = ss ! i \<cdot> \<tau>"
      using i by (simp add: nth_map)
  qed
  have l_inst: "l \<cdot> \<sigma> = Fun f (map (\<lambda>s. s \<cdot> \<tau>) ss)"
    using args unfolding l g by simp
  have "mu_supt \<mu> (l \<cdot> \<sigma>) (ss ! i \<cdot> \<tau>)"
    unfolding l_inst by (rule root_active)
  then show ?thesis by (rule normal)
qed

lemma innermost_pair_source_root_supt_NF:
  assumes source: "innermost_pair_source Sharp \<mu> R (u \<cdot> \<tau>)"
    and active: "csr_dp_root_supt \<mu> u w"
  shows "w \<cdot> \<tau> \<in> NF (csstep \<mu> R)"
proof -
  have fun_u: "is_Fun u"
    using active unfolding csr_dp_root_supt_def mu_supt_def
    by (cases u rule: csr_dp_unsharp_root.cases) auto
  from source obtain l r \<sigma> where rule: "(l,r) \<in> R"
    and fun_l: "is_Fun l"
    and source_eq: "u \<cdot> \<tau> = sharp_term Sharp (l \<cdot> \<sigma>)"
    and normal: "\<And>x. mu_supt \<mu> (l \<cdot> \<sigma>) x \<Longrightarrow>
      x \<in> NF (csstep \<mu> R)"
    unfolding innermost_pair_source_def by blast
  have fun_inst: "is_Fun (l \<cdot> \<sigma>)"
    using fun_l by (cases l) auto
  from csr_dp_root_supt_subst[OF fun_u active, of \<tau>]
  have active0: "csr_dp_root_supt \<mu>
      (sharp_term Sharp (l \<cdot> \<sigma>)) (w \<cdot> \<tau>)"
    unfolding source_eq .
  from active0 have "mu_supt \<mu> (l \<cdot> \<sigma>) (w \<cdot> \<tau>)"
    unfolding csr_dp_root_supt_sharp[OF fun_inst] .
  then show ?thesis by (rule normal)
qed

definition innermost_csr_sct_target_covered ::
  "((('f::{showl,compare_order}, 'l::{showl,compare_order}) lab), 'v) trs
    \<Rightarrow> (('f, 'l) lab) mu \<Rightarrow> bool"
where
  "innermost_csr_sct_target_covered P \<mu> \<longleftrightarrow>
    (\<forall>(u,v)\<in>P. \<exists>f us g vs.
      u = Fun (Sharp f) us \<and> v = Fun (Sharp g) vs \<and>
      (\<forall>j < length vs. j \<in> \<mu> (g, length vs) \<longrightarrow>
        csr_dp_root_supt \<mu> u (vs ! j)))"

lemma innermost_rrstep_target_NF_csdp:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and covered: "innermost_csr_sct_target_covered P \<mu>"
    and step: "(s,t) \<in> innermost_rrstep Sharp \<mu> R P"
  shows "t \<in> NF (csdp_step Sharp \<mu> R)"
proof -
  from step have rr: "(s,t) \<in> rrstep P"
    and source: "innermost_pair_source Sharp \<mu> R s"
    unfolding innermost_rrstep_def by auto
  have ex: "\<exists>u v \<tau>. (u,v) \<in> P \<and>
      s = u \<cdot> \<tau> \<and> t = v \<cdot> \<tau>"
    using rr unfolding rrstep_def' by simp
  show ?thesis
  proof (rule exE[OF ex])
    fix u
    assume ex_v: "\<exists>v \<tau>. (u,v) \<in> P \<and>
      s = u \<cdot> \<tau> \<and> t = v \<cdot> \<tau>"
    show ?thesis
    proof (rule exE[OF ex_v])
      fix v
      assume ex_tau: "\<exists>\<tau>. (u,v) \<in> P \<and>
        s = u \<cdot> \<tau> \<and> t = v \<cdot> \<tau>"
      show ?thesis
      proof (rule exE[OF ex_tau])
        fix \<tau>
        assume st: "(u,v) \<in> P \<and>
          s = u \<cdot> \<tau> \<and> t = v \<cdot> \<tau>"
        have pair: "(u,v) \<in> P" by (rule conjunct1[OF st])
        have s: "s = u \<cdot> \<tau>"
          by (rule conjunct1[OF conjunct2[OF st]])
        have t: "t = v \<cdot> \<tau>"
          by (rule conjunct2[OF conjunct2[OF st]])
        have ex_shape: "\<exists>f us g vs.
            u = Fun (Sharp f) us \<and> v = Fun (Sharp g) vs \<and>
            (\<forall>j < length vs. j \<in> \<mu> (g, length vs) \<longrightarrow>
              csr_dp_root_supt \<mu> u (vs ! j))"
          using covered pair
          unfolding innermost_csr_sct_target_covered_def by auto
        show ?thesis
        proof (rule exE[OF ex_shape])
          fix f
          assume ex_us: "\<exists>us g vs.
            u = Fun (Sharp f) us \<and> v = Fun (Sharp g) vs \<and>
            (\<forall>j < length vs. j \<in> \<mu> (g, length vs) \<longrightarrow>
              csr_dp_root_supt \<mu> u (vs ! j))"
          show ?thesis
          proof (rule exE[OF ex_us])
            fix us
            assume ex_g: "\<exists>g vs.
              u = Fun (Sharp f) us \<and> v = Fun (Sharp g) vs \<and>
              (\<forall>j < length vs. j \<in> \<mu> (g, length vs) \<longrightarrow>
                csr_dp_root_supt \<mu> u (vs ! j))"
            show ?thesis
            proof (rule exE[OF ex_g])
              fix g
              assume ex_vs: "\<exists>vs.
                u = Fun (Sharp f) us \<and> v = Fun (Sharp g) vs \<and>
                (\<forall>j < length vs. j \<in> \<mu> (g, length vs) \<longrightarrow>
                  csr_dp_root_supt \<mu> u (vs ! j))"
              show ?thesis
              proof (rule exE[OF ex_vs])
                fix vs
                assume shape: "u = Fun (Sharp f) us \<and>
                  v = Fun (Sharp g) vs \<and>
                  (\<forall>j < length vs. j \<in> \<mu> (g, length vs) \<longrightarrow>
                    csr_dp_root_supt \<mu> u (vs ! j))"
                have u: "u = Fun (Sharp f) us"
                  by (rule conjunct1[OF shape])
                have tail: "v = Fun (Sharp g) vs \<and>
                    (\<forall>j < length vs. j \<in> \<mu> (g, length vs) \<longrightarrow>
                      csr_dp_root_supt \<mu> u (vs ! j))"
                  by (rule conjunct2[OF shape])
                have v: "v = Fun (Sharp g) vs"
                  by (rule conjunct1[OF tail])
                have cover0: "\<forall>j < length vs.
                    j \<in> \<mu> (g, length vs) \<longrightarrow>
                    csr_dp_root_supt \<mu> u (vs ! j)"
                  by (rule conjunct2[OF tail])
                have cover: "\<And>j. j < length vs \<Longrightarrow>
                    j \<in> \<mu> (g, length vs) \<Longrightarrow>
                    csr_dp_root_supt \<mu> u (vs ! j)"
                  by (rule cover0[rule_format])
                have args_NF: "map (\<lambda>x. x \<cdot> \<tau>) vs ! j \<in>
                    NF (csstep \<mu> R)"
                  if j: "j < length (map (\<lambda>x. x \<cdot> \<tau>) vs)"
                    and active: "j \<in> \<mu>
                      (g, length (map (\<lambda>x. x \<cdot> \<tau>) vs))"
                  for j
                proof -
                  have j': "j < length vs" using j by simp
                  have active': "j \<in> \<mu> (g, length vs)" using active by simp
                  from innermost_pair_source_root_supt_NF[
                      OF source[unfolded s] cover[OF j' active']]
                  show ?thesis using j' by (simp add: nth_map)
                qed
                have "Fun (Sharp g) (map (\<lambda>x. x \<cdot> \<tau>) vs) \<in>
                    NF (csdp_step Sharp \<mu> R)"
                  by (rule csdp_Fun_undefined_active_args_NF[
                    OF wf fresh inj_Sharp args_NF])
                then show ?thesis unfolding t v by simp
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma finite_min_csr_dpp_imp_finite_innermost_mode:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and covered: "innermost_csr_sct_target_covered P \<mu>"
    and fin: "finite_min_csr_dpp Sharp \<mu> P R"
  shows "finite_mode_csr_dpp Sharp CSR_Innermost \<mu> P R"
proof -
  have pair_sub: "innermost_rrstep Sharp \<mu> R P \<subseteq>
      csr_min_pair_step Sharp \<mu> P R"
  proof
    fix st
    assume st: "st \<in> innermost_rrstep Sharp \<mu> R P"
    obtain s t where st_eq: "st = (s,t)" by (cases st)
    from st[unfolded st_eq] have rr: "(s,t) \<in> rrstep P"
      unfolding innermost_rrstep_def by blast
    have nf: "t \<in> NF (csdp_step Sharp \<mu> R)"
      by (rule innermost_rrstep_target_NF_csdp[
        OF wf fresh covered st[unfolded st_eq]])
    have sn: "SN_on (csdp_step Sharp \<mu> R) {t}"
      by (rule NF_imp_SN_on[OF nf])
    show "st \<in> csr_min_pair_step Sharp \<mu> P R"
      unfolding st_eq csr_min_pair_step_def using rr sn by simp
  qed
  from fin show ?thesis
    unfolding finite_min_csr_dpp_def finite_mode_csr_dpp_def
      csr_mode_rrstep.simps csr_mode_csdp_step.simps
    by (rule SN_rel_mono[OF pair_sub innermost_csdp_step_subset_csdp_step])
qed

theorem finite_innermost_csr_dpp_sct_active_subterm:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and covered: "innermost_csr_sct_target_covered P \<mu>"
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
  shows "finite_mode_csr_dpp Sharp CSR_Innermost \<mu> P R"
proof (rule finite_min_csr_dpp_imp_finite_innermost_mode[
    OF wf fresh covered])
  show "finite_min_csr_dpp Sharp \<mu> P R"
    by (rule finite_min_csr_dpp_sct_active_subterm[
      OF wf fresh pair_shape graphs edge check])
qed

fun innermost_csr_sct_target_covered_check where
  "innermost_csr_sct_target_covered_check \<mu> (u, Fun (Sharp g) vs) =
    (csr_sct_sharp_term u \<and>
      list_all (\<lambda>j. j \<notin> mu_of \<mu> (g, length vs) \<or>
        vs ! j \<in> set (csr_dp_root_supt_list \<mu> u)) [0..<length vs])"
| "innermost_csr_sct_target_covered_check \<mu> st = False"

lemma innermost_csr_sct_target_covered_check_sound:
  assumes "list_all (innermost_csr_sct_target_covered_check \<mu>) P"
  shows "innermost_csr_sct_target_covered (set P) (mu_of \<mu>)"
  unfolding innermost_csr_sct_target_covered_def
proof (intro ballI)
  fix st
  assume st: "st \<in> set P"
  show "case st of (u,v) \<Rightarrow> \<exists>f us g vs.
      u = Fun (Sharp f) us \<and> v = Fun (Sharp g) vs \<and>
      (\<forall>j<length vs. j \<in> mu_of \<mu> (g, length vs) \<longrightarrow>
        csr_dp_root_supt (mu_of \<mu>) u (vs ! j))"
  proof (cases st)
    case (Pair u v)
    from assms st have check:
      "innermost_csr_sct_target_covered_check \<mu> (u,v)"
      unfolding list_all_iff Pair by blast
    show ?thesis
    proof (cases v)
      case (Var x)
      then show ?thesis using check Pair by simp
    next
      case (Fun h vs)
      show ?thesis
      proof (cases h)
        case (Lab h a)
        then show ?thesis using check Pair Fun by simp
      next
        case (FunLab h hs)
        then show ?thesis using check Pair Fun by simp
      next
        case (UnLab h)
        then show ?thesis using check Pair Fun by simp
      next
        case (Sharp g)
        from check Fun Sharp have source: "csr_sct_sharp_term u"
          and cover: "list_all (\<lambda>j.
            j \<notin> mu_of \<mu> (g, length vs) \<or>
            vs ! j \<in> set (csr_dp_root_supt_list \<mu> u))
            [0..<length vs]" by auto
        from source obtain f us where source_eq: "u = Fun (Sharp f) us"
          by auto
        show ?thesis
          using cover source_eq Pair Fun Sharp
          by (auto simp: list_all_iff)
      qed
    qed
  qed
qed

definition innermost_csr_sct_active_subterm_proc where
  "innermost_csr_sct_active_subterm_proc J \<mu> Gs dpp = do {
    check_wf_trs (dpp_ops.rules J dpp);
    csr_rules_sharp_fresh_check (dpp_ops.rules J dpp);
    check (list_all (innermost_csr_sct_target_covered_check \<mu>)
      (dpp_ops.pairs J dpp))
      (showsl_lit (STR ''innermost CSR SCT target arguments are not source-covered''));
    csr_sct_active_subterm_proc J \<mu> Gs dpp
  }"

lemma innermost_csr_sct_active_subterm_proc_sound:
  assumes J: "dpp_spec J"
    and ok: "isOK (innermost_csr_sct_active_subterm_proc J \<mu> Gs dpp)"
  shows "finite_mode_csr_dpp Sharp CSR_Innermost (mu_of \<mu>)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
proof -
  from ok have wf_check: "isOK (check_wf_trs (dpp_ops.rules J dpp))"
    and fresh_check:
      "isOK (csr_rules_sharp_fresh_check (dpp_ops.rules J dpp))"
    and covered_check:
      "list_all (innermost_csr_sct_target_covered_check \<mu>)
        (dpp_ops.pairs J dpp)"
    and sct_ok: "isOK (csr_sct_active_subterm_proc J \<mu> Gs dpp)"
    unfolding innermost_csr_sct_active_subterm_proc_def by auto
  from wf_check have wf: "wf_trs (set (dpp_ops.rules J dpp))"
    by auto
  have fresh: "\<And>f n.
      \<not> defined (set (dpp_ops.rules J dpp)) (Sharp f,n)"
    by (rule csr_rules_sharp_fresh_check_sound[OF fresh_check])
  have covered: "innermost_csr_sct_target_covered
      (set (dpp_ops.pairs J dpp)) (mu_of \<mu>)"
    by (rule innermost_csr_sct_target_covered_check_sound[OF covered_check])
  have fin_min: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
    by (rule csr_sct_active_subterm_proc_sound[OF J wf fresh sct_ok])
  show ?thesis
    by (rule finite_min_csr_dpp_imp_finite_innermost_mode[
      OF wf fresh covered fin_min])
qed

fun check_innermost_csr_dp_termination_proof_active_sct ::
  "('tp, ('f::{showl,compare_order,countable}, label_type) lab,
      string) tp_ops \<Rightarrow>
   ('dpp, ('f,label_type) lab,string) dpp_ops \<Rightarrow>
   (('f,label_type) lab) muL \<Rightarrow> showsl \<Rightarrow> 'dpp \<Rightarrow>
   ('f,label_type,string) csr_dp_termination_proof \<Rightarrow> showsl check"
and check_innermost_csr_dp_graph_components_active_sct ::
  "('tp, ('f::{showl,compare_order,countable}, label_type) lab,
      string) tp_ops \<Rightarrow>
   ('dpp, ('f,label_type) lab,string) dpp_ops \<Rightarrow>
   (('f,label_type) lab) muL \<Rightarrow> showsl \<Rightarrow> 'dpp \<Rightarrow>
   (('f,label_type,string) csr_dp_termination_proof option \<times>
    ('f,label_type,string) trsLL) list \<Rightarrow> showsl check"
where
  "check_innermost_csr_dp_termination_proof_active_sct I J \<mu> i dpp
      (CSR_DP_Dep_Graph_Proc edps) =
    debug i (STR ''innermost CSR-DP dependency graph'') (do {
      _ \<leftarrow> check_innermost_csr_dep_graph_proc J \<mu> dpp edps;
      check_innermost_csr_dp_graph_components_active_sct I J \<mu> i dpp edps
    })"
| "check_innermost_csr_dp_termination_proof_active_sct I J \<mu> i dpp
      (CSR_DP_Size_Change_Subterm_Proc graphs) =
    (if list_all (innermost_csr_sct_target_covered_check \<mu>)
          (dpp_ops.pairs J dpp)
     then debug i (STR ''innermost CSR active size-change'')
       (innermost_csr_sct_active_subterm_proc J \<mu> graphs dpp)
     else check_innermost_csr_dp_termination_proof I J \<mu> i dpp
       (CSR_DP_Size_Change_Subterm_Proc graphs))"
| "check_innermost_csr_dp_termination_proof_active_sct I J \<mu> i dpp prf =
    check_innermost_csr_dp_termination_proof I J \<mu> i dpp prf"
| "check_innermost_csr_dp_graph_components_active_sct I J \<mu> i dpp [] =
    succeed"
| "check_innermost_csr_dp_graph_components_active_sct I J \<mu> i dpp
      ((None,P)#rest) =
    check_innermost_csr_dp_graph_components_active_sct I J \<mu>
      (add_index i 1) dpp rest"
| "check_innermost_csr_dp_graph_components_active_sct I J \<mu> i dpp
      ((Some prf,P)#rest) = do {
    check_innermost_csr_dp_termination_proof_active_sct I J \<mu>
      (add_index i 1) (dpp_ops.intersect_pairs J dpp P) prf;
    check_innermost_csr_dp_graph_components_active_sct I J \<mu>
      (add_index i 1) dpp rest
  }"

lemma check_innermost_csr_dp_graph_components_active_sct_member:
  assumes ok: "isOK (check_innermost_csr_dp_graph_components_active_sct
      I J \<mu> i dpp edps)"
    and mem: "(Some prf,P) \<in> set edps"
  shows "\<exists>j. isOK (check_innermost_csr_dp_termination_proof_active_sct
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
    from Cons.prems head None have tail:
      "isOK (check_innermost_csr_dp_graph_components_active_sct
        I J \<mu> (add_index i 1) dpp rest)" by simp
    from Cons.prems head None have mem': "(Some prf,P) \<in> set rest"
      by auto
    show ?thesis by (rule Cons.hyps[OF tail mem'])
  next
    case (Some p)
    show ?thesis
    proof (cases "(Some prf,P) = head")
      case True
      from Cons.prems head Some True show ?thesis by auto
    next
      case False
      from Cons.prems head Some have tail:
        "isOK (check_innermost_csr_dp_graph_components_active_sct
          I J \<mu> (add_index i 1) dpp rest)" by simp
      from Cons.prems False have mem': "(Some prf,P) \<in> set rest"
        by auto
      show ?thesis by (rule Cons.hyps[OF tail mem'])
    qed
  qed
qed

lemma check_innermost_csr_dp_termination_proof_active_sct_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and plain: "plain_csr_dpp J dpp"
    and ok: "isOK (check_innermost_csr_dp_termination_proof_active_sct
      I J \<mu> i dpp prf)"
  shows "finite_mode_csr_dpp Sharp CSR_Innermost (mu_of \<mu>)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
  using ok plain
proof (induct "prf" arbitrary: dpp i)
  case CSR_DP_P_is_Empty
  from CSR_DP_P_is_Empty.prems(1) have old:
    "isOK (check_innermost_csr_dp_termination_proof I J \<mu> i dpp
      CSR_DP_P_is_Empty)"
    by (simp only: check_innermost_csr_dp_termination_proof_active_sct.simps)
  show ?case by (rule check_innermost_csr_dp_termination_proof_sound[
    OF I J CSR_DP_P_is_Empty.prems(2) old])
next
  case (CSR_DP_Ordinary_Proof x)
  from CSR_DP_Ordinary_Proof.prems(1) have old:
    "isOK (check_innermost_csr_dp_termination_proof I J \<mu> i dpp
      (CSR_DP_Ordinary_Proof x))"
    by (simp only: check_innermost_csr_dp_termination_proof_active_sct.simps)
  show ?case by (rule check_innermost_csr_dp_termination_proof_sound[
    OF I J CSR_DP_Ordinary_Proof.prems(2) old])
next
  case (CSR_DP_Subterm_Criterion_Proc x1 x2 x3 subproof)
  from CSR_DP_Subterm_Criterion_Proc.prems(1) have old:
    "isOK (check_innermost_csr_dp_termination_proof I J \<mu> i dpp
      (CSR_DP_Subterm_Criterion_Proc x1 x2 x3 subproof))"
    by (simp only: check_innermost_csr_dp_termination_proof_active_sct.simps)
  show ?case by (rule check_innermost_csr_dp_termination_proof_sound[
    OF I J CSR_DP_Subterm_Criterion_Proc.prems(2) old])
next
  case (CSR_DP_Gen_Subterm_Criterion_Proc x1 x2 subproof)
  from CSR_DP_Gen_Subterm_Criterion_Proc.prems(1) have old:
    "isOK (check_innermost_csr_dp_termination_proof I J \<mu> i dpp
      (CSR_DP_Gen_Subterm_Criterion_Proc x1 x2 subproof))"
    by (simp only: check_innermost_csr_dp_termination_proof_active_sct.simps)
  show ?case by (rule check_innermost_csr_dp_termination_proof_sound[
    OF I J CSR_DP_Gen_Subterm_Criterion_Proc.prems(2) old])
next
  case (CSR_DP_Usable_Rules_Proc x1 subproof)
  from CSR_DP_Usable_Rules_Proc.prems(1) have old:
    "isOK (check_innermost_csr_dp_termination_proof I J \<mu> i dpp
      (CSR_DP_Usable_Rules_Proc x1 subproof))"
    by (simp only: check_innermost_csr_dp_termination_proof_active_sct.simps)
  show ?case by (rule check_innermost_csr_dp_termination_proof_sound[
    OF I J CSR_DP_Usable_Rules_Proc.prems(2) old])
next
  case (CSR_DP_Dep_Graph_Proc edps)
  from CSR_DP_Dep_Graph_Proc.prems(1) have graph_ok:
      "isOK (check_innermost_csr_dep_graph_proc J \<mu> dpp edps)"
    and components_ok:
      "isOK (check_innermost_csr_dp_graph_components_active_sct
        I J \<mu> i dpp edps)" by auto
  show ?case
  proof (rule check_innermost_csr_dep_graph_proc_sound[
      OF J CSR_DP_Dep_Graph_Proc.prems(2) graph_ok])
    fix proof_id C
    assume mem: "(Some proof_id,C) \<in> set edps"
    let ?d = "dpp_ops.intersect_pairs J dpp C"
    from check_innermost_csr_dp_graph_components_active_sct_member[
      OF components_ok mem]
    obtain j where rec:
      "isOK (check_innermost_csr_dp_termination_proof_active_sct
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
  from CSR_DP_Instantiation_Proc.prems(1) have old:
    "isOK (check_innermost_csr_dp_termination_proof I J \<mu> i dpp
      (CSR_DP_Instantiation_Proc x1 x2 subproof))"
    by (simp only: check_innermost_csr_dp_termination_proof_active_sct.simps)
  show ?case by (rule check_innermost_csr_dp_termination_proof_sound[
    OF I J CSR_DP_Instantiation_Proc.prems(2) old])
next
  case (CSR_DP_Forward_Instantiation_Proc x1 x2 subproof)
  from CSR_DP_Forward_Instantiation_Proc.prems(1) have old:
    "isOK (check_innermost_csr_dp_termination_proof I J \<mu> i dpp
      (CSR_DP_Forward_Instantiation_Proc x1 x2 subproof))"
    by (simp only: check_innermost_csr_dp_termination_proof_active_sct.simps)
  show ?case by (rule check_innermost_csr_dp_termination_proof_sound[
    OF I J CSR_DP_Forward_Instantiation_Proc.prems(2) old])
next
  case (CSR_DP_Redpair_UR_Proc x1 x2 x3 subproof)
  from CSR_DP_Redpair_UR_Proc.prems(1) have old:
    "isOK (check_innermost_csr_dp_termination_proof I J \<mu> i dpp
      (CSR_DP_Redpair_UR_Proc x1 x2 x3 subproof))"
    by (simp only: check_innermost_csr_dp_termination_proof_active_sct.simps)
  show ?case by (rule check_innermost_csr_dp_termination_proof_sound[
    OF I J CSR_DP_Redpair_UR_Proc.prems(2) old])
next
  case (CSR_DP_Size_Change_Subterm_Proc graphs)
  show ?case
  proof (cases "list_all (innermost_csr_sct_target_covered_check \<mu>)
      (dpp_ops.pairs J dpp)")
    case True
    from CSR_DP_Size_Change_Subterm_Proc.prems(1) True have proc:
      "isOK (innermost_csr_sct_active_subterm_proc J \<mu> graphs dpp)"
      by simp
    show ?thesis
      by (rule innermost_csr_sct_active_subterm_proc_sound[OF J proc])
  next
    case False
    from CSR_DP_Size_Change_Subterm_Proc.prems(1) False have old:
      "isOK (check_innermost_csr_dp_termination_proof I J \<mu> i dpp
        (CSR_DP_Size_Change_Subterm_Proc graphs))"
      by simp
    show ?thesis by (rule check_innermost_csr_dp_termination_proof_sound[
      OF I J CSR_DP_Size_Change_Subterm_Proc.prems(2) old])
  qed
qed

definition check_innermost_csr_termination_proof_active_sct ::
  "('tp, ('f::{showl,compare_order,countable}, label_type) lab,
      string) tp_ops \<Rightarrow>
   ('dpp, ('f,label_type) lab,string) dpp_ops \<Rightarrow>
   showsl \<Rightarrow> (('f,label_type) lab) muL \<Rightarrow>
   ('f,label_type,string) trsLL \<Rightarrow>
   ('f,label_type,string) trsLL \<Rightarrow>
   ('f,label_type,string) csr_dp_termination_proof \<Rightarrow> showsl check"
where
  "check_innermost_csr_termination_proof_active_sct I J i \<mu> R P prf =
    debug i (STR ''innermost CSR dependency pairs'') (do {
      check_csr_orthogonal R;
      csr_sharp_mu_check \<mu>;
      dpp \<leftarrow> mu_csr_dependency_pairs_tt Sharp J \<mu> R P;
      check_innermost_csr_dp_termination_proof_active_sct I J \<mu>
        (add_index i 1) dpp prf
    })"

lemma check_innermost_csr_termination_proof_active_sct_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_innermost_csr_termination_proof_active_sct
      I J i \<mu> R P prf)"
  shows "SN (csstep (mu_of \<mu>) (set R))"
proof -
  from ok obtain d where ortho_ok: "isOK (check_csr_orthogonal R)"
    and mu_dp: "mu_csr_dependency_pairs_tt Sharp J \<mu> R P = return d"
    and rec: "isOK (check_innermost_csr_dp_termination_proof_active_sct
      I J \<mu> (add_index i 1) d prf)"
    unfolding check_innermost_csr_termination_proof_active_sct_def by auto
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
    by (rule check_innermost_csr_dp_termination_proof_active_sct_sound[
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
