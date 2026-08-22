(*
Author:  Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Frozen_Recursive_Subterm
  imports CSR_Mixed_Subterm_Proofs
begin

text \<open>
  A marked CS-DP root cannot be rewritten, and a replacement-map-inactive
  argument of that root is preserved by every connecting CS-DP sequence.
  The same is true of the sole argument of the fresh unsharp unhiding symbol.
  Consequently we may apply an arbitrary, well-formed collapsing argument
  filter inside that frozen argument before comparing it by the proper
  subterm relation.  This is strictly more precise than the ordinary simple
  projection, which projects only the DP root once.
\<close>

definition csr_frozen_projection_index ::
  "((('f,'l) lab) mu) \<Rightarrow> (('f,'l) lab) \<Rightarrow>
   ((('f,'l) lab) proj) \<Rightarrow> ((('f,'l) lab), 'v) term \<Rightarrow> bool"
where
  "csr_frozen_projection_index \<mu> U p t \<longleftrightarrow>
    (case t of
       Fun (Sharp f) ts \<Rightarrow>
         p (Sharp f, length ts) < length ts \<and>
         p (Sharp f, length ts) \<notin> csr_dp_root_mu \<mu> (Sharp f, length ts)
     | Fun V ts \<Rightarrow> V = U \<and> length ts = 1 \<and> p (V, 1) = 0
     | Var _ \<Rightarrow> False)"

definition csr_frozen_recursive_view ::
  "'f afs \<Rightarrow> 'f proj \<Rightarrow> ('f,'v) term \<Rightarrow> ('f,'v) term"
where
  "csr_frozen_recursive_view \<pi> p t = af_term \<pi> (proj_term p t)"

lemma csr_frozen_projection_index_shape:
  assumes valid: "csr_frozen_projection_index \<mu> U p t"
  shows "csr_u3_mixed_term_shape U t"
  using valid unfolding csr_frozen_projection_index_def csr_u3_mixed_term_shape_def
  by (cases t; auto split: lab.splits)

lemma csr_frozen_projection_transition:
  fixes U :: "(('f::{showl, compare_order}, 'l::{showl, compare_order}) lab)"
    and af :: "((('f,'l) lab)) afs"
  assumes wf: "wf_trs R"
    and fresh_sharp: "\<And>f n. \<not> defined R (Sharp f,n)"
    and fresh_U: "\<And>n. \<not> defined R (U,n)"
    and unsharp: "\<not> is_sharp_lab U"
    and valid_t: "csr_frozen_projection_index \<mu> U p t"
    and valid_s: "csr_frozen_projection_index \<mu> U p s"
    and steps: "(t \<cdot> \<sigma>, s \<cdot> \<tau>) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "csr_frozen_recursive_view af p t \<cdot> af_subst af \<sigma> =
    csr_frozen_recursive_view af p s \<cdot> af_subst af \<tau>"
proof -
  have shape_t: "csr_u3_mixed_term_shape U t"
    by (rule csr_frozen_projection_index_shape[OF valid_t])
  have shape_s: "csr_u3_mixed_term_shape U s"
    by (rule csr_frozen_projection_index_shape[OF valid_s])
  have roots: "root s = root t"
    by (rule csr_mixed_sct_root_transition[
      OF wf fresh_sharp fresh_U unsharp shape_t shape_s steps])
  show ?thesis
  proof (cases t)
    case (Var x)
    with valid_t show ?thesis
      unfolding csr_frozen_projection_index_def by simp
  next
    case (Fun ft ts)
    have hidden_case: ?thesis if ftU: "ft = U"
    proof -
      have data: "length ts = 1 \<and> p (U, 1) = 0"
        using valid_t unsharp
        unfolding csr_frozen_projection_index_def Fun ftU
        by (cases U; simp_all)
      then have len: "length ts = 1" and index: "p (U, 1) = 0" by auto
      have steps': "(Fun U (map (\<lambda>u. u \<cdot> \<sigma>) ts), s \<cdot> \<tau>) \<in>
          (csdp_step Sharp \<mu> R)\<^sup>*"
        using steps Fun ftU by simp
      from csr_u3_unhiding_csdp_steps_identity[OF wf fresh_U unsharp steps']
      have finish: "s \<cdot> \<tau> = Fun U (map (\<lambda>u. u \<cdot> \<sigma>) ts)" by simp
      from valid_s obtain ss where s: "s = Fun U ss"
        unfolding csr_frozen_projection_index_def
        using finish unsharp by (cases s; auto split: lab.splits)
      from finish[unfolded s] have maps:
        "map (\<lambda>u. u \<cdot> \<tau>) ss = map (\<lambda>u. u \<cdot> \<sigma>) ts" by simp
      have lens: "length ss = 1"
        using arg_cong[OF maps, of length] len by simp
      have selected_s: "ss ! 0 \<cdot> \<tau> = ts ! 0 \<cdot> \<sigma>"
      proof -
        have "ss ! 0 \<cdot> \<tau> = (map (\<lambda>u. u \<cdot> \<tau>) ss) ! 0"
          using lens by simp
        also have "... = (map (\<lambda>u. u \<cdot> \<sigma>) ts) ! 0" by (rule arg_cong[OF maps])
        also have "... = ts ! 0 \<cdot> \<sigma>" using len by simp
        finally show ?thesis .
      qed
      have proj_t: "proj_term p t = ts ! 0"
        using Fun ftU len index by (simp add: Let_def)
      have proj_s: "proj_term p s = ss ! 0"
        using s lens index by (simp add: Let_def)
      show ?thesis
        unfolding csr_frozen_recursive_view_def proj_t proj_s
        using selected_s by (simp only: af_subst[symmetric])
    qed
    show ?thesis
    proof (cases ft)
      case (Sharp f)
      let ?i = "p (Sharp f, length ts)"
      from valid_t Fun Sharp have i: "?i < length ts"
        and inactive: "?i \<notin> csr_dp_root_mu \<mu> (Sharp f, length ts)"
        unfolding csr_frozen_projection_index_def by auto
      have undef: "\<not> defined R (Sharp f, length (map (\<lambda>u. u \<cdot> \<sigma>) ts))"
        using fresh_sharp by simp
      have steps': "(Fun (Sharp f) (map (\<lambda>u. u \<cdot> \<sigma>) ts), s \<cdot> \<tau>) \<in>
          (csdp_step Sharp \<mu> R)\<^sup>*"
        using steps Fun Sharp by simp
      from cssteps_Fun_inactive_arg_preserved[
          OF wf undef _ _ steps']
      obtain us where target:
          "s \<cdot> \<tau> = Fun (Sharp f) us"
        and len: "length us = length ts"
        and selected: "us ! ?i = ts ! ?i \<cdot> \<sigma>"
        using i inactive by auto
      from shape_s obtain g ss where s: "s = Fun (Sharp g) ss"
        unfolding csr_u3_mixed_term_shape_def
        using roots Fun Sharp by (cases s; auto split: lab.splits)
      from target[unfolded s] have gf: "g = f"
        and args: "map (\<lambda>u. u \<cdot> \<tau>) ss = us" by auto
      have lens: "length ss = length ts"
        using arg_cong[OF args, of length] len by simp
      have selected_s: "ss ! ?i \<cdot> \<tau> = ts ! ?i \<cdot> \<sigma>"
      proof -
        have "ss ! ?i \<cdot> \<tau> = (map (\<lambda>u. u \<cdot> \<tau>) ss) ! ?i"
          using i lens by simp
        also have "... = us ! ?i" using args by simp
        also have "... = ts ! ?i \<cdot> \<sigma>" by (rule selected)
        finally show ?thesis .
      qed
      have proj_t: "proj_term p t = ts ! ?i"
        using Fun Sharp i by (simp add: Let_def)
      have proj_s: "proj_term p s = ss ! ?i"
        using s gf roots Fun Sharp i lens by (simp add: Let_def)
      show ?thesis
        unfolding csr_frozen_recursive_view_def proj_t proj_s
        using selected_s by (simp only: af_subst[symmetric])
    next
      case (Lab f l)
      from valid_t Fun Lab have "ft = U"
        unfolding csr_frozen_projection_index_def by auto
      then show ?thesis by (rule hidden_case)
    next
      case (FunLab f ls)
      from valid_t Fun FunLab have "ft = U"
        unfolding csr_frozen_projection_index_def by auto
      then show ?thesis by (rule hidden_case)
    next
      case (UnLab f)
      from valid_t Fun UnLab have "ft = U"
        unfolding csr_frozen_projection_index_def by auto
      then show ?thesis by (rule hidden_case)
    qed
  qed
qed

theorem finite_min_csr_dpp_frozen_recursive_subterm:
  fixes U :: "(('f::{showl, compare_order}, 'l::{showl, compare_order}) lab)"
    and p :: "((('f,'l) lab) proj)"
    and af :: "((('f,'l) lab)) afs"
  assumes wf: "wf_trs R"
    and fresh_sharp: "\<And>f n. \<not> defined R (Sharp f,n)"
    and fresh_U: "\<And>n. \<not> defined R (U,n)"
    and unsharp: "\<not> is_sharp_lab U"
    and valid: "\<forall>(u,v)\<in>P.
      csr_frozen_projection_index \<mu> U p u \<and>
      csr_frozen_projection_index \<mu> U p v"
    and deleted: "D \<subseteq> P"
    and strict: "\<forall>(u,v)\<in>D.
      csr_frozen_recursive_view af p u \<rhd>
      csr_frozen_recursive_view af p v"
    and weak: "\<forall>(u,v)\<in>P-D.
      csr_frozen_recursive_view af p u = csr_frozen_recursive_view af p v \<or>
      csr_frozen_recursive_view af p u \<rhd>
      csr_frozen_recursive_view af p v"
    and fin: "finite_min_csr_dpp Sharp \<mu> (P-D) R"
  shows "finite_min_csr_dpp Sharp \<mu> P R"
proof (rule ccontr)
  let ?RS = "csdp_step Sharp \<mu> R"
  let ?S = "{\<rhd>}"
  let ?W = "Id"
  assume not_fin: "\<not> finite_min_csr_dpp Sharp \<mu> P R"
  from not_finite_min_csr_dpp_obtain_chain[OF not_fin]
  obtain s t \<sigma> where pair: "\<And>k. (s k,t k) \<in> P"
    and target_SN: "\<And>k. SN_on ?RS {t k \<cdot> \<sigma> k}"
    and steps: "\<And>k. (t k \<cdot> \<sigma> k,
      s (Suc k) \<cdot> \<sigma> (Suc k)) \<in> ?RS\<^sup>*"
    by blast
  let ?view = "csr_frozen_recursive_view af p"
  let ?v = "\<lambda>k. ?view (s k) \<cdot> af_subst af (\<sigma> k)"
  have between: "?view (t k) \<cdot> af_subst af (\<sigma> k) =
      ?view (s (Suc k)) \<cdot> af_subst af (\<sigma> (Suc k))" for k
  proof -
    from valid pair[of k] have valid_t:
      "csr_frozen_projection_index \<mu> U p (t k)" by auto
    from valid pair[of "Suc k"] have valid_s:
      "csr_frozen_projection_index \<mu> U p (s (Suc k))" by auto
    show ?thesis by (rule csr_frozen_projection_transition[
      OF wf fresh_sharp fresh_U unsharp valid_t valid_s steps])
  qed
  have strict_step: "(u,v) \<in> D \<Longrightarrow>
      (?view u \<cdot> af_subst af \<rho>, ?view v \<cdot> af_subst af \<rho>) \<in> ?S"
    for u v \<rho>
    using strict supt_subst by blast
  have projected: "(?v k, ?v (Suc k)) \<in> ?S \<union> ?W" for k
  proof (cases "(s k,t k) \<in> D")
    case True
    have first: "(?v k, ?view (t k) \<cdot> af_subst af (\<sigma> k)) \<in> ?S"
      by (rule strict_step[OF True])
    with between[of k] show ?thesis by auto
  next
    case False
    with pair[of k] have residual: "(s k,t k) \<in> P-D" by auto
    from weak[rule_format, OF residual]
    consider (eq) "?view (s k) = ?view (t k)"
      | (sub) "?view (s k) \<rhd> ?view (t k)" by blast
    then show ?thesis
    proof cases
      case eq
      have "?v k = ?view (t k) \<cdot> af_subst af (\<sigma> k)"
        using eq by simp
      with between[of k] show ?thesis by auto
    next
      case sub
      have first: "(?v k, ?view (t k) \<cdot> af_subst af (\<sigma> k)) \<in> ?S"
        using supt_subst[OF sub, of "af_subst af (\<sigma> k)"] by simp
      with between[of k] show ?thesis by auto
    qed
  qed
  have proj_chain: "chain (?W \<union> ?S) ?v"
    using projected by (simp add: Un_commute)
  have compat: "?W O ?S \<subseteq> ?S" by auto
  have sn_on_S: "SN_on ?S {?v 0}"
    by (rule SN_on_subset2[OF _ SN_supt], simp)
  have "\<exists>j. \<forall>k\<ge>j. (?v k, ?v (Suc k)) \<in> ?W - ?S"
    by (rule non_strict_ending[OF proj_chain compat sn_on_S])
  then obtain j where tail: "\<And>k. k \<ge> j \<Longrightarrow>
    (?v k, ?v (Suc k)) \<in> ?W - ?S" by auto
  have pair_tail: "(s (k+j),t (k+j)) \<in> P-D" for k
  proof (rule DiffI)
    show "(s (k+j),t (k+j)) \<in> P" by (rule pair)
    show "(s (k+j),t (k+j)) \<notin> D"
    proof
      assume inD: "(s (k+j),t (k+j)) \<in> D"
      have first: "(?v (k+j), ?view (t (k+j)) \<cdot>
          af_subst af (\<sigma> (k+j))) \<in> ?S"
        by (rule strict_step[OF inD])
      with between[of "k+j"] have inS:
        "(?v (k+j), ?v (Suc (k+j))) \<in> ?S" by auto
      from tail[of "k+j"] inS show False by auto
    qed
  qed
  let ?ss = "shift s j"
  let ?tt = "shift t j"
  let ?\<tau> = "shift \<sigma> j"
  let ?RP = "csr_min_pair_step Sharp \<mu> (P-D) R"
  let ?rel = "?RS\<^sup>* O ?RP O ?RS\<^sup>*"
  let ?vals = "\<lambda>k. ?ss k \<cdot> ?\<tau> k"
  have rel_step: "(?vals k, ?vals (Suc k)) \<in> ?rel" for k
  proof -
    have pair_k: "(?ss k,?tt k) \<in> P-D" using pair_tail[of k] by simp
    have rr_k: "(?ss k \<cdot> ?\<tau> k, ?tt k \<cdot> ?\<tau> k) \<in> rrstep (P-D)"
      unfolding rrstep_def' by (rule Quasi_Order.mem_rel_ofI, use pair_k in auto)
    have sn_k: "SN_on ?RS {?tt k \<cdot> ?\<tau> k}"
      using target_SN[of "k+j"] by simp
    have min_k: "(?ss k \<cdot> ?\<tau> k, ?tt k \<cdot> ?\<tau> k) \<in> ?RP"
      unfolding csr_min_pair_step_def using rr_k sn_k by auto
    have steps_k: "(?tt k \<cdot> ?\<tau> k, ?ss (Suc k) \<cdot> ?\<tau> (Suc k)) \<in> ?RS\<^sup>*"
      using steps[of "k+j"] by simp
    show ?thesis using min_k steps_k by auto
  qed
  have vals_chain: "chain ?rel ?vals" using rel_step by simp
  have "\<not> SN_on ?rel UNIV"
    by (rule not_SN_onI[OF _ vals_chain], simp)
  moreover from fin have "SN_on ?rel UNIV"
    unfolding finite_min_csr_dpp_def SN_rel_on_def .
  ultimately show False by contradiction
qed

fun csr_projection_collapsing_afs :: "'f projL \<Rightarrow> 'f afs_list" where
  "csr_projection_collapsing_afs (Projection xs) =
    map (\<lambda>(fn,i). (fn, Collapse i)) xs"

definition csr_frozen_projection_pair_valid where
  "csr_frozen_projection_pair_valid \<mu> U p lr \<longleftrightarrow>
    (case lr of (l,r) \<Rightarrow>
      csr_frozen_projection_index (mu_of \<mu>) U p l \<and>
      csr_frozen_projection_index (mu_of \<mu>) U p r)"

definition csr_frozen_projection_pair_strict ::
  "'f afs \<Rightarrow> 'f proj \<Rightarrow> (('f,'v) term \<times> ('f,'v) term) \<Rightarrow> bool"
where
  "csr_frozen_projection_pair_strict \<pi> p lr \<longleftrightarrow>
    (case lr of (l,r) \<Rightarrow>
      csr_frozen_recursive_view \<pi> p r \<in>
        set (supt_list (csr_frozen_recursive_view \<pi> p l)))"

definition csr_frozen_projection_pair_weak ::
  "'f afs \<Rightarrow> 'f proj \<Rightarrow> (('f,'v) term \<times> ('f,'v) term) \<Rightarrow> bool"
where
  "csr_frozen_projection_pair_weak \<pi> p lr \<longleftrightarrow>
    (case lr of (l,r) \<Rightarrow>
      csr_frozen_recursive_view \<pi> p l = csr_frozen_recursive_view \<pi> p r \<or>
      csr_frozen_recursive_view \<pi> p r \<in>
        set (supt_list (csr_frozen_recursive_view \<pi> p l)))"

definition csr_frozen_recursive_subterm_proc ::
  "('dpp, (('f::{showl, compare_order}, 'l::{showl, compare_order}) lab),
      string) dpp_ops \<Rightarrow>
   (('f, 'l) lab) \<Rightarrow> (('f, 'l) lab) muL \<Rightarrow>
   (('f, 'l) lab) projL \<Rightarrow>
   (((('f, 'l) lab), string) rule \<times>
      ((('f, 'l) lab), string) rseq) list \<Rightarrow>
   ((('f, 'l) lab), string) rules \<Rightarrow> 'dpp \<Rightarrow> 'dpp result"
where
  "csr_frozen_recursive_subterm_proc J U \<mu> pL rseq Pr dpp =
    (case afs_of (csr_projection_collapsing_afs pL) of
      None \<Rightarrow> error (showsl_lit (STR ''invalid recursive projection''))
    | Some \<pi> \<Rightarrow> check_return (let
        p = create_proj pL;
        P = dpp_ops.pairs J dpp;
        (ps, pns) = dpp_ops.split_pairs J dpp Pr
        in check (rseq = [] \<and>
          list_all (csr_frozen_projection_pair_valid \<mu> U p) P \<and>
          list_all (csr_frozen_projection_pair_strict \<pi> p) ps \<and>
          list_all (csr_frozen_projection_pair_weak \<pi> p) pns)
          (showsl_lit (STR ''invalid frozen recursive CSR subterm criterion'')))
        (dpp_spec.delete_pairs J dpp Pr))"

lemma csr_frozen_recursive_subterm_proc_sound:
  fixes J :: "('dpp, (('f::{showl, compare_order},
      'l::{showl, compare_order}) lab), string) dpp_ops"
  assumes J: "dpp_spec J"
    and plain: "plain_csr_dpp J dpp"
    and wf: "wf_trs (set (dpp_ops.rules J dpp))"
    and fresh_sharp: "\<And>f n.
      \<not> defined (set (dpp_ops.rules J dpp)) (Sharp f,n)"
    and fresh_U: "\<And>n. \<not> defined (set (dpp_ops.rules J dpp)) (U,n)"
    and unsharp: "\<not> is_sharp_lab U"
    and proc: "csr_frozen_recursive_subterm_proc J U \<mu> pL rseq Pr dpp = return dpp'"
    and fin: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (dpp_ops.pairs J dpp')) (set (dpp_ops.rules J dpp'))"
  shows "finite_min_csr_dpp Sharp (mu_of \<mu>)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
proof -
  interpret dpp_spec J by fact
  obtain \<pi> where af: "afs_of (csr_projection_collapsing_afs pL) = Some \<pi>"
    using proc unfolding csr_frozen_recursive_subterm_proc_def
    by (cases "afs_of (csr_projection_collapsing_afs pL)"; auto)
  obtain ps pns where split: "split_pairs dpp Pr = (ps,pns)" by force
  from split_pairs_sound[OF split]
  have ps: "set ps = set (pairs dpp) \<inter> set Pr"
    and pns: "set pns = set (pairs dpp) - set Pr" by auto
  let ?p = "create_proj pL"
  note ok = proc[unfolded csr_frozen_recursive_subterm_proc_def af split Let_def,
    simplified]
  from ok have valid: "\<forall>(u,v)\<in>set (pairs dpp).
      csr_frozen_projection_index (mu_of \<mu>) U ?p u \<and>
      csr_frozen_projection_index (mu_of \<mu>) U ?p v"
    by (auto simp: list_all_iff csr_frozen_projection_pair_valid_def)
  from ok have strict: "\<forall>(u,v)\<in>set ps.
      csr_frozen_recursive_view \<pi> ?p u \<rhd>
      csr_frozen_recursive_view \<pi> ?p v"
    by (auto simp: list_all_iff csr_frozen_projection_pair_strict_def)
  from ok have weak: "\<forall>(u,v)\<in>set pns.
      csr_frozen_recursive_view \<pi> ?p u = csr_frozen_recursive_view \<pi> ?p v \<or>
      csr_frozen_recursive_view \<pi> ?p u \<rhd>
      csr_frozen_recursive_view \<pi> ?p v"
    by (auto simp: list_all_iff csr_frozen_projection_pair_weak_def)
  from ok have dpp': "dpp' = delete_pairs dpp Pr" by auto
  have sem: "dpp_ops.dpp J (delete_pairs dpp Pr) =
      (NFS dpp, M dpp, set (P dpp) - set Pr,
       set (Pw dpp) - set Pr, set (Q dpp), set (R dpp), set (Rw dpp))"
    by (rule delete_P_Pw_sound)
  have sem': "dpp_ops.dpp J (delete_pairs dpp Pr) =
      (NFS (delete_pairs dpp Pr), M (delete_pairs dpp Pr),
       set (P (delete_pairs dpp Pr)), set (Pw (delete_pairs dpp Pr)),
       set (Q (delete_pairs dpp Pr)), set (R (delete_pairs dpp Pr)),
       set (Rw (delete_pairs dpp Pr)))" by (rule dpp_sound)
  from plain have plain_fields:
      "set (pairs dpp) = set (P dpp)" "set (Pw dpp) = {}"
    unfolding plain_csr_dpp_def using pairs_sound[of dpp] by auto
  have pairs': "set (pairs dpp') = set (pairs dpp) - set Pr"
    using sem sem' dpp' plain_fields pairs_sound[of "delete_pairs dpp Pr"] by auto
  have rules': "set (rules dpp') = set (rules dpp)"
    using sem sem' dpp' rules_sound[of dpp] rules_sound[of "delete_pairs dpp Pr"] by auto
  have remaining: "set (pairs dpp) - set ps = set (pairs dpp) - set Pr"
    using ps by auto
  have fin_res: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (pairs dpp) - set ps) (set (rules dpp))"
    using fin pairs' rules' remaining by simp
  show ?thesis
  proof (rule finite_min_csr_dpp_frozen_recursive_subterm[
      where D="set ps" and p="?p" and af=\<pi>])
    show "wf_trs (set (rules dpp))" by (rule wf)
    show "\<And>f n. \<not> defined (set (rules dpp)) (Sharp f,n)"
      by (rule fresh_sharp)
    show "\<And>n. \<not> defined (set (rules dpp)) (U,n)" by (rule fresh_U)
    show "\<not> is_sharp_lab U" by (rule unsharp)
    show "\<forall>(u,v)\<in>set (pairs dpp).
      csr_frozen_projection_index (mu_of \<mu>) U ?p u \<and>
      csr_frozen_projection_index (mu_of \<mu>) U ?p v" by (rule valid)
    show "set ps \<subseteq> set (pairs dpp)" using ps by auto
    show "\<forall>(u,v)\<in>set ps.
      csr_frozen_recursive_view \<pi> ?p u \<rhd>
      csr_frozen_recursive_view \<pi> ?p v" by (rule strict)
    show "\<forall>(u,v)\<in>set (pairs dpp) - set ps.
      csr_frozen_recursive_view \<pi> ?p u = csr_frozen_recursive_view \<pi> ?p v \<or>
      csr_frozen_recursive_view \<pi> ?p u \<rhd>
      csr_frozen_recursive_view \<pi> ?p v" using pns weak ps by auto
    show "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (pairs dpp) - set ps) (set (rules dpp))" by (rule fin_res)
  qed
qed

end
