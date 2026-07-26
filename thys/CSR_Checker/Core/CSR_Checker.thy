(*
Author:  Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Checker
  imports CSR_Checker_Base.CSR_Checker_Base
begin

definition check_csr_dep_graph_proc ::
  "('dpp, ('f::{showl, compare_order}, 'l::{showl, compare_order}) lab, string) dpp_ops \<Rightarrow>
   (('f, 'l) lab) muL \<Rightarrow> 'dpp \<Rightarrow>
   ('a option \<times> ((('f, 'l) lab), string) rules) list \<Rightarrow> showsl check"
where
  "check_csr_dep_graph_proc J \<mu> dpp dps = do {
    let P = dpp_ops.pairs J dpp;
    let R = dpp_ops.rules J dpp;
    check_wf_trs R;
    check_subseteq P (concat (map snd dps))
      <+? (\<lambda>dp. showsl_lit (STR ''CSR dependency pair '') \<circ> showsl_rule dp
        \<circ> showsl_lit (STR '' is missing in decomposition\<newline>''));
    check_graph_decomp
      (showsl \<circ> fst)
      (Multi_Map.empty (root o fst o fst))
      graph_approx_csr_rt
      Multi_Map.insert
      (csr_dep_graph_edge_check (csr_dp_root_mu (mu_of \<mu>)) R)
      (map (\<lambda>(real, Cs).
        (real \<noteq> None, map (\<lambda>(s,t). ((s,t), ())) Cs)) dps)
        <+? (\<lambda>s. showsl_lit (STR ''our CSR dependency-graph estimation could not show that you have a valid decomposition '')
          \<circ> showsl_lit (STR ''due to the following reason\<newline>'') \<circ> s)
  }"

definition csr_dep_graph_proc ::
  "('dpp, ('f::{showl, compare_order}, 'l::{showl, compare_order}) lab, string) dpp_ops \<Rightarrow>
   (('f, 'l) lab) muL \<Rightarrow> 'dpp \<Rightarrow>
   ('a option \<times> ((('f, 'l) lab), string) rules) list \<Rightarrow>
   ('a \<times> 'dpp) list result"
where
  "csr_dep_graph_proc J \<mu> dpp dps =
    check_return
      (check_csr_dep_graph_proc J \<mu> dpp dps)
      (map (\<lambda>aP. (the (fst aP), dpp_ops.intersect_pairs J dpp (snd aP)))
        (filter (\<lambda>aP. fst aP \<noteq> None) dps))"

fun check_csr_dp_termination_proof_core ::
  "('tp, ('f::{showl, compare_order,countable}, label_type) lab, string) tp_ops \<Rightarrow>
   ('dpp, ('f, label_type) lab, string) dpp_ops \<Rightarrow>
   (('f, label_type) lab) muL \<Rightarrow> bool \<Rightarrow>
   showsl \<Rightarrow> 'dpp \<Rightarrow>
   ('f, label_type, string) csr_dp_termination_proof \<Rightarrow> showsl check"
and check_csr_dp_graph_components ::
  "('tp, ('f::{showl, compare_order,countable}, label_type) lab, string) tp_ops \<Rightarrow>
   ('dpp, ('f, label_type) lab, string) dpp_ops \<Rightarrow>
   (('f, label_type) lab) muL \<Rightarrow> bool \<Rightarrow>
   showsl \<Rightarrow> 'dpp \<Rightarrow>
   (('f, label_type, string) csr_dp_termination_proof option \<times>
    ('f, label_type, string) trsLL) list \<Rightarrow> showsl check"
where
  "check_csr_dp_termination_proof_core I J \<mu> a i dpp CSR_DP_P_is_Empty =
    debug i (STR ''CSR-DP P is empty'')
      (if dpp_ops.pairs J dpp = []
       then succeed
       else error (i \<circ> showsl_lit (STR '': CSR-DP P is not empty in the following DP-problem\<newline>'')
         \<circ> showsl_dpp J dpp))"
| "check_csr_dp_termination_proof_core I J \<mu> a i dpp (CSR_DP_Ordinary_Proof prf) =
    check_csr_dp_termination_proof I J a i dpp (CSR_DP_Ordinary_Proof prf)"
| "check_csr_dp_termination_proof_core I J \<mu> a i dpp
    (CSR_DP_Subterm_Criterion_Proc p rseq Pr prf) =
    check_csr_dp_termination_proof I J a i dpp
      (CSR_DP_Subterm_Criterion_Proc p rseq Pr prf)"
| "check_csr_dp_termination_proof_core I J \<mu> a i dpp
    (CSR_DP_Gen_Subterm_Criterion_Proc p Pr prf) =
    check_csr_dp_termination_proof I J a i dpp
      (CSR_DP_Gen_Subterm_Criterion_Proc p Pr prf)"
| "check_csr_dp_termination_proof_core I J \<mu> a i dpp (CSR_DP_Usable_Rules_Proc U prf) =
    debug i (STR ''CSR-DP usable rules'') (do {
      dpp' \<leftarrow> csr_mu_usable_rules_proc J \<mu> U dpp
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying CSR usable rules\<newline>'') \<circ> s);
      check_allm (\<lambda>lr. check (lr \<in> set U)
        (i \<circ> showsl_lit (STR '': conservative CSR usable-rules checker requires the usable rules to contain '')
          \<circ> showsl_rule lr)) (dpp_ops.rules J dpp);
      check_csr_dp_termination_proof_core I J \<mu> a (add_index i 1) dpp' prf
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below CSR usable rules\<newline>'') \<circ> s)
    })"
| "check_csr_dp_termination_proof_core I J \<mu> a i dpp (CSR_DP_Dep_Graph_Proc edpts) =
    debug i (STR ''CSR-DP dependency graph'') (do {
      _ \<leftarrow> check_csr_dep_graph_proc J \<mu> dpp edpts
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying CSR dependency graph\<newline>'') \<circ> s);
      check_csr_dp_graph_components I J \<mu> a i dpp edpts
        <+? (\<lambda>s. i \<circ> showsl_lit
          (STR '': error below CSR dependency graph\<newline>'') \<circ> s)
    })"
| "check_csr_dp_termination_proof_core I J \<mu> a i dpp
    (CSR_DP_Size_Change_Subterm_Proc graphs) =
    check_csr_dp_termination_proof I J a i dpp
      (CSR_DP_Size_Change_Subterm_Proc graphs)"
| "check_csr_dp_graph_components I J \<mu> a i dpp [] = succeed"
| "check_csr_dp_graph_components I J \<mu> a i dpp ((None, P) # rest) =
    check_csr_dp_graph_components I J \<mu> a (add_index i 1) dpp rest"
| "check_csr_dp_graph_components I J \<mu> a i dpp ((Some prf, P) # rest) = do {
    check_csr_dp_termination_proof_core I J \<mu> a (add_index i 1)
      (dpp_ops.intersect_pairs J dpp P) prf;
    check_csr_dp_graph_components I J \<mu> a (add_index i 1) dpp rest
  }"

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
      (case mu_csr_dependency_pairs_tt Sharp J \<mu> R P of
        Inr dpp \<Rightarrow> check_csr_dp_termination_proof_core I J \<mu> False (add_index i 1) dpp prf
          <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below replacement-map-specific CSR dependency pairs\<newline>'') \<circ> s)
      | Inl e \<Rightarrow> do {
          dpp \<leftarrow> safe_csr_dependency_pairs_tt Sharp J \<mu> R P
            <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when switching from CSR to a safe CS-DP problem\<newline>'')
              \<circ> showsl_rules R \<circ> showsl_lit (STR ''\<newline>with pairs\<newline>'') \<circ> showsl_rules P
              \<circ> showsl_nl \<circ> s);
          check_csr_dp_termination_proof I J False (add_index i 1) dpp prf
            <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below safe CSR dependency pairs\<newline>'') \<circ> s)
        })
    })"
| "check_csr_termination_proof I J a i \<mu> R (CSR_Safe_Dependency_Pairs P prf) =
    debug i (STR ''safe CSR dependency pairs'') (do {
      csr_sharp_mu_check \<mu>
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': invalid replacement map for safe CSR dependency pairs\<newline>'') \<circ> s);
      dpp \<leftarrow> safe_csr_dependency_pairs_tt Sharp J \<mu> R P
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when switching from CSR to a safe CS-DP problem\<newline>'')
          \<circ> showsl_rules R \<circ> showsl_lit (STR ''\<newline>with pairs\<newline>'') \<circ> showsl_rules P
          \<circ> showsl_nl \<circ> s);
      check_csr_dp_termination_proof I J False (add_index i 1) dpp prf
        <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below safe CSR dependency pairs\<newline>'') \<circ> s)
    })"

lemma check_csr_dp_termination_proof_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_csr_dp_termination_proof I J False i dpp prf)"
  shows "finite_dpp (dpp_ops.dpp J dpp)"
  using ok unfolding check_csr_dp_termination_proof_def
  by (rule check_dp_termination_proof[OF I J])

lemma plain_csr_dpp_finite_dpp_imp_finite_csr_dpp:
  assumes J: "dpp_spec J"
    and plain: "plain_csr_dpp J dpp"
    and fin: "finite_dpp (dpp_ops.dpp J dpp)"
  shows "finite_csr_dpp Sharp \<mu> (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
proof -
  interpret dpp_spec J by fact
  from plain have plain':
    "\<not> NFS dpp" "\<not> M dpp" "Pw dpp = []" "Q dpp = []" "R dpp = []"
    unfolding plain_csr_dpp_def by auto
  have Pset: "set (dpp_ops.P J dpp) = set (dpp_ops.pairs J dpp)"
    using pairs_sound plain' by auto
  have Rset: "set (dpp_ops.Rw J dpp) = set (dpp_ops.rules J dpp)"
    using rules_sound plain' by auto
  have dpp: "dpp_ops.dpp J dpp =
    (False, False, set (dpp_ops.pairs J dpp), {}, {}, {}, set (dpp_ops.rules J dpp))"
    using dpp_sound plain' Pset Rset by auto
  show ?thesis
    by (rule finite_dpp_imp_finite_csr_dpp[OF fin[unfolded dpp]])
qed

lemma check_csr_dp_termination_proof_sound_csr:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and plain: "plain_csr_dpp J dpp"
    and ok: "isOK (check_csr_dp_termination_proof I J False i dpp prf)"
  shows "finite_csr_dpp Sharp \<mu> (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
  by (rule plain_csr_dpp_finite_dpp_imp_finite_csr_dpp[OF J plain
      check_csr_dp_termination_proof_sound[OF I J ok]])

lemma plain_csr_dpp_intersect_rules:
  assumes J: "dpp_spec J"
    and plain: "plain_csr_dpp J dpp"
  shows "plain_csr_dpp J (dpp_ops.intersect_rules J dpp U)"
proof -
  interpret dpp_spec J by fact
  let ?d = "intersect_rules dpp U"
  have sem: "dpp_ops.dpp J ?d = (NFS dpp, M dpp, set (P dpp), set (Pw dpp), set (Q dpp),
      set (R dpp) \<inter> set U, set (Rw dpp) \<inter> set U)"
    by (rule intersect_rules_sound)
  have sem': "dpp_ops.dpp J ?d = (NFS ?d, M ?d, set (P ?d), set (Pw ?d), set (Q ?d),
      set (R ?d), set (Rw ?d))"
    by (rule dpp_sound)
  from plain sem sem' have fields: "\<not> NFS ?d" "\<not> M ?d" "set (Pw ?d) = {}"
    "set (Q ?d) = {}" "set (R ?d) = {}"
    unfolding plain_csr_dpp_def by auto
  show ?thesis
    using fields by (auto simp: plain_csr_dpp_def)
qed

lemma plain_csr_dpp_intersect_pairs:
  assumes J: "dpp_spec J"
    and plain: "plain_csr_dpp J dpp"
  shows "plain_csr_dpp J (dpp_ops.intersect_pairs J dpp P)"
proof -
  interpret dpp_spec J by fact
  let ?d = "intersect_pairs dpp P"
  have sem: "dpp_ops.dpp J ?d =
    (NFS dpp, M dpp, set (dpp_ops.P J dpp) \<inter> set P,
      set (dpp_ops.Pw J dpp) \<inter> set P, set (Q dpp), set (R dpp), set (Rw dpp))"
    by (rule intersect_pairs_sound)
  have sem': "dpp_ops.dpp J ?d =
    (NFS ?d, M ?d, set (dpp_ops.P J ?d), set (dpp_ops.Pw J ?d),
      set (Q ?d), set (R ?d), set (Rw ?d))"
    by (rule dpp_sound)
  from plain sem sem'
  show ?thesis
    unfolding plain_csr_dpp_def by auto
qed

lemma check_csr_dp_graph_components_member:
  assumes ok: "isOK (check_csr_dp_graph_components I J \<mu> a i dpp edps)"
    and mem: "(Some prf, P) \<in> set edps"
  shows "\<exists>j. isOK (check_csr_dp_termination_proof_core I J \<mu> a
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
    from Cons.prems(1) head None have tail:
      "isOK (check_csr_dp_graph_components I J \<mu> a
        (add_index i 1) dpp rest)"
      by simp
    from Cons.prems(2) head None have mem': "(Some prf, P) \<in> set rest"
      by auto
    show ?thesis
      by (rule Cons.hyps[OF tail mem'])
  next
    case (Some p)
    show ?thesis
    proof (cases "(Some prf, P) = head")
      case True
      from Cons.prems(1) head Some True show ?thesis
        by auto
    next
      case False
      from Cons.prems(1) head Some have tail:
        "isOK (check_csr_dp_graph_components I J \<mu> a
          (add_index i 1) dpp rest)"
        by simp
      from Cons.prems(2) False have mem': "(Some prf, P) \<in> set rest"
        by auto
      show ?thesis
        by (rule Cons.hyps[OF tail mem'])
    qed
  qed
qed

lemma finite_csr_dpp_intersect_rules_all:
  assumes J: "dpp_spec J"
    and all: "set (dpp_ops.rules J dpp) \<subseteq> set U"
    and fin: "finite_csr_dpp Sharp \<mu>
      (set (dpp_ops.pairs J (dpp_ops.intersect_rules J dpp U)))
      (set (dpp_ops.rules J (dpp_ops.intersect_rules J dpp U)))"
  shows "finite_csr_dpp Sharp \<mu> (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
proof -
  interpret dpp_spec J by fact
  let ?d = "intersect_rules dpp U"
  have sem: "dpp_ops.dpp J ?d = (NFS dpp, M dpp, set (P dpp), set (Pw dpp), set (Q dpp),
      set (R dpp) \<inter> set U, set (Rw dpp) \<inter> set U)"
    by (rule intersect_rules_sound)
  have sem': "dpp_ops.dpp J ?d = (NFS ?d, M ?d, set (P ?d), set (Pw ?d), set (Q ?d),
      set (R ?d), set (Rw ?d))"
    by (rule dpp_sound)
  have P: "set (pairs ?d) = set (pairs dpp)"
    using sem sem' pairs_sound[of ?d] pairs_sound[of dpp] by auto
  have R: "set (rules ?d) = set (rules dpp)"
    using all sem sem' rules_sound[of ?d] rules_sound[of dpp] by auto
  show ?thesis
    using fin unfolding P R .
qed

lemma check_csr_dep_graph_proc_sound:
  assumes J: "dpp_spec J"
    and plain: "plain_csr_dpp J dpp"
    and check: "isOK (check_csr_dep_graph_proc J \<mu> dpp edps)"
    and fin: "\<And>prf C. (Some prf, C) \<in> set edps \<Longrightarrow>
      finite_csr_dpp Sharp (mu_of \<mu>)
        (set (dpp_ops.pairs J dpp) \<inter> set C)
        (set (dpp_ops.rules J dpp))"
  shows "finite_csr_dpp Sharp (mu_of \<mu>) (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
proof -
  interpret dpp_spec J by fact
  let ?P = "set (pairs dpp)"
  let ?RL = "rules dpp"
  let ?R = "set (rules dpp)"
  let ?echeck = "csr_dep_graph_edge_check (csr_dp_root_mu (mu_of \<mu>)) ?RL"
  let ?conv = "\<lambda>(real, Cs). (real \<noteq> None, map (\<lambda>(s,t). ((s,t), ())) Cs)"
  from check have wf: "wf_trs ?R"
    and subset: "?P \<subseteq> set (concat (map snd edps))"
    and scc: "isOK (check_graph_decomp (showsl \<circ> fst)
      (Multi_Map.empty (root o fst o fst))
      graph_approx_csr_rt Multi_Map.insert ?echeck (map ?conv edps))"
    unfolding check_csr_dep_graph_proc_def
    by (auto simp: Let_def)
  show ?thesis
    unfolding finite_csr_dpp_def SN_rel_defs SN_defs
  proof (rule notI)
    assume infinite: "\<exists>f. f 0 \<in> UNIV \<and>
      (\<forall>i. (f i, f (Suc i)) \<in>
        (relto (rrstep ?P) (csdp_step Sharp (mu_of \<mu>) ?R)))"
    from infinite obtain ch where chain:
      "\<And>i. (ch i, ch (Suc i)) \<in>
        relto (rrstep ?P) (csdp_step Sharp (mu_of \<mu>) ?R)"
      by auto
    from chain have chain':
      "\<And>i. (ch i, ch (Suc i)) \<in> (csdp_step Sharp (mu_of \<mu>) ?R)\<^sup>* O
        rrstep ?P O (csdp_step Sharp (mu_of \<mu>) ?R)\<^sup>*"
      by auto
    have ex_step: "\<forall>i. \<exists>l r \<sigma>.
      (l, r) \<in> ?P \<and>
      (ch i, l \<cdot> \<sigma>) \<in> (csdp_step Sharp (mu_of \<mu>) ?R)\<^sup>* \<and>
      (r \<cdot> \<sigma>, ch (Suc i)) \<in> (csdp_step Sharp (mu_of \<mu>) ?R)\<^sup>*"
    proof
      fix i
      from chain'[of i] obtain x y where pre:
        "(ch i, x) \<in> (csdp_step Sharp (mu_of \<mu>) ?R)\<^sup>*"
        and strict: "(x, y) \<in> rrstep ?P"
        and post: "(y, ch (Suc i)) \<in> (csdp_step Sharp (mu_of \<mu>) ?R)\<^sup>*"
        by auto
      from strict obtain l r \<sigma> where lr: "(l, r) \<in> ?P" and x: "x = l \<cdot> \<sigma>" and y: "y = r \<cdot> \<sigma>"
        unfolding rrstep_def' by auto
      show "\<exists>l r \<sigma>. (l, r) \<in> ?P \<and>
        (ch i, l \<cdot> \<sigma>) \<in> (csdp_step Sharp (mu_of \<mu>) ?R)\<^sup>* \<and>
        (r \<cdot> \<sigma>, ch (Suc i)) \<in> (csdp_step Sharp (mu_of \<mu>) ?R)\<^sup>*"
        using lr pre post unfolding x y by blast
    qed
    then obtain s t \<sigma> where
      pair: "\<And>i. (s i, t i) \<in> ?P"
      and pre: "\<And>i. (ch i, s i \<cdot> \<sigma> i) \<in>
        (csdp_step Sharp (mu_of \<mu>) ?R)\<^sup>*"
      and post: "\<And>i. (t i \<cdot> \<sigma> i, ch (Suc i)) \<in>
        (csdp_step Sharp (mu_of \<mu>) ?R)\<^sup>*"
      by metis
    have steps: "\<And>i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in>
      (csdp_step Sharp (mu_of \<mu>) ?R)\<^sup>*"
      using post pre by (meson rtrancl_trans)
    let ?p = "\<lambda>i. ((s i, t i), ())"
    have path: "\<And>i. ?echeck (?p i, ?p (Suc i))"
    proof -
      fix i
      have echeck_i: "?echeck (?p i, ?p (Suc i)) =
        (\<not> csr_inactive_arg_no_edge (csr_dp_root_mu (mu_of \<mu>)) ?RL
          (t i) (s (Suc i)) \<and>
         \<not> csr_frozen_root_no_edge (csr_dp_root_mu (mu_of \<mu>)) ?RL
          (t i) (s (Suc i)) \<and>
         \<not> csr_tcap_no_edge ?RL (t i) (s (Suc i)) \<and>
         \<not> csr_reverse_tcap_no_edge ?RL (t i) (s (Suc i)) \<and>
         \<not> csr_root_tcap_no_edge (csr_dp_root_mu (mu_of \<mu>)) ?RL
          (t i) (s (Suc i)) \<and>
         \<not> csr_shared_inactive_arg_no_edge (csr_dp_root_mu (mu_of \<mu>)) ?RL
          (t i) (s (Suc i)))"
        by simp
      show "?echeck (?p i, ?p (Suc i))"
        unfolding echeck_i
      proof (intro conjI notI)
        assume no: "csr_inactive_arg_no_edge (csr_dp_root_mu (mu_of \<mu>)) ?RL
          (t i) (s (Suc i))"
        from csr_inactive_arg_no_edge_sound[OF wf no, of "\<sigma> i" "\<sigma> (Suc i)"]
          steps[of i] show False by blast
      next
        assume no: "csr_frozen_root_no_edge (csr_dp_root_mu (mu_of \<mu>)) ?RL
          (t i) (s (Suc i))"
        from csr_frozen_root_no_edge_sound[OF wf no, of "\<sigma> i" "\<sigma> (Suc i)"]
          steps[of i] show False by blast
      next
        assume no: "csr_tcap_no_edge ?RL (t i) (s (Suc i))"
        from csr_tcap_no_edge_sound[OF no, of "\<sigma> i" "\<sigma> (Suc i)"]
          steps[of i] show False by blast
      next
        assume no: "csr_reverse_tcap_no_edge ?RL (t i) (s (Suc i))"
        from csr_reverse_tcap_no_edge_sound[OF no, of "\<sigma> i" "\<sigma> (Suc i)"]
          steps[of i] show False by blast
      next
        assume no: "csr_root_tcap_no_edge (csr_dp_root_mu (mu_of \<mu>)) ?RL
          (t i) (s (Suc i))"
        from csr_root_tcap_no_edge_sound[OF wf no, of "\<sigma> i" "\<sigma> (Suc i)"]
          steps[of i] show False by blast
      next
        assume no: "csr_shared_inactive_arg_no_edge
          (csr_dp_root_mu (mu_of \<mu>)) ?RL (t i) (s (Suc i))"
        from csr_shared_inactive_arg_no_edge_sound[OF wf no,
          of "\<sigma> i" "\<sigma> (Suc i)"] steps[of i]
        show False by blast
      qed
    qed
    have lift_node: "\<And>l r. (l, r) \<in> set (concat (map snd edps)) \<Longrightarrow>
      ((l, r), ()) \<in> set (concat (map snd (map ?conv edps)))"
    proof -
      fix l r
      assume lr: "(l, r) \<in> set (concat (map snd edps))"
      then obtain x where x: "x \<in> set edps" and lrx: "(l, r) \<in> set (snd x)"
        by auto
      obtain real Cs where xeq: "x = (real, Cs)"
        by (cases x, auto)
      from x xeq have mem: "(real, Cs) \<in> set edps"
        by simp
      from lrx xeq have lrCs: "(l, r) \<in> set Cs"
        by simp
      have node: "((l, r), ()) \<in> set (map (\<lambda>(s, t). ((s, t), ())) Cs)"
        using lrCs by force
      have conv_mem: "?conv (real, Cs) \<in> set (map ?conv edps)"
        using mem by (auto split: prod.splits)
      have comp_mem: "snd (?conv (real, Cs)) \<in> set (map snd (map ?conv edps))"
        using conv_mem unfolding set_map by blast
      have node': "((l, r), ()) \<in> set (snd (?conv (real, Cs)))"
        using node by simp
      show "((l, r), ()) \<in> set (concat (map snd (map ?conv edps)))"
        using comp_mem node' unfolding set_concat by blast
    qed
    have nodes: "path_nodes ?p \<subseteq> set (concat (map snd (map ?conv edps)))"
    proof
      fix x
      assume "x \<in> path_nodes ?p"
      then obtain i where x: "x = ?p i"
        unfolding path_nodes_def by auto
      from pair[of i] subset have "(s i, t i) \<in> set (concat (map snd edps))"
        by auto
      then show "x \<in> set (concat (map snd (map ?conv edps)))"
        unfolding x by (rule lift_node)
    qed
    have key_insert: "\<And>x m. Multi_Map.key_fun m = root \<circ> fst \<circ> fst \<Longrightarrow>
      Multi_Map.key_fun (Multi_Map.insert x m) = root \<circ> fst \<circ> fst"
      by simp
    have approx: "\<And>m a b. Multi_Map.key_fun m = root \<circ> fst \<circ> fst \<Longrightarrow>
      ?echeck (a, b) \<Longrightarrow> b \<in> set (Multi_Map.values m) \<Longrightarrow>
      b \<in> set (graph_approx_csr_rt m a)"
      unfolding graph_approx_csr_rt.simps by simp
    have component: "\<exists>q C. ?p =\<dots> q \<and> C \<in> set (map snd (filter fst (map ?conv edps)))
      \<and> path_nodes q \<subseteq> set C"
      by (rule check_graph_decomp_sound[of "\<lambda>m. set (Multi_Map.values m)",
        OF values_empty values_insert, of "\<lambda>m. Multi_Map.key_fun m = (root o fst o fst)",
        OF key_fun_empty key_insert approx scc path nodes])
    from component obtain q C where
      suffix: "?p =\<dots> q"
      and ending: "path_nodes q \<subseteq> set C"
      and component_mem: "C \<in> set (map snd (filter fst (map ?conv edps)))"
      by blast
    from component_mem obtain p Cs where
      mem: "(Some p, Cs) \<in> set edps"
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
    let ?tail = "\<lambda>m. ch (m + n)"
    have tail_chain: "\<And>m. (?tail m, ?tail (Suc m)) \<in>
      relto (rrstep (?P \<inter> set Cs))
        (csdp_step Sharp (mu_of \<mu>) ?R)"
    proof -
      fix m
      have suc_add: "Suc m + n = Suc (m + n)"
        by simp
      from pre[of "m + n"] post[of "m + n"] CP[of m]
      show "(?tail m, ?tail (Suc m)) \<in>
        relto (rrstep (?P \<inter> set Cs))
          (csdp_step Sharp (mu_of \<mu>) ?R)"
        unfolding suc_add by auto
    qed
    have tail_is_chain: "chain
      (relto (rrstep (?P \<inter> set Cs))
        (csdp_step Sharp (mu_of \<mu>) ?R)) ?tail"
      using tail_chain by simp
    have tail_sn: "SN
      (relto (rrstep (?P \<inter> set Cs))
        (csdp_step Sharp (mu_of \<mu>) ?R))"
      using fin[OF mem]
      unfolding finite_csr_dpp_def SN_rel_on_def .
    have not_tail_sn: "\<not> SN
      (relto (rrstep (?P \<inter> set Cs))
        (csdp_step Sharp (mu_of \<mu>) ?R))"
      by (rule not_SN_onI[of ?tail], simp, rule tail_is_chain)
    from tail_sn not_tail_sn show False
      by contradiction
  qed
qed

lemma check_csr_dp_termination_proof_core_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and plain: "plain_csr_dpp J dpp"
    and ok: "isOK (check_csr_dp_termination_proof_core I J \<mu> False i dpp prf)"
  shows "finite_csr_dpp Sharp (mu_of \<mu>) (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
  using ok plain
proof (induct "prf" arbitrary: dpp i)
  case CSR_DP_P_is_Empty
  then show ?case
    unfolding finite_csr_dpp_def SN_rel_defs by auto
next
  case (CSR_DP_Ordinary_Proof x)
  then have ok': "isOK (check_csr_dp_termination_proof I J False i dpp (CSR_DP_Ordinary_Proof x))"
    by simp
  from CSR_DP_Ordinary_Proof.prems(2) ok' show ?case
    by (rule check_csr_dp_termination_proof_sound_csr[OF I J])
next
  case (CSR_DP_Subterm_Criterion_Proc p rseq prules subprf)
  then have ok': "isOK (check_csr_dp_termination_proof I J False i dpp
      (CSR_DP_Subterm_Criterion_Proc p rseq prules subprf))"
    by simp
  from CSR_DP_Subterm_Criterion_Proc.prems(2) ok' show ?case
    by (rule check_csr_dp_termination_proof_sound_csr[OF I J])
next
  case (CSR_DP_Gen_Subterm_Criterion_Proc p prules subprf)
  then have ok': "isOK (check_csr_dp_termination_proof I J False i dpp
      (CSR_DP_Gen_Subterm_Criterion_Proc p prules subprf))"
    by simp
  from CSR_DP_Gen_Subterm_Criterion_Proc.prems(2) ok' show ?case
    by (rule check_csr_dp_termination_proof_sound_csr[OF I J])
next
  case (CSR_DP_Usable_Rules_Proc U subprf)
  then obtain dpp' where
    proc: "csr_mu_usable_rules_proc J \<mu> U dpp = return dpp'"
    and all_ok: "isOK (check_allm (\<lambda>lr. check (lr \<in> set U)
        (i \<circ> showsl_lit (STR '': conservative CSR usable-rules checker requires the usable rules to contain '')
          \<circ> showsl_rule lr)) (dpp_ops.rules J dpp))"
    and rec: "isOK (check_csr_dp_termination_proof_core I J \<mu> False (add_index i 1) dpp' subprf)"
    by auto
  from proc[unfolded csr_mu_usable_rules_proc_def, simplified]
  have dpp': "dpp' = dpp_ops.intersect_rules J dpp U"
    by auto
  from all_ok have all: "set (dpp_ops.rules J dpp) \<subseteq> set U"
    by (auto simp: isOK_check_allm isOK_check)
  have plain': "plain_csr_dpp J dpp'"
    unfolding dpp' by (rule plain_csr_dpp_intersect_rules[OF J CSR_DP_Usable_Rules_Proc.prems(2)])
  from CSR_DP_Usable_Rules_Proc.hyps[OF rec plain']
  have fin': "finite_csr_dpp Sharp (mu_of \<mu>) (set (dpp_ops.pairs J dpp')) (set (dpp_ops.rules J dpp'))" .
  show ?case
    by (rule finite_csr_dpp_intersect_rules_all[OF J all fin'[unfolded dpp']])
next
  case (CSR_DP_Dep_Graph_Proc x)
  from CSR_DP_Dep_Graph_Proc.prems(1) have graph_ok:
    "isOK (check_csr_dep_graph_proc J \<mu> dpp x)"
    and components_ok:
    "isOK (check_csr_dp_graph_components I J \<mu> False i dpp x)"
    by auto
  show ?case
  proof (rule check_csr_dep_graph_proc_sound[
      OF J CSR_DP_Dep_Graph_Proc.prems(2) graph_ok])
    fix p C
    assume mem: "(Some p, C) \<in> set x"
    let ?d = "dpp_ops.intersect_pairs J dpp C"
    from check_csr_dp_graph_components_member[OF components_ok mem]
    obtain j where rec:
      "isOK (check_csr_dp_termination_proof_core I J \<mu> False j ?d p)"
      by blast
    have plain': "plain_csr_dpp J ?d"
      by (rule plain_csr_dpp_intersect_pairs[
        OF J CSR_DP_Dep_Graph_Proc.prems(2)])
    have ih: "finite_csr_dpp Sharp (mu_of \<mu>)
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
      (NFS dpp, M dpp, set (P dpp) \<inter> set C,
        set (Pw dpp) \<inter> set C, set (Q dpp), set (R dpp), set (Rw dpp))"
      by (rule intersect_pairs_sound)
    have sem': "dpp_ops.dpp J ?d =
      (NFS ?d, M ?d, set (P ?d), set (Pw ?d),
        set (Q ?d), set (R ?d), set (Rw ?d))"
      by (rule dpp_sound)
    have pairs: "set (pairs ?d) = set (pairs dpp) \<inter> set C"
      using sem sem' pairs_sound[of dpp] pairs_sound[of ?d] by auto
    have rules: "set (rules ?d) = set (rules dpp)"
      using sem sem' rules_sound[of dpp] rules_sound[of ?d] by auto
    show "finite_csr_dpp Sharp (mu_of \<mu>)
      (set (dpp_ops.pairs J dpp) \<inter> set C)
      (set (dpp_ops.rules J dpp))"
      using ih unfolding pairs rules .
  qed
next
  case (CSR_DP_Size_Change_Subterm_Proc x)
  then have ok': "isOK (check_csr_dp_termination_proof I J False i dpp
      (CSR_DP_Size_Change_Subterm_Proc x))"
    by simp
  from CSR_DP_Size_Change_Subterm_Proc.prems(2) ok' show ?case
    by (rule check_csr_dp_termination_proof_sound_csr[OF I J])
qed

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
    show ?thesis
    proof (cases "mu_csr_dependency_pairs_tt Sharp J \<mu> R0 P")
      case (Inl e)
      from ok_case Inl obtain dpp where
        safe_dp: "safe_csr_dependency_pairs_tt Sharp J \<mu> R0 P = return dpp"
        and rec: "isOK (check_csr_dp_termination_proof I J False ?i dpp dp_prf)"
        by auto
      have fin: "finite_dpp (dpp_ops.dpp J dpp)"
        by (rule check_csr_dp_termination_proof_sound[OF I J rec])
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
      from ok_case Inr have rec:
        "isOK (check_csr_dp_termination_proof_core I J \<mu> False ?i d dp_prf)"
        by auto
      have mu_dp: "mu_csr_dependency_pairs_tt Sharp J \<mu> R0 P = return d"
        using Inr by simp
      have plain: "plain_csr_dpp J d"
      proof -
        interpret dpp_spec J by fact
        from Inr[unfolded mu_csr_dependency_pairs_tt_def Let_def, simplified]
        have d: "d = dpp_ops.mk J False False P [] [] [] R0"
          by auto
        have sem: "dpp_ops.dpp J d = (False, False, set P, {}, {}, {}, set R0)"
          using d unfolding dpp_spec.mk_sound[OF J] by simp
        have sem': "dpp_ops.dpp J d = (NFS d, M d, set (local.P d), set (Pw d), set (Q d),
          set (local.R d), set (Rw d))"
          by (rule dpp_sound)
        from sem sem' have "\<not> NFS d" "\<not> M d" "set (Pw d) = {}"
          "set (Q d) = {}" "set (local.R d) = {}"
          by auto
        then show ?thesis
          unfolding plain_csr_dpp_def by auto
      qed
      have fin_mu_csr: "finite_csr_dpp Sharp (mu_of \<mu>)
        (mu_CSDP_on Sharp (mu_of \<mu>) (set (defined_list R0)) (set R0)) (set R0)"
      proof -
        have fin_core: "finite_csr_dpp Sharp (mu_of \<mu>) (set (dpp_ops.pairs J d)) (set (dpp_ops.rules J d))"
          by (rule check_csr_dp_termination_proof_core_sound[OF I J plain rec])
        show ?thesis
          by (rule mu_csr_dependency_pairs_tt_finite_csr_mu_CSDP_on[OF J mu_dp fin_core])
      qed
      note mu_dp' = mu_dp[unfolded mu_csr_dependency_pairs_tt_def Let_def, simplified]
      have wf: "wf_trs (set R0)"
        using mu_dp' by auto
      have vc: "rhs_mu_vars_condition (mu_of \<mu>) (set R0)"
        by (rule rhs_mu_vars_condition_list_sound, insert mu_dp', auto)
      have D: "{f. defined (set R0) f} \<subseteq> set (defined_list R0)"
        using mu_dp' by auto
      show ?thesis
        by (rule finite_csr_mu_CSDP_on_imp_SN_csstep[OF wf vc D fin_mu_csr])
    qed
  qed
  subgoal for P dp_prf R0
  proof -
    assume ok_case:
      "isOK (check_csr_termination_proof I J a i \<mu> R0
        (CSR_Safe_Dependency_Pairs P dp_prf))"
    let ?i = "add_index i 1"
    from ok_case obtain dpp where
      safe_dp: "safe_csr_dependency_pairs_tt Sharp J \<mu> R0 P = return dpp"
      and rec: "isOK (check_csr_dp_termination_proof I J False ?i dpp dp_prf)"
      by auto
    have fin: "finite_dpp (dpp_ops.dpp J dpp)"
      by (rule check_csr_dp_termination_proof_sound[OF I J rec])
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
