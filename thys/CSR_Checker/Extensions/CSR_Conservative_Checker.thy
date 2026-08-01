(*
Author:  Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Conservative_Checker
  imports
    CSR_Innermost_Switch
    CSR_Improved_CSDP_Proofs
begin

lemma fresh_unsharp_Fun_no_csdp_step:
  assumes wf: "wf_trs R"
    and fresh: "\<And>n. \<not> defined R (U,n)"
    and unsharp: "\<not> is_sharp_lab U"
  shows "(Fun U ts, v) \<notin> csdp_step Sharp \<mu> R"
proof
  assume step: "(Fun U ts, v) \<in> csdp_step Sharp \<mu> R"
  then obtain p lr \<sigma> where
    rewrite: "(Fun U ts, v) \<in> rstep_r_p_s R lr p \<sigma>"
    and cond: "csdp_step_cond Sharp \<mu> p (Fun U ts)"
    unfolding csdp_step_def csdp_step_p_def by auto
  show False
  proof (cases p)
    case Nil
    from rewrite Nil have lr: "lr \<in> R"
      and lhs: "fst lr \<cdot> \<sigma> = Fun U ts"
      unfolding rstep_r_p_s_def' by auto
    from wf lr have lhs_fun: "is_Fun (fst lr)"
      unfolding wf_trs_def by (cases lr, force)
    then obtain f ss where lhs0: "fst lr = Fun f ss"
      by (cases "fst lr", auto)
    from lhs lhs0 have f: "f = U" and len: "length ss = length ts"
      by auto
    from lr lhs0 f len have "defined R (U,length ts)"
      unfolding defined_def by (cases lr, auto)
    with fresh show False by contradiction
  next
    case (Cons i q)
    from rewrite Cons have poss: "i # q \<in> poss (Fun U ts)"
      unfolding rstep_r_p_s_def' by auto
    from cond[unfolded csdp_step_cond_def, rule_format,
        of "[]" i q] poss Cons
    obtain f where "U = Sharp f"
      by auto
    with unsharp show False by simp
  qed
qed

lemma fresh_unsharp_Fun_SN_csdp:
  assumes wf: "wf_trs R"
    and fresh: "\<And>n. \<not> defined R (U,n)"
    and unsharp: "\<not> is_sharp_lab U"
  shows "SN_on (csdp_step Sharp \<mu> R) {Fun U ts}"
proof (unfold SN_on_def, intro notI)
  assume "\<exists>f. f 0 \<in> {Fun U ts} \<and>
    (\<forall>i. (f i, f (Suc i)) \<in> csdp_step Sharp \<mu> R)"
  then obtain f where init: "f 0 = Fun U ts"
    and steps: "\<And>i. (f i, f (Suc i)) \<in> csdp_step Sharp \<mu> R"
    by auto
  from fresh_unsharp_Fun_no_csdp_step[OF wf fresh unsharp,
      of ts "f (Suc 0)"] steps[of 0, unfolded init]
  show False by contradiction
qed

definition unhiding_subterm_pairs where
  "unhiding_subterm_pairs U P \<longleftrightarrow>
    (\<forall>(l,r)\<in>P. \<exists>s t. l = Fun U [s] \<and> r = Fun U [t] \<and> s \<rhd> t)"

lemma fresh_unsharp_Fun_csdp_steps_eq:
  assumes wf: "wf_trs R"
    and fresh: "\<And>n. \<not> defined R (U,n)"
    and unsharp: "\<not> is_sharp_lab U"
    and steps: "(Fun U ts, v) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "v = Fun U ts"
  using steps
proof (induct rule: rtrancl_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  from step.hyps(3) have y: "y = Fun U ts"
    using step.prems by simp
  from fresh_unsharp_Fun_no_csdp_step[OF wf fresh unsharp,
      of ts z] step.hyps(2)[unfolded y]
  show ?case by contradiction
qed

lemma rrstep_unhiding_subterm:
  assumes pairs: "unhiding_subterm_pairs U P"
    and step: "(s,t) \<in> rrstep P"
  obtains a b where "s = Fun U [a]" "t = Fun U [b]" "a \<rhd> b"
proof -
  from step obtain l r \<sigma> where lr: "(l,r) \<in> P"
    and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
    unfolding rrstep_def' by auto
  from pairs lr obtain a b where l: "l = Fun U [a]"
    and r: "r = Fun U [b]" and sub: "a \<rhd> b"
    unfolding unhiding_subterm_pairs_def by blast
  have "a \<cdot> \<sigma> \<rhd> b \<cdot> \<sigma>"
    by (rule supt_subst[OF sub])
  with that[of "a \<cdot> \<sigma>" "b \<cdot> \<sigma>"] s t l r
  show thesis by simp
qed

theorem finite_min_csr_dpp_unhiding_subterm:
  assumes wf: "wf_trs R"
    and fresh: "\<And>n. \<not> defined R (U,n)"
    and unsharp: "\<not> is_sharp_lab U"
    and pairs: "unhiding_subterm_pairs U P"
  shows "finite_min_csr_dpp Sharp \<mu> P R"
proof (unfold finite_min_csr_dpp_def SN_rel_on_def SN_on_def, intro notI)
  assume "\<exists>f. f 0 \<in> UNIV \<and>
    (\<forall>i. (f i, f (Suc i)) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>* O
      csr_min_pair_step Sharp \<mu> P R O
      (csdp_step Sharp \<mu> R)\<^sup>*)"
  then obtain f where chain:
    "\<And>i. (f i, f (Suc i)) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>* O
      csr_min_pair_step Sharp \<mu> P R O
      (csdp_step Sharp \<mu> R)\<^sup>*"
    by auto
  have shaped: "\<exists>t. f (Suc n) = Fun U [t]" for n
  proof (induct n)
    case 0
    from chain[of 0] obtain a b where
      pair: "(a,b) \<in> csr_min_pair_step Sharp \<mu> P R"
      and suffix: "(b,f (Suc 0)) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
      by auto
    from pair have rr: "(a,b) \<in> rrstep P"
      unfolding csr_min_pair_step_def by auto
    from rrstep_unhiding_subterm[OF pairs rr]
    obtain x y where ax: "a = Fun U [x]" and b: "b = Fun U [y]"
      and xy: "x \<rhd> y" .
    have suffix': "(Fun U [y], f (Suc 0)) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>*"
      using suffix unfolding b .
    from fresh_unsharp_Fun_csdp_steps_eq[OF wf fresh unsharp suffix']
    show ?case using b by auto
  next
    case (Suc n)
    then obtain x where start: "f (Suc n) = Fun U [x]" by auto
    from chain[of "Suc n"] obtain a b where
      prefix: "(f (Suc n),a) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
      and pair: "(a,b) \<in> csr_min_pair_step Sharp \<mu> P R"
      and suffix: "(b,f (Suc (Suc n))) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
      by auto
    have prefix': "(Fun U [x], a) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>*"
      using prefix unfolding start .
    from fresh_unsharp_Fun_csdp_steps_eq[OF wf fresh unsharp prefix']
    have a: "a = Fun U [x]" .
    from pair have rr: "(a,b) \<in> rrstep P"
      unfolding csr_min_pair_step_def by auto
    from rrstep_unhiding_subterm[OF pairs rr]
    obtain y z where ay: "a = Fun U [y]" and b: "b = Fun U [z]"
      and yz: "y \<rhd> z" .
    have suffix': "(Fun U [z], f (Suc (Suc n))) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>*"
      using suffix unfolding b .
    from fresh_unsharp_Fun_csdp_steps_eq[OF wf fresh unsharp suffix']
    show ?case using b by auto
  qed
  define args where "args n = (SOME t. f (Suc n) = Fun U [t])" for n
  have args: "f (Suc n) = Fun U [args n]" for n
    unfolding args_def by (rule someI_ex[OF shaped])
  have descent: "args n \<rhd> args (Suc n)" for n
  proof -
    from chain[of "Suc n"] obtain a b where
      prefix: "(f (Suc n),a) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
      and pair: "(a,b) \<in> csr_min_pair_step Sharp \<mu> P R"
      and suffix: "(b,f (Suc (Suc n))) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
      by auto
    have prefix': "(Fun U [args n], a) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>*"
      using prefix unfolding args .
    from fresh_unsharp_Fun_csdp_steps_eq[OF wf fresh unsharp prefix']
    have a: "a = Fun U [args n]" .
    from pair have rr: "(a,b) \<in> rrstep P"
      unfolding csr_min_pair_step_def by auto
    from rrstep_unhiding_subterm[OF pairs rr]
    obtain x y where a': "a = Fun U [x]" and b: "b = Fun U [y]"
      and sub: "x \<rhd> y" .
    from a a' have x: "x = args n" by simp
    have suffix': "(Fun U [y], f (Suc (Suc n))) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>*"
      using suffix unfolding b .
    from fresh_unsharp_Fun_csdp_steps_eq[OF wf fresh unsharp suffix']
    have "f (Suc (Suc n)) = Fun U [y]" by simp
    with args[of "Suc n"] have y: "y = args (Suc n)" by simp
    show ?thesis using sub x y by simp
  qed
  from SN_supt descent show False
    unfolding SN_defs by blast
qed

fun unhiding_subterm_pair_check where
  "unhiding_subterm_pair_check U (Fun V [s], Fun W [t]) =
    (V = U \<and> W = U \<and> supt_impl s t)"
| "unhiding_subterm_pair_check U lr = False"

definition unhiding_subterm_pairs_check where
  "unhiding_subterm_pairs_check U P =
    list_all (unhiding_subterm_pair_check U) P"

lemma unhiding_subterm_pairs_check_sound:
  assumes "unhiding_subterm_pairs_check U P"
  shows "unhiding_subterm_pairs U (set P)"
  unfolding unhiding_subterm_pairs_def
proof clarify
  fix a b
  assume mem: "(a, b) \<in> set P"
  from assms have all:
    "\<forall>x\<in>set P. unhiding_subterm_pair_check U x"
    unfolding unhiding_subterm_pairs_check_def
    by (simp add: list_all_iff)
  from all[rule_format, OF mem] have check:
    "unhiding_subterm_pair_check U (a, b)" .
  show "\<exists>s t. a = Fun U [s] \<and> b = Fun U [t] \<and> s \<rhd> t"
  proof (cases a)
    case (Var x)
    then show ?thesis using check by simp
  next
    case (Fun V ss)
    note a_shape = Fun
    show ?thesis
    proof (cases ss)
      case Nil
      then show ?thesis using check a_shape by simp
    next
      case (Cons s rest)
      note ss_shape = Cons
      show ?thesis
      proof (cases rest)
        case (Cons s' rest')
        then show ?thesis using check a_shape ss_shape by simp
      next
        case Nil
        note rest_shape = Nil
        show ?thesis
        proof (cases b)
          case (Var y)
          then show ?thesis using check a_shape ss_shape rest_shape by simp
        next
          case (Fun W ts)
          note b_shape = Fun
          show ?thesis
          proof (cases ts)
            case Nil2: Nil
            then show ?thesis
              using check a_shape ss_shape rest_shape b_shape by simp
          next
            case (Cons t tail)
            note ts_shape = Cons
            show ?thesis
            proof (cases tail)
              case (Cons t' tail')
              then show ?thesis
                using check a_shape ss_shape rest_shape b_shape ts_shape by simp
            next
              case Nil
              then show ?thesis
                using check a_shape ss_shape rest_shape b_shape ts_shape
                by (simp add: supt_impl)
            qed
          qed
        qed
      qed
    qed
  qed
qed

fun check_improved_csr_dp_termination_proof ::
  "('tp, ('f::{showl, compare_order,countable}, label_type) lab, string) tp_ops \<Rightarrow>
   ('dpp, ('f, label_type) lab, string) dpp_ops \<Rightarrow>
   (('f, label_type) lab) \<Rightarrow>
   (('f, label_type) lab) muL \<Rightarrow> bool \<Rightarrow>
   showsl \<Rightarrow> 'dpp \<Rightarrow>
   ('f, label_type, string) csr_dp_termination_proof \<Rightarrow> showsl check"
and check_improved_csr_dp_graph_components ::
  "('tp, ('f::{showl, compare_order,countable}, label_type) lab, string) tp_ops \<Rightarrow>
   ('dpp, ('f, label_type) lab, string) dpp_ops \<Rightarrow>
   (('f, label_type) lab) \<Rightarrow>
   (('f, label_type) lab) muL \<Rightarrow> bool \<Rightarrow>
   showsl \<Rightarrow> 'dpp \<Rightarrow>
   (('f, label_type, string) csr_dp_termination_proof option \<times>
    ('f, label_type, string) trsLL) list \<Rightarrow> showsl check"
where
  "check_improved_csr_dp_termination_proof I J U \<mu> a i dpp
      (CSR_DP_Usable_Rules_Proc Us prf) =
    debug i (STR ''improved QCS usable rules'') (do {
      dpp' \<leftarrow> csr_qcs_usable_rules_proc J \<mu> Us dpp;
      check_improved_csr_dp_termination_proof I J U \<mu> a
        (add_index i 1) dpp' prf
    })"
| "check_improved_csr_dp_termination_proof I J U \<mu> a i dpp
      (CSR_DP_Dep_Graph_Proc edpts) =
    debug i (STR ''improved minimal CSR-DP dependency graph'') (do {
      _ \<leftarrow> check_csr_dep_graph_proc J \<mu> dpp edpts;
      check_improved_csr_dp_graph_components I J U \<mu> a i dpp edpts
    })"
| "check_improved_csr_dp_termination_proof I J U \<mu> a i dpp
      (CSR_DP_Instantiation_Proc st sts prf) =
    debug i (STR ''LPAR08 CS instantiation'') (do {
      dpp' \<leftarrow> csr_instantiation_proc J \<mu> st sts dpp;
      check_improved_csr_dp_termination_proof I J U \<mu> a
        (add_index i 1) dpp' prf
    })"
| "check_improved_csr_dp_termination_proof I J U \<mu> a i dpp
      (CSR_DP_Size_Change_Subterm_Proc graphs) =
    (if unhiding_subterm_pairs_check U (dpp_ops.pairs J dpp)
     then debug i (STR ''LPAR08 unhiding subterm'') succeed
     else check_csr_dp_termination_proof_min I J \<mu> a i dpp
       (CSR_DP_Size_Change_Subterm_Proc graphs))"
| "check_improved_csr_dp_termination_proof I J U \<mu> a i dpp prf =
    check_csr_dp_termination_proof_min I J \<mu> a i dpp prf"
| "check_improved_csr_dp_graph_components I J U \<mu> a i dpp [] =
    succeed"
| "check_improved_csr_dp_graph_components I J U \<mu> a i dpp
      ((None, P) # rest) =
    check_improved_csr_dp_graph_components I J U \<mu> a
      (add_index i 1) dpp rest"
| "check_improved_csr_dp_graph_components I J U \<mu> a i dpp
      ((Some prf, P) # rest) = do {
    check_improved_csr_dp_termination_proof I J U \<mu> a
      (add_index i 1) (dpp_ops.intersect_pairs J dpp P) prf;
    check_improved_csr_dp_graph_components I J U \<mu> a
      (add_index i 1) dpp rest
  }"

lemma check_improved_csr_dp_graph_components_member:
  assumes ok: "isOK (check_improved_csr_dp_graph_components
      I J U \<mu> a i dpp edps)"
    and mem: "(Some prf, P) \<in> set edps"
  shows "\<exists>j. isOK (check_improved_csr_dp_termination_proof
    I J U \<mu> a j (dpp_ops.intersect_pairs J dpp P) prf)"
  using ok mem
proof (induct edps arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons head rest)
  obtain po C where head: "head = (po, C)" by (cases head)
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

lemma check_improved_csr_dp_termination_proof_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and plain: "plain_csr_dpp J dpp"
    and wf: "wf_trs (set (dpp_ops.rules J dpp))"
    and fresh_sharp: "\<And>f n.
      \<not> defined (set (dpp_ops.rules J dpp)) (Sharp f, n)"
    and fresh_U: "\<And>n.
      \<not> defined (set (dpp_ops.rules J dpp)) (U, n)"
    and unsharp: "\<not> is_sharp_lab U"
    and ok: "isOK (check_improved_csr_dp_termination_proof
      I J U \<mu> False i dpp prf)"
  shows "finite_min_csr_dpp Sharp (mu_of \<mu>)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
  using ok plain wf fresh_sharp fresh_U
proof (induct "prf" arbitrary: dpp i)
  case (CSR_DP_Dep_Graph_Proc edpts)
  from CSR_DP_Dep_Graph_Proc.prems(1) have graph_ok:
      "isOK (check_csr_dep_graph_proc J \<mu> dpp edpts)"
    and components_ok: "isOK (check_improved_csr_dp_graph_components
      I J U \<mu> False i dpp edpts)"
    by auto
  show ?case
  proof (rule check_csr_dep_graph_proc_min_sound[
      OF J CSR_DP_Dep_Graph_Proc.prems(2) graph_ok])
    fix p0 C
    assume mem: "(Some p0, C) \<in> set edpts"
    from check_improved_csr_dp_graph_components_member[
      OF components_ok mem]
    obtain j where rec: "isOK (check_improved_csr_dp_termination_proof
      I J U \<mu> False j (dpp_ops.intersect_pairs J dpp C) p0)"
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
    have wf': "wf_trs (set (rules ?d))"
      using CSR_DP_Dep_Graph_Proc.prems(3) unfolding rules' .
    have fresh_sharp': "\<And>f n.
      \<not> defined (set (rules ?d)) (Sharp f, n)"
      using CSR_DP_Dep_Graph_Proc.prems(4) unfolding rules' .
    have fresh_U': "\<And>n. \<not> defined (set (rules ?d)) (U, n)"
      using CSR_DP_Dep_Graph_Proc.prems(5) unfolding rules' .
    have fin': "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (pairs ?d)) (set (rules ?d))"
      apply (rule CSR_DP_Dep_Graph_Proc.hyps)
          apply (rule mem)
         apply simp
        apply simp
      apply (rule rec)
      apply (rule plain')
      apply (rule wf')
      apply (rule fresh_sharp')
      apply (rule fresh_U')
      done
    show "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (dpp_ops.pairs J dpp) \<inter> set C)
      (set (dpp_ops.rules J dpp))"
      using fin' unfolding pairs' rules' .
  qed
next
  case (CSR_DP_Instantiation_Proc st sts sub)
  from CSR_DP_Instantiation_Proc.prems(1)
  obtain dpp' where proc:
      "csr_instantiation_proc J \<mu> st sts dpp = return dpp'"
    and rec: "isOK (check_improved_csr_dp_termination_proof
      I J U \<mu> False (add_index i 1) dpp' sub)"
    by auto
  note proc_sound = csr_instantiation_proc_sound[OF proc]
  obtain s t where st: "st = (s,t)"
    by (cases st)
  interpret dpp_spec J by fact
  have selected: "(s,t) \<in> set (pairs dpp)"
    using proc_sound(2) st by simp
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
  have selected_P: "(s,t) \<in> set (P dpp)"
    using selected pairs_sound plain_fields by auto
  have pairs': "set (pairs dpp') =
      replace (s,t) (set sts) (set (pairs dpp))"
    using sem sem' pairs_sound[of dpp] pairs_sound[of dpp']
      plain_fields selected_P
    unfolding Util.replace_def by auto
  have rules': "set (rules dpp') = set (rules dpp)"
    using sem sem' rules_sound[of dpp] rules_sound[of dpp'] by auto
  have plain': "plain_csr_dpp J dpp'"
    using sem sem' plain_fields
    unfolding plain_csr_dpp_def Util.replace_def by auto
  have wf': "wf_trs (set (rules dpp'))"
    using CSR_DP_Instantiation_Proc.prems(3) unfolding rules' .
  have fresh_sharp': "\<And>f n.
      \<not> defined (set (rules dpp')) (Sharp f, n)"
    using CSR_DP_Instantiation_Proc.prems(4) unfolding rules' .
  have fresh_U': "\<And>n. \<not> defined (set (rules dpp')) (U, n)"
    using CSR_DP_Instantiation_Proc.prems(5) unfolding rules' .
  from CSR_DP_Instantiation_Proc.hyps[
      OF rec plain' wf' fresh_sharp' fresh_U']
  have fin': "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (pairs dpp')) (set (rules dpp'))" .
  show ?case
  proof (rule finite_min_csr_dpp_csr_instantiation[
      where RL = "rules dpp" and s = s and t = t
        and sts = "set sts"])
    show "wf_trs (set (rules dpp))"
      by (rule CSR_DP_Instantiation_Proc.prems(3))
    show "set (rules dpp) = set (rules dpp)"
      by simp
    fix u v
    assume uv: "(u,v) \<in> set (pairs dpp)"
    from proc_sound(4)[OF uv]
    have undef_list: "case root v of None \<Rightarrow> True
      | Some fn \<Rightarrow> fn \<notin> set (defined_list (rules dpp))" .
    show "case root v of None \<Rightarrow> True
      | Some fn \<Rightarrow> \<not> defined (set (rules dpp)) fn"
    proof (cases "root v")
      case None
      then show ?thesis by simp
    next
      case (Some fn)
      from undef_list Some
      have "fn \<notin> set (defined_list (rules dpp))"
        by simp
      with Some show ?thesis
        by simp
    qed
  next
    fix st'
    assume "st' \<in> set sts"
    from proc_sound(3)[OF this]
    show "instance_rule st' (s,t)"
      unfolding st .
  next
    fix u v \<gamma>
    assume uv: "(u,v) \<in> set (pairs dpp)"
      and matcher:
        "gc_matcher
          (csr_instantiation_cap (mu_of \<mu>) (rules dpp) v) s =
          Some \<gamma>"
    from proc_sound(5)[OF st uv matcher]
    show "\<exists>st'\<in>set sts.
      instance_rule (s \<cdot> \<gamma>, t \<cdot> \<gamma>) st'" .
  next
    show "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (replace (s,t) (set sts) (set (pairs dpp)))
      (set (rules dpp))"
      using fin' unfolding pairs' rules' .
  qed
next
  case (CSR_DP_Size_Change_Subterm_Proc graphs)
  show ?case
  proof (cases "unhiding_subterm_pairs_check U
      (dpp_ops.pairs J dpp)")
    case True
    show ?thesis
      by (rule finite_min_csr_dpp_unhiding_subterm[
        OF CSR_DP_Size_Change_Subterm_Proc.prems(3)
          CSR_DP_Size_Change_Subterm_Proc.prems(5) unsharp
          unhiding_subterm_pairs_check_sound[OF True]])
  next
    case False
    from CSR_DP_Size_Change_Subterm_Proc.prems(1) False
    have old: "isOK (check_csr_dp_termination_proof_min I J \<mu> False
      i dpp (CSR_DP_Size_Change_Subterm_Proc graphs))"
      by simp
    show ?thesis
      by (rule check_csr_dp_termination_proof_min_sound[
        OF I J CSR_DP_Size_Change_Subterm_Proc.prems(2)
          CSR_DP_Size_Change_Subterm_Proc.prems(3)
          CSR_DP_Size_Change_Subterm_Proc.prems(4) old])
  qed
next
  case CSR_DP_P_is_Empty
  from CSR_DP_P_is_Empty.prems(1) have old:
    "isOK (check_csr_dp_termination_proof_min I J \<mu> False i dpp
      CSR_DP_P_is_Empty)"
    by simp
  show ?case by (rule check_csr_dp_termination_proof_min_sound[
    OF I J CSR_DP_P_is_Empty.prems(2) CSR_DP_P_is_Empty.prems(3)
      CSR_DP_P_is_Empty.prems(4) old])
next
  case (CSR_DP_Ordinary_Proof p0)
  from CSR_DP_Ordinary_Proof.prems(1) have old:
    "isOK (check_csr_dp_termination_proof_min I J \<mu> False i dpp
      (CSR_DP_Ordinary_Proof p0))"
    by simp
  show ?case by (rule check_csr_dp_termination_proof_min_sound[
    OF I J CSR_DP_Ordinary_Proof.prems(2) CSR_DP_Ordinary_Proof.prems(3)
      CSR_DP_Ordinary_Proof.prems(4) old])
next
  case (CSR_DP_Subterm_Criterion_Proc p rseq Pr sub)
  from CSR_DP_Subterm_Criterion_Proc.prems(1) have old:
    "isOK (check_csr_dp_termination_proof_min I J \<mu> False i dpp
      (CSR_DP_Subterm_Criterion_Proc p rseq Pr sub))"
    by simp
  show ?case by (rule check_csr_dp_termination_proof_min_sound[
    OF I J CSR_DP_Subterm_Criterion_Proc.prems(2)
      CSR_DP_Subterm_Criterion_Proc.prems(3)
      CSR_DP_Subterm_Criterion_Proc.prems(4) old])
next
  case (CSR_DP_Gen_Subterm_Criterion_Proc p Pr sub)
  from CSR_DP_Gen_Subterm_Criterion_Proc.prems(1) have old:
    "isOK (check_csr_dp_termination_proof_min I J \<mu> False i dpp
      (CSR_DP_Gen_Subterm_Criterion_Proc p Pr sub))"
    by simp
  show ?case by (rule check_csr_dp_termination_proof_min_sound[
    OF I J CSR_DP_Gen_Subterm_Criterion_Proc.prems(2)
      CSR_DP_Gen_Subterm_Criterion_Proc.prems(3)
      CSR_DP_Gen_Subterm_Criterion_Proc.prems(4) old])
next
  case (CSR_DP_Usable_Rules_Proc U0 sub)
  from CSR_DP_Usable_Rules_Proc.prems(1)
  obtain dpp' where proc:
      "csr_qcs_usable_rules_proc J \<mu> U0 dpp = return dpp'"
    and rec: "isOK (check_improved_csr_dp_termination_proof
      I J U \<mu> False (add_index i 1) dpp' sub)"
    by auto
  from csr_qcs_usable_rules_proc_sound[OF J proc]
  have dpp': "dpp' = dpp_ops.intersect_rules J dpp U0"
    and closed: "qcs_csr_ur_closed (set (dpp_ops.rules J dpp)) (set U0)
      (mu_of \<mu>) (set (dpp_ops.pairs J dpp))"
    by auto
  interpret dpp_spec J by fact
  have sem: "dpp_ops.dpp J dpp' =
    (NFS dpp, M dpp, set (P dpp), set (Pw dpp), set (Q dpp),
      set (R dpp) \<inter> set U0, set (Rw dpp) \<inter> set U0)"
    unfolding dpp' by (rule intersect_rules_sound)
  have sem': "dpp_ops.dpp J dpp' =
    (NFS dpp', M dpp', set (P dpp'), set (Pw dpp'), set (Q dpp'),
      set (R dpp'), set (Rw dpp'))"
    by (rule dpp_sound)
  from closed have subset: "set U0 \<subseteq> set (rules dpp)"
    unfolding qcs_csr_ur_closed_def by auto
  have P': "set (pairs dpp') = set (pairs dpp)"
    using sem sem' pairs_sound[of dpp] pairs_sound[of dpp'] by auto
  have R': "set (rules dpp') = set U0"
    using sem sem' rules_sound[of dpp] rules_sound[of dpp'] subset by auto
  have plain': "plain_csr_dpp J dpp'"
    unfolding dpp' by (rule plain_csr_dpp_intersect_rules[
      OF J CSR_DP_Usable_Rules_Proc.prems(2)])
  have wf': "wf_trs (set (rules dpp'))"
    using CSR_DP_Usable_Rules_Proc.prems(3) subset
    unfolding R' wf_trs_def by auto
  have fresh_sharp': "\<And>f n.
      \<not> defined (set (rules dpp')) (Sharp f, n)"
    using CSR_DP_Usable_Rules_Proc.prems(4) subset
    unfolding R' defined_def by blast
  have fresh_U': "\<And>n. \<not> defined (set (rules dpp')) (U, n)"
    using CSR_DP_Usable_Rules_Proc.prems(5) subset
    unfolding R' defined_def by blast
  from CSR_DP_Usable_Rules_Proc.hyps[
    OF rec plain' wf' fresh_sharp' fresh_U']
  have fin': "finite_min_csr_dpp Sharp (mu_of \<mu>)
    (set (pairs dpp')) (set (rules dpp'))" .
  show ?case
    by (rule finite_min_csr_dpp_qcs_usable_rules[
      OF CSR_DP_Usable_Rules_Proc.prems(3)
        CSR_DP_Usable_Rules_Proc.prems(4)
        closed fin'[unfolded P' R']])
qed

lemma improved_hiding_context_unhides_min:
  assumes cover: "improved_csdp_coverage Sharp U \<mu> D R P"
    and C: "hiding_context_on \<mu> D R C"
    and wf: "wf_trs R"
    and fresh: "\<And>n. \<not> defined R (U,n)"
    and unsharp: "\<not> is_sharp_lab U"
  shows "(Fun U [C\<langle>t\<rangle>], Fun U [t]) \<in>
    (csr_min_pair_step Sharp \<mu> P R)\<^sup>*"
  using C
proof (induct rule: hiding_context_on.induct)
  case hole
  then show ?case by simp
next
  case (more f bef aft C)
  let ?args = "bef @ C\<langle>t\<rangle> # aft"
  let ?whole = "Fun f ?args"
  have i: "length bef < length ?args" by simp
  have nth: "?args ! length bef = C\<langle>t\<rangle>" by simp
  have hide: "hides_position_on \<mu> D R
      (f,length ?args) (length bef)"
    using more.hyps(1) by simp
  from cover[unfolded improved_csdp_coverage_def]
  have step0: "(Fun U [?whole], Fun U [?args ! length bef]) \<in> rrstep P"
    using hide i by blast
  have target:
    "SN_on (csdp_step Sharp \<mu> R) {Fun U [C\<langle>t\<rangle>]}"
    by (rule fresh_unsharp_Fun_SN_csdp[OF wf fresh unsharp])
  have step: "(Fun U [?whole], Fun U [C\<langle>t\<rangle>]) \<in>
      csr_min_pair_step Sharp \<mu> P R"
    using step0 target nth unfolding csr_min_pair_step_def by auto
  from step more.hyps(3) show ?case by auto
qed

lemma improved_hidden_instance_min:
  assumes cover: "improved_csdp_coverage Sharp U \<mu> D R P"
    and hidden: "hidden_term_on \<mu> D R h"
    and wf: "wf_trs R"
    and fresh_sharp: "\<And>f n. \<not> defined R (Sharp f,n)"
    and T: "h \<cdot> \<sigma> \<in> mu_Tinf \<mu> (csstep \<mu> R)"
  shows "(Fun U [h \<cdot> \<sigma>], sharp_term Sharp (h \<cdot> \<sigma>)) \<in>
    csr_min_pair_step Sharp \<mu> P R"
proof -
  have step: "(Fun U [h \<cdot> \<sigma>], sharp_term Sharp (h \<cdot> \<sigma>))
      \<in> rrstep P"
    by (rule hidden_instance_unhides[OF cover hidden])
  have target: "SN_on (csdp_step Sharp \<mu> R)
      {sharp_term Sharp (h \<cdot> \<sigma>)}"
    by (rule mu_Tinf_imp_SN_sharp_csdp[OF wf fresh_sharp T])
  show ?thesis using step target unfolding csr_min_pair_step_def by auto
qed

lemma improved_collapsing_instance_min:
  assumes cover: "improved_csdp_coverage Sharp U \<mu> D R P"
    and lr: "(l,r) \<in> R"
    and xr: "x \<in> mu_vars_term \<mu> r"
    and xl: "x \<notin> mu_vars_term \<mu> l"
    and lhs: "is_Fun l"
    and wf: "wf_trs R"
    and fresh_U: "\<And>n. \<not> defined R (U,n)"
    and unsharp: "\<not> is_sharp_lab U"
  shows "(sharp_term Sharp (l \<cdot> \<sigma>), Fun U [\<sigma> x]) \<in>
    csr_min_pair_step Sharp \<mu> P R"
proof -
  have step: "(sharp_term Sharp (l \<cdot> \<sigma>), Fun U [\<sigma> x])
      \<in> rrstep P"
    by (rule collapsing_instance_step[OF cover lr xr xl lhs])
  have target: "SN_on (csdp_step Sharp \<mu> R) {Fun U [\<sigma> x]}"
    by (rule fresh_unsharp_Fun_SN_csdp[OF wf fresh_U unsharp])
  show ?thesis using step target unfolding csr_min_pair_step_def by auto
qed

lemma improved_collapsing_hiding_min_path:
  assumes cover: "improved_csdp_coverage Sharp U \<mu> D R P"
    and lr: "(l,r) \<in> R"
    and xr: "x \<in> mu_vars_term \<mu> r"
    and xl: "x \<notin> mu_vars_term \<mu> l"
    and lhs: "is_Fun l"
    and C: "hiding_context_on \<mu> D R C"
    and hidden: "hidden_term_on \<mu> D R h"
    and sx: "\<sigma> x = C\<langle>h \<cdot> \<tau>\<rangle>"
    and wf: "wf_trs R"
    and fresh_U: "\<And>n. \<not> defined R (U,n)"
    and unsharp: "\<not> is_sharp_lab U"
    and fresh_sharp: "\<And>f n. \<not> defined R (Sharp f,n)"
    and T: "h \<cdot> \<tau> \<in> mu_Tinf \<mu> (csstep \<mu> R)"
  shows "(sharp_term Sharp (l \<cdot> \<sigma>), sharp_term Sharp (h \<cdot> \<tau>))
    \<in> (csr_min_pair_step Sharp \<mu> P R)\<^sup>+"
proof -
  have first: "(sharp_term Sharp (l \<cdot> \<sigma>), Fun U [\<sigma> x]) \<in>
      csr_min_pair_step Sharp \<mu> P R"
    by (rule improved_collapsing_instance_min[
        OF cover lr xr xl lhs wf fresh_U unsharp])
  have middle: "(Fun U [\<sigma> x], Fun U [h \<cdot> \<tau>]) \<in>
      (csr_min_pair_step Sharp \<mu> P R)\<^sup>*"
    using improved_hiding_context_unhides_min[
      OF cover C wf fresh_U unsharp, of "h \<cdot> \<tau>"] sx by simp
  have last: "(Fun U [h \<cdot> \<tau>], sharp_term Sharp (h \<cdot> \<tau>)) \<in>
      csr_min_pair_step Sharp \<mu> P R"
    by (rule improved_hidden_instance_min[
        OF cover hidden wf fresh_sharp T])
  from first middle have prefix:
      "(sharp_term Sharp (l \<cdot> \<sigma>), Fun U [h \<cdot> \<tau>]) \<in>
        (csr_min_pair_step Sharp \<mu> P R)\<^sup>+"
    by (meson r_into_trancl rtrancl_into_trancl2)
  from prefix last show ?thesis by (rule trancl_into_trancl)
qed

lemma csrstep_hiding_rhs_imp_improved_min_path:
  assumes wf: "wf_trs R"
    and step: "(s,t) \<in> csrstep \<mu> R"
    and hp: "has_hiding_property \<mu> D R (csstep \<mu> R) s"
    and notSN: "\<not> SN_on (csstep \<mu> R) {t}"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "improved_csdp_coverage Sharp U \<mu> D R P"
    and fresh_U: "\<And>n. \<not> defined R (U,n)"
    and unsharp: "\<not> is_sharp_lab U"
    and fresh_sharp: "\<And>f n. \<not> defined R (Sharp f,n)"
  shows "\<exists>u. u \<in> mu_Tinf \<mu> (csstep \<mu> R) \<and>
    (t = u \<or> mu_supt \<mu> t u) \<and>
    (sharp_term Sharp s, sharp_term Sharp u) \<in>
      (csr_min_pair_step Sharp \<mu> P R)\<^sup>+"
proof -
  from step obtain l r \<sigma> where lr: "(l,r) \<in> R"
    and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
    by (elim csrstepE)
  from wf lr have lhs: "is_Fun l"
    and vars: "vars_term r \<subseteq> vars_term l"
    unfolding wf_trs_def by (cases l, auto)
  from hp have sT: "s \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    unfolding has_hiding_property_def by auto
  from csstep_notSN_imp_mu_Tinf_defined_subterm[OF wf notSN[unfolded t]]
  obtain p f us where p_mu: "p \<in> mu_fun_poss \<mu> (r \<cdot> \<sigma>)"
    and sub_inst: "(r \<cdot> \<sigma>) |_ p = Fun f us"
    and def: "defined R (f, length us)"
    and T_p: "(r \<cdot> \<sigma>) |_ p \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    by blast
  let ?u = "(r \<cdot> \<sigma>) |_ p"
  have active_rhs: "t = ?u \<or> mu_supt \<mu> t ?u"
  proof (cases p)
    case Nil
    with t show ?thesis by simp
  next
    case (Cons i q)
    have pos: "i # q \<in> mu_poss \<mu> (r \<cdot> \<sigma>)"
      using p_mu Cons mu_fun_poss_imp_mu_poss by blast
    have "(r \<cdot> \<sigma>) |_ (i # q) = ?u"
      unfolding Cons by simp
    then have "mu_supt \<mu> (r \<cdot> \<sigma>) ?u"
      unfolding mu_supt_def using pos by blast
    with t show ?thesis by simp
  qed
  from T_p have notSN_p: "\<not> SN_on (csstep \<mu> R) {?u}"
    unfolding mu_Tinf_def by auto
  from mu_fun_poss_subst_cases_aux_mu[OF p_mu]
  show ?thesis
  proof
    assume orig: "p \<in> mu_fun_poss \<mu> r \<and>
      (r \<cdot> \<sigma>) |_ p = (r |_ p) \<cdot> \<sigma>"
    then have p_r: "p \<in> mu_fun_poss \<mu> r"
      and sub_subst: "?u = (r |_ p) \<cdot> \<sigma>" by auto
    from mu_fun_poss_imp_fun_poss[OF p_r] obtain g ts where
      rp0: "r |_ p = Fun g ts"
      using fun_poss_fun_conv by blast
    with sub_subst sub_inst have rp: "r |_ p = Fun f ts"
      and len: "length us = length ts" by auto
    from defs def len have fD: "(f, length ts) \<in> D" by auto
    have ns: "\<not> mu_supt \<mu> l (r |_ p)"
    proof
      assume supt: "mu_supt \<mu> l (r |_ p)"
      then obtain i q where iq: "i # q \<in> mu_poss \<mu> l"
        and sub_l: "l |_ (i # q) = r |_ p"
        unfolding mu_supt_def by auto
      have iq_poss: "i # q \<in> poss l"
        using iq mu_poss_imp_poss by blast
      have sub_eq: "(l \<cdot> \<sigma>) |_ (i # q) = (r |_ p) \<cdot> \<sigma>"
        using subt_at_subst[OF iq_poss] sub_l by simp
      have "mu_supt \<mu> (l \<cdot> \<sigma>) ((r |_ p) \<cdot> \<sigma>)"
        unfolding mu_supt_def
        by (intro exI[of _ i] exI[of _ q],
            insert mu_poss_subst_lift[OF iq, of \<sigma>] sub_eq, auto)
      with sT have "SN_on (csstep \<mu> R) {(r |_ p) \<cdot> \<sigma>}"
        unfolding s mu_Tinf_def by blast
      with notSN_p sub_subst show False by simp
    qed
    have dp0:
      "(sharp_term Sharp (l \<cdot> \<sigma>), sharp_term Sharp ((r |_ p) \<cdot> \<sigma>))
        \<in> rrstep (mu_CSDP_on Sharp \<mu> D R)"
      by (rule rrstep_mu_CSDP_onI[OF lr lhs p_r rp fD ns])
    have mono: "rrstep (mu_CSDP_on Sharp \<mu> D R) \<subseteq> rrstep P"
      by (rule rrstep_mono[OF improved_csdp_coverage_mu[OF cover]])
    have pair: "(sharp_term Sharp s, sharp_term Sharp ?u) \<in> rrstep P"
      using dp0 mono unfolding s sub_subst by auto
    have target: "SN_on (csdp_step Sharp \<mu> R) {sharp_term Sharp ?u}"
      by (rule mu_Tinf_imp_SN_sharp_csdp[OF wf fresh_sharp T_p])
    have min_pair:
      "(sharp_term Sharp s, sharp_term Sharp ?u) \<in>
        csr_min_pair_step Sharp \<mu> P R"
      using pair target unfolding csr_min_pair_step_def by auto
    with T_p active_rhs show ?thesis by (blast intro: r_into_trancl)
  next
    assume subst_case: "\<exists>x q1 q2. q1 \<in> mu_poss \<mu> r \<and>
      r |_ q1 = Var x \<and> x \<in> vars_term r \<and> p = q1 @ q2 \<and>
      q2 \<in> mu_fun_poss \<mu> (\<sigma> x) \<and> ?u = \<sigma> x |_ q2"
    then obtain x q1 q2 where q1: "q1 \<in> mu_poss \<mu> r"
      and r_q1: "r |_ q1 = Var x" and x_r: "x \<in> vars_term r"
      and p: "p = q1 @ q2" and q2: "q2 \<in> mu_fun_poss \<mu> (\<sigma> x)"
      and u: "?u = \<sigma> x |_ q2" by blast
    have xr_mu: "x \<in> mu_vars_term \<mu> r"
      unfolding mu_vars_term_def using q1 r_q1 by blast
    show ?thesis
    proof (cases "x \<in> mu_vars_term \<mu> l")
      case True
      have "SN_on (csstep \<mu> R) {\<sigma> x |_ q2}"
        by (rule mu_Tinf_SN_on_active_subst_mu_subterm[
            OF lhs sT[unfolded s] True q2])
      with notSN_p u show ?thesis by simp
    next
      case False
      from vars x_r have x_l: "x \<in> vars_term l" by auto
      from lhs x_l have l_supt_x: "l \<rhd> Var x"
        using supteq_Var[of x l] unfolding supt_supteq_conv
        by (cases l, auto)
      have s_supt_x: "s \<rhd> \<sigma> x"
        using supt_subst[OF l_supt_x, of \<sigma>] unfolding s by simp
      have not_mu_supt_x: "\<not> mu_supt \<mu> s (\<sigma> x)"
      proof
        assume active: "mu_supt \<mu> s (\<sigma> x)"
        from sT active have snx: "SN_on (csstep \<mu> R) {\<sigma> x}"
          unfolding mu_Tinf_def by auto
        have snu: "SN_on (csstep \<mu> R) {\<sigma> x |_ q2}"
          by (rule SN_on_mu_subterm[OF wf q2 snx])
        with notSN_p u show False by simp
      qed
      have active_u: "\<sigma> x = ?u \<or> mu_supt \<mu> (\<sigma> x) ?u"
      proof (cases q2)
        case Nil
        with u show ?thesis by simp
      next
        case (Cons i q)
        from q2 have ip: "i # q \<in> mu_poss \<mu> (\<sigma> x)"
          using mu_fun_poss_imp_mu_poss Cons by blast
        have sub: "\<sigma> x |_ (i # q) = ?u" using u Cons by simp
        show ?thesis unfolding mu_supt_def using ip sub by blast
      qed
      from hp s_supt_x not_mu_supt_x active_u T_p
      obtain C h \<tau> where C: "hiding_context_on \<mu> D R C"
        and hidden: "hidden_term_on \<mu> D R h"
        and sx: "\<sigma> x = C\<langle>h \<cdot> \<tau>\<rangle>"
        and uh: "?u = h \<cdot> \<tau>"
        unfolding has_hiding_property_def by blast
      have path:
        "(sharp_term Sharp (l \<cdot> \<sigma>), sharp_term Sharp (h \<cdot> \<tau>))
          \<in> (csr_min_pair_step Sharp \<mu> P R)\<^sup>+"
        by (rule improved_collapsing_hiding_min_path[
            where U=U and \<mu>=\<mu> and D=D and R=R and P=P and l=l and r=r
              and x=x and \<sigma>=\<sigma> and C=C and h=h and \<tau>=\<tau>,
            OF cover lr xr_mu False lhs C hidden sx wf fresh_U unsharp
              fresh_sharp T_p[unfolded uh]])
      with T_p active_rhs show ?thesis unfolding s uh by blast
    qed
  qed
qed

lemma hiding_imp_improved_min_relstep:
  assumes wf: "wf_trs R"
    and defs: "{f. defined R f} \<subseteq> D"
    and hp: "has_hiding_property \<mu> D R (csstep \<mu> R) t"
    and cover: "improved_csdp_coverage Sharp U \<mu> D R P"
    and fresh_U: "\<And>n. \<not> defined R (U,n)"
    and unsharp: "\<not> is_sharp_lab U"
    and fresh_sharp: "\<And>f n. \<not> defined R (Sharp f,n)"
  shows "\<exists>u. has_hiding_property \<mu> D R (csstep \<mu> R) u \<and>
    (sharp_term Sharp t, sharp_term Sharp u) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>* O
      (csr_min_pair_step Sharp \<mu> P R)\<^sup>+ O
      (csdp_step Sharp \<mu> R)\<^sup>*"
proof -
  from hp have Tinf: "t \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    unfolding has_hiding_property_def by auto
  from mu_Tinf_imp_SN_csnr_first_csrstep[OF wf Tinf]
  obtain s v where pref: "(t,s) \<in> (csnrstep \<mu> R)\<^sup>*"
    and root: "(s,v) \<in> csrstep \<mu> R"
    and notSN_v: "\<not> SN_on (csstep \<mu> R) {v}" by auto
  have sv: "(s,v) \<in> csstep \<mu> R"
    using root unfolding csstep_root_nonroot by auto
  have notSN_s: "\<not> SN_on (csstep \<mu> R) {s}"
    by (rule step_notSN_on_source[OF sv notSN_v])
  have sT: "s \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    by (rule csnrsteps_mu_Tinf_preserve[OF wf pref Tinf notSN_s])
  have hp_s: "has_hiding_property \<mu> D R (csstep \<mu> R) s"
    by (rule csnrsteps_hiding_property_preserve[OF wf defs pref hp sT])
  from csrstep_hiding_rhs_imp_improved_min_path[
      OF wf root hp_s notSN_v defs cover fresh_U unsharp fresh_sharp]
  obtain u where uT: "u \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    and active: "v = u \<or> mu_supt \<mu> v u"
    and pair_path:
      "(sharp_term Sharp s, sharp_term Sharp u) \<in>
        (csr_min_pair_step Sharp \<mu> P R)\<^sup>+" by blast
  have hp_u: "has_hiding_property \<mu> D R (csstep \<mu> R) u"
    by (rule csrstep_hiding_property_active_target[
        OF wf defs root hp_s active uT])
  have prefix: "(sharp_term Sharp t, sharp_term Sharp s) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>*"
    by (rule csnrsteps_imp_sharp_csdp_steps[OF pref])
  have suffix: "(sharp_term Sharp u, sharp_term Sharp u) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>*" by simp
  show ?thesis using hp_u prefix pair_path suffix by blast
qed

theorem finite_min_improved_CSDP_imp_SN_csstep:
  assumes wf: "wf_trs R"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "improved_csdp_coverage Sharp U \<mu> D R P"
    and fresh_U: "\<And>n. \<not> defined R (U,n)"
    and unsharp: "\<not> is_sharp_lab U"
    and fresh_sharp: "\<And>f n. \<not> defined R (Sharp f,n)"
    and fin: "finite_min_csr_dpp Sharp \<mu> P R"
  shows "SN (csstep \<mu> R)"
proof (rule ccontr)
  assume notSN: "\<not> SN (csstep \<mu> R)"
  from not_SN_imp_Tinf[OF notSN]
  obtain t0 where t0_T: "t0 \<in> Tinf (csstep \<mu> R)" by blast
  have hp0: "has_hiding_property \<mu> D R (csstep \<mu> R) t0"
    by (rule Tinf_has_hiding_property[OF t0_T])
  let ?S = "csdp_step Sharp \<mu> R"
  let ?M = "csr_min_pair_step Sharp \<mu> P R"
  let ?A = "?S\<^sup>* O ?M O ?S\<^sup>*"
  let ?B = "?S\<^sup>* O ?M\<^sup>+ O ?S\<^sup>*"
  have step_ex: "\<And>t. has_hiding_property \<mu> D R (csstep \<mu> R) t \<Longrightarrow>
      \<exists>u. has_hiding_property \<mu> D R (csstep \<mu> R) u \<and>
        (sharp_term Sharp t, sharp_term Sharp u) \<in> ?B"
    by (rule hiding_imp_improved_min_relstep[
        OF wf defs _ cover fresh_U unsharp fresh_sharp])
  have all_ex: "\<forall>t. \<exists>u.
      has_hiding_property \<mu> D R (csstep \<mu> R) t \<longrightarrow>
      has_hiding_property \<mu> D R (csstep \<mu> R) u \<and>
        (sharp_term Sharp t, sharp_term Sharp u) \<in> ?B"
    using step_ex by blast
  from choice[OF all_ex]
  obtain nxt where nxt:
    "\<And>t. has_hiding_property \<mu> D R (csstep \<mu> R) t \<Longrightarrow>
      has_hiding_property \<mu> D R (csstep \<mu> R) (nxt t) \<and>
      (sharp_term Sharp t, sharp_term Sharp (nxt t)) \<in> ?B"
    by blast
  define ts where "ts = rec_nat t0 (\<lambda>n t. nxt t)"
  have ts_hp: "has_hiding_property \<mu> D R (csstep \<mu> R) (ts n)" for n
  proof (induct n)
    case 0
    show ?case unfolding ts_def using hp0 by simp
  next
    case (Suc n)
    from nxt[OF Suc.hyps] show ?case unfolding ts_def by simp
  qed
  have ts_step:
      "(sharp_term Sharp (ts n), sharp_term Sharp (ts (Suc n))) \<in> ?B"
    for n
    using nxt[OF ts_hp[of n]] unfolding ts_def by simp
  define f where "f n = sharp_term Sharp (ts n)" for n
  have chain: "\<And>n. (f n, f (Suc n)) \<in> ?B"
    unfolding f_def using ts_step by simp
  have B_sub: "?B \<subseteq> ?A\<^sup>+" by regexp
  have "\<not> SN (?A\<^sup>+)"
  proof -
    have "\<not> SN ?B" unfolding SN_defs using chain by blast
    then show ?thesis using SN_subset[of "?A\<^sup>+" ?B] B_sub by blast
  qed
  moreover have "SN ?A"
    using fin unfolding finite_min_csr_dpp_def SN_rel_on_def .
  then have "SN (?A\<^sup>+)" by (rule SN_imp_SN_trancl)
  ultimately show False by contradiction
qed

datatype ('f, 'l, 'v) extended_csr_termination_proof =
    Direct_CSR_Proof "('f, 'l, 'v) csr_termination_proof"
  | Orthogonality_Checked_CSR_Proof
      "('f, 'l, 'v) csr_termination_proof"
  | Improved_CSR_Dependency_Pairs
      "('f, 'l) lab"
      "('f, 'l, 'v) trsLL"
      "('f, 'l, 'v) csr_dp_termination_proof"
  | CSR_Rule_Removal_Then_Improved
      "('f, 'l) lab redtriple_impl"
      "('f, 'l, 'v) trsLL"
      "('f, 'l) lab"
      "('f, 'l, 'v) trsLL"
      "('f, 'l, 'v) csr_dp_termination_proof"
  | Conservative_CSR_Dependency_Pairs
      "('f, 'l) lab"
      "('f, 'l, 'v) trsLL"
      "('f, 'l, 'v) trsLL"
      "('f, 'l, 'v) csr_dp_termination_proof"

fun check_extended_csr_termination_proof ::
  "('tp, ('f::{showl,compare_order,countable}, label_type) lab, string) tp_ops \<Rightarrow>
   ('dpp, ('f,label_type) lab, string) dpp_ops \<Rightarrow>
   bool \<Rightarrow> showsl \<Rightarrow> (('f,label_type) lab) muL \<Rightarrow>
   ('f,label_type,string) trsLL \<Rightarrow>
   ('f,label_type,string) extended_csr_termination_proof \<Rightarrow> showsl check"
where
  "check_extended_csr_termination_proof I J a i \<mu> R
      (Direct_CSR_Proof prf) =
    check_csr_termination_proof_min I J a i \<mu> R prf"
| "check_extended_csr_termination_proof I J a i \<mu> R
      (Orthogonality_Checked_CSR_Proof prf) =
    debug i (STR ''CSR orthogonality check'') (do {
      check_csr_orthogonal R
        <+? (\<lambda>s. i \<circ> showsl_lit
          (STR '': invalid orthogonality witness\<newline>'') \<circ> s);
      check_csr_termination_proof_min I J a (add_index i 1) \<mu> R prf
        <+? (\<lambda>s. i \<circ> showsl_lit
          (STR '': error below CSR orthogonality check\<newline>'') \<circ> s)
    })"
| "check_extended_csr_termination_proof I J a i \<mu> R
      (Improved_CSR_Dependency_Pairs U P prf) =
    debug i (STR ''improved CSR dependency pairs'') (do {
      dpp \<leftarrow> improved_csr_dependency_pairs_tt J U \<mu> R P
        <+? (\<lambda>s. i \<circ> showsl_lit
          (STR '': invalid improved CSR-DP transformation\<newline>'') \<circ> s);
      check_improved_csr_dp_termination_proof I J U \<mu> False
        (add_index i 1) dpp prf
        <+? (\<lambda>s. i \<circ> showsl_lit
          (STR '': error below improved CSR dependency pairs\<newline>'') \<circ> s)
    })"
| "check_extended_csr_termination_proof I J a i \<mu> R
      (CSR_Rule_Removal_Then_Improved redp Rr U P prf) =
    debug i (STR ''CSR rule removal followed by improved CSR dependency pairs'') (do {
      r2 \<leftarrow> csr_rule_removal_impl redp \<mu> Rr R;
      dpp \<leftarrow> improved_csr_dependency_pairs_tt J U \<mu> r2 P
        <+? (\<lambda>s. i \<circ> showsl_lit
          (STR '': invalid improved CSR-DP transformation after CSR rule removal\<newline>'') \<circ> s);
      check_improved_csr_dp_termination_proof I J U \<mu> False
        (add_index i 1) dpp prf
        <+? (\<lambda>s. i \<circ> showsl_lit
          (STR '': error below improved CSR dependency pairs after CSR rule removal\<newline>'') \<circ> s)
    })"
| "check_extended_csr_termination_proof I J a i \<mu> R
      (Conservative_CSR_Dependency_Pairs U P S prf) =
    debug i (STR ''conservative CSR dependency pairs'') (do {
      dpp \<leftarrow> conservative_csr_dependency_pairs_tt J U \<mu> R P S
        <+? (\<lambda>s. i \<circ> showsl_lit
          (STR '': invalid conservative CSR-DP transformation\<newline>'') \<circ> s);
      check_csr_dp_termination_proof I J False (add_index i 1) dpp prf
        <+? (\<lambda>s. i \<circ> showsl_lit
          (STR '': error below conservative CSR dependency pairs\<newline>'') \<circ> s)
    })"

lemma check_extended_csr_termination_proof_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_extended_csr_termination_proof
      I J a i \<mu> R prf)"
  shows "SN (sig_step (set (funas_trs_list R))
    (csstep (mu_of \<mu>) (set R)))"
  using ok
proof (cases "prf")
  case (Direct_CSR_Proof old)
  from ok Direct_CSR_Proof have old_ok:
    "isOK (check_csr_termination_proof_min I J a i \<mu> R old)"
    by simp
  have global: "SN (csstep (mu_of \<mu>) (set R))"
    by (rule check_csr_termination_proof_min_sound[OF I J old_ok])
  show ?thesis
    by (rule SN_subset[OF global], unfold sig_step_def, auto)
next
  case (Orthogonality_Checked_CSR_Proof child)
  from ok Orthogonality_Checked_CSR_Proof have child_ok:
    "isOK (check_csr_termination_proof_min I J a (add_index i 1) \<mu> R child)"
    by auto
  have global: "SN (csstep (mu_of \<mu>) (set R))"
    by (rule check_csr_termination_proof_min_sound[OF I J child_ok])
  show ?thesis
    by (rule SN_subset[OF global], unfold sig_step_def, auto)
next
  case (Improved_CSR_Dependency_Pairs U P dp_prf)
  from ok Improved_CSR_Dependency_Pairs
  obtain dpp where tt:
      "improved_csr_dependency_pairs_tt J U \<mu> R P = Inr dpp"
    and rec:
      "isOK (check_improved_csr_dp_termination_proof
        I J U \<mu> False (add_index i 1) dpp dp_prf)"
    by auto
  from improved_csr_dependency_pairs_tt_sound[OF J tt]
  have dpp: "dpp = dpp_ops.mk J False False P [] [] [] R"
    and wf: "wf_trs (set R)"
    and fresh_U: "\<And>n. (U,n) \<notin> set (funas_trs_list R)"
    and unsharp: "\<not> is_sharp_lab U"
    and fresh_sharp: "\<And>f n. \<not> defined (set R) (Sharp f,n)"
    and cover: "improved_csdp_coverage Sharp U (mu_of \<mu>)
      (set (defined_list R)) (set R) (set P)"
    by auto
  interpret dpp_spec J by fact
  have sem: "dpp_ops.dpp J dpp =
      (False, False, set P, {}, {}, {}, set R)"
    using dpp dpp_spec.mk_sound[OF J] by simp
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
  have fresh_dpp: "\<And>f n. \<not> defined (set (rules dpp)) (Sharp f,n)"
    using fresh_sharp rules by simp
  have fresh_U': "\<And>n. \<not> defined (set R) (U,n)"
  proof
    fix n
    assume def: "defined (set R) (U,n)"
    from def obtain l r where lr: "(l,r) \<in> set R"
      and root: "root l = Some (U,n)"
      unfolding defined_def by blast
    have root_mem: "(U,n) \<in> funas_term l"
      using root by (cases l, auto)
    have mem: "(U,n) \<in> set (funas_trs_list R)"
      using lr root_mem
      by (force simp: funas_trs_def funas_rule_def)
    with fresh_U show False by contradiction
  qed
  have fresh_U_dpp: "\<And>n. \<not> defined (set (rules dpp)) (U,n)"
    using fresh_U' rules by simp
  have fin_dpp: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (pairs dpp)) (set (rules dpp))"
    by (rule check_improved_csr_dp_termination_proof_sound[
        OF I J plain wf_dpp fresh_dpp fresh_U_dpp unsharp rec])
  have fin: "finite_min_csr_dpp Sharp (mu_of \<mu>) (set P) (set R)"
    using fin_dpp unfolding rules pairs .
  have defs: "{f. defined (set R) f} \<subseteq> set (defined_list R)"
    by auto
  have global: "SN (csstep (mu_of \<mu>) (set R))"
    by (rule finite_min_improved_CSDP_imp_SN_csstep[
        OF wf defs cover fresh_U' unsharp fresh_sharp fin])
  show ?thesis
    by (rule SN_subset[OF global], unfold sig_step_def, auto)
next
  case (CSR_Rule_Removal_Then_Improved redp rr u ps dp_prf)
  from ok CSR_Rule_Removal_Then_Improved have remove_ok:
    "isOK (csr_rule_removal_impl redp \<mu> rr R)"
    by simp
  then obtain r2 where remove:
      "csr_rule_removal_impl redp \<mu> rr R = Inr r2"
    by (cases "csr_rule_removal_impl redp \<mu> rr R", auto)
  from ok CSR_Rule_Removal_Then_Improved remove have tt_ok:
    "isOK (improved_csr_dependency_pairs_tt J u \<mu> r2 ps)"
    by simp
  then obtain dpp where tt:
      "improved_csr_dependency_pairs_tt J u \<mu> r2 ps = Inr dpp"
    by (cases "improved_csr_dependency_pairs_tt J u \<mu> r2 ps", auto)
  from ok CSR_Rule_Removal_Then_Improved remove tt have rec:
    "isOK (check_improved_csr_dp_termination_proof
      I J u \<mu> False (add_index i 1) dpp dp_prf)"
    by simp
  from improved_csr_dependency_pairs_tt_sound[OF J tt]
  have dpp: "dpp = dpp_ops.mk J False False ps [] [] [] r2"
    and wf: "wf_trs (set r2)"
    and fresh_U: "\<And>n. (u,n) \<notin> set (funas_trs_list r2)"
    and unsharp: "\<not> is_sharp_lab u"
    and fresh_sharp: "\<And>f n. \<not> defined (set r2) (Sharp f,n)"
    and cover: "improved_csdp_coverage Sharp u (mu_of \<mu>)
      (set (defined_list r2)) (set r2) (set ps)"
    by auto
  interpret dpp_spec J by fact
  have sem: "dpp_ops.dpp J dpp =
      (False, False, set ps, {}, {}, {}, set r2)"
    using dpp dpp_spec.mk_sound[OF J] by simp
  have sem': "dpp_ops.dpp J dpp =
      (NFS dpp, M dpp, set (local.P dpp), set (Pw dpp), set (Q dpp),
        set (local.R dpp), set (Rw dpp))"
    by (rule dpp_sound)
  have plain: "plain_csr_dpp J dpp"
    using sem sem' unfolding plain_csr_dpp_def by auto
  have rules: "set (rules dpp) = set r2"
    using sem sem' rules_sound[of dpp] by auto
  have pairs: "set (pairs dpp) = set ps"
    using sem sem' pairs_sound[of dpp] by auto
  have wf_dpp: "wf_trs (set (rules dpp))"
    using wf rules by simp
  have fresh_dpp: "\<And>f n. \<not> defined (set (rules dpp)) (Sharp f,n)"
    using fresh_sharp rules by simp
  have fresh_U': "\<And>n. \<not> defined (set r2) (u,n)"
  proof
    fix n
    assume def: "defined (set r2) (u,n)"
    from def obtain l r where lr: "(l,r) \<in> set r2"
      and root: "root l = Some (u,n)"
      unfolding defined_def by blast
    have root_mem: "(u,n) \<in> funas_term l"
      using root by (cases l, auto)
    have mem: "(u,n) \<in> set (funas_trs_list r2)"
      using lr root_mem
      by (force simp: funas_trs_def funas_rule_def)
    with fresh_U show False by contradiction
  qed
  have fresh_U_dpp: "\<And>n. \<not> defined (set (rules dpp)) (u,n)"
    using fresh_U' rules by simp
  have fin_dpp: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (pairs dpp)) (set (rules dpp))"
    by (rule check_improved_csr_dp_termination_proof_sound[
        OF I J plain wf_dpp fresh_dpp fresh_U_dpp unsharp rec])
  have fin: "finite_min_csr_dpp Sharp (mu_of \<mu>) (set ps) (set r2)"
    using fin_dpp unfolding rules pairs .
  have defs: "{f. defined (set r2) f} \<subseteq> set (defined_list r2)"
    by auto
  have residual: "SN (csstep (mu_of \<mu>) (set r2))"
    by (rule finite_min_improved_CSDP_imp_SN_csstep[
        OF wf defs cover fresh_U' unsharp fresh_sharp fin])
  have global: "SN (csstep (mu_of \<mu>) (set R))"
    by (rule csr_rule_removal_impl[OF remove residual])
  show ?thesis
    by (rule SN_subset[OF global], unfold sig_step_def, auto)
next
  case (Conservative_CSR_Dependency_Pairs U P S dp_prf)
  from ok Conservative_CSR_Dependency_Pairs
  obtain dpp where tt:
      "conservative_csr_dependency_pairs_tt J U \<mu> R P S = Inr dpp"
    and rec:
      "isOK (check_csr_dp_termination_proof
        I J False (add_index i 1) dpp dp_prf)"
    by auto
  have fin: "finite_dpp (dpp_ops.dpp J dpp)"
    by (rule check_csr_dp_termination_proof_sound[OF I J rec])
  show ?thesis
    by (rule conservative_csr_dependency_pairs_tt_finite_imp_SN_sig[
      OF J tt fin])
qed

end
