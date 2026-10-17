(* Independently discharge the GM04 DP premise with an explicit CSR child. *)
theory GM04_Standalone_DP_Checker
  imports "Proof_Checker.GM04_Complete_Checker"
begin

datatype ('f,'l,'v) gm04_standalone_dp_proof =
  GM04_Standalone_DP_Proof
    "(('f,'l) lab \<times> nat) list" "('f,'l) lab muL" "('f,'l,'v) trsLL"
    "('f,'l) lab" "('f,'l) lab" "('f,'l) lab" "('f,'l) lab"
    "('f,'l) lab" "('f,'l) lab"
    "('f,'l,'v) dp_termination_proof"
    "('f,'l,'v) gm_extended_csr_termination_proof"

fun check_gm04_standalone_dp_proof ::
  "('tp, ('f::{showl,compare_order,countable},label_type) lab,string) tp_ops \<Rightarrow>
   ('dpp, ('f,label_type) lab,string) dpp_ops \<Rightarrow> showsl \<Rightarrow> 'dpp \<Rightarrow>
   ('f,label_type,string) gm04_standalone_dp_proof \<Rightarrow> showsl check"
where
  "check_gm04_standalone_dp_proof I J i dpp
    (GM04_Standalone_DP_Proof F \<mu> R active mark proper ok top_sym top_sharp child source_child) =
    debug i (STR ''standalone Giesl-Middeldorp residual with CSR child'') (do {
      check_wf_trs R;
      check (set (funas_trs_list R) \<subseteq> set F)
        (showsl_lit (STR ''source signature is incomplete''));
      check (set F = set (funas_trs_list R) \<or> gm04_source_proof_is_global source_child)
        (showsl_lit (STR ''extended signature requires a global source proof''));
      check (gm04_roles_fresh_list active mark proper ok top_sym F)
        (showsl_lit (STR ''GM04 administrative roles are not fresh''));
      let S = gm04_non_top_rules (mu_of \<mu>) active mark proper ok F R;
      let P = gm04_top_pairs active mark proper ok top_sharp;
      check (gm04_schema_signature_list active mark proper ok F S)
        (showsl_lit (STR ''GM04 non-top signature is invalid''));
      check (gm04_pair_args_signature_list top_sharp P S)
        (showsl_lit (STR ''GM04 pair arguments escape the signature''));
      check (list_all (\<lambda>(f,n). f \<noteq> top_sharp) (funas_trs_list S))
        (showsl_lit (STR ''GM04 sharp role is not fresh''));
      check_gm_extended_csr_termination_proof I J False (add_index i 1) \<mu> R source_child;
      check_dp_termination_proof I J True (add_index i 2) dpp child;
      check (gm04_residual_assm P S (map fst S) (dp_assms True child))
        (showsl_lit (STR ''DP proof does not have exactly the certified GM04 premise''))
    })"

lemma check_gm04_standalone_dp_proof_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and checked: "isOK (check_gm04_standalone_dp_proof I J i dpp prf)"
  shows "finite_dpp (dpp_ops.dpp J dpp)"
proof (cases "prf")
  case (GM04_Standalone_DP_Proof F \<mu> R active mark proper ok_sym top_sym top_sharp child source_child)
  let ?S = "gm04_non_top_rules (mu_of \<mu>) active mark proper ok_sym F R"
  let ?P = "gm04_top_pairs active mark proper ok_sym top_sharp"
  from checked GM04_Standalone_DP_Proof have wf: "wf_trs (set R)"
    and signature: "funas_trs (set R) \<subseteq> set F"
    and global_or_same: "set F = set (funas_trs_list R) \<or> gm04_source_proof_is_global source_child"
    and fresh_list: "gm04_roles_fresh_list active mark proper ok_sym top_sym F"
    and schema_check: "gm04_schema_signature_list active mark proper ok_sym F ?S"
    and pair_check: "gm04_pair_args_signature_list top_sharp ?P ?S"
    and sharp_fresh: "list_all (\<lambda>(f,n). f \<noteq> top_sharp) (funas_trs_list ?S)"
    and source_ok: "isOK (check_gm_extended_csr_termination_proof I J False
      (add_index i 1) \<mu> R source_child)"
    and child_ok: "isOK (check_dp_termination_proof I J True (add_index i 2) dpp child)"
    and residual: "gm04_residual_assm ?P ?S (map fst ?S) (dp_assms True child)"
    by (simp_all add: Let_def)
  have source: "SN (sig_step (set F) (csstep (mu_of \<mu>) (set R)))"
  proof (cases "set F = set (funas_trs_list R)")
    case True
    have "SN (sig_step (set (funas_trs_list R)) (csstep (mu_of \<mu>) (set R)))"
      by (rule check_gm_extended_csr_termination_proof_sound[OF I J source_ok])
    with True show ?thesis by simp
  next
    case False
    with global_or_same have global: "gm04_source_proof_is_global source_child" by blast
    then obtain old where child: "source_child = Existing_CSR_Proof old"
      and old_global: "extended_csr_proof_is_global old"
      by (cases source_child) auto
    have global_source: "SN (csstep (mu_of \<mu>) (set R))"
      using check_gm_existing_global_sound[OF I J _ old_global] source_ok child by simp
    show ?thesis by (rule SN_subset[OF global_source], unfold sig_step_def, auto)
  qed
  have fresh: "gm04_roles_fresh active mark proper ok_sym top_sym F"
    by (rule gm04_roles_fresh_list_sound[OF fresh_list])
  have wf_S: "wf_trs (set ?S)" by (rule gm04_non_top_rules_wf[OF wf])
  have fresh_top: "\<not> defined (set ?S) (top_sharp,1)"
  proof
    assume def: "defined (set ?S) (top_sharp,1)"
    from defined_funas_trs[OF def] have "(top_sharp,1) \<in> set (funas_trs_list ?S)" by simp
    with sharp_fresh show False by (auto simp: list_all_iff)
  qed
  have pair_args: "funas_args_trs (set ?P) \<subseteq> funas_trs (set ?S)"
    by (rule gm04_pair_args_signature_list_sound[OF refl pair_check])
  have schema_sig: "funas_trs (set ?S) \<subseteq> set F \<union> {(active,1),(mark,1),(proper,1),(ok_sym,1)}"
    by (rule gm04_schema_signature_list_sound[OF schema_check])
  have finite_mu: "\<And>f n. finite (mu_of \<mu> (f,n))"
  proof -
    fix f n
    show "finite (mu_of \<mu> (f,n))" unfolding mu_of_def Let_def
      by (cases "map_of \<mu> (f,n)") simp_all
  qed
  have fin: "\<And>m. finite_dpp (True,m,set ?P,{},set (map fst ?S),set ?S,{})"
  proof -
    fix m
    have q: "set (map fst ?S) = lhss (set ?S)" by auto
    show "finite_dpp (True,m,set ?P,{},set (map fst ?S),set ?S,{})"
      unfolding q
      by (rule gm04_finite_schema_top_pairs_q_sig[
        OF gm04_inj_clean_string source refl fresh signature wf wf_S finite_mu fresh_top pair_args schema_sig])
  qed
  have assumptions: "\<forall>a\<in>set (dp_assms True child). holds a"
    by (rule gm04_residual_assm_holds[OF fin residual])
  show ?thesis by (rule check_dp_termination_proof_with_assms[OF I J child_ok assumptions])
qed

fun gm04_single_dp_assumption where
  "gm04_single_dp_assumption [Finite_assm [] d] = Some d"
| "gm04_single_dp_assumption _ = None"

lemma gm04_single_dp_assumption_sound:
  "gm04_single_dp_assumption xs = Some d \<Longrightarrow> xs = [Finite_assm [] d]"
  by (induct xs rule: gm04_single_dp_assumption.induct) auto

fun gm04_mk_dpp where
  "gm04_mk_dpp J (nfs,m,P,Pw,Q,R,Rw) = dpp_ops.mk J nfs m P Pw Q R Rw"

definition check_gm04_standalone_trs_proof where
  "check_gm04_standalone_trs_proof I J i tp context child =
    (case gm04_single_dp_assumption (sn_assms True child) of
      None \<Rightarrow> error (showsl_lit (STR ''expected one unconditional GM04 DP premise''))
    | Some d \<Rightarrow> do {
        check_gm04_standalone_dp_proof I J (add_index i 1) (gm04_mk_dpp J d) context;
        check_trs_termination_proof I J True (add_index i 2) tp child
      })"

lemma check_gm04_standalone_trs_proof_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and checked: "isOK (check_gm04_standalone_trs_proof I J i tp context child)"
  shows "SN_qrel (tp_ops.qreltrs I tp)"
proof -
  obtain d where single: "gm04_single_dp_assumption (sn_assms True child) = Some d"
    and dp: "isOK (check_gm04_standalone_dp_proof I J (add_index i 1) (gm04_mk_dpp J d) context)"
    and trs: "isOK (check_trs_termination_proof I J True (add_index i 2) tp child)"
    using checked unfolding check_gm04_standalone_trs_proof_def
    by (auto split: option.splits)
  interpret J: dpp_spec J by fact
  have fin: "finite_dpp (mk_dpp_set d)"
    using check_gm04_standalone_dp_proof_sound[OF I J dp]
    by (cases d) (simp add: J.mk_sound)
  have assumptions: "\<forall>a\<in>set (sn_assms True child). holds a"
    using gm04_single_dp_assumption_sound[OF single] fin by simp
  show ?thesis by (rule check_trs_termination_proof_with_assms[OF I J trs assumptions])
qed

end
