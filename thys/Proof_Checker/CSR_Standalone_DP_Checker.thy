theory CSR_Standalone_DP_Checker
  imports CSR_Guarded_List_Measure_Check.CSR_Guarded_List_Checker
begin

text \<open>A residual obligation, not a new dependency-pair construction.  In
particular P need not contain the original construction's deleted pairs.
Minimality is the CSR chain condition; the internal ordinary-DP minimality
flag stays False, as in the root improved-CSR checker.\<close>

definition check_standalone_nonminimal_csr_dp where
  "check_standalone_nonminimal_csr_dp I J i \<mu> P R prf =
    (case prf of Guarded_CSR_DP_Existing p \<Rightarrow>
      check_csr_dp_termination_proof_core I J \<mu> False i
        (dpp_ops.mk J False False P [] [] [] R) p
    | _ \<Rightarrow> error (showsl_lit
        (STR ''this CSR processor requires minimality'')))"

lemma check_standalone_nonminimal_csr_dp_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_standalone_nonminimal_csr_dp I J i \<mu> P R prf)"
  shows "finite_csr_dpp Sharp (mu_of \<mu>) (set P) (set R)"
proof -
  define d where "d = dpp_ops.mk J False False P [] [] [] R"
  obtain p where checked:
    "isOK (check_csr_dp_termination_proof_core I J \<mu> False i d p)"
    using ok unfolding check_standalone_nonminimal_csr_dp_def d_def
    by (cases "prf", auto)
  interpret dpp_spec J by fact
  have sem: "dpp_ops.dpp J d = (False, False, set P, {}, {}, {}, set R)"
    by (simp add: d_def dpp_spec.mk_sound[OF J])
  have sem': "dpp_ops.dpp J d =
      (NFS d, M d, set (local.P d), set (Pw d), set (Q d),
       set (local.R d), set (Rw d))"
    by (rule dpp_sound)
  have plain: "plain_csr_dpp J d"
    using sem sem' unfolding plain_csr_dpp_def by auto
  have rules: "set (rules d) = set R"
    using sem sem' rules_sound[of d] by auto
  have pairs: "set (pairs d) = set P"
    using sem sem' pairs_sound[of d] by auto
  from check_csr_dp_termination_proof_core_sound[OF I J plain checked]
  show ?thesis unfolding pairs rules .
qed

definition check_standalone_minimal_csr_dp ::
  "('tp, ('f::{showl,compare_order,countable},label_type) lab, string) tp_ops \<Rightarrow>
   ('dpp, ('f,label_type) lab, string) dpp_ops \<Rightarrow>
   showsl \<Rightarrow> bool \<Rightarrow> ('f,label_type) lab \<Rightarrow>
   (('f,label_type) lab) muL \<Rightarrow>
   (('f,label_type) lab,string) rules \<Rightarrow>
   (('f,label_type) lab,string) rules \<Rightarrow>
   ('f,label_type,string) guarded_csr_dp_proof \<Rightarrow> showsl check"
where
  "check_standalone_minimal_csr_dp I J i m U \<mu> P R prf = do {
    check m (showsl_lit (STR ''standalone improved CSR-DPs require CSR minimality''));
    check_wf_trs R;
    check_allm (\<lambda>(f,n). check (\<not> is_sharp_lab f \<and> f \<noteq> U)
      (showsl_lit (STR ''standalone CSR rules define a marked or unhiding symbol'')))
      (defined_list R);
    check (\<not> is_sharp_lab U)
      (showsl_lit (STR ''unhiding symbol must not be sharp''));
    check_guarded_improved_csr_dp_proof I J U \<mu> i
      (dpp_ops.mk J False False P [] [] [] R) prf
  }"

lemma check_standalone_minimal_csr_dp_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_standalone_minimal_csr_dp I J i m U \<mu> P R prf)"
  shows "m \<and> finite_min_csr_dpp Sharp (mu_of \<mu>) (set P) (set R)"
proof -
  note checked = ok[unfolded check_standalone_minimal_csr_dp_def, simplified]
  define d where "d = dpp_ops.mk J False False P [] [] [] R"
  let ?d = d
  from checked have m: m and wf: "wf_trs (set R)"
    and unsharp: "\<not> is_sharp_lab U"
    and rec: "isOK (check_guarded_improved_csr_dp_proof I J U \<mu> i ?d prf)"
    by (auto simp: d_def)
  have fresh_sharp: "\<And>f n. \<not> defined (set R) (Sharp f,n)"
    using checked by auto
  have fresh_U: "\<And>n. \<not> defined (set R) (U,n)"
    using checked by auto
  interpret dpp_spec J by fact
  have sem: "dpp_ops.dpp J ?d = (False, False, set P, {}, {}, {}, set R)"
    by (simp add: d_def dpp_spec.mk_sound[OF J])
  have sem': "dpp_ops.dpp J ?d =
      (NFS ?d, M ?d, set (local.P ?d), set (Pw ?d), set (Q ?d),
       set (local.R ?d), set (Rw ?d))"
    by (rule dpp_sound)
  have plain: "plain_csr_dpp J ?d"
    using sem sem' unfolding plain_csr_dpp_def by auto
  have rules: "set (rules ?d) = set R"
    using sem sem' rules_sound[of ?d] by auto
  have pairs: "set (pairs ?d) = set P"
    using sem sem' pairs_sound[of ?d] by auto
  have wf_d: "wf_trs (set (rules ?d))"
    using wf by (simp only: rules)
  have sharp_d: "\<And>f n. \<not> defined (set (rules ?d)) (Sharp f,n)"
    by (simp only: rules, rule fresh_sharp)
  have U_d: "\<And>n. \<not> defined (set (rules ?d)) (U,n)"
    by (simp only: rules, rule fresh_U)
  have fin: "finite_min_csr_dpp Sharp (mu_of \<mu>) (set (pairs ?d)) (set (rules ?d))"
    by (rule check_guarded_improved_csr_dp_proof_sound[
      OF I J plain wf_d sharp_d U_d unsharp rec])
  show ?thesis by (rule conjI[OF m], rule fin[unfolded pairs rules])
qed

definition check_standalone_improved_csr_dp where
  "check_standalone_improved_csr_dp I J i m U \<mu> P R prf =
    (if m then check_standalone_minimal_csr_dp I J i m U \<mu> P R prf
     else check_standalone_nonminimal_csr_dp I J i \<mu> P R prf)"

lemma check_standalone_improved_csr_dp_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_standalone_improved_csr_dp I J i m U \<mu> P R prf)"
  shows "if m then finite_min_csr_dpp Sharp (mu_of \<mu>) (set P) (set R)
    else finite_csr_dpp Sharp (mu_of \<mu>) (set P) (set R)"
  using ok check_standalone_minimal_csr_dp_sound[OF I J]
    check_standalone_nonminimal_csr_dp_sound[OF I J]
  unfolding check_standalone_improved_csr_dp_def by (cases m, auto)

end
