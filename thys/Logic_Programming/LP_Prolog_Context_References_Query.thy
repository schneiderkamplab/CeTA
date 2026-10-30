theory LP_Prolog_Context_References_Query
 imports LP_Prolog_Context_Query LP_Prolog_Context_References
begin

definition lpp_check_context_reference_root where
  "lpp_check_context_reference_root fuel P Q modules nds states contexts T typings returned arity actions i =
    (i<length nds \<and> contexts!i=([],[],[]) \<and>
      lpp_check_reference_modules fuel P Q T modules \<and>
      lpp_check_context_reference fuel P Q (map lpp_reference_data modules) nds states contexts T typings returned arity actions)"

theorem lpp_context_reference_root_domain_SN:
  fixes SP :: "string lpp_success_clause list"
  assumes checked: "lpp_check_context_reference_root fuel P Q modules nds states contexts T typings returned arity actions i"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
    and residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]}"
  shows "SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
    {map fst (lpc_return_eval eta (states!i))}"
proof -
  have references: "list_all (lpp_context_data_semantics SP P Q) (map lpp_reference_data modules)"
    by (rule lpp_reference_modules_semantics[where fuel=fuel, OF _ transfer program])
      (use checked in \<open>simp add: lpp_check_context_reference_root_def\<close>)
  have contract: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
    (lpc_return_eval eta (states!i)) (lp_ild Q)
    [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
    by (rule lpp_context_reference_contract[OF _ references transfer _ program _ known residual])
      (use checked in \<open>auto simp: lpp_check_context_reference_root_def lpp_path_context_holds_def\<close>)
  show ?thesis by (rule lpp_domain_instrumentation_SN)
    (use contract in \<open>simp add: lp_answer_contract_def\<close>)
qed

definition lpp_check_context_reference_query where
  "lpp_check_context_reference_query fuel P Q modules nds states contexts T typings returned arity actions i q modes =
    (lp_cut_source_program P \<and>
     lpp_check_context_reference_root fuel P Q modules nds states contexts T typings returned arity actions i \<and>
     lp_cut_check_root q modes (lpcn_vars (nds!i)) (lpcn_state (nds!i))
       (lpcn_ground (nds!i)) (lpcn_guards (nds!i)))"

theorem lpp_context_reference_query_sound:
  fixes SP :: "string lpp_success_clause list"
    and ts :: "(string lp_cut_symbol,string) term list"
    and p d :: "string lp_cut_symbol\<Rightarrow>'b"
  assumes checked: "lpp_check_context_reference_query fuel P Q modules nds states contexts T typings returned arity actions i q modes"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and len: "length ts=length modes"
    and ground: "\<And>j. j\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!j)"
    and child: "\<And>us::('b,string) term list. length us=length modes \<Longrightarrow>
      (\<And>j. j\<in>set (lpc_positions modes) \<Longrightarrow> ground (us!j)) \<Longrightarrow>
      SN_on (lp_ild (lp_roles_program p d Q))
        {[(p (lpcn_pred (nds!i)),map (\<lambda>t. lp_ieval t LPIVar) us)]}"
  shows "SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
proof (rule lpp_context_query_contract_sound[where p=p and d=d, OF _ _ _ len ground child])
  show "lp_cut_check_root q modes (lpcn_vars (nds!i)) (lpcn_state (nds!i))
    (lpcn_ground (nds!i)) (lpcn_guards (nds!i))"
    using checked by (simp add: lpp_check_context_reference_query_def)
  show "map fst (states!i)=lpcn_state (nds!i)"
    using checked by (auto simp: lpp_check_context_reference_query_def lpp_check_context_reference_root_def lpp_check_context_reference_def list_all_iff)
next
  fix eta
  assume known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
    and residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]}"
  show "SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
    {map fst (lpc_return_eval eta (states!i))}"
    by (rule lpp_context_reference_root_domain_SN[OF _ transfer _ known residual])
      (use checked in \<open>auto simp: lpp_check_context_reference_query_def\<close>)
qed

ML \<open>
val checked = [@{thm lpp_context_reference_query_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted contextual source query dependency" else ();
\<close>
end
