theory LP_Prolog_Context_Query
 imports LP_Prolog_Context_Graph LP_Prolog_Return_XML
begin
theorem lpp_context_query_contract_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
    and p d :: "string lp_cut_symbol\<Rightarrow>'b"
  assumes root: "lp_cut_check_root q modes (lpcn_vars (nds!r)) (lpcn_state (nds!r))
      (lpcn_ground (nds!r)) (lpcn_guards (nds!r))"
    and state: "map fst (states!r)=lpcn_state (nds!r)"
    and contract_rule: "\<And>eta. lp_cut_knowledge (set (lpcn_ground (nds!r))) (lpcn_guards (nds!r)) eta \<Longrightarrow>
      SN_on (lp_ild Q) {[(lpcn_pred (nds!r),map eta (lpcn_vars (nds!r)))]} \<Longrightarrow>
      SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) {map fst (lpc_return_eval eta (states!r))}"
    and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
    and child: "\<And>us::('b,string) term list. length us=length modes \<Longrightarrow>
      (\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (us!i)) \<Longrightarrow>
      SN_on (lp_ild (lp_roles_program p d Q))
        {[(p (lpcn_pred (nds!r)),map (\<lambda>t. lp_ieval t LPIVar) us)]}"
  shows "SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
proof -
  let ?nd = "nds!r"
  let ?vs = "lpcn_vars ?nd"
  let ?vals = "map (\<lambda>t. lp_ieval t LPIVar) ts"
  let ?env = "lp_cut_query_env ?vs ?vals"
  have lengths: "length ?vs=length ?vals" and distinct: "distinct ?vs"
    using root len by (auto simp: lp_cut_check_root_def)
  have vals: "map ?env ?vs=?vals" by (rule lp_cut_query_env_values[OF lengths distinct])
  have finite_index: "\<And>i. i<length modes \<Longrightarrow> modes!i \<Longrightarrow> lp_seg_ground (?vals!i)"
    using ground len by (auto simp: lpc_positions_def lp_seg_ground_eval ground_vars_term_empty)
  have finite: "\<forall>(t,b)\<in>set (zip ?vals modes). b \<longrightarrow> lp_seg_ground t"
    using finite_index len by (auto simp: in_set_zip)
  have finite': "\<forall>(t,b)\<in>set (zip (map ?env ?vs) modes). b \<longrightarrow> lp_seg_ground t"
    using finite by (simp only: vals)
  have known: "lp_cut_knowledge (set (lpcn_ground ?nd)) (lpcn_guards ?nd) ?env"
    using root finite' by (auto simp: lp_cut_check_root_def lp_cut_knowledge_def zip_map1)
  have mapped: "SN_on (lp_ild (lp_roles_program p d Q))
    {[(p (lpcn_pred ?nd),map (\<lambda>t. lp_ieval t LPIVar) (map (map_term d id) ts))]}"
    by (rule child) (use len ground in \<open>auto simp: lpc_positions_def\<close>)
  have residual: "SN_on (lp_ild Q) {[(lpcn_pred ?nd,map ?env ?vs)]}"
    by (rule lp_roles_termination_reflect[where p=p and d=d])
      (use mapped vals in \<open>simp add: lp_roles_iatom_def map_map o_def lp_map_finite_eval\<close>)
  have contract: "SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) {map fst (lpc_return_eval ?env (states!r))}"
    by (rule contract_rule[OF known residual])
  have source: "SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) {lp_cut_state_eval (lpcn_state ?nd) ?env}"
    using contract by (simp add: lpc_return_eval_erases state)
  show ?thesis using source root vals
    by (simp add: lp_cut_check_root_def lp_cut_state_map_def map_map o_def)
qed

definition lpp_check_context_query where
  "lpp_check_context_query fuel P Q nds states contexts T typings returned arity actions i q modes =
    (lp_cut_source_program P \<and>
     lpp_check_context_root fuel P Q nds states contexts T typings returned arity actions i \<and>
     lp_cut_check_root q modes (lpcn_vars (nds!i)) (lpcn_state (nds!i))
       (lpcn_ground (nds!i)) (lpcn_guards (nds!i)))"

theorem lpp_context_query_sound:
  fixes SP :: "string lpp_success_clause list"
    and ts :: "(string lp_cut_symbol,string) term list"
    and p d :: "string lp_cut_symbol\<Rightarrow>'b"
  assumes checked: "lpp_check_context_query fuel P Q nds states contexts T typings returned arity actions i q modes"
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
    using checked by (simp add: lpp_check_context_query_def)
  show "map fst (states!i)=lpcn_state (nds!i)"
    using checked by (auto simp: lpp_check_context_query_def lpp_check_context_root_def lpp_check_context_graph_def list_all_iff)
next
  fix eta
  assume known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
    and residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]}"
  show "SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
    {map fst (lpc_return_eval eta (states!i))}"
    by (rule lpp_context_root_domain_SN[OF _ transfer _ known residual])
      (use checked in \<open>auto simp: lpp_check_context_query_def\<close>)
qed

ML \<open>
val checked = [@{thm lpp_context_query_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted contextual source query dependency" else ();
\<close>
end
